// Copyright 2017 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use syntax::ext::quote::rt::Span;
use syntax::codemap::CodeMap;
use std::collections::{hash_map, HashMap};
use syntax_pos::{self, BytePos};
use std::path::PathBuf;
use itertools::Itertools;
use std::io;
use syntax::codemap::FileLoader;

pub(crate) struct SourceChunk<'a> {
    source: &'a str,
    start_pos: BytePos,
}

impl<'a> SourceChunk<'a> {
    pub(crate) fn new(source: &'a str, start_pos: BytePos) -> SourceChunk<'a> {
        SourceChunk { source, start_pos }
    }

    fn get_snippet(&self, lo: BytePos, hi: BytePos) -> &'a str {
        use syntax_pos::Pos;
        &self.source[(lo - self.start_pos).to_usize()..(hi - self.start_pos).to_usize()]
    }

    fn to_end_from(&self, from: BytePos) -> &'a str {
        use syntax_pos::Pos;
        &self.source[(from - self.start_pos).to_usize()..]
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct CodeSubstitution {
    // The span to be replaced.
    pub(crate) span: Span,
    // New code to replace what's at span.
    pub(crate) new_code: String,
    // Whether parenthesis are needed around the substitution.
    pub(crate) needs_parenthesis: bool,
}

impl CodeSubstitution {
    pub(crate) fn new(span: Span, new_code: String) -> CodeSubstitution {
        CodeSubstitution {
            span,
            new_code,
            needs_parenthesis: false,
        }
    }

    pub(crate) fn needs_parenthesis(mut self, needs_parenthesis: bool) -> CodeSubstitution {
        self.needs_parenthesis = needs_parenthesis;
        self
    }

    pub(crate) fn apply_with_codemap<'a>(
        substitutions: &[CodeSubstitution],
        codemap: &CodeMap,
        base_span: Span,
    ) -> String {
        let base_source = codemap.span_to_snippet(base_span).unwrap();
        CodeSubstitution::apply(
            substitutions,
            SourceChunk::new(&base_source, base_span.lo()),
        )
    }

    // Take the code represented by base_span and apply all the substitutions, returning the
    // resulting code. All spans for the supplied substitutions must be within base_span and must be
    // non-overlapping.
    pub(crate) fn apply<'a>(
        substitutions: &[CodeSubstitution],
        source_chunk: SourceChunk<'a>,
    ) -> String {
        let mut output = String::new();
        let mut span_lo = source_chunk.start_pos;
        for substitution in substitutions {
            output.push_str(source_chunk.get_snippet(span_lo, substitution.span.lo()));
            if substitution.needs_parenthesis {
                output.push('(');
            }
            output.push_str(&substitution.new_code);
            if substitution.needs_parenthesis {
                output.push(')');
            }
            span_lo = substitution.span.hi();
            // Macro invocations consume a ; that follows them. Check if the code we're replacing
            // ends with a ;. If it does and the new code doesn't then insert one. This may need to
            // be smarter, but hopefully this will do.
            let code_being_replaced =
                source_chunk.get_snippet(substitution.span.lo(), substitution.span.hi());
            if code_being_replaced.ends_with(';') && !substitution.new_code.ends_with(';') {
                output.push(';');
            }
        }
        output.push_str(source_chunk.to_end_from(span_lo));
        output
    }

    pub(crate) fn as_file_relative_substitutions(
        substitutions: Vec<CodeSubstitution>,
        codemap: &CodeMap,
    ) -> FileRelativeSubstitutions {
        let mut by_file: HashMap<PathBuf, Vec<CodeSubstitution>> = HashMap::new();
        let substitutions_grouped_by_file = substitutions
            .into_iter()
            .group_by(|subst| codemap.span_to_filename(subst.span));
        for (filename, file_substitutions) in &substitutions_grouped_by_file {
            if let syntax_pos::FileName::Real(ref path) = filename {
                let file_relative_for_file = by_file
                    .entry(path.to_path_buf())
                    .or_insert_with(Default::default);
                let filemap = codemap.get_filemap(&filename).unwrap();
                for subst in file_substitutions {
                    file_relative_for_file.push(subst.relative_to(filemap.start_pos));
                }
                file_relative_for_file.sort()
            }
        }
        FileRelativeSubstitutions {
            substitutions_by_filename: by_file,
        }
    }

    fn relative_to(mut self, new_lo: BytePos) -> CodeSubstitution {
        self.span = self.span
            .with_lo(self.span.lo() - new_lo)
            .with_hi(self.span.hi() - new_lo);
        self
    }
}

#[derive(Debug)]
pub struct FileRelativeSubstitutions {
    // Substitutions keyed by filename. Each vector of substitutions must be sorted.
    substitutions_by_filename: HashMap<PathBuf, Vec<CodeSubstitution>>,
}

impl FileRelativeSubstitutions {
    pub(crate) fn empty() -> FileRelativeSubstitutions {
        FileRelativeSubstitutions {
            substitutions_by_filename: HashMap::new(),
        }
    }

    pub fn merge(&mut self, other: FileRelativeSubstitutions) {
        for (filename, substitutions) in other.substitutions_by_filename {
            match self.substitutions_by_filename.entry(filename) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(substitutions);
                }
                hash_map::Entry::Occupied(mut entry) => {
                    let merged = entry.get_mut();
                    merged.extend(substitutions);
                    // Remove equal or overlapping substitutions.
                    // TODO: Issue warning for any overlapping substitutions that aren't equal.
                    let mut last_span_opt: Option<Span> = None;
                    merged.retain(|subst| {
                        let retain = if let Some(last_span) = last_span_opt {
                            last_span.hi() <= subst.span.lo()
                        } else {
                            true
                        };
                        last_span_opt = Some(subst.span);
                        retain
                    });
                }
            }
        }
    }

    pub fn updated_files(&self, file_loader: &FileLoader) -> io::Result<HashMap<PathBuf, String>> {
        let mut updated_files = HashMap::new();
        for (filename, substitutions) in &self.substitutions_by_filename {
            let source = file_loader.read_file(&filename)?;
            let mut output = CodeSubstitution::apply(
                substitutions,
                SourceChunk::new(&source, syntax_pos::BytePos(0)),
            );
            updated_files.insert(filename.clone(), output);
        }
        Ok(updated_files)
    }
}
