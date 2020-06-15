// Copyright 2020 Google Inc.
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

// This module is responsible for applying a replacement pattern based on matches found by the
// matching module. We produce an that replaces each top-level match with its replacement. Inner
// matches are applied as part of their respective top-level replacements.

use crate::matching::Match;
use crate::patterns::PatternElement;
use ra_syntax::TextSize;
use ra_text_edit::TextEdit;

pub(crate) fn matches_to_edit(
    matches: &[Match],
    replacement: &[PatternElement],
    file_source: &str,
    relative_start: TextSize,
) -> TextEdit {
    let mut edit_builder = ra_text_edit::TextEditBuilder::default();
    for m in matches {
        edit_builder.replace(
            m.range.checked_sub(relative_start).unwrap(),
            m.apply_placeholders(replacement, file_source),
        );
    }
    edit_builder.finish()
}

impl Match {
    fn apply_placeholders(&self, replacement: &[PatternElement], file_source: &str) -> String {
        let mut out = String::new();
        for r in replacement {
            match r {
                PatternElement::Token(t) => out.push_str(t.text.as_str()),
                PatternElement::Placeholder(p) => {
                    if let Some(placeholder_value) = self.placeholder_values.get(&p.ident) {
                        let range = &placeholder_value.range.range;
                        let mut matched_text = file_source
                            [usize::from(range.start())..usize::from(range.end())]
                            .to_owned();
                        matches_to_edit(
                            &placeholder_value.inner_matches,
                            replacement,
                            file_source,
                            range.start(),
                        )
                        .apply(&mut matched_text);
                        out.push_str(&matched_text);
                    } else {
                        // We validated that all placeholder references were valid before we
                        // started, so this shouldn't happen.
                        panic!(
                            "Internal error: replacement referenced unknown placeholder {}",
                            p.ident
                        );
                    }
                }
            }
        }
        out
    }
}
