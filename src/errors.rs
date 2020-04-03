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

use rustc_middle::ty::TyCtxt;
use rustc_span::{FileLinesResult, Span, SpanLinesError};
use std;
use std::fmt;
use std::io;
use std::io::Write;
use std::sync::{Arc, Mutex};

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ErrorWithSpan {
    message: String,
    span: Span,
}

impl ErrorWithSpan {
    pub(crate) fn new<T: Into<String>>(message: T, span: Span) -> ErrorWithSpan {
        ErrorWithSpan {
            message: message.into(),
            span,
        }
    }

    pub(crate) fn with_snippet<'a, 'tcx>(self, tcx: TyCtxt<'tcx>) -> RerastError {
        RerastError {
            message: self.message,
            file_lines: Some(FileLines::from_lines_result(
                tcx.sess.source_map().span_to_lines(self.span),
            )),
        }
    }
}

impl From<ErrorWithSpan> for Vec<ErrorWithSpan> {
    fn from(error: ErrorWithSpan) -> Vec<ErrorWithSpan> {
        vec![error]
    }
}

pub struct RerastError {
    pub(crate) message: String,
    pub(crate) file_lines: Option<Result<FileLines, FileLinesError>>,
}

pub struct FileLines {
    pub(crate) file_name: rustc_span::FileName,
    pub(crate) lines: Vec<Line>,
}

pub struct Line {
    pub(crate) code: Option<String>,
    pub(crate) line_index: usize,
    pub(crate) start_col: usize,
    pub(crate) end_col: usize,
}

pub struct FileLinesError {
    message: String,
}

impl RerastError {
    fn with_message<T: Into<String>>(message: T) -> RerastError {
        RerastError {
            message: message.into(),
            file_lines: None,
        }
    }
}

impl FileLines {
    fn from_lines_result(file_lines_result: FileLinesResult) -> Result<FileLines, FileLinesError> {
        match file_lines_result {
            Ok(file_lines) => Ok(FileLines {
                file_name: file_lines.file.name.clone(),
                lines: file_lines
                    .lines
                    .iter()
                    .map(|line_info| Line {
                        code: file_lines
                            .file
                            .get_line(line_info.line_index)
                            .and_then(|code| Some(code.into_owned())),
                        line_index: line_info.line_index,
                        start_col: line_info.start_col.0,
                        end_col: line_info.end_col.0,
                    })
                    .collect(),
            }),
            Err(span_lines_error) => Err(FileLinesError {
                message: match span_lines_error {
                    SpanLinesError::DistinctSources(_) => {
                        format!("Unable to report location. Spans distinct sources")
                    }
                },
            }),
        }
    }
}

impl fmt::Display for FileLines {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(first_line) = self.lines.get(0) {
            writeln!(
                f,
                "    --> {}:{}:{}",
                self.file_name, first_line.line_index, first_line.start_col
            )?;
        }
        for line_info in &self.lines {
            if let Some(line) = &line_info.code {
                writeln!(f, "{}", line)?;
                writeln!(
                    f,
                    "{}{}",
                    " ".repeat(line_info.start_col),
                    "^".repeat(line_info.end_col - line_info.start_col)
                )?;
            } else {
                writeln!(
                    f,
                    "Error occurred on non-existent line {}",
                    line_info.line_index
                )?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for RerastError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "error: {}", self.message)?;
        match &self.file_lines {
            Some(Ok(file_lines)) => writeln!(f, "{}", file_lines)?,
            Some(Err(error)) => writeln!(f, "{}", error.message)?,
            None => {}
        }
        Ok(())
    }
}

impl fmt::Display for FileLinesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.message)
    }
}

pub struct RerastErrors(Vec<RerastError>);

impl RerastErrors {
    pub(crate) fn new(errors: Vec<RerastError>) -> RerastErrors {
        RerastErrors(errors)
    }
    pub fn with_message<T: Into<String>>(message: T) -> RerastErrors {
        RerastErrors(vec![RerastError::with_message(message)])
    }

    pub fn iter(&self) -> impl Iterator<Item = &RerastError> {
        self.0.iter()
    }
}

impl std::ops::Index<usize> for RerastErrors {
    type Output = RerastError;

    fn index(&self, index: usize) -> &RerastError {
        &self.0[index]
    }
}

impl fmt::Debug for RerastErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for RerastErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for error in &self.0 {
            writeln!(f, "{}", error)?;
        }
        Ok(())
    }
}

impl From<io::Error> for RerastErrors {
    fn from(err: io::Error) -> RerastErrors {
        RerastErrors::with_message(err.to_string())
    }
}

#[derive(Clone)]
pub(crate) struct DiagnosticOutput {
    storage: Arc<Mutex<Vec<u8>>>,
}

impl Write for DiagnosticOutput {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut storage = self.storage.lock().unwrap();
        storage.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl DiagnosticOutput {
    pub(crate) fn new() -> DiagnosticOutput {
        DiagnosticOutput {
            storage: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub(crate) fn errors(&self) -> RerastErrors {
        let storage = self.storage.lock().unwrap();
        if let Ok(output) = std::str::from_utf8(&storage) {
            RerastErrors(
                output
                    .lines()
                    .filter_map(|line| {
                        if let Ok(json) = json::parse(line) {
                            if let Some(rendered) = json["rendered"].as_str() {
                                return Some(RerastError::with_message(rendered));
                            }
                        }
                        None
                    })
                    .collect(),
            )
        } else {
            RerastErrors::with_message("Compiler emitted invalid UTF8")
        }
    }
}
