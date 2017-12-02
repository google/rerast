use std::io;
use syntax::ext::quote::rt::Span;
use rustc::ty::TyCtxt;
use std::fmt;
use syntax_pos::{FileLinesResult, SpanLinesError};
use std;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ErrorWithSpan {
    message: String,
    span: Span,
}

impl ErrorWithSpan {
    pub(crate) fn new<T: Into<String>>(message: T, span: Span) -> ErrorWithSpan {
        ErrorWithSpan {
            message: message.into(),
            span: span,
        }
    }

    pub(crate) fn with_snippet<'a, 'gcx>(self, tcx: TyCtxt<'a, 'gcx, 'gcx>) -> RerastError {
        RerastError {
            message: self.message,
            file_lines: Some(tcx.sess.codemap().span_to_lines(self.span)),
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
    pub(crate) file_lines: Option<FileLinesResult>,
}

impl fmt::Display for RerastError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "error: {}", self.message)?;
        match self.file_lines {
            Some(Ok(ref file_lines)) => {
                if let Some(first_line) = file_lines.lines.get(0) {
                    writeln!(
                        f,
                        "    --> {}:{}:{}",
                        file_lines.file.name,
                        first_line.line_index,
                        first_line.start_col.0
                    )?;
                }
                for line_info in &file_lines.lines {
                    if let Some(line) = file_lines.file.get_line(line_info.line_index) {
                        writeln!(f, "{}", line)?;
                        writeln!(
                            f,
                            "{}{}",
                            " ".repeat(line_info.start_col.0),
                            "^".repeat(line_info.end_col.0 - line_info.start_col.0)
                        )?;
                    } else {
                        writeln!(
                            f,
                            "Error occurred on non-existent line {}",
                            line_info.line_index
                        )?;
                    }
                }
            }
            Some(Err(ref span_lines_error)) => match *span_lines_error {
                SpanLinesError::IllFormedSpan(span) => {
                    writeln!(f, "Unable to report location. Ill-formed span: {:?}", span)?;
                }
                SpanLinesError::DistinctSources(_) => {
                    writeln!(f, "Unable to report location. Spans distinct sources")?;
                }
            },
            None => {}
        }
        Ok(())
    }
}

pub struct RerastErrors(Vec<RerastError>);

impl RerastErrors {
    pub(crate) fn new(errors: Vec<RerastError>) -> RerastErrors {
        RerastErrors(errors)
    }
    pub(crate) fn with_message<T: Into<String>>(message: T) -> RerastErrors {
        RerastErrors(vec![
            RerastError {
                message: message.into(),
                file_lines: None,
            },
        ])
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item=&'a RerastError> {
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for RerastErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.0 {
            write!(f, "{}\n", error)?;
        }
        Ok(())
    }
}

impl From<io::Error> for RerastErrors {
    fn from(err: io::Error) -> RerastErrors {
        RerastErrors::with_message(err.to_string())
    }
}
