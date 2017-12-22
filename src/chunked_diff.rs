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

use std::collections::VecDeque;
use colored::Colorize;
use diff;
use std::fmt;
use std::ops::Range;

pub fn print_diff(filename: &str, left: &str, right: &str) {
    println!("{}", format!("--- {}", filename).red());
    println!("{}", format!("+++ {}", filename).green());
    for chunk in chunked_diff(left, right, 3) {
        println!("{}", chunk);
    }
}

struct Chunk<'a> {
    lines: Vec<diff::Result<&'a str>>,
    left_range: Range<usize>,
    right_range: Range<usize>,
}

impl<'a> Chunk<'a> {
    fn new() -> Chunk<'a> {
        Chunk {
            lines: Vec::new(),
            left_range: 0..0,
            right_range: 0..0,
        }
    }
}

impl<'a> fmt::Display for Chunk<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "{}",
            format!(
                "@@ -{},{} +{},{} @@",
                self.left_range.start,
                self.left_range.len(),
                self.right_range.start,
                self.right_range.len()
            ).cyan()
        )?;
        for line in &self.lines {
            match *line {
                diff::Result::Left(l) => writeln!(f, "{}", format!("-{}", l).red())?,
                diff::Result::Right(r) => writeln!(f, "{}", format!("+{}", r).green())?,
                diff::Result::Both(l, _) => writeln!(f, " {}", l)?,
            }
        }
        Ok(())
    }
}

fn chunked_diff<'a>(left: &'a str, right: &'a str, context: usize) -> Vec<Chunk<'a>> {
    let mut chunks = Vec::new();
    let mut recent_common = VecDeque::new();
    let mut after_context_remaining = 0;
    let mut chunk = Chunk::new();
    let mut left_line_num = 1;
    let mut right_line_num = 1;
    for diff in diff::lines(left, right) {
        let line_delta = match diff {
            diff::Result::Left(_) => (1, 0),
            diff::Result::Right(_) => (0, 1),
            diff::Result::Both(_, _) => (1, 1),
        };
        left_line_num += line_delta.0;
        right_line_num += line_delta.1;
        match diff {
            diff::Result::Left(_) | diff::Result::Right(_) => {
                if chunk.lines.is_empty() {
                    chunk.left_range =
                        left_line_num - recent_common.len() - line_delta.0..left_line_num;
                    chunk.right_range =
                        right_line_num - recent_common.len() - line_delta.1..right_line_num;
                }
                chunk.left_range.end = left_line_num;
                chunk.right_range.end = right_line_num;
                chunk.lines.extend(recent_common.drain(0..));
                chunk.lines.push(diff);
                after_context_remaining = context;
            }
            diff::Result::Both(_, _) => if after_context_remaining > 0 {
                chunk.lines.push(diff);
                chunk.left_range.end = left_line_num;
                chunk.right_range.end = right_line_num;
                after_context_remaining -= 1;
            } else {
                recent_common.push_back(diff);
                if recent_common.len() > context {
                    if !chunk.lines.is_empty() {
                        chunks.push(chunk);
                        chunk = Chunk::new();
                    }
                    recent_common.pop_front();
                }
            },
        }
    }
    if !chunk.lines.is_empty() {
        chunks.push(chunk);
    }
    chunks
}

#[cfg(test)]
mod tests {
    use super::*;
    use colored;

    #[test]
    fn changed_at_start() {
        let chunks = chunked_diff("1\n2\n3\n", "3\n", 2);
        assert_eq!(chunks.len(), 1);
        colored::control::set_override(false);
        assert_eq!(format!("{}", chunks[0]), "@@ -1,4 +1,2 @@\n-1\n-2\n 3\n \n");
    }

    #[test]
    fn changed_at_end() {
        let chunks = chunked_diff("1\n2\n3\n", "1\n2\n", 2);
        assert_eq!(chunks.len(), 1);
        colored::control::set_override(false);
        assert_eq!(format!("{}", chunks[0]), "@@ -1,4 +1,3 @@\n 1\n 2\n-3\n \n");
    }

    #[test]
    fn two_chunks() {
        let chunks = chunked_diff("1\n2\n3\n4\n5\n", "2\n3\n4\n", 1);
        assert_eq!(chunks.len(), 2);
        colored::control::set_override(false);
        assert_eq!(format!("{}", chunks[0]), "@@ -1,2 +1,1 @@\n-1\n 2\n");
        assert_eq!(format!("{}", chunks[1]), "@@ -4,3 +3,2 @@\n 4\n-5\n \n");
    }
}
