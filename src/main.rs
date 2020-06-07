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

use argh::FromArgs;
use ra_syntax::ast::{self, AstNode, SourceFile};
use ra_syntax::{NodeOrToken, SmolStr, SyntaxElement, SyntaxKind, SyntaxNode};
use rowan;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Eq, PartialEq)]
struct Error {
    message: String,
}

impl Error {
    fn message(message: String) -> Error {
        Error { message }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

macro_rules! bail {
    ($e:expr) => {return Err($crate::Error::message($e.to_owned()))};
    ($fmt:expr, $($arg:tt)+) => {return Err($crate::Error::message(format!($fmt, $($arg)+)))}
}

#[derive(Debug, Clone)]
struct Token {
    kind: SyntaxKind,
    text: SmolStr,
}

enum PatternElement {
    Token(Token),
    Placeholder(Placeholder),
}

impl fmt::Debug for PatternElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternElement::Token(t) => write!(f, "\"{}\" - {:?}", t.text, t.kind),
            PatternElement::Placeholder(p) => write!(f, "${} - placeholder", p.ident),
        }
    }
}

fn parse_pattern(pattern_str: &str, remove_whitespace: bool) -> Result<Vec<PatternElement>, Error> {
    let mut result = Vec::new();
    let mut start = 0;
    let (tokens, errors) = ra_syntax::tokenize(pattern_str);
    if let Some(first_error) = errors.first() {
        bail!("Failed to parse pattern: {}", first_error);
    }
    let mut dollar = false;
    for token in tokens {
        let token_len = usize::from(token.len);
        let text = SmolStr::new(&pattern_str[start..start + token_len]);
        if dollar {
            if token.kind == SyntaxKind::IDENT {
                result.push(PatternElement::Placeholder(Placeholder {
                    ident: text,
                    terminator: None,
                }));
                dollar = false;
            } else {
                bail!("Missing placeholder name");
            }
        } else if text.as_str() == "$" {
            dollar = true;
        } else if !remove_whitespace || token.kind != SyntaxKind::WHITESPACE {
            let token = Token {
                kind: token.kind,
                text,
            };
            if let Some(PatternElement::Placeholder(last_placeholder)) = result.last_mut() {
                last_placeholder.terminator = Some(token.clone());
            }
            result.push(PatternElement::Token(token));
        }
        start += token_len;
    }
    if dollar {
        bail!("Placeholder ($) with no name");
    }
    Ok(result)
}

fn validate_rule(pattern: &[PatternElement], replacement: &[PatternElement]) -> Result<(), Error> {
    let mut defined_placeholders = std::collections::HashSet::new();
    for p in pattern {
        if let PatternElement::Placeholder(placeholder) = p {
            defined_placeholders.insert(&placeholder.ident);
        }
    }
    let mut undefined = Vec::new();
    for p in replacement {
        if let PatternElement::Placeholder(placeholder) = p {
            if !defined_placeholders.contains(&placeholder.ident) {
                undefined.push(format!("${}", placeholder.ident));
            }
        }
    }
    if !undefined.is_empty() {
        bail!(
            "Replacement contains undefined placeholders: {}",
            undefined.join(", ")
        );
    }
    Ok(())
}

struct Placeholder {
    ident: SmolStr,
    // The next token after this placeholder in the pattern, if any. When matching, we then consume
    // the outermost node that is followed by this token. This allows `$a: 1` to match `foo: 1`
    // instead of the placeholder consuming the whole thing then failing when we get to the `:`
    terminator: Option<Token>,
}

impl Placeholder {
    // Returns whether this placeholder should consume `code`.
    fn can_consume(&self, code: &SyntaxNode) -> bool {
        if let Some(SyntaxElement::Token(_)) = code.first_child_or_token() {
            // If code starts with a token not another node, then we have no choice but to consume
            // the current node. Note, this isn't needed for correctness, but helps when reporting
            // the reason why we didn't match. e.g. if the code is `(),` and the pattern is `$a:`
            // then we want to report that `,` didn't match `:` rather than having the placeholder
            // try to match a token (which normally can't happen) then report that `)` didn't match
            // `:`.
            return true;
        }
        // Figure out what the next token will be if we consume `code`.
        let next_token = match code.next_sibling_or_token() {
            Some(SyntaxElement::Node(next_node)) => next_node.first_token(),
            Some(SyntaxElement::Token(t)) => Some(t),
            None => None,
        };
        // If either there's no next token in the pattern or there's no next token in the code then
        // just consume the current node.
        match (&next_token, &self.terminator) {
            (None, _) => true,
            (_, None) => true,
            (Some(next), Some(terminator)) => *next.text() == terminator.text,
        }
    }
}

// An "error" indicating that matching failed. Use the fail_match! macro to create and return this.
struct MatchFailed {
    // Only present when --debug-snippet is set.
    reason: Option<String>,
}

/// Fails the current match attempt. If we're currently attempting to match some code that we
/// thought we were going to match, as indicated by the --debug-snippet flag, then populate the
/// reason field.
macro_rules! fail_match {
    ($s:expr, $e:expr) => {
        if $s.debug_active {
            return Err(MatchFailed { reason: Some(format!("{}", $e)) });
        }
        return Err(MatchFailed { reason: None })
    };
    ($s:expr, $fmt:expr, $($arg:tt)+) => {
        if $s.debug_active {
            return Err(MatchFailed { reason: Some(format!($fmt, $($arg)+)) });
        }
        return Err(MatchFailed { reason: None })
    };
}

fn indent(num_spaces: usize) -> String {
    std::iter::repeat(' ').take(num_spaces).collect()
}

fn print_tree(n: &SyntaxNode, depth: usize) {
    println!("{}{:?}", indent(depth), n.kind());
    for child_node_or_token in n.children_with_tokens() {
        match child_node_or_token {
            SyntaxElement::Node(child) => {
                print_tree(&child, depth + 2);
            }
            SyntaxElement::Token(token) => {
                println!("{}{:?}", indent(depth + 2), token);
            }
        }
    }
}

fn print_debug_start(search: &[PatternElement], code: &SyntaxNode) {
    println!("========= PATTERN ==========\n{:#?}\n", search);
    println!("\n============ AST ===========\n");
    print_tree(code, 0);
    println!("\n============================");
}

// Converts a RA NodeOrToken to a green NodeOrToken.
fn to_green_node_or_token(
    n: &ra_syntax::NodeOrToken<SyntaxNode, ra_syntax::SyntaxToken>,
) -> NodeOrToken<rowan::GreenNode, rowan::GreenToken> {
    match n {
        SyntaxElement::Node(n) => NodeOrToken::Node(n.green().clone()),
        SyntaxElement::Token(t) => NodeOrToken::Token(t.green().clone()),
    }
}

struct MatchState {
    debug_active: bool,
    placeholder_values: HashMap<SmolStr, SyntaxNode>,
}

type PatternIterator<'a> = std::iter::Peekable<std::slice::Iter<'a, PatternElement>>;

impl MatchState {
    fn matches(
        debug_active: bool,
        search: &[PatternElement],
        code: &SyntaxNode,
    ) -> Result<MatchState, MatchFailed> {
        let mut match_state = MatchState {
            debug_active,
            placeholder_values: HashMap::new(),
        };
        let mut pattern_iter = search.iter().peekable();
        match_state.attempt_match_node(&mut pattern_iter, code)?;
        if let Some(pattern_next) = pattern_iter.next() {
            fail_match!(
                match_state,
                "Code exhausted, but pattern still has content: {:?}",
                pattern_next
            );
        }
        Ok(match_state)
    }

    fn get_match(
        debug_active: bool,
        search: &[PatternElement],
        code: &SyntaxNode,
    ) -> Option<MatchState> {
        match Self::matches(debug_active, search, code) {
            Ok(state) => Some(state),
            Err(match_failed) => {
                if debug_active {
                    if let Some(reason) = match_failed.reason {
                        println!("{}", reason);
                    } else {
                        println!("Match failed, but no reason was given");
                    }
                }
                None
            }
        }
    }

    fn attempt_match_node(
        &mut self,
        pattern: &mut PatternIterator,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Handle placeholders.
        if let Some(PatternElement::Placeholder(placeholder)) = pattern.peek() {
            if placeholder.can_consume(code) {
                self.placeholder_values
                    .insert(placeholder.ident.clone(), code.clone());
                pattern.next();
                return Ok(());
            }
        }
        if code.kind() == SyntaxKind::TOKEN_TREE {
            self.attempt_match_token_tree(pattern, code)?;
        } else if code.kind() == SyntaxKind::RECORD_FIELD_LIST {
            self.attempt_match_record_field_list(pattern, &code)?;
        } else {
            self.attempt_match_node_children(pattern, &code)?;
        }

        Ok(())
    }

    fn attempt_match_node_children(
        &mut self,
        pattern: &mut PatternIterator,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        for child in code.children_with_tokens() {
            match child {
                SyntaxElement::Node(c) => self.attempt_match_node(pattern, &c)?,
                SyntaxElement::Token(c) => self.attempt_match_token(pattern, &c)?,
            }
        }
        Ok(())
    }

    // We want to allow the records to match in any order, so we have special matching logic for
    // them.
    fn attempt_match_record_field_list(
        &mut self,
        pattern: &mut PatternIterator,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        let pattern_start = pattern.clone();
        // Build a map keyed by field name.
        let mut fields_by_name = HashMap::new();
        for child in code.children() {
            if let Some(record) = ast::RecordField::cast(child.clone()) {
                if let Some(name) = record.field_name() {
                    fields_by_name.insert(name.text().clone(), child.clone());
                }
            }
        }
        for child in code.children_with_tokens() {
            match child {
                SyntaxElement::Node(_) => match pattern.peek() {
                    Some(PatternElement::Token(p)) => {
                        if let Some(c) = fields_by_name.remove(&p.text) {
                            self.attempt_match_node(pattern, &c)?;
                        }
                    }
                    Some(PatternElement::Placeholder(_)) => {
                        // If the pattern is using placeholders for field names then order
                        // independence doesn't make sense. Fall back to regular ordered matching.
                        *pattern = pattern_start;
                        return self.attempt_match_node_children(pattern, code);
                    }
                    None => {
                        // Nothing to do, we'll fail the match below due to unmatched fields.
                    }
                },
                SyntaxElement::Token(c) => self.attempt_match_token(pattern, &c)?,
            }
        }
        if let Some(unmatched_fields) = fields_by_name.keys().next() {
            fail_match!(
                self,
                "{} field(s) of a record literal failed to match, starting with {}",
                fields_by_name.len(),
                unmatched_fields
            );
        }
        Ok(())
    }

    fn attempt_match_token(
        &self,
        pattern: &mut PatternIterator,
        code: &ra_syntax::SyntaxToken,
    ) -> Result<(), MatchFailed> {
        // Ignore whitespace and comments.
        if code.kind().is_trivia() {
            return Ok(());
        }
        let code_text = code.text().to_string();
        // A token in the syntax tree might correspond to multiple tokens in the pattern. For
        // example, in the syntax tree `->` would be a single token of type THIN_ARROW, whereas in
        // the pattern it will be MINUS, R_ANGLE.
        let mut code_remaining = code_text.as_str();
        while !code_remaining.is_empty() {
            match pattern.next() {
                Some(PatternElement::Placeholder(_)) => {
                    // Not sure if this is actually reachable.
                    fail_match!(self, "Placeholders matching tokens is not yet implemented");
                }
                Some(PatternElement::Token(p)) => {
                    if code_remaining.starts_with(p.text.as_str()) {
                        code_remaining = &code_remaining[p.text.as_str().len()..];
                    } else {
                        fail_match!(
                            self,
                            "Pattern had token `{}` while code had token `{}`",
                            p.text,
                            code_text,
                        );
                    }
                }
                None => {
                    fail_match!(
                        self,
                        "Pattern exhausted, while code remains: `{}`",
                        code_remaining
                    );
                }
            }
        }
        Ok(())
    }

    // Placeholders have different semantics within token trees. Outside of token trees, a
    // placeholder can only match a single AST node, whereas in a token tree it can match a sequence
    // of tokens.
    fn attempt_match_token_tree(
        &mut self,
        pattern: &mut PatternIterator,
        code: &ra_syntax::SyntaxNode,
    ) -> Result<(), MatchFailed> {
        let mut children = code.children_with_tokens();
        while let Some(child) = children.next() {
            if let Some(PatternElement::Placeholder(_)) = pattern.peek() {
                if let Some(PatternElement::Placeholder(placeholder)) = pattern.next() {
                    let next_pattern_token = if let Some(PatternElement::Token(t)) = pattern.peek()
                    {
                        Some(t.text.to_string())
                    } else {
                        None
                    };
                    let mut matched = Vec::new();
                    matched.push(to_green_node_or_token(&child));
                    // Read code tokens util we reach one equal to the next token from our pattern
                    // or we reach the end of the token tree.
                    while let Some(next) = children.next() {
                        match &next {
                            SyntaxElement::Token(t) => {
                                if Some(t.to_string()) == next_pattern_token {
                                    pattern.next();
                                    break;
                                }
                            }
                            SyntaxElement::Node(n) => {
                                if let Some(first_token) = n.first_token() {
                                    if Some(first_token.to_string()) == next_pattern_token {
                                        // We have a subtree that starts with the next token in our pattern.
                                        self.attempt_match_token_tree(pattern, &n)?;
                                        break;
                                    }
                                }
                            }
                        };
                        matched.push(to_green_node_or_token(&next));
                    }
                    self.placeholder_values.insert(
                        placeholder.ident.clone(),
                        SyntaxNode::new_root(rowan::GreenNode::new(code.green().kind(), matched)),
                    );
                }
                continue;
            }
            // Match literal (non-placeholder) tokens.
            match child {
                SyntaxElement::Token(token) => {
                    // Ignore whitespace and comments.
                    if token.kind().is_trivia() {
                        continue;
                    }
                    if let Some(p) = pattern.next() {
                        if let PatternElement::Token(pattern_token) = p {
                            if *token.text() != pattern_token.text {
                                fail_match!(
                                    self,
                                    "Pattern had token {:?}, code had {:?}",
                                    pattern_token,
                                    token
                                );
                            }
                        } else {
                            // We peeked above to see if it was a placeholder.
                            unreachable!();
                        }
                    } else {
                        fail_match!(self,
                            "Reached end of pattern, but we're part way through a token tree at token {:?}",
                            token);
                    }
                }
                SyntaxElement::Node(node) => {
                    if node.kind() != SyntaxKind::TOKEN_TREE {
                        fail_match!(self, "Found unexpected node inside token tree {:?}", node);
                    }
                    self.attempt_match_token_tree(pattern, &node)?;
                }
            }
        }
        Ok(())
    }

    fn apply_placeholders(&self, replacement: &[PatternElement]) -> Result<SyntaxNode, Error> {
        let mut out = String::new();
        for r in replacement {
            match r {
                PatternElement::Token(t) => out.push_str(t.text.as_str()),
                PatternElement::Placeholder(p) => {
                    if let Some(placeholder_value) = self.placeholder_values.get(&p.ident) {
                        out.push_str(&placeholder_value.text().to_string());
                    } else {
                        // We validated that all placeholder references were valid before we started.
                        unreachable!();
                    }
                }
            }
        }
        // This almost certainly won't parse as a SourceFile, but all we need is to get out a
        // SyntaxNode that can later on be converted to text, so it doesn't matter. Parsing
        // preserves all text, even on error!
        Ok(SourceFile::parse(&out).tree().syntax().clone())
    }
}

#[derive(Debug)]
struct Match {
    matched_node: SyntaxNode,
    placeholder_values: HashMap<SmolStr, SyntaxNode>,
}

#[derive(Default)]
struct MatchFinder {
    debug_snippet: Option<String>,
}

impl MatchFinder {
    fn find_matches(&self, search: &[PatternElement], code: &SyntaxNode, matches: &mut Vec<Match>) {
        for c in code.children() {
            let debug_active =
                self.debug_snippet.is_some() && Some(c.text().to_string()) == self.debug_snippet;
            if debug_active {
                print_debug_start(search, &c);
            }
            if let Some(match_state) = MatchState::get_match(debug_active, &search, &c) {
                matches.push(Match {
                    matched_node: c.clone(),
                    placeholder_values: match_state.placeholder_values,
                });
            } else {
                self.find_matches(search, &c, matches);
            }
        }
    }

    fn find_match_str(&self, pattern_str: &str, code: &str) -> Result<Vec<String>, Error> {
        let mut matches = Vec::new();
        self.find_matches(
            &parse_pattern(pattern_str, true)?,
            SourceFile::parse(code).tree().syntax(),
            &mut matches,
        );
        return Ok(matches
            .into_iter()
            .map(|m| m.matched_node.text().to_string())
            .collect());
    }

    fn apply(
        &self,
        search: &[PatternElement],
        replace: &[PatternElement],
        code: &SyntaxNode,
    ) -> Result<SyntaxNode, Error> {
        let debug_active =
            self.debug_snippet.is_some() && Some(code.text().to_string()) == self.debug_snippet;
        if debug_active {
            print_debug_start(search, code);
        }
        if let Some(mut match_state) = MatchState::get_match(debug_active, &search, &code) {
            // Continue searching in each of our placeholders and make replacements there as well.
            for placeholder_value in match_state.placeholder_values.values_mut() {
                *placeholder_value = self.apply(search, replace, placeholder_value)?;
            }
            return match_state.apply_placeholders(replace);
        }
        let mut child_replacements = Vec::new();
        let mut changed = false;
        for child_node_or_token in code.children_with_tokens() {
            match child_node_or_token {
                SyntaxElement::Node(child) => {
                    let replacement = self.apply(search, replace, &child)?;
                    if replacement.parent().is_none() {
                        // If the returned child has no parent, then it's not the child that we passed in.
                        changed = true;
                    }
                    child_replacements.push(NodeOrToken::Node(replacement.green().clone()));
                }
                SyntaxElement::Token(token) => {
                    child_replacements.push(NodeOrToken::Token(token.green().clone()))
                }
            }
        }
        if changed {
            Ok(SyntaxNode::new_root(rowan::GreenNode::new(
                code.green().kind(),
                child_replacements,
            )))
        } else {
            Ok(code.clone())
        }
    }

    fn apply_str(&self, search: &str, replace: &str, code: &str) -> Result<String, Error> {
        let search = parse_pattern(search, true)?;
        let replace = parse_pattern(replace, false)?;
        validate_rule(&search, &replace)?;
        Ok(self
            .apply(&search, &replace, SourceFile::parse(code).tree().syntax())?
            .text()
            .to_string())
    }
}

/// Searches for and replaces code based on token trees.
#[derive(FromArgs)]
struct RerastConfig {
    /// pattern to search for.
    #[argh(option, short = 's')]
    search: String,

    /// what to replace matches with.
    #[argh(option)]
    replace: Option<String>,

    /// code in which to search.
    #[argh(option)]
    code: String,

    /// a snippet of code that you expect to match. When exactly this snippet is encountered, debug
    /// information will be printed during matching.
    #[argh(option)]
    debug_snippet: Option<String>,
}

fn main() -> Result<(), Error> {
    let config: RerastConfig = argh::from_env();
    let match_finder = MatchFinder {
        debug_snippet: config.debug_snippet,
    };
    if let Some(replace) = &config.replace {
        println!(
            "OUT: {}",
            match_finder.apply_str(&config.search, replace, &config.code)?
        );
    } else {
        let matches = match_finder.find_match_str(&config.search, &config.code)?;
        if matches.is_empty() {
            println!("No match found");
        } else {
            println!("Matches:");
            for m in matches {
                println!("{}", m);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find(pattern: &str, code: &str) -> Vec<String> {
        let match_finder = MatchFinder::default();
        match_finder.find_match_str(pattern, code).unwrap()
    }

    macro_rules! assert_matches {
        ($pat:expr, $code:expr, [$($expected:expr),*]) => {
            let r = find($pat, $code);
            let e = vec![$($expected),*].iter().map(|e: &&str| e.to_string()).collect::<Vec<String>>();
            if r != e && !e.is_empty() {
                println!(
                    "Test is about to fail, to debug run:\
                    \n  cargo run -- --code '{}' --search '{}' --debug-snippet '{}'",
                    $code, $pat, e[0]);
            }
            assert_eq!(r, e);
        };
    }

    macro_rules! assert_no_match {
        ($pat:expr, $code:expr) => {
            assert_matches!($pat, $code, []);
        };
    }

    #[test]
    fn ignores_whitespace() {
        assert_matches!("1+2", "fn f() -> i32 {1  +  2}", ["1  +  2"]);
        assert_matches!("1 + 2", "fn f() -> i32 {1+2}", ["1+2"]);
    }

    #[test]
    fn no_match() {
        assert_no_match!("1 + 3", "fn f() -> i32 {1  +  2}");
    }

    #[test]
    fn match_fn_return_type() {
        assert_matches!("->i32", "fn f() -> i32 {1  +  2}", ["-> i32"]);
    }

    #[test]
    fn match_fn_definition() {
        assert_matches!(
            "fn $a($b) $c",
            "fn f(a: i32) {bar()}",
            ["fn f(a: i32) {bar()}"]
        );
    }

    #[test]
    fn match_expr() {
        let code = "fn f() -> i32 {foo(40 + 2, 42)}";
        assert_matches!("foo($a, $b)", code, ["foo(40 + 2, 42)"]);
        assert_no_match!("foo($a, $b, $c)", code);
        assert_no_match!("foo($a)", code);
    }

    #[test]
    fn match_complex_expr() {
        let code = "fn f() -> i32 {foo(bar(40, 2), 42)}";
        assert_matches!("foo($a, $b)", code, ["foo(bar(40, 2), 42)"]);
        assert_no_match!("foo($a, $b, $c)", code);
        assert_no_match!("foo($a)", code);
        assert_matches!("bar($a, $b)", code, ["bar(40, 2)"]);
    }

    #[test]
    fn match_type() {
        assert_matches!("i32", "fn f() -> i32 {1  +  2}", ["i32"]);
        assert_matches!("Option<$a>", "fn f() -> Option<i32> {42}", ["Option<i32>"]);
        assert_no_match!("Option<$a>", "fn f() -> Result<i32, ()> {42}");
    }

    #[test]
    fn match_struct_instantiation() {
        assert_matches!(
            "Foo {bar: 1, baz: 2}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            ["Foo {bar: 1, baz: 2}"]
        );
        // Now with placeholders for all parts of the struct. If we're not careful here, then $a
        // will consume the whole record field (`bar: 1`) then the `:` in the pattern will fail to
        // match.
        assert_matches!(
            "Foo {$a: $b, $c: $d}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            ["Foo {bar: 1, baz: 2}"]
        );
        assert_matches!("Foo {}", "fn f() {Foo {}}", ["Foo {}"]);
    }

    #[test]
    fn match_reordered_struct_instantiation() {
        assert_matches!(
            "Foo {aa: 1, b: 2, ccc: 3}",
            "fn f() {Foo {b: 2, ccc: 3, aa: 1}}",
            ["Foo {b: 2, ccc: 3, aa: 1}"]
        );
        assert_no_match!("Foo {a: 1}", "fn f() {Foo {b: 1}}");
        assert_no_match!("Foo {a: 1}", "fn f() {Foo {a: 2}}");
        assert_no_match!("Foo {a: 1, b: 2}", "fn f() {Foo {a: 1}}");
        assert_no_match!("Foo {a: 1, b: 2}", "fn f() {Foo {b: 2}}");
        assert_no_match!("Foo {a: 1, }", "fn f() {Foo {a: 1, b: 2}}");
        assert_no_match!("Foo {a: 1, z: 9}", "fn f() {Foo {a: 1}}");
    }

    #[test]
    fn match_macro_invocation() {
        assert_matches!("foo!($a)", "fn() {foo(foo!(foo()))}", ["foo!(foo())"]);
        assert_matches!(
            "foo!(41, $a, 43)",
            "fn() {foo!(41, 42, 43)}",
            ["foo!(41, 42, 43)"]
        );
        assert_no_match!("foo!(50, $a, 43)", "fn() {foo!(41, 42, 43}");
        assert_no_match!("foo!(41, $a, 50)", "fn() {foo!(41, 42, 43}");
        assert_matches!("foo!($a())", "fn() {foo!(bar())}", ["foo!(bar())"]);
    }

    #[test]
    fn invalid_placeholder() {
        assert_eq!(
            MatchFinder::default().find_match_str("($)", "fn foo() {}"),
            Err(Error::message("Missing placeholder name".to_owned()))
        );
    }

    fn apply(search: &str, replace: &str, code: &str) -> Result<String, Error> {
        let match_finder = MatchFinder::default();
        match_finder.apply_str(search, replace, code)
    }

    #[test]
    fn replace_function_call() -> Result<(), Error> {
        assert_eq!(
            apply("foo()", "bar()", "fn f1() {foo(); foo();}")?,
            "fn f1() {bar(); bar();}"
        );
        Ok(())
    }

    #[test]
    fn replace_function_call_with_placeholders() -> Result<(), Error> {
        assert_eq!(
            apply("foo($a, $b)", "bar($b, $a)", "fn f1() {foo(5, 42)}")?,
            "fn f1() {bar(42, 5)}"
        );
        Ok(())
    }

    #[test]
    fn replace_nested_function_calls() -> Result<(), Error> {
        assert_eq!(
            apply("foo($a)", "bar($a)", "fn f1() {foo(foo(42))}")?,
            "fn f1() {bar(bar(42))}"
        );
        Ok(())
    }

    #[test]
    fn replace_type() -> Result<(), Error> {
        assert_eq!(
            apply(
                "Result<(), $a>",
                "Option<$a>",
                "fn f1() -> Result<(), Vec<Error>> {foo()}"
            )?,
            "fn f1() -> Option<Vec<Error>> {foo()}"
        );
        Ok(())
    }

    #[test]
    fn replace_macro_invocations() -> Result<(), Error> {
        assert_eq!(
            apply(
                "try!($a)",
                "$a?",
                "fn f1() -> Result<(), E> {bar(try!(foo()));}"
            )?,
            "fn f1() -> Result<(), E> {bar(foo()?);}"
        );
        assert_eq!(
            apply(
                "foo!($a($b))",
                "foo($b, $a)",
                "fn f1() {foo!(abc(def() + 2));}"
            )?,
            "fn f1() {foo(def() + 2, abc);}"
        );
        Ok(())
    }

    // Although matching macros is supported, matching within macros isn't. For patterns that don't
    // start or end with a placeholder (like this one) it wouldn't be too hard to implement, but for
    // patterns like $a.foo(), we wouldn't know where to start matching.
    #[test]
    #[ignore]
    fn replace_nested_macro_invocations() -> Result<(), Error> {
        assert_eq!(
            apply("try!($a)", "$a?", "fn f1() {try!(bar(try!(foo())));")?,
            "fn f1() {bar(foo()?)?;}"
        );
        Ok(())
    }

    #[test]
    fn undefined_placeholder_in_replacement() {
        assert_eq!(
            apply("42", "$a", "fn f() ->i32 {42}"),
            Err(Error::message(
                "Replacement contains undefined placeholders: $a".to_owned()
            ))
        );
        assert_eq!(
            apply("43", "$a", "fn f() ->i32 {42}"),
            Err(Error::message(
                "Replacement contains undefined placeholders: $a".to_owned()
            ))
        );
    }
}
