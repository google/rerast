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

#![allow(dead_code, unused_imports, unused_variables)]

use argh::FromArgs;
use ra_syntax::ast::{self, AstNode, SourceFile};
use ra_syntax::{
    match_ast, Direction, NodeOrToken, SyntaxError, SyntaxKind, SyntaxNode, SyntaxText, TextRange,
    WalkEvent, T,
};
use ra_tt::SmolStr;
use ra_tt::{Subtree, TokenTree};
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

impl From<ra_mbe::ParseError> for Error {
    fn from(error: ra_mbe::ParseError) -> Self {
        match error {
            ra_mbe::ParseError::Expected(expected) => Error {
                message: format!("Failed to parse rule. Expected: {}", expected),
            },
            _ => Error::message("Failed to parse rule".to_owned()),
        }
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

    /// a snippet of code that you expect to match. When exactly this snippet is
    /// encountered, debug information will be printed during matching.
    #[argh(option)]
    debug_snippet: Option<String>,
}

fn report_errors(context: &str, errors: &[SyntaxError]) {
    if errors.is_empty() {
        return;
    }
    eprintln!(
        "{} has errors: {}",
        context,
        errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<String>>()
            .join("\n")
    );
    std::process::exit(2);
}

#[derive(Debug)]
enum RuleTree {
    Leaf(ra_tt::Leaf),
    Subtree(RuleSubtree),
    Placeholder(Placeholder),
}

#[derive(Debug)]
struct RuleSubtree {
    delimiter: Option<ra_tt::Delimiter>,
    token_trees: Vec<RuleTree>,
}

#[derive(Debug, Copy, Clone)]
enum PlaceholderType {
    Block,
    Expr,
    Ident,
    Item,
    Literal,
    Pat,
    Path,
    Stmt,
    Tt,
    Ty,
    Vis,
}

impl PlaceholderType {
    fn from(type_name: &SmolStr) -> Result<Self, Error> {
        if type_name == "block" {
            Ok(PlaceholderType::Block)
        } else if type_name == "expr" {
            Ok(PlaceholderType::Expr)
        } else if type_name == "ident" {
            Ok(PlaceholderType::Ident)
        } else if type_name == "literal" {
            Ok(PlaceholderType::Literal)
        } else if type_name == "pat" {
            Ok(PlaceholderType::Pat)
        } else if type_name == "path" {
            Ok(PlaceholderType::Path)
        } else if type_name == "stmt" {
            Ok(PlaceholderType::Stmt)
        } else if type_name == "tt" {
            Ok(PlaceholderType::Tt)
        } else if type_name == "ty" {
            Ok(PlaceholderType::Ty)
        } else if type_name == "vis" {
            Ok(PlaceholderType::Vis)
        } else {
            bail!("Invalid placeholder type '{}'", type_name);
        }
    }

    fn matches_node(self, node: &SyntaxNode) -> bool {
        let kind = node.kind();
        match self {
            PlaceholderType::Block => ast::BlockExpr::can_cast(kind),
            PlaceholderType::Expr => ast::Expr::can_cast(kind),
            PlaceholderType::Ident => ast::Name::can_cast(kind),
            PlaceholderType::Item => ast::AssocItem::can_cast(kind),
            PlaceholderType::Literal => ast::Literal::can_cast(kind),
            PlaceholderType::Pat => ast::Pat::can_cast(kind),
            PlaceholderType::Path => ast::Path::can_cast(kind),
            PlaceholderType::Stmt => ast::Stmt::can_cast(kind),
            PlaceholderType::Tt => true,
            PlaceholderType::Ty => ast::TypeRef::can_cast(kind),
            PlaceholderType::Vis => ast::Visibility::can_cast(kind),
        }
    }
}

#[derive(Debug)]
struct Placeholder {
    ident: SmolStr,
    ty: PlaceholderType,
}

fn get_punct(tt: Option<&TokenTree>) -> Option<char> {
    if let Some(tt) = tt {
        if let TokenTree::Leaf(ra_tt::Leaf::Punct(ra_tt::Punct { char, .. })) = tt {
            return Some(*char);
        }
    }
    None
}

fn get_ident(tt: Option<TokenTree>) -> Option<SmolStr> {
    if let Some(tt) = tt {
        if let TokenTree::Leaf(ra_tt::Leaf::Ident(ra_tt::Ident { text, .. })) = tt {
            return Some(text);
        }
    }
    None
}

impl RuleSubtree {
    fn from(subtree: Subtree) -> Result<Self, Error> {
        let mut token_trees = Vec::new();
        let mut tt_in = subtree.token_trees.into_iter();
        while let Some(tt) = tt_in.next() {
            if let Some('$') = get_punct(Some(&tt)) {
                if let Some(ident) = get_ident(tt_in.next()) {
                    if let Some(':') = get_punct(tt_in.next().as_ref()) {
                        if let Some(ty) = get_ident(tt_in.next()) {
                            token_trees.push(RuleTree::Placeholder(Placeholder {
                                ident,
                                ty: PlaceholderType::from(&ty)?,
                            }))
                        } else {
                            bail!("Missing placeholder type");
                        }
                    } else {
                        bail!("Placeholder missing :type");
                    }
                } else {
                    bail!("Missing placeholder name");
                }
            } else {
                token_trees.push(RuleTree::from(tt)?);
            }
        }
        Ok(RuleSubtree {
            delimiter: subtree.delimiter,
            token_trees,
        })
    }
}

impl RuleTree {
    fn from(tokentree: TokenTree) -> Result<Self, Error> {
        Ok(match tokentree {
            TokenTree::Leaf(leaf) => RuleTree::Leaf(leaf),
            TokenTree::Subtree(subtree) => RuleTree::Subtree(RuleSubtree::from(subtree)?),
        })
    }
}

/// Acts like printf, but only if we're currently attempting to match the part of the source code
/// that the user indicated via the --debug-snippet flag. The first argument needs to be something
/// that has debug_active on it. e.g. MatchState.
macro_rules! dbg {
    ($s:expr, $e:expr) => {if $s.debug_active {println!("{}", $e);}};
    ($s:expr, $fmt:expr, $($arg:tt)+) => {if $s.debug_active { println!($fmt, $($arg)+);}};
}

struct MatchState {
    debug_active: bool,
    syntax_node: SyntaxNode,
    token_map: ra_mbe::TokenMap,
    placeholder_values: HashMap<SmolStr, Vec<TokenTree>>,
}

impl MatchState {
    fn attempt_match_st(&mut self, pattern: &RuleSubtree, code: &Subtree) -> bool {
        if pattern.delimiter.is_none() && pattern.token_trees.len() == 1 {
            if let RuleTree::Placeholder(p) = &pattern.token_trees[0] {
                if self.attempt_match_placeholder(
                    p,
                    &TokenTree::Subtree(code.clone()),
                    &mut Vec::new().iter().peekable(),
                ) {
                    return true;
                }
            }
        }
        if !self.attempt_match_delimiter(pattern, code) {
            return false;
        }
        let mut pattern = pattern.token_trees.iter();
        let mut code = code.token_trees.iter().peekable();
        loop {
            match (pattern.next(), code.next()) {
                (None, None) => return true,
                (Some(RuleTree::Placeholder(p)), Some(c)) => {
                    if !self.attempt_match_placeholder(p, c, &mut code) {
                        return false;
                    }
                }
                (Some(RuleTree::Leaf(p)), Some(TokenTree::Leaf(c))) => {
                    if !self.attempt_match_leaf(p, c) {
                        return false;
                    }
                }
                (Some(RuleTree::Subtree(p)), Some(TokenTree::Subtree(c))) => {
                    if !self.attempt_match_st(p, c) {
                        return false;
                    }
                }
                (Some(p), None) => {
                    dbg!(self, "Pattern {:?} remains, but there's no code to match");
                    return false;
                }
                (None, Some(c)) => {
                    dbg!(
                        self,
                        "Code {:?} remains, but there's no pattern to match it"
                    );
                    return false;
                }
                _ => return false,
            }
        }
    }

    fn attempt_match_delimiter(&mut self, pattern: &RuleSubtree, code: &Subtree) -> bool {
        let p = pattern.delimiter.map(|d| d.kind);
        let c = code.delimiter.map(|d| d.kind);
        if p != c {
            dbg!(self, "Delimiter is different {:?} vs {:?}", c, p);
            return false;
        }
        true
    }

    fn attempt_match_leaf(&mut self, pattern: &ra_tt::Leaf, code: &ra_tt::Leaf) -> bool {
        match (pattern, code) {
            (ra_tt::Leaf::Ident(p), ra_tt::Leaf::Ident(c)) => p.text == c.text,
            (ra_tt::Leaf::Punct(p), ra_tt::Leaf::Punct(c)) => p.char == c.char,
            (ra_tt::Leaf::Literal(p), ra_tt::Leaf::Literal(c)) => p.text == c.text,
            _ => {
                dbg!(self, "Leaf didn't match {:?} vs {:?}", code, pattern);
                false
            }
        }
    }

    fn attempt_match_placeholder(
        &mut self,
        placeholder: &Placeholder,
        initial_tt: &TokenTree,
        code: &mut std::iter::Peekable<std::slice::Iter<TokenTree>>,
    ) -> bool {
        match &placeholder.ty {
            PlaceholderType::Tt => {
                let mut contents = Vec::new();
                contents.push(initial_tt.to_owned());
                // Consume everything.
                for t in code {
                    contents.push(t.to_owned());
                }
                self.record_placeholder_match(placeholder, contents);
                true
            }
            ty => {
                if let Some(node) = self.syntax_node_starting(*ty, initial_tt) {
                    let range = node.text_range();
                    let mut contents = Vec::new();
                    contents.push(initial_tt.to_owned());
                    while let Some(t) = code.peek() {
                        if let Some(token_end) = self.get_token_end(t) {
                            if token_end > range.end() {
                                break;
                            }
                        }
                        // Unwrap must succeed because we peeked just above.
                        contents.push(code.next().unwrap().to_owned());
                    }
                    self.record_placeholder_match(placeholder, contents);
                    true
                } else {
                    dbg!(
                        self,
                        "No node of type {:?} starting with token {:?}",
                        ty,
                        initial_tt
                    );
                    false
                }
            }
        }
    }

    fn record_placeholder_match(&mut self, placeholder: &Placeholder, contents: Vec<TokenTree>) {
        self.placeholder_values
            .insert(placeholder.ident.clone(), contents);
    }

    // Returns the outermost node that starts with and encloses `initial_tt` and is of type `ty`.
    fn syntax_node_starting(
        &self,
        ty: PlaceholderType,
        initial_tt: &TokenTree,
    ) -> Option<SyntaxNode> {
        if let (Some(token_start), Some(token_end)) = (
            self.get_token_start(initial_tt),
            self.get_token_end(initial_tt),
        ) {
            dbg!(
                self,
                "token {:?}..{:?} <<<{}>>>",
                token_start,
                token_end,
                &self.syntax_node.text().to_string()[u32::from(
                    token_start - self.syntax_node.text_range().start()
                ) as usize
                    ..u32::from(token_end - self.syntax_node.text_range().start()) as usize]
            );
            for c in self.syntax_node.descendants() {
                let range = c.text_range();
                if range.start() == token_start && range.end() >= token_end && ty.matches_node(&c) {
                    return Some(c);
                }
            }
        }
        None
    }

    /// Returns the start position of `tt`.
    fn get_token_start(&self, tt: &TokenTree) -> Option<ra_syntax::TextSize> {
        match tt {
            TokenTree::Leaf(ra_tt::Leaf::Ident(ra_tt::Ident { id, .. }))
            | TokenTree::Leaf(ra_tt::Leaf::Literal(ra_tt::Literal { id, .. }))
            | TokenTree::Leaf(ra_tt::Leaf::Punct(ra_tt::Punct { id, .. }))
            | TokenTree::Subtree(Subtree {
                delimiter: Some(ra_tt::Delimiter { id, .. }),
                ..
            }) => self
                .token_map
                .range_by_token(*id)
                .and_then(|token_range| token_range.by_kind(T!['{']))
                .map(|range| range.start() + self.syntax_node.text_range().start()),
            TokenTree::Subtree(s) => s.token_trees.first().and_then(|s| self.get_token_start(s)),
        }
    }

    /// Returns the end position of `tt`.
    fn get_token_end(&self, tt: &TokenTree) -> Option<ra_syntax::TextSize> {
        match tt {
            TokenTree::Leaf(ra_tt::Leaf::Ident(ra_tt::Ident { id, .. }))
            | TokenTree::Leaf(ra_tt::Leaf::Literal(ra_tt::Literal { id, .. }))
            | TokenTree::Leaf(ra_tt::Leaf::Punct(ra_tt::Punct { id, .. }))
            | TokenTree::Subtree(Subtree {
                delimiter: Some(ra_tt::Delimiter { id, .. }),
                ..
            }) => self
                .token_map
                .range_by_token(*id)
                .and_then(|token_range| token_range.by_kind(T!['}']))
                .map(|range| range.end() + self.syntax_node.text_range().start()),
            TokenTree::Subtree(s) => s.token_trees.last().and_then(|s| self.get_token_end(s)),
        }
    }

    fn apply_placeholders(&self, replacement: Subtree) -> Subtree {
        let mut token_trees_in = replacement.token_trees.into_iter();
        let mut token_trees_out = Vec::new();
        while let Some(tt) = token_trees_in.next() {
            if let Some('$') = get_punct(Some(&tt)) {
                if let Some(ident) = get_ident(token_trees_in.next()) {
                    if let Some(contents) = self.placeholder_values.get(&ident) {
                        token_trees_out.extend(contents.iter().cloned());
                    }
                }
            } else {
                match tt {
                    TokenTree::Subtree(subtree) => {
                        token_trees_out.push(TokenTree::Subtree(self.apply_placeholders(subtree)))
                    }
                    tt => token_trees_out.push(tt),
                }
            }
        }
        Subtree {
            delimiter: replacement.delimiter,
            token_trees: token_trees_out,
        }
    }
}

#[derive(Debug)]
struct Match {
    matched_node: SyntaxNode,
    placeholder_values: HashMap<SmolStr, Vec<TokenTree>>,
}

#[derive(Default)]
struct MatchFinder {
    debug_snippet: Option<String>,
}

impl MatchFinder {
    fn find_matches(&self, search: RuleSubtree, code: SourceFile) -> Vec<Match> {
        let mut matches = Vec::new();
        let mut nodes = code.syntax().descendants().peekable();
        while let Some(c) = nodes.next() {
            if let Some((tt, token_map)) = ra_mbe::syntax_node_to_token_tree(&c) {
                let debug_active = self.debug_snippet.is_some()
                    && Some(c.text().to_string()) == self.debug_snippet;
                if debug_active {
                    println!(
                        "========= PATTERN ==========\n{:#?}\n\
                            ============ TT ============\n{:?}\n\
                            ============ AST ===========\n{:?}\n\
                            ============================",
                        &search, tt, c
                    );
                }
                let mut match_state = MatchState {
                    debug_active,
                    syntax_node: c.clone(),
                    token_map,
                    placeholder_values: HashMap::new(),
                };
                if match_state.attempt_match_st(&search, &tt) {
                    matches.push(Match {
                        matched_node: match_state.syntax_node,
                        placeholder_values: match_state.placeholder_values,
                    });
                    // Skip past the rest of c. We don't want nested or overlapping matches, at least not here.
                    while let Some(p) = nodes.peek() {
                        if !p.ancestors().any(|a| a == c) {
                            break;
                        }
                        nodes.next();
                    }
                }
            }
        }
        matches
    }

    fn find_match_str(&self, pattern: &str, code: &str) -> Result<Vec<String>, Error> {
        if let Some((pattern, _)) = ra_mbe::parse_to_token_tree(pattern) {
            return Ok(self
                .find_matches(RuleSubtree::from(pattern)?, SourceFile::parse(code).tree())
                .into_iter()
                .map(|m| m.matched_node.text().to_string())
                .collect());
        }
        Ok(vec![])
    }

    fn apply(
        &self,
        search: &RuleSubtree,
        replace: &Subtree,
        code: &SyntaxNode,
    ) -> Result<SyntaxNode, Error> {
        if let Some((tt, token_map)) = ra_mbe::syntax_node_to_token_tree(&code) {
            let debug_active =
                self.debug_snippet.is_some() && Some(code.text().to_string()) == self.debug_snippet;
            if debug_active {
                println!(
                    "========= PATTERN ==========\n{:#?}\n\
                    ============ TT ============\n{:?}\n\
                    ============ AST ===========\n{:?}\n\
                    ============================",
                    &search, tt, code
                );
            }
            let mut match_state = MatchState {
                debug_active,
                syntax_node: code.clone(),
                token_map,
                placeholder_values: HashMap::new(),
            };
            if match_state.attempt_match_st(&search, &tt) {
                match ra_mbe::token_tree_to_syntax_node(
                    &match_state.apply_placeholders(replace.to_owned()),
                    ra_parser::FragmentKind::Expr,
                ) {
                    Ok((parse, _)) => {
                        return Ok(parse.syntax_node());
                    }
                    Err(e) => bail!("Failed to parse replacement as an expression"),
                }
            }
        }
        let mut child_replacements = Vec::new();
        let mut changed = false;
        for child_node_or_token in code.children_with_tokens() {
            match child_node_or_token {
                rowan::NodeOrToken::Node(child) => {
                    let replacement = self.apply(search, replace, &child)?;
                    if replacement.parent().is_none() {
                        // If the returned child has no parent, then it's not the child that we passed in.
                        changed = true;
                    }
                    child_replacements.push(rowan::NodeOrToken::Node(replacement.green().clone()));
                }
                rowan::NodeOrToken::Token(token) => {
                    child_replacements.push(rowan::NodeOrToken::Token(token.green().clone()))
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
        let search = if let Some((search, _)) = ra_mbe::parse_to_token_tree(search) {
            search
        } else {
            bail!("Failed to parse search pattern");
        };
        let replace = if let Some((replace, _)) = ra_mbe::parse_to_token_tree(replace) {
            replace
        } else {
            bail!("Failed to parse replace pattern");
        };
        Ok(self
            .apply(
                &RuleSubtree::from(search)?,
                &replace,
                SourceFile::parse(code).tree().syntax(),
            )?
            .text()
            .to_string())
    }
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
            assert_eq!(find($pat, $code), vec![$($expected),*].iter().map(|e: &&str| e.to_string()).collect::<Vec<String>>());
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
    }

    #[test]
    fn no_match() {
        assert_no_match!("1 + 3", "fn f() -> i32 {1  +  2}");
    }

    #[test]
    fn match_type() {
        assert_matches!("i32", "fn f() -> i32 {1  +  2}", ["i32"]);
    }

    #[test]
    fn match_fn_return_type() {
        assert_matches!("->i32", "fn f() -> i32 {1  +  2}", ["-> i32"]);
    }

    #[test]
    fn match_tt() {
        assert_matches!(
            "foo($a:tt)",
            "fn f() -> i32 {foo(40 + 2, 4)}",
            ["foo(40 + 2, 4)"]
        );
    }

    #[test]
    fn match_expr() {
        let code = "fn f() -> i32 {foo(40 + 2, 42)}";
        assert_matches!("foo($a:expr, $b:expr)", code, ["foo(40 + 2, 42)"]);
        assert_no_match!("foo($a:expr, $b:expr, $c:expr)", code);
        assert_no_match!("foo($a:expr)", code);
    }

    #[test]
    fn match_complex_expr() {
        let code = "fn f() -> i32 {foo(bar(40, 2), 42)}";
        assert_matches!("foo($a:expr, $b:expr)", code, ["foo(bar(40, 2), 42)"]);
        assert_no_match!("foo($a:expr, $b:expr, $c:expr)", code);
        assert_no_match!("foo($a:expr)", code);
    }

    #[test]
    fn match_literal_placeholder() {
        assert_matches!("$a:literal", "fn f() -> i32 {42}", ["42"]);
        assert_matches!("$a:literal", "fn f() -> &str {\"x\"}", ["\"x\""]);
        assert_no_match!("$a:literal", "fn f() {}");
    }

    #[test]
    fn match_type_placeholder() {
        assert_matches!("$a:ty", "fn f() -> i32 {42}", ["i32"]);
        assert_matches!("$a:ty", "fn f() -> Option<i32> {42}", ["Option<i32>"]);
        assert_matches!(
            "Option<$a:ty>",
            "fn f() -> Option<i32> {42}",
            ["Option<i32>"]
        );
        assert_no_match!("Option<$a:ty>", "fn f() -> Result<i32, ()> {42}");
        assert_matches!(
            "$a:ty",
            "fn f(a: i64, b: bool) -> i32 {42}",
            ["i64", "bool", "i32"]
        );
    }

    #[test]
    fn match_name_def_name_placeholder() {
        assert_matches!("$a:ident", "fn foo() -> i32 {42}", ["foo"]);
        assert_matches!("$a:ident", "const BAR: i32 = 42", ["BAR"]);
    }

    #[test]
    fn match_vis_placeholder() {
        assert_matches!("$a:vis", "pub fn foo() -> i32 {42}", ["pub"]);
        assert_no_match!("$a:vis", "fn foo() -> i32 {42}");
    }

    #[test]
    fn match_path_placeholder() {
        let code = "fn foo() {foo::bar::baz()}";
        assert_matches!("$a:path", code, ["foo::bar::baz"]);
    }

    #[test]
    fn match_pattern_placeholder() {
        let code = "fn foo() {let Some(x) = bar();}";
        assert_matches!("$a:pat", code, ["Some(x)"]);
    }

    #[test]
    fn match_block_placeholder() {
        assert_matches!("$a:block", "fn foo() -> i32 {42}", ["{42}"]);
    }

    #[test]
    fn match_expr_argument() {
        // Make sure that we don't match foo(x: i32), since x: i32 isn't an expression.
        assert_matches!(
            "foo($a:expr)",
            "fn foo(x: i32) -> i32 {foo(42)}",
            ["foo(42)"]
        );
    }

    #[test]
    fn match_stmt_placeholder() {
        let code = "fn foo() -> i32 {bar(); 42}";
        assert_matches!("$a:stmt", code, ["bar();"]);
        assert_no_match!("$a:stmt", "fn foo() -> i32 {42}");
    }

    #[test]
    fn invalid_placeholder() {
        assert_eq!(
            MatchFinder::default().find_match_str("$a:invalid", "fn foo() {}"),
            Err(Error::message(
                "Invalid placeholder type 'invalid'".to_owned()
            ))
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
            apply(
                "foo($a:expr,$b: expr)",
                "bar($b, $a)",
                "fn f1() {foo(5, 42)}"
            )?,
            "fn f1() {bar(42,5)}"
        );
        Ok(())
    }
}
