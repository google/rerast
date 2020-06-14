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

use crate::Error;
use ra_syntax::{SmolStr, SyntaxKind};
use std::collections::HashSet;
use std::fmt::{self, Debug, Display};

/// Returns from the current function with an error, supplied by arguments as for format!
macro_rules! bail {
    ($e:expr) => {return Err($crate::Error::new($e))};
    ($fmt:expr, $($arg:tt)+) => {return Err($crate::Error::new(format!($fmt, $($arg)+)))}
}

/// The error returned when a search pattern can't be parsed as a particular kind of syntax
/// fragment. e.g. it isn't a valid expression, type, etc.
pub(crate) struct InvalidPatternTree {
    pub(crate) reason: String,
}

// Part of a search or replace pattern.
#[derive(Clone)]
pub(crate) enum PatternElement {
    Token(Token),
    Placeholder(Placeholder),
}

#[derive(Debug, Clone)]
pub(crate) struct Token {
    pub(crate) kind: SyntaxKind,
    pub(crate) text: SmolStr,
    is_jointed_to_next: bool,
}

/// A search pattern once it has been parsed as a specific kind of syntax. e.g. an expression or a
/// type.
#[derive(Debug)]
pub(crate) enum PatternTree {
    Node(PatternNode),
    Token(Token),
    Placeholder(Placeholder),
}

pub(crate) struct PatternNode {
    pub(crate) kind: SyntaxKind,
    pub(crate) children: Vec<PatternTree>,
}

#[derive(Clone, Debug)]
pub(crate) struct Placeholder {
    pub(crate) ident: SmolStr,
    pub(crate) constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub(crate) enum Constraint {
    Type(Vec<SmolStr>),
    Kind(NodeKind),
    Not(Box<Constraint>),
}

#[derive(Clone, Debug)]
pub(crate) enum NodeKind {
    Literal,
}

impl Debug for PatternNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print_tree(f, "")
    }
}

struct PatternTokenSource<'a> {
    tokens: &'a [PatternElement],
    position: usize,
}

struct PatternTreeSink<'a> {
    tokens: std::slice::Iter<'a, PatternElement>,
    stack: Vec<PatternNode>,
    error: Option<ra_parser::ParseError>,
    root: Option<PatternNode>,
}

/// Returns `pattern_str`, parsed as a search or replace pattern. If `remove_whitespace` is true,
/// then any whitespace tokens will be removed, which we do for the search pattern, but not for the
/// replace pattern.
pub(crate) fn parse_pattern(
    pattern_str: &str,
    remove_whitespace: bool,
) -> Result<Vec<PatternElement>, Error> {
    let mut result = Vec::new();
    let mut placeholder_names = HashSet::new();
    let mut tokens = tokenize(pattern_str)?.into_iter();
    while let Some(token) = tokens.next() {
        if token.kind == SyntaxKind::DOLLAR {
            let placeholder = parse_placeholder(&mut tokens)?;
            if !placeholder_names.insert(placeholder.ident.clone()) {
                bail!("Duplicate placeholder: ${}", placeholder.ident);
            }
            result.push(PatternElement::Placeholder(placeholder));
        } else if !remove_whitespace || token.kind != SyntaxKind::WHITESPACE {
            result.push(PatternElement::Token(token));
        }
    }
    Ok(result)
}

pub(crate) fn validate_rule(
    pattern: &[PatternElement],
    replacement: &[PatternElement],
) -> Result<(), Error> {
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
            if !placeholder.constraints.is_empty() {
                bail!("Replacement placeholders cannot have constraints");
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

pub(crate) fn create_pattern_tree(
    tokens: &[PatternElement],
    fragment_kind: ra_parser::FragmentKind,
) -> Result<PatternNode, InvalidPatternTree> {
    let mut token_source = PatternTokenSource::new(tokens);
    let mut tree_sink = PatternTreeSink::new(tokens);
    ra_parser::parse_fragment(&mut token_source, &mut tree_sink, fragment_kind);
    if let Some(parse_error) = tree_sink.error {
        Err(InvalidPatternTree {
            reason: format!(
                "Pattern isn't a valid {:?}: {:?}",
                fragment_kind, parse_error
            ),
        })
    } else if let Some(remaining) = token_source.tokens.get(token_source.position) {
        Err(InvalidPatternTree {
            reason: format!(
                "Parsing pattern as {:?} stoped at token: {:?}",
                fragment_kind, remaining
            ),
        })
    } else if let Some(root) = tree_sink.root {
        Ok(root)
    } else {
        // Not sure if this can actually happen. Presumably an error should have been reported
        // above, but just in case.
        Err(InvalidPatternTree {
            reason: format!(
                "Parsing pattern as a {:?} didn't produce a valid parse tree",
                fragment_kind
            ),
        })
    }
}

impl<'a> PatternTreeSink<'a> {
    fn new(tokens: &'a [PatternElement]) -> Self {
        Self {
            tokens: tokens.iter(),
            stack: Vec::new(),
            error: None,
            root: None,
        }
    }
}

impl<'a> PatternTokenSource<'a> {
    fn new(tokens: &'a [PatternElement]) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }
}

impl ra_parser::TokenSource for PatternTokenSource<'_> {
    fn current(&self) -> ra_parser::Token {
        self.lookahead_nth(0)
    }

    fn lookahead_nth(&self, n: usize) -> ra_parser::Token {
        match self.tokens.get(self.position + n) {
            None => ra_parser::Token {
                kind: SyntaxKind::EOF,
                is_jointed_to_next: false,
            },
            Some(PatternElement::Token(token)) => ra_parser::Token {
                kind: token.kind,
                is_jointed_to_next: token.is_jointed_to_next,
            },
            Some(PatternElement::Placeholder(_)) => ra_parser::Token {
                kind: SyntaxKind::IDENT,
                is_jointed_to_next: false,
            },
        }
    }

    fn bump(&mut self) {
        self.position += 1
    }

    fn is_keyword(&self, kw: &str) -> bool {
        if let Some(PatternElement::Token(token)) = self.tokens.get(self.position) {
            token.text == kw
        } else {
            false
        }
    }
}

impl ra_parser::TreeSink for PatternTreeSink<'_> {
    fn token(&mut self, kind: SyntaxKind, n_tokens: u8) {
        let node = self.stack.last_mut().unwrap();
        if n_tokens == 1 {
            // A single token, which might be a placeholder.
            node.children.push(match self.tokens.next() {
                Some(PatternElement::Token(t)) => PatternTree::Token(Token {
                    kind,
                    text: t.text.clone(),
                    is_jointed_to_next: false,
                }),
                Some(PatternElement::Placeholder(p)) => PatternTree::Placeholder(p.clone()),
                None => unreachable!(),
            })
        } else {
            // A composite token which should not include any placeholder parts, concatenate the
            // tokens together into a single token.
            let mut text = String::new();
            for _ in 0..n_tokens {
                if let Some(PatternElement::Token(t)) = self.tokens.next() {
                    text.push_str(t.text.as_str());
                }
            }
            node.children.push(PatternTree::Token(Token {
                kind,
                text: SmolStr::new(text),
                is_jointed_to_next: false,
            }))
        }
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        self.stack.push(PatternNode {
            kind,
            children: Vec::new(),
        })
    }

    fn finish_node(&mut self) {
        // unwrap can only fail if the parser calls finish_node more than start_node, which would be
        // a bug.
        let node = self.stack.pop().unwrap();
        if let Some(parent) = self.stack.last_mut() {
            parent.children.push(PatternTree::Node(node));
        } else {
            self.root = Some(node);
        }
    }

    fn error(&mut self, error: ra_parser::ParseError) {
        self.error = Some(error);
    }
}

impl NodeKind {
    fn from(name: &SmolStr) -> Result<NodeKind, Error> {
        Ok(match name.as_str() {
            "literal" => NodeKind::Literal,
            _ => bail!("Unknown node kind '{}'", name),
        })
    }
}

impl Display for PatternElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternElement::Token(t) => write!(f, "{}", t.text),
            PatternElement::Placeholder(p) => write!(f, "${}", p.ident),
        }
    }
}

impl fmt::Debug for PatternElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternElement::Token(t) => write!(f, "\"{}\" - {:?}", t.text, t.kind),
            PatternElement::Placeholder(p) => write!(f, "${} - placeholder", p.ident),
        }
    }
}

fn tokenize(source: &str) -> Result<Vec<Token>, Error> {
    let mut start = 0;
    let (raw_tokens, errors) = ra_syntax::tokenize(source);
    if let Some(first_error) = errors.first() {
        bail!("Failed to parse pattern: {}", first_error);
    }
    let mut tokens: Vec<Token> = Vec::new();
    for raw_token in raw_tokens {
        if let Some(previous) = tokens.last_mut() {
            if raw_token.kind != SyntaxKind::WHITESPACE {
                previous.is_jointed_to_next = true;
            }
        }
        let token_len = usize::from(raw_token.len);
        tokens.push(Token {
            kind: raw_token.kind,
            text: SmolStr::new(&source[start..start + token_len]),
            is_jointed_to_next: false,
        });
        start += token_len;
    }
    Ok(tokens)
}

fn parse_placeholder(tokens: &mut std::vec::IntoIter<Token>) -> Result<Placeholder, Error> {
    let mut name = None;
    let mut constraints = Vec::new();
    if let Some(token) = tokens.next() {
        match token.kind {
            SyntaxKind::IDENT => {
                name = Some(token.text);
            }
            SyntaxKind::L_CURLY => {
                let token = tokens
                    .next()
                    .ok_or_else(|| Error::new("Unexpected end of placeholder"))?;
                if token.kind == SyntaxKind::IDENT {
                    name = Some(token.text);
                }
                loop {
                    let token = tokens
                        .next()
                        .ok_or_else(|| Error::new("Placeholder is missing closing brace '}'"))?;
                    match token.kind {
                        SyntaxKind::COLON => {
                            constraints.push(parse_constraint(tokens)?);
                        }
                        SyntaxKind::R_CURLY => break,
                        _ => bail!(
                            "Unexpected token while parsing placeholder: '{}'",
                            token.text
                        ),
                    }
                }
            }
            _ => {
                bail!("Placeholders should either be $name or ${name:constraints}");
            }
        }
    }
    let name = name.ok_or_else(|| Error::new("Placeholder ($) with no name"))?;
    Ok(Placeholder {
        ident: name,
        constraints,
    })
}

fn parse_constraint(tokens: &mut std::vec::IntoIter<Token>) -> Result<Constraint, Error> {
    let constraint_type = tokens
        .next()
        .ok_or_else(|| Error::new(""))?
        .text
        .to_string();
    match constraint_type.as_str() {
        "type" => {
            let mut path = Vec::new();
            expect_token(tokens, "(")?;
            loop {
                let token = tokens.next().ok_or_else(|| {
                    Error::new("Unexpected end of constraint while looking for closing ')'")
                })?;
                match token.kind {
                    SyntaxKind::IDENT => path.push(token.text),
                    SyntaxKind::COLON => {}
                    SyntaxKind::R_PAREN => break,
                    _ => bail!("Unexpected token '{}' while parsing constraint", token.text),
                }
            }
            Ok(Constraint::Type(path))
        }
        "kind" => {
            expect_token(tokens, "(")?;
            let t = tokens
                .next()
                .ok_or_else(|| Error::new("Unexpected end of constraint while looking for kind"))?;
            if t.kind != SyntaxKind::IDENT {
                bail!(
                    "Expected ident, found {:?} while parsing kind constraint",
                    t.kind
                );
            }
            expect_token(tokens, ")")?;
            Ok(Constraint::Kind(NodeKind::from(&t.text)?))
        }
        "not" => {
            expect_token(tokens, "(")?;
            let sub = parse_constraint(tokens)?;
            expect_token(tokens, ")")?;
            Ok(Constraint::Not(Box::new(sub)))
        }
        x => bail!("Unsupported constraint type {}", x),
    }
}

fn expect_token(tokens: &mut std::vec::IntoIter<Token>, expected: &str) -> Result<(), Error> {
    if let Some(t) = tokens.next() {
        if t.text == expected {
            return Ok(());
        }
        bail!("Expected {} found {}", expected, t.text);
    }
    bail!("Expected {} found end of stream");
}

impl fmt::Display for PatternTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternTree::Node(n) => write!(f, "{}", n)?,
            PatternTree::Token(t) => write!(f, "{}", t.text)?,
            PatternTree::Placeholder(p) => write!(f, "${}", p.ident)?,
        }
        Ok(())
    }
}

impl PatternTree {
    fn print_tree(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        match self {
            PatternTree::Node(n) => n.print_tree(f, indent),
            PatternTree::Token(t) => writeln!(f, "{}{:?} -- \"{}\"", indent, t.kind, t.text),
            PatternTree::Placeholder(p) => writeln!(f, "{}Placeholder({})", indent, p.ident),
        }
    }

    pub(crate) fn first_token(&self) -> Option<&Token> {
        match self {
            PatternTree::Token(t) => Some(t),
            PatternTree::Node(n) => n.children.first().and_then(|c| c.first_token()),
            _ => None,
        }
    }
}

impl fmt::Display for PatternNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in &self.children {
            write!(f, "{}", c)?
        }
        Ok(())
    }
}

impl PatternNode {
    // If `self` contains nothing but a placeholder then return it, otherwise return None.
    pub(crate) fn placeholder(&self) -> Option<&Placeholder> {
        if self.children.len() != 1 {
            return None;
        }
        match &self.children[0] {
            PatternTree::Placeholder(p) => Some(p),
            PatternTree::Node(n) => n.placeholder(),
            _ => None,
        }
    }

    // If `self` contains nothing but an ident then return it, otherwise return None.
    pub(crate) fn ident(&self) -> Option<&SmolStr> {
        if self.children.len() != 1 {
            return None;
        }
        match &self.children[0] {
            PatternTree::Token(t) => Some(&t.text),
            PatternTree::Node(n) => n.ident(),
            _ => None,
        }
    }

    fn print_tree(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        writeln!(f, "{}{:?}", indent, self.kind)?;
        for c in &self.children {
            c.print_tree(f, &format!("{}  ", indent))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_placeholder() {
        assert_eq!(
            parse_pattern("($)", true).err(),
            Some(Error::new(
                "Placeholders should either be $name or ${name:constraints}"
            ))
        );
    }
}
