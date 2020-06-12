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
use fmt::{Debug, Display};
use ra_db::{FileId, FileRange};
use ra_syntax::ast::{self, AstNode};
use ra_syntax::{SmolStr, SyntaxElement, SyntaxKind, SyntaxNode, TextRange, TextSize};
use ra_text_edit::TextEdit;
use std::collections::{HashMap, HashSet};
use std::{cell::Cell, fmt};

#[derive(Debug, Eq, PartialEq)]
struct Error {
    message: String,
}

impl Error {
    fn new(message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

macro_rules! bail {
    ($e:expr) => {return Err($crate::Error::new($e))};
    ($fmt:expr, $($arg:tt)+) => {return Err($crate::Error::new(format!($fmt, $($arg)+)))}
}

#[derive(Debug, Clone)]
struct Token {
    kind: SyntaxKind,
    text: SmolStr,
    is_jointed_to_next: bool,
}

#[derive(Clone)]
enum PatternElement {
    Token(Token),
    Placeholder(Placeholder),
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

fn parse_pattern(pattern_str: &str, remove_whitespace: bool) -> Result<Vec<PatternElement>, Error> {
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
            if let Some(PatternElement::Placeholder(last_placeholder)) = result.last_mut() {
                last_placeholder.terminator = Some(token.clone());
            }
            result.push(PatternElement::Token(token));
        }
    }
    Ok(result)
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
        terminator: None,
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
            Ok(Constraint::ExprType(path))
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

// A search pattern once it has been parsed as a specific kind of syntax. e.g. an expression or a
// type.
#[derive(Debug)]
enum PatternTree {
    Node(PatternNode),
    Token(Token),
    Placeholder(Placeholder),
}

impl PatternTree {
    fn print_tree(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        match self {
            PatternTree::Node(n) => n.print_tree(f, indent),
            PatternTree::Token(t) => writeln!(f, "{}{:?} -- \"{}\"", indent, t.kind, t.text),
            PatternTree::Placeholder(p) => writeln!(f, "{}Placeholder({})", indent, p.ident),
        }
    }

    fn first_token(&self) -> Option<&Token> {
        match self {
            PatternTree::Token(t) => Some(t),
            PatternTree::Node(n) => n.children.first().and_then(|c| c.first_token()),
            _ => None,
        }
    }
}

struct PatternNode {
    kind: SyntaxKind,
    children: Vec<PatternTree>,
}

impl PatternNode {
    // If `self` contains nothing but a placeholder then return it, otherwise return None.
    fn placeholder(&self) -> Option<&Placeholder> {
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
    fn ident(&self) -> Option<&SmolStr> {
        if self.children.len() != 1 {
            return None;
        }
        match &self.children[0] {
            PatternTree::Token(t) => Some(&t.text),
            PatternTree::Node(n) => n.ident(),
            _ => None,
        }
    }

    // Calls `callback` for each token in `self` in order.
    fn tokens_do(&self, callback: &mut impl FnMut(&Token)) {
        for c in &self.children {
            match c {
                PatternTree::Node(n) => n.tokens_do(callback),
                PatternTree::Token(t) => callback(t),
                _ => {}
            }
        }
    }

    // Returns whether this node is a path node equal to `path`.
    fn matches_path(&self, path: &[SmolStr]) -> bool {
        let mut path = path.iter();
        // We can't early return when  we get a failure, since closures don't work like that in
        // Rust, so we have to keep track of whether we've failed and keep iterating to the end. If
        // we find ourselves doing this again, we should probably either replace tokens_do with an
        // iterator, or investigate using rowan. For now, this seems simplest.
        let mut equal = true;
        self.tokens_do(&mut |t: &Token| match t.kind {
            SyntaxKind::IDENT => {
                if let Some(p) = path.next() {
                    if *p != t.text {
                        equal = false;
                    }
                } else {
                    equal = false;
                }
            }
            SyntaxKind::COLON2 => {}
            _ => {equal = false}
        });
        equal && path.next().is_none()
    }

    fn print_tree(&self, f: &mut fmt::Formatter<'_>, indent: &str) -> fmt::Result {
        writeln!(f, "{}{:?}", indent, self.kind)?;
        for c in &self.children {
            c.print_tree(f, &format!("{}  ", indent))?;
        }
        Ok(())
    }
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

#[derive(Clone, Debug)]
struct Placeholder {
    ident: SmolStr,
    // The next token after this placeholder in the pattern, if any. When matching, we then consume
    // the outermost node that is followed by this token. This allows `$a: 1` to match `foo: 1`
    // instead of the placeholder consuming the whole thing then failing when we get to the `:`
    terminator: Option<Token>,
    constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
enum Constraint {
    ExprType(Vec<SmolStr>),
}

// An "error" indicating that matching failed. Use the fail_match! macro to create and return this.
#[derive(Clone)]
struct MatchFailed {
    // Only present when --debug-snippet is set.
    reason: Option<String>,
}

// For performance reasons, we don't want to record the reason why every match fails, only the bit
// of code that the user indicated they thought would match. We use a thread local to indicate when
// we are trying to match that bit of code. This saves us having to pass a boolean into all the bits
// of code that can make the decision to not match.
thread_local! {
    pub static RECORDING_MATCH_FAIL_REASONS: Cell<bool> = Cell::new(false);
}

fn recording_match_fail_reasons() -> bool {
    RECORDING_MATCH_FAIL_REASONS.with(|c| c.get())
}

/// Fails the current match attempt. If we're currently attempting to match some code that we
/// thought we were going to match, as indicated by the --debug-snippet flag, then populate the
/// reason field.
macro_rules! fail_match {
    ($e:expr) => {{
        if recording_match_fail_reasons() {
            return Err(MatchFailed { reason: Some(format!("{}", $e)) });
        }
        return Err(MatchFailed { reason: None });
    }};
    ($fmt:expr, $($arg:tt)+) => {{
        if recording_match_fail_reasons() {
            return Err(MatchFailed { reason: Some(format!($fmt, $($arg)+)) });
        }
        return Err(MatchFailed { reason: None });
    }};
}

struct InvalidPatternTree {
    reason: String,
}

fn create_pattern_tree(
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

struct MatchState<'db, 'sema> {
    placeholder_values: HashMap<SmolStr, PlaceholderMatch>,
    sema: &'sema ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
    root_module: ra_hir::Module,
    restrict_range: Option<FileRange>,
}

type PatternIterator<'a> = std::iter::Peekable<std::slice::Iter<'a, PatternTree>>;

impl<'db, 'sema> MatchState<'db, 'sema> {
    fn try_match(
        search_scope: &SearchScope,
        code: &SyntaxNode,
        sema: &'sema ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
    ) -> Result<MatchState<'db, 'sema>, MatchFailed> {
        let mut match_state = MatchState {
            placeholder_values: HashMap::new(),
            sema,
            root_module: search_scope.root_module.clone(),
            restrict_range: search_scope.restrict_range.clone(),
        };
        match_state.attempt_match_node(search_scope.search.tree_for_kind(code.kind())?, code)?;
        match_state.validate_range(&sema.original_range(code))?;
        Ok(match_state)
    }

    // Checks that `range` is within the permitted range if any. This is applicable when we're
    // processing a macro expansion and we want to fail the match if we're working with a node that
    // didn't originate from the token tree of the macro call.
    fn validate_range(&self, range: &FileRange) -> Result<(), MatchFailed> {
        if let Some(restrict_range) = &self.restrict_range {
            if restrict_range.file_id != range.file_id
                || !restrict_range.range.contains_range(range.range)
            {
                fail_match!("Node originated from a macro");
            }
        }
        Ok(())
    }

    fn get_match(
        debug_active: bool,
        search_scope: &SearchScope,
        code: &SyntaxNode,
        sema: &'sema ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
    ) -> Option<Match> {
        RECORDING_MATCH_FAIL_REASONS.with(|c| c.set(debug_active));
        let result = match Self::try_match(search_scope, code, sema) {
            Ok(state) => Some(Match {
                range: sema.original_range(code).range,
                matched_node: code.clone(),
                placeholder_values: state.placeholder_values,
            }),
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
        };
        RECORDING_MATCH_FAIL_REASONS.with(|c| c.set(false));
        result
    }

    fn attempt_match_node(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Handle placeholders.
        if let Some(placeholder) = pattern.placeholder() {
            for constraint in &placeholder.constraints {
                self.validate_constraint(constraint, code)?;
            }
            let original_range = self.sema.original_range(code);
            // We validated the range for the node when we started the match, so the placeholder
            // probably can't fail range validation, but just to be safe...
            self.validate_range(&original_range)?;
            self.placeholder_values.insert(
                placeholder.ident.clone(),
                PlaceholderMatch::new(code, original_range.range),
            );
            return Ok(());
        }
        // Non-placeholders.
        if pattern.kind != code.kind() {
            fail_match!(
                "Pattern had a {:?}, code had {:?}",
                pattern.kind,
                code.kind()
            );
        }
        // Some kinds of nodes have special handling. For everything else, we fall back to default
        // matching.
        match code.kind() {
            SyntaxKind::RECORD_FIELD_LIST => self.attempt_match_record_field_list(pattern, code),
            SyntaxKind::TOKEN_TREE => self.attempt_match_token_tree(pattern, code),
            SyntaxKind::PATH => self.attempt_match_path(pattern, code),
            _ => self.attempt_match_node_children(pattern, code),
        }
    }

    fn attempt_match_node_children(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        let mut pattern_it = pattern.children.iter().peekable();
        let mut code_it = code.children_with_tokens();
        loop {
            match next_non_trivial(&mut code_it) {
                None => {
                    if let Some(p) = pattern_it.next() {
                        fail_match!("Part of the pattern was unmached: {:?}", p);
                    }
                    return Ok(());
                }
                Some(SyntaxElement::Token(c)) => {
                    self.attempt_match_token(&mut pattern_it, &c)?;
                }
                Some(SyntaxElement::Node(c)) => match pattern_it.next() {
                    Some(PatternTree::Node(p)) => {
                        self.attempt_match_node(p, &c)?;
                    }
                    p => fail_match!("Pattern wanted {:?}, code has {:?}", p, c),
                },
            }
        }
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
        if let Some(PatternTree::Token(p)) = pattern.peek() {
            // If the code has a comma and the pattern is about to close something, then accept the
            // comma without advancing the pattern. i.e. ignore trailing commas.
            if code.kind() == SyntaxKind::COMMA && is_closing_token(p.kind) {
                return Ok(());
            }
            // Conversely, if the pattern has a comma and the code doesn't, skip that part of the
            // pattern and continue to match the code.
            if p.kind == SyntaxKind::COMMA && is_closing_token(code.kind()) {
                pattern.next();
            }
        }
        // Consume an element from the pattern and make sure it matches.
        match pattern.next() {
            Some(PatternTree::Token(p)) => {
                if p.kind != code.kind() || p.text != *code.text() {
                    fail_match!(
                        "Pattern wanted token '{}' ({:?}), but code had token '{}' ({:?})",
                        p.text,
                        p.kind,
                        code.text(),
                        code.kind()
                    )
                }
            }
            Some(PatternTree::Node(p)) => {
                // Not sure if this is actually reachable.
                fail_match!(
                    "Pattern wanted {:?}, but code had token '{}' ({:?})",
                    p,
                    code.text(),
                    code.kind()
                );
            }
            Some(PatternTree::Placeholder(_)) => {
                // Not sure if this is actually reachable.
                fail_match!(
                    "Placeholders matching tokens is not yet implemented: '{}'",
                    code.text()
                );
            }
            None => {
                fail_match!("Pattern exhausted, while code remains: `{}`", code.text());
            }
        }
        Ok(())
    }

    fn validate_constraint(
        &self,
        constraint: &Constraint,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        match constraint {
            Constraint::ExprType(constraint_path) => {
                if let Some(expr) = ast::Expr::cast(code.clone()) {
                    if let Some(ty) = self.sema.type_of_expr(&expr) {
                        let ty_path = self.get_type_path(&ty)?;
                        if ty_path != constraint_path.as_slice() {
                            fail_match!(
                                "Expected type {}, found {}",
                                constraint_path.join("::"),
                                ty_path.join("::")
                            );
                        }
                    } else {
                        fail_match!("Couldn't get expression type for code `{}`", code.text());
                    }
                } else {
                    fail_match!("Not an expression `{}`", code.text());
                }
            }
        }
        Ok(())
    }

    fn get_type_path(&self, ty: &ra_hir::Type) -> Result<Vec<SmolStr>, MatchFailed> {
        if let Some(adt) = ty.as_adt() {
            let module = adt.module(self.sema.db);
            let mut ty_path: Vec<SmolStr> = self.module_path(&module);
            ty_path.push(SmolStr::new(adt.name(self.sema.db).to_string()));
            Ok(ty_path)
        } else {
            match ra_hir::HirDisplay::display_source_code(ty, self.sema.db, self.root_module.into())
            {
                Ok(type_name) => Ok(vec![SmolStr::new(type_name)]),
                Err(e) => fail_match!("Failed to get type: {:?}", e),
            }
        }
    }

    fn module_path(&self, module: &ra_hir::Module) -> Vec<SmolStr> {
        let mut path: Vec<SmolStr> = module
            .path_to_root(self.sema.db)
            .iter()
            .filter_map(|m| m.name(self.sema.db))
            .map(|name| SmolStr::new(name.to_string()))
            .collect();
        path.reverse();
        path
    }

    // We want to allow fully-qualified paths to match non-fully-qualified paths that resolve to the
    // same thing.
    fn attempt_match_path(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        if let Some(path) = ast::Path::cast(code.clone()) {
            if let Some(ra_hir::PathResolution::Def(resolved_def)) = self.sema.resolve_path(&path) {
                // TODO: Handle more than just paths to functions.
                if let ra_hir::ModuleDef::Function(fn_def) = resolved_def {
                    if let Some(module) = resolved_def.module(self.sema.db) {
                        let mut full_path = self.module_path(&module);
                        full_path.push(SmolStr::new(fn_def.name(self.sema.db).to_string()));
                        if pattern.matches_path(&full_path) {
                            return Ok(());
                        }
                    }
                }
            }
        }
        // Fall back to regular matching.
        self.attempt_match_node_children(pattern, code)
    }

    // We want to allow the records to match in any order, so we have special matching logic for
    // them.
    fn attempt_match_record_field_list(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Build a map keyed by field name.
        let mut fields_by_name = HashMap::new();
        for child in code.children() {
            if let Some(record) = ast::RecordField::cast(child.clone()) {
                if let Some(name) = record.field_name() {
                    fields_by_name.insert(name.text().clone(), child.clone());
                }
            }
        }
        for p in &pattern.children {
            if let PatternTree::Node(p) = p {
                if let Some(PatternTree::Node(name_node)) = p.children.first() {
                    if name_node.placeholder().is_some() {
                        // If the pattern is using placeholders for field names then order
                        // independence doesn't make sense. Fall back to regular ordered
                        // matching.
                        return self.attempt_match_node_children(pattern, code);
                    }
                    if let Some(ident) = name_node.ident() {
                        if let Some(code_record) = fields_by_name.remove(ident) {
                            self.attempt_match_node(p, &code_record)?;
                        } else {
                            fail_match!(
                                "Placeholder has record field '{}', but code doesn't",
                                ident
                            );
                        }
                    }
                }
            }
        }
        if let Some(unmatched_fields) = fields_by_name.keys().next() {
            fail_match!(
                "{} field(s) of a record literal failed to match, starting with {}",
                fields_by_name.len(),
                unmatched_fields
            );
        }
        Ok(())
    }

    // Outside of token trees, a placeholder can only match a single AST node, whereas in a token
    // tree it can match a sequence of tokens. Note, that this code will only be used when the
    // pattern matches the macro invocation. For matches within the macro call, we'll already have
    // expanded the macro.
    fn attempt_match_token_tree(
        &mut self,
        pattern: &PatternNode,
        code: &ra_syntax::SyntaxNode,
    ) -> Result<(), MatchFailed> {
        let mut pattern = pattern.children.iter().peekable();
        let mut children = code.children_with_tokens();
        while let Some(child) = children.next() {
            if let Some(PatternTree::Placeholder(placeholder)) = pattern.peek() {
                pattern.next();
                // Unwrap must succeed since the token tree must have a close delimiter.
                let next_pattern_token = pattern
                    .peek()
                    .and_then(|p| p.first_token())
                    .map(|p| p.text.to_string());
                let first_matched_token = child.clone();
                let mut last_matched_token = child;
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
                                    if let Some(PatternTree::Node(p)) = pattern.next() {
                                        // We have a subtree that starts with the next token in our pattern.
                                        self.attempt_match_token_tree(p, &n)?;
                                        break;
                                    }
                                }
                            }
                        }
                    };
                    last_matched_token = next;
                }
                self.placeholder_values.insert(
                    placeholder.ident.clone(),
                    PlaceholderMatch::from_range(
                        first_matched_token
                            .text_range()
                            .cover(last_matched_token.text_range()),
                    ),
                );
                continue;
            }
            // Match literal (non-placeholder) tokens.
            match child {
                SyntaxElement::Token(token) => {
                    self.attempt_match_token(&mut pattern, &token)?;
                }
                SyntaxElement::Node(node) => {
                    match pattern.next() {
                        Some(PatternTree::Node(p)) => {
                            self.attempt_match_token_tree(p, &node)?;
                        }
                        Some(PatternTree::Placeholder(_)) => {
                            // We peeked above to see if it was a placeholder.
                            unreachable!();
                        }
                        Some(PatternTree::Token(p)) => fail_match!(
                            "Pattern has token '{}', code has subtree '{}'",
                            p.text,
                            node.text()
                        ),
                        None => fail_match!("Pattern has nothing, code has '{}'", node.text()),
                    }
                }
            }
        }
        if let Some(p) = pattern.next() {
            fail_match!(
                "Reached end of token tree in code, but pattern still has {:?}",
                p
            );
        }
        Ok(())
    }
}

fn next_non_trivial(code_it: &mut ra_syntax::SyntaxElementChildren) -> Option<SyntaxElement> {
    loop {
        let c = code_it.next();
        if let Some(SyntaxElement::Token(t)) = &c {
            if t.kind().is_trivia() {
                continue;
            }
        }
        return c;
    }
}

fn is_closing_token(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::R_PAREN || kind == SyntaxKind::R_CURLY || kind == SyntaxKind::R_BRACK
}

#[derive(Debug)]
struct Match {
    range: TextRange,
    matched_node: SyntaxNode,
    placeholder_values: HashMap<SmolStr, PlaceholderMatch>,
}

#[derive(Debug)]
struct PlaceholderMatch {
    node: Option<SyntaxNode>,
    range: TextRange,
    inner_matches: Vec<Match>,
}

impl PlaceholderMatch {
    fn new(node: &SyntaxNode, range: TextRange) -> Self {
        Self {
            node: Some(node.clone()),
            range,
            inner_matches: Vec::new(),
        }
    }

    fn from_range(range: TextRange) -> Self {
        Self {
            node: None,
            range,
            inner_matches: Vec::new(),
        }
    }
}

impl Match {
    fn apply_placeholders(&self, replacement: &[PatternElement], file_source: &str) -> String {
        let mut out = String::new();
        for r in replacement {
            match r {
                PatternElement::Token(t) => out.push_str(t.text.as_str()),
                PatternElement::Placeholder(p) => {
                    if let Some(placeholder_value) = self.placeholder_values.get(&p.ident) {
                        let range = &placeholder_value.range;
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

struct MatchFinder<'db> {
    debug_snippet: Option<String>,
    sema: ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
}

struct SearchTrees {
    tokens: Vec<PatternElement>,
    expr: Result<PatternNode, InvalidPatternTree>,
    type_ref: Result<PatternNode, InvalidPatternTree>,
    item: Result<PatternNode, InvalidPatternTree>,
    path: Result<PatternNode, InvalidPatternTree>,
    pattern: Result<PatternNode, InvalidPatternTree>,
}

// Our search pattern, parsed as each different kind of syntax node we might encounter.
impl SearchTrees {
    fn new(tokens: &[PatternElement]) -> Self {
        Self {
            tokens: tokens.to_vec(),
            expr: create_pattern_tree(tokens, ra_parser::FragmentKind::Expr),
            type_ref: create_pattern_tree(tokens, ra_parser::FragmentKind::Type),
            item: create_pattern_tree(tokens, ra_parser::FragmentKind::Item),
            path: create_pattern_tree(tokens, ra_parser::FragmentKind::Path),
            pattern: create_pattern_tree(tokens, ra_parser::FragmentKind::Pattern),
        }
    }

    fn tree_for_kind(&self, kind: SyntaxKind) -> Result<&PatternNode, MatchFailed> {
        let tree = if ast::Expr::can_cast(kind) {
            &self.expr
        } else if ast::TypeRef::can_cast(kind) {
            &self.type_ref
        } else if ast::ModuleItem::can_cast(kind) {
            &self.item
        } else if ast::Path::can_cast(kind) {
            &self.path
        } else if ast::Pat::can_cast(kind) {
            &self.pattern
        } else {
            fail_match!("Matching nodes of kind {:?} is not supported", kind);
        };
        match tree {
            Ok(tree) => Ok(tree),
            Err(err) => fail_match!("{}", err.reason),
        }
    }
}

struct SearchScope<'a> {
    search: &'a SearchTrees,
    root_module: &'a ra_hir::Module,
    restrict_range: Option<FileRange>,
}

impl<'db> MatchFinder<'db> {
    fn new(debug_snippet: Option<String>, db: &'db ra_ide_db::RootDatabase) -> MatchFinder<'db> {
        MatchFinder {
            debug_snippet,
            sema: ra_hir::Semantics::new(db),
        }
    }

    fn root_module(&self, node: &SyntaxNode) -> Result<ra_hir::Module, Error> {
        self.sema
            .scope(node)
            .module()
            .ok_or_else(|| Error::new("Failed to get root module"))
    }

    fn find_matches(
        &self,
        search_scope: &SearchScope,
        code: &SyntaxNode,
        matches_out: &mut Vec<Match>,
    ) {
        let debug_active =
            self.debug_snippet.is_some() && Some(code.text().to_string()) == self.debug_snippet;
        if debug_active {
            if let Ok(tree) = search_scope.search.tree_for_kind(code.kind()) {
                println!("========= PATTERN ==========\n{:#?}", tree);
            } else {
                println!(
                    "========= PATTERN ==========\n{:#?}",
                    search_scope.search.tokens
                );
            }

            println!(
                "\n============ AST ===========\n\
                {:#?}\n============================",
                code
            );
        }
        if let Some(mut m) = MatchState::get_match(debug_active, search_scope, &code, &self.sema) {
            // Continue searching in each of our placeholders.
            for placeholder_value in m.placeholder_values.values_mut() {
                if let Some(placeholder_node) = &placeholder_value.node {
                    // Don't search our placeholder if it's the entire matched node, otherwise we'd
                    // find the same match over and over until we got a stack overflow.
                    if placeholder_node != code {
                        self.find_matches(
                            search_scope,
                            placeholder_node,
                            &mut placeholder_value.inner_matches,
                        );
                    }
                }
            }
            matches_out.push(m);
            return;
        }
        // If we've got a macro call, we already tried matching it pre-expansion, which is the only
        // way to match the whole macro, now try expanding it and matching the expansion.
        if let Some(macro_call) = ast::MacroCall::cast(code.clone()) {
            if let Some(expanded) = self.sema.expand(&macro_call) {
                if let Some(tt) = macro_call.token_tree() {
                    // When matching within a macro expansion, we only want to allow matches of
                    // nodes that originated entirely from within the token tree of the macro call.
                    // i.e. we don't want to match something that came from the macro itself.
                    self.find_matches(
                        &SearchScope {
                            restrict_range: Some(self.sema.original_range(tt.syntax())),
                            ..*search_scope
                        },
                        &expanded,
                        matches_out,
                    );
                }
            }
        }
        for child in code.children() {
            self.find_matches(search_scope, &child, matches_out);
        }
    }

    fn find_match_str(&self, pattern_str: &str, file_id: FileId) -> Result<Vec<String>, Error> {
        let mut matches = Vec::new();
        let file = self.sema.parse(file_id);
        let code = file.syntax();
        self.find_matches(
            &SearchScope {
                search: &SearchTrees::new(&parse_pattern(pattern_str, true)?),
                root_module: &self.root_module(code)?,
                restrict_range: None,
            },
            code,
            &mut matches,
        );
        let mut flattened_matches = Vec::new();
        flatten_matches(&matches, &mut flattened_matches);
        return Ok(flattened_matches);
    }

    fn apply_str(
        &self,
        search: &str,
        replacement: &str,
        file_id: FileId,
    ) -> Result<Option<String>, Error> {
        let search = parse_pattern(search, true)?;
        let replacement = parse_pattern(replacement, false)?;
        validate_rule(&search, &replacement)?;
        let file = self.sema.parse(file_id);
        let code = file.syntax();
        let mut matches = Vec::new();
        self.find_matches(
            &SearchScope {
                search: &SearchTrees::new(&search),
                root_module: &self.root_module(code)?,
                restrict_range: None,
            },
            code,
            &mut matches,
        );
        if matches.is_empty() {
            return Ok(None);
        }
        use ra_db::FileLoader;
        let mut file_source = self.sema.db.file_text(file_id).to_string();
        let edit = matches_to_edit(&matches, &replacement, &file_source, TextSize::from(0));
        edit.apply(&mut file_source);
        Ok(Some(file_source))
    }
}

fn flatten_matches(matches: &[Match], flattened_matches: &mut Vec<String>) {
    for m in matches {
        println!("M: {}", m.matched_node.text());
        flattened_matches.push(m.matched_node.text().to_string());
        for p in m.placeholder_values.values() {
            if let Some(n) = &p.node {
                println!("  P: {}", n.text());
            }
            flatten_matches(&p.inner_matches, flattened_matches);
        }
    }
}

fn matches_to_edit(
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

fn single_file(code: &str) -> (ra_ide_db::RootDatabase, FileId) {
    use ra_db::fixture::WithFixture;
    ra_ide_db::RootDatabase::with_single_file(code)
}

fn main() -> Result<(), Error> {
    let config: RerastConfig = argh::from_env();
    let (db, file_id) = single_file(&config.code);
    let match_finder = MatchFinder::new(config.debug_snippet, &db);
    if let Some(replace) = &config.replace {
        if let Some(rewritten) = match_finder.apply_str(&config.search, replace, file_id)? {
            println!("OUT: {}", rewritten);
        } else {
            println!("No replacement occurred");
        }
    } else {
        let matches = match_finder.find_match_str(&config.search, file_id)?;
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
        let (db, file_id) = single_file(code);
        let match_finder = MatchFinder::new(None, &db);
        match_finder.find_match_str(pattern, file_id).unwrap()
    }

    fn assert_matches(pattern: &str, code: &str, expected: &[&str]) {
        if !expected.is_empty() {
            println!(
                "If this test fails, run the following to debug it:\
                    \n  cargo run -- --code '{}' --search '{}' --debug-snippet '{}'",
                code, pattern, &expected[0]
            );
        }
        let r = find(pattern, code);
        assert_eq!(r, expected);
    }

    fn assert_no_match(pattern: &str, code: &str) {
        assert_matches(pattern, code, &[]);
    }

    fn apply(search: &str, replace: &str, code: &str) -> Result<Option<String>, Error> {
        let (db, file_id) = single_file(code);
        let match_finder = MatchFinder::new(None, &db);
        match_finder.apply_str(search, replace, file_id)
    }

    fn assert_replace(search: &str, replace: &str, code: &str, expected: &str) {
        let out = apply(search, replace, code).unwrap();
        if out != Some(expected.to_owned()) {
            println!(
                "Test is about to fail, to debug run (ideally with --debug-snippet set as well):\
                \n  cargo run -- --search '{}' --replace '{}' --code '{}'",
                search, replace, code,
            );
            if let Some(out) = out {
                println!("Expected:\n{}\n\nActual:\n{}\n", expected, out);
            } else {
                panic!("No replacement occurred");
            }
            panic!("Test failed, see above for details");
        }
    }

    #[test]
    fn ignores_whitespace() {
        assert_matches("1+2", "fn f() -> i32 {1  +  2}", &["1  +  2"]);
        assert_matches("1 + 2", "fn f() -> i32 {1+2}", &["1+2"]);
    }

    #[test]
    fn no_match() {
        assert_no_match("1 + 3", "fn f() -> i32 {1  +  2}");
    }

    #[test]
    fn match_fn_definition() {
        assert_matches(
            "fn $a($b: $t) {$c}",
            "fn f(a: i32) {bar()}",
            &["fn f(a: i32) {bar()}"],
        );
    }

    #[test]
    fn match_expr() {
        let code = "fn f() -> i32 {foo(40 + 2, 42)}";
        assert_matches("foo($a, $b)", code, &["foo(40 + 2, 42)"]);
        assert_no_match("foo($a, $b, $c)", code);
        assert_no_match("foo($a)", code);
    }

    // Make sure that when a placeholder has a choice of several nodes that it could consume, that
    // it doesn't consume too early and then fail the rest of the match.
    #[test]
    fn match_nested_method_calls() {
        assert_matches(
            "$a.z().z().z()",
            "fn f() {h().i().j().z().z().z().d().e()}",
            &["h().i().j().z().z().z()"],
        );
    }

    // Make sure that our node matching semantics don't differ within macro calls.
    #[test]
    fn match_nested_method_calls_with_macro_call() {
        assert_matches(
            "$a.z().z().z()",
            r#"
                macro_rules! m1 { ($a:expr) => {$a}; }
                fn f() {m1!(h().i().j().z().z().z().d().e())}"#,
            &["h().i().j().z().z().z()"],
        );
    }

    #[test]
    fn match_complex_expr() {
        let code = "fn f() -> i32 {foo(bar(40, 2), 42)}";
        assert_matches("foo($a, $b)", code, &["foo(bar(40, 2), 42)"]);
        assert_no_match("foo($a, $b, $c)", code);
        assert_no_match("foo($a)", code);
        assert_matches("bar($a, $b)", code, &["bar(40, 2)"]);
    }

    // Trailing commas in the code should be ignored.
    #[test]
    fn match_with_trailing_commas() {
        // Code has comma, pattern doesn't.
        assert_matches("foo($a, $b)", "fn f() {foo(1, 2,);}", &["foo(1, 2,)"]);
        assert_matches("Foo{$a, $b}", "fn f() {Foo{1, 2,};}", &["Foo{1, 2,}"]);

        // Pattern has comma, code doesn't.
        assert_matches("foo($a, $b,)", "fn f() {foo(1, 2);}", &["foo(1, 2)"]);
        assert_matches("Foo{$a, $b,}", "fn f() {Foo{1, 2};}", &["Foo{1, 2}"]);
    }

    #[test]
    fn match_type() {
        assert_matches("i32", "fn f() -> i32 {1  +  2}", &["i32"]);
        assert_matches("Option<$a>", "fn f() -> Option<i32> {42}", &["Option<i32>"]);
        assert_no_match("Option<$a>", "fn f() -> Result<i32, ()> {42}");
    }

    #[test]
    fn match_struct_instantiation() {
        assert_matches(
            "Foo {bar: 1, baz: 2}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            &["Foo {bar: 1, baz: 2}"],
        );
        // Now with placeholders for all parts of the struct. If we're not careful here, then $a
        // will consume the whole record field (`bar: 1`) then the `:` in the pattern will fail to
        // match.
        assert_matches(
            "Foo {$a: $b, $c: $d}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            &["Foo {bar: 1, baz: 2}"],
        );
        assert_matches("Foo {}", "fn f() {Foo {}}", &["Foo {}"]);
    }

    #[test]
    fn match_path() {
        assert_matches("foo::bar", "fn f() {foo::bar(42)}", &["foo::bar"]);
        assert_matches("$a::bar", "fn f() {foo::bar(42)}", &["foo::bar"]);
        assert_matches("foo::$b", "fn f() {foo::bar(42)}", &["foo::bar"]);
    }

    #[test]
    fn match_pattern() {
        assert_matches(
            "Some($a)",
            "fn f() {if let Some(x) = foo() {}}",
            &["Some(x)"],
        );
    }

    // If our pattern has a full path, e.g. a::b::c() and the code has c(), but c resolves to
    // a::b::c, then we should match.
    #[test]
    fn match_fully_qualified_fn_path() {
        let code = r#"
            mod a {
                mod b {
                    fn c() {}
                }
            }
            use a::b::c;
            fn f1() {
                c(42);
            }
            "#;
        assert_matches("a::b::c($a)", code, &["c(42)"]);
    }

    #[test]
    fn match_reordered_struct_instantiation() {
        assert_matches(
            "Foo {aa: 1, b: 2, ccc: 3}",
            "fn f() {Foo {b: 2, ccc: 3, aa: 1}}",
            &["Foo {b: 2, ccc: 3, aa: 1}"],
        );
        assert_no_match("Foo {a: 1}", "fn f() {Foo {b: 1}}");
        assert_no_match("Foo {a: 1}", "fn f() {Foo {a: 2}}");
        assert_no_match("Foo {a: 1, b: 2}", "fn f() {Foo {a: 1}}");
        assert_no_match("Foo {a: 1, b: 2}", "fn f() {Foo {b: 2}}");
        assert_no_match("Foo {a: 1, }", "fn f() {Foo {a: 1, b: 2}}");
        assert_no_match("Foo {a: 1, z: 9}", "fn f() {Foo {a: 1}}");
    }

    #[test]
    fn match_macro_invocation() {
        assert_matches("foo!($a)", "fn() {foo(foo!(foo()))}", &["foo!(foo())"]);
        assert_matches(
            "foo!(41, $a, 43)",
            "fn() {foo!(41, 42, 43)}",
            &["foo!(41, 42, 43)"],
        );
        assert_no_match("foo!(50, $a, 43)", "fn() {foo!(41, 42, 43}");
        assert_no_match("foo!(41, $a, 50)", "fn() {foo!(41, 42, 43}");
        assert_matches("foo!($a())", "fn() {foo!(bar())}", &["foo!(bar())"]);
    }

    // When matching within a macro expansion, we only allow matches of nodes that originated from
    // the macro call, not from the macro definition.
    #[test]
    fn no_match_expression_from_macro() {
        assert_no_match(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    () => {42.clone()}
                }
                fn f1() {m1!()}
                "#,
        );
    }

    // We definitely don't want to allow matching of an expression that part originates from the
    // macro call `42` and part from the macro definition `.clone()`.
    #[test]
    fn no_match_split_expression() {
        assert_no_match(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    ($x:expr) => {$x.clone()}
                }
                fn f1() {m1!(42)}
                "#,
        );
    }

    #[test]
    fn expression_type_constraints() {
        let code = r#"
            mod m1 {
                pub mod m2 {
                    #[derive(Clone)]
                    struct Foo {}
                }
                fn f1() -> m2::Foo {
                    m2::Foo {}
                }
            }
            fn f2() {
                String::new().clone();
                true.clone();
                m1::f1().clone();
            }
            "#;
        assert_matches(
            "${a:type(m1::m2::Foo)}.clone()",
            code,
            &["m1::f1().clone()"],
        );
        assert_no_match("${a:type(m1::m2::Bar)}.clone()", code);
        assert_matches("${a:type(bool)}.clone()", code, &["true.clone()"]);
    }

    #[test]
    fn invalid_placeholder() {
        assert_eq!(
            parse_pattern("($)", true).err(),
            Some(Error::new(
                "Placeholders should either be $name or ${name:constraints}"
            ))
        );
    }

    #[test]
    fn replace_function_call() {
        assert_replace(
            "foo()",
            "bar()",
            "fn f1() {foo(); foo();}",
            "fn f1() {bar(); bar();}",
        );
    }

    #[test]
    fn replace_function_call_with_placeholders() {
        assert_replace(
            "foo($a, $b)",
            "bar($b, $a)",
            "fn f1() {foo(5, 42)}",
            "fn f1() {bar(42, 5)}",
        );
    }

    #[test]
    fn replace_nested_function_calls() {
        assert_replace(
            "foo($a)",
            "bar($a)",
            "fn f1() {foo(foo(42))}",
            "fn f1() {bar(bar(42))}",
        );
    }

    #[test]
    fn replace_type() {
        assert_replace(
            "Result<(), $a>",
            "Option<$a>",
            "fn f1() -> Result<(), Vec<Error>> {foo()}",
            "fn f1() -> Option<Vec<Error>> {foo()}",
        );
    }

    #[test]
    fn replace_struct_init() {
        assert_replace(
            "Foo {a: $a, b: $b}",
            "Foo::new($a, $b)",
            "fn f1() {Foo{b: 1, a: 2}}",
            "fn f1() {Foo::new(2, 1)}",
        );
    }

    #[test]
    fn replace_macro_invocations() {
        assert_replace(
            "try!($a)",
            "$a?",
            "fn f1() -> Result<(), E> {bar(try!(foo()));}",
            "fn f1() -> Result<(), E> {bar(foo()?);}",
        );
        assert_replace(
            "foo!($a($b))",
            "foo($b, $a)",
            "fn f1() {foo!(abc(def() + 2));}",
            "fn f1() {foo(def() + 2, abc);}",
        );
    }

    #[test]
    fn match_within_macro_invocation() {
        let code = r#"
                macro_rules! foo {
                    ($a:stmt; $b:expr) => {
                        $b    
                    };
                }
                struct A {}
                impl A {
                    fn bar() {}
                }
                fn f1() {
                    let aaa = A {};
                    foo!(macro_ignores_this(); aaa.bar());
                }
            "#;
        assert_matches("$a.bar()", code, &["aaa.bar()"]);
    }

    // We support matching of whole macros pre-expansion. We also support matching nodes
    // post-expansion. However post expansion, no macro calls are present, so if there's a macro
    // call within a macro call, we currently can't match it. It would probably be possible to
    // implement provided the search pattern didn't start or end with a placeholder.
    #[test]
    #[ignore]
    fn match_nested_macro_invocations() {
        assert_matches(
            "try!($a)",
            "fn f1() {other_macro!(bar(try!(foo())));",
            &["try!(foo())"],
        );
    }

    #[test]
    #[ignore]
    fn replace_nested_macro_invocations() {
        assert_replace(
            "try!($a)",
            "$a?",
            "fn f1() {try!(bar(try!(foo())));",
            "fn f1() {bar(foo()?)?;}",
        );
    }

    #[test]
    fn undefined_placeholder_in_replacement() {
        assert_eq!(
            apply("42", "$a", "fn f() ->i32 {42}"),
            Err(Error::new(
                "Replacement contains undefined placeholders: $a"
            ))
        );
        assert_eq!(
            apply("43", "$a", "fn f() ->i32 {42}"),
            Err(Error::new(
                "Replacement contains undefined placeholders: $a"
            ))
        );
    }

    #[test]
    fn replace_within_macro_invocation() {
        let code = r#"
                macro_rules! foo {
                    ($a:stmt; $b:expr) => {
                        $b
                    };
                }
                struct A {}
                impl A {
                    fn bar() {}
                }
                fn f1() -> i32 {
                    let aaa = A {};
                    foo!(macro_ignores_this(); aaa.bar());
                    foo!(macro_ignores_this(); 1 + 2 + 3);
                    1 + 2 + 3
                }
            "#;
        assert_replace(
            "$a.bar()",
            "bar2($a)",
            code,
            &code.replace("aaa.bar()", "bar2(aaa)"),
        );
        assert_replace(
            "$a + $b",
            "$b - $a",
            code,
            &code.replace("1 + 2 + 3", "3 - 2 - 1"),
        );
    }

    #[test]
    fn duplicate_placeholders() {
        assert_eq!(
            apply("foo($a, $a)", "42", "fn f() {}"),
            Err(Error::new("Duplicate placeholder: $a"))
        );
    }

    #[test]
    fn replace_binary_op() {
        assert_replace(
            "$a + $b",
            "$b + $a",
            "fn f() {2 * 3 + 4 * 5}",
            "fn f() {4 * 5 + 2 * 3}",
        );
        assert_replace(
            "$a + $b",
            "$b + $a",
            "fn f() {1 + 2 + 3 + 4}",
            "fn f() {4 + 3 + 2 + 1}",
        );
    }

    #[test]
    fn match_binary_op() {
        assert_matches(
            "$a + $b",
            "fn f() {1 + 2 + 3 + 4}",
            &["1 + 2 + 3 + 4", "1 + 2 + 3", "1 + 2"],
        );
    }
}
