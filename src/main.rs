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
use fmt::Display;
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
}

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
    Ok(raw_tokens
        .iter()
        .map(|raw_token| {
            let token_len = usize::from(raw_token.len);
            let token = Token {
                kind: raw_token.kind,
                text: SmolStr::new(&source[start..start + token_len]),
            };
            start += token_len;
            token
        })
        .collect())
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

struct Placeholder {
    ident: SmolStr,
    // The next token after this placeholder in the pattern, if any. When matching, we then consume
    // the outermost node that is followed by this token. This allows `$a: 1` to match `foo: 1`
    // instead of the placeholder consuming the whole thing then failing when we get to the `:`
    terminator: Option<Token>,
    constraints: Vec<Constraint>,
}

enum Constraint {
    ExprType(Vec<SmolStr>),
}

// An "error" indicating that matching failed. Use the fail_match! macro to create and return this.
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

struct MatchState<'db, 'sema> {
    placeholder_values: HashMap<SmolStr, PlaceholderMatch>,
    sema: &'sema ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
    root_module: ra_hir::Module,
}

type PatternIterator<'a> = std::iter::Peekable<std::slice::Iter<'a, PatternElement>>;

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
        };
        let mut pattern_iter = search_scope.search.iter().peekable();
        match_state.attempt_match_node(&mut pattern_iter, code)?;
        let remaining_pattern: Vec<_> = pattern_iter.map(|p| p.to_string()).collect();
        if !remaining_pattern.is_empty() {
            fail_match!(
                "Code exhausted, but pattern still has content: {}",
                remaining_pattern.join("")
            );
        }
        if let Some(restrict_range) = &search_scope.restrict_range {
            let code_range = sema.original_range(code);
            if restrict_range.file_id != code_range.file_id
                || !restrict_range.range.contains_range(code_range.range)
            {
                fail_match!("Node originated from a macro");
            }
        }
        Ok(match_state)
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
        pattern: &mut PatternIterator,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Handle placeholders.
        let pattern_start = pattern.clone();
        if let Some(PatternElement::Placeholder(placeholder)) = pattern.peek() {
            let mut children = code.children_with_tokens();
            if let Some(SyntaxElement::Node(child)) = children.next() {
                // We have the option to go deeper before binding the placeholder since our first
                // child is another node, with no tokens before it. Try going deeper and if that
                // fails, reset our pattern and try again binding the placeholder to this node.
                if self.attempt_match_node(pattern, &child).is_ok()
                    && self.attempt_match_children(pattern, &mut children).is_ok()
                {
                    return Ok(());
                } else {
                    *pattern = pattern_start;
                }
            }
            // Actually consume the placeholder that we peeked above.
            pattern.next();
            for constraint in &placeholder.constraints {
                self.validate_constraint(constraint, code)?;
            }
            // TODO: Check that the original range is from our file, otherwise reject the match.
            let original_range = self.sema.original_range(code);
            self.placeholder_values.insert(
                placeholder.ident.clone(),
                PlaceholderMatch::new(code, original_range.range),
            );
            return Ok(());
        }
        match code.kind() {
            SyntaxKind::TOKEN_TREE => self.attempt_match_token_tree(pattern, code)?,
            SyntaxKind::RECORD_FIELD_LIST => {
                self.attempt_match_record_field_list(pattern, &code)?
            }
            _ => self.attempt_match_node_children(pattern, &code)?,
        }

        Ok(())
    }

    fn attempt_match_node_children(
        &mut self,
        pattern: &mut PatternIterator,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        self.attempt_match_children(pattern, &mut code.children_with_tokens())
    }

    fn attempt_match_children(
        &mut self,
        pattern: &mut PatternIterator,
        code: &mut ra_syntax::SyntaxElementChildren,
    ) -> Result<(), MatchFailed> {
        for child in code {
            match child {
                SyntaxElement::Node(c) => self.attempt_match_node(pattern, &c)?,
                SyntaxElement::Token(c) => self.attempt_match_token(pattern, &c)?,
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
            let mut ty_path: Vec<SmolStr> = module
                .path_to_root(self.sema.db)
                .iter()
                .filter_map(|m| m.name(self.sema.db))
                .map(|name| SmolStr::new(name.to_string()))
                .collect();
            ty_path.reverse();
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
        if let Some(PatternElement::Token(p)) = pattern.peek() {
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
        let code_text = code.text().to_string();
        // A token in the syntax tree might correspond to multiple tokens in the pattern. For
        // example, in the syntax tree `->` would be a single token of type THIN_ARROW, whereas in
        // the pattern it will be MINUS, R_ANGLE.
        let mut code_remaining = code_text.as_str();
        while !code_remaining.is_empty() {
            match pattern.next() {
                Some(PatternElement::Placeholder(_)) => {
                    // Not sure if this is actually reachable.
                    fail_match!("Placeholders matching tokens is not yet implemented");
                }
                Some(PatternElement::Token(p)) => {
                    if code_remaining.starts_with(p.text.as_str()) {
                        code_remaining = &code_remaining[p.text.as_str().len()..];
                    } else {
                        fail_match!(
                            "Pattern had token `{}` while code had token `{}`",
                            p.text,
                            code_text,
                        );
                    }
                }
                None => {
                    fail_match!(
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
    // of tokens. TODO: See if we can use the macro expansion to identify nodes within the macro.
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
                                        // We have a subtree that starts with the next token in our pattern.
                                        self.attempt_match_token_tree(pattern, &n)?;
                                        break;
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
                        fail_match!(
                            "Reached end of pattern, but we're part way through a token tree at token {:?}",
                            token);
                    }
                }
                SyntaxElement::Node(node) => {
                    if node.kind() != SyntaxKind::TOKEN_TREE {
                        fail_match!("Found unexpected node inside token tree {:?}", node);
                    }
                    self.attempt_match_token_tree(pattern, &node)?;
                }
            }
        }
        Ok(())
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
                        // We validated that all placeholder references were valid before we started.
                        unreachable!();
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

struct SearchScope<'a> {
    search: &'a [PatternElement],
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
            println!(
                "========= PATTERN ==========\n{:#?}\
                \n\n============ AST ===========\n\
                {:#?}\n============================",
                search_scope.search, code
            );
        }
        if let Some(mut m) = MatchState::get_match(debug_active, search_scope, &code, &self.sema) {
            // Continue searching in each of our placeholders.
            for placeholder_value in m.placeholder_values.values_mut() {
                if let Some(placeholder_node) = &placeholder_value.node {
                    self.find_matches(
                        search_scope,
                        placeholder_node,
                        &mut placeholder_value.inner_matches,
                    );
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
                search: &parse_pattern(pattern_str, true)?,
                root_module: &self.root_module(code)?,
                restrict_range: None,
            },
            code,
            &mut matches,
        );
        return Ok(matches
            .into_iter()
            .map(|m| m.matched_node.text().to_string())
            .collect());
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
                search: &search,
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

    // Make sure that when a placeholder has a choice of several nodes that it could consume, that
    // it doesn't consume too early and then fail the rest of the match.
    #[test]
    fn match_nested_method_calls() {
        assert_matches!(
            "$a.z().z().z()",
            "fn f() {h().i().j().z().z().z().d().e()}",
            ["h().i().j().z().z().z()"]
        );
    }

    #[test]
    fn match_complex_expr() {
        let code = "fn f() -> i32 {foo(bar(40, 2), 42)}";
        assert_matches!("foo($a, $b)", code, ["foo(bar(40, 2), 42)"]);
        assert_no_match!("foo($a, $b, $c)", code);
        assert_no_match!("foo($a)", code);
        assert_matches!("bar($a, $b)", code, ["bar(40, 2)"]);
    }

    // Trailing commas in the code should be ignored.
    #[test]
    fn match_with_trailing_commas() {
        // Code has comma, pattern doesn't.
        assert_matches!("foo($a, $b)", "fn f() {foo(1, 2,);}", ["foo(1, 2,)"]);
        assert_matches!("Foo{$a, $b}", "fn f() {Foo{1, 2,};}", ["Foo{1, 2,}"]);

        // Pattern has comma, code doesn't.
        assert_matches!("foo($a, $b,)", "fn f() {foo(1, 2);}", ["foo(1, 2)"]);
        assert_matches!("Foo{$a, $b,}", "fn f() {Foo{1, 2};}", ["Foo{1, 2}"]);
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

    // When matching within a macro expansion, we only allow matches of nodes that originated from
    // the macro call, not from the macro definition.
    #[test]
    fn no_match_expression_from_macro() {
        assert_no_match!(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    () => {42.clone()}
                }
                fn f1() {m1!()}
                "#
        );
    }

    // We definitely don't want to allow matching of an expression that part originates from the
    // macro call `42` and part from the macro definition `.clone()`.
    #[test]
    fn no_match_split_expression() {
        assert_no_match!(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    ($x:expr) => {$x.clone()}
                }
                fn f1() {m1!(42)}
                "#
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
        assert_matches!("${a:type(m1::m2::Foo)}.clone()", code, ["m1::f1().clone()"]);
        assert_no_match!("${a:type(m1::m2::Bar)}.clone()", code);
        assert_matches!("${a:type(bool)}.clone()", code, ["true.clone()"]);
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
        assert_matches!("$a.bar()", code, ["aaa.bar()"]);
    }

    // Although matching macros is supported, matching within macros isn't. For patterns that don't
    // start or end with a placeholder (like this one) it wouldn't be too hard to implement, but for
    // patterns like $a.foo(), we wouldn't know where to start matching.
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
                fn f1() {
                    let aaa = A {};
                    foo!(macro_ignores_this(); aaa.bar());
                }
            "#;
        assert_replace(
            "$a.bar()",
            "bar2($a)",
            code,
            &code.replace("aaa.bar()", "bar2(aaa)"),
        );
    }

    // TODO: Macro that swaps the order of expressions so that the order we match in is not the
    // order in the file.

    // TODO: Match an expression that originates entirely from the macro.

    #[test]
    fn duplicate_placeholders() {
        assert_eq!(
            apply("foo($a, $a)", "42", "fn f() {}"),
            Err(Error::new("Duplicate placeholder: $a"))
        );
    }
}
