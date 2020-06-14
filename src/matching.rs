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

///! This module is responsible for checking if code matches a pattern.
use super::SearchScope;
use crate::patterns::{
    self, Constraint, InvalidPatternTree, PatternElement, PatternNode, PatternTree, Token,
};
use ra_db::FileRange;
use ra_syntax::ast::{self, AstNode};
use ra_syntax::{SmolStr, SyntaxElement, SyntaxKind, SyntaxNode, TextRange};
use std::cell::Cell;
use std::collections::HashMap;

// Creates a match error. If we're currently attempting to match some code that we thought we were
// going to match, as indicated by the --debug-snippet flag, then populate the reason field.
macro_rules! match_error {
    ($e:expr) => {{
            MatchFailed {
                reason: if recording_match_fail_reasons() {
                    Some(format!("{}", $e))
                } else {
                    None
                }
            }
    }};
    ($fmt:expr, $($arg:tt)+) => {{
        MatchFailed {
            reason: if recording_match_fail_reasons() {
                Some(format!($fmt, $($arg)+))
            } else {
                None
            }
        }
    }};
}

// Fails the current match attempt, recording the supplied reason if we're recording match fail reasons.
macro_rules! fail_match {
    ($($args:tt)*) => {return Err(match_error!($($args)*))};
}

/// Information about a match that was found.
#[derive(Debug)]
pub(crate) struct Match {
    pub(crate) range: TextRange,
    pub(crate) matched_node: SyntaxNode,
    pub(crate) placeholder_values: HashMap<SmolStr, PlaceholderMatch>,
}

/// Information about a placeholder bound in a match.
#[derive(Debug)]
pub(crate) struct PlaceholderMatch {
    /// The node that the placeholder matched to. If set, then we'll search for further matches
    /// within this node. It isn't set when we match tokens within a macro call's token tree.
    pub(crate) node: Option<SyntaxNode>,
    pub(crate) range: FileRange,
    /// More matches, found within `node`.
    pub(crate) inner_matches: Vec<Match>,
}

/// Stores our search pattern, parsed as each different kind of thing we can look for. As we
/// traverse the AST, we get the appropriate one of these for the type of node we're on. For many
/// search patterns, only some of these will be present.
pub(crate) struct SearchTrees {
    expr: Result<PatternNode, InvalidPatternTree>,
    type_ref: Result<PatternNode, InvalidPatternTree>,
    item: Result<PatternNode, InvalidPatternTree>,
    path: Result<PatternNode, InvalidPatternTree>,
    pattern: Result<PatternNode, InvalidPatternTree>,
}

/// An "error" indicating that matching failed. Use the fail_match! macro to create and return this.
#[derive(Clone)]
pub(crate) struct MatchFailed {
    /// The reason why we failed to match. Only present when debug_active true in call to
    /// `get_match`.
    reason: Option<String>,
}

/// Checks if `code` matches the search pattern found in `search_scope`, returning information about
/// the match, if it does. Since we only do matching in this module and searching is done by the
/// parent module, we don't populate nested matches.
pub(crate) fn get_match(
    debug_active: bool,
    search_scope: &SearchScope,
    code: &SyntaxNode,
    sema: &ra_hir::Semantics<ra_ide_db::RootDatabase>,
) -> Option<Match> {
    RECORDING_MATCH_FAIL_REASONS.with(|c| c.set(debug_active));
    let result = match MatchState::try_match(search_scope, code, sema) {
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

/// State used while attempting to match our search pattern against a particular node of the AST.
struct MatchState<'db, 'sema> {
    placeholder_values: HashMap<SmolStr, PlaceholderMatch>,
    sema: &'sema ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
    root_module: ra_hir::Module,
    /// If any placeholders come from anywhere outside of this range, then the match will be
    /// rejected.
    restrict_range: Option<FileRange>,
}

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

    /// Checks that `range` is within the permitted range if any. This is applicable when we're
    /// processing a macro expansion and we want to fail the match if we're working with a node that
    /// didn't originate from the token tree of the macro call.
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

    fn attempt_match_node(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Handle placeholders.
        if let Some(placeholder) = pattern.placeholder() {
            for constraint in &placeholder.constraints {
                self.check_constraint(constraint, code)?;
            }
            let original_range = self.sema.original_range(code);
            // We validated the range for the node when we started the match, so the placeholder
            // probably can't fail range validation, but just to be safe...
            self.validate_range(&original_range)?;
            self.placeholder_values.insert(
                placeholder.ident.clone(),
                PlaceholderMatch::new(code, original_range),
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
        self.attempt_match_sequences(pattern.children.iter(), code.children_with_tokens())
    }

    fn attempt_match_sequences(
        &mut self,
        pattern_it: std::slice::Iter<PatternTree>,
        mut code_it: ra_syntax::SyntaxElementChildren,
    ) -> Result<(), MatchFailed> {
        let mut pattern_it = pattern_it.peekable();
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
                    Some(p) => fail_match!("Pattern wanted '{}', code has {}", p, c.text()),
                    None => fail_match!("Pattern reached end, code has {}", c.text()),
                },
            }
        }
    }

    fn attempt_match_token(
        &self,
        pattern: &mut std::iter::Peekable<std::slice::Iter<PatternTree>>,
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

    fn check_constraint(
        &self,
        constraint: &Constraint,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        match constraint {
            Constraint::Type(constraint_path) => {
                let ty = self.node_type(code)?;
                let ty_path = self.get_type_path(&ty)?;
                if ty_path != constraint_path.as_slice() {
                    fail_match!(
                        "Expected type {}, found {}",
                        constraint_path.join("::"),
                        ty_path.join("::")
                    );
                }
            }
            Constraint::Kind(kind) => {
                kind.matches(code)?;
            }
            Constraint::Not(sub) => {
                if self.check_constraint(&*sub, code).is_ok() {
                    fail_match!("Constraint {:?} failed for '{}'", constraint, code.text());
                }
            }
        }
        Ok(())
    }

    fn node_type(&self, code: &SyntaxNode) -> Result<ra_hir::Type, MatchFailed> {
        if let Some(expr) = ast::Expr::cast(code.clone()) {
            self.sema.type_of_expr(&expr).ok_or_else(|| {
                match_error!("Couldn't get expression type for code `{}`", code.text())
            })
        } else if let Some(pat) = ast::Pat::cast(code.clone()) {
            self.sema
                .type_of_pat(&pat)
                .ok_or_else(|| match_error!("Couldn't get pat type for code `{}`", code.text()))
        } else {
            fail_match!(
                "Placeholder requested type of unsupported node {:?}",
                code.kind()
            )
        }
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

    /// We want to allow fully-qualified paths to match non-fully-qualified paths that resolve to
    /// the same thing.
    fn attempt_match_path(
        &mut self,
        pattern: &PatternNode,
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        // Start by doing a straight-up matching of tokens. That way any match-failure reasons will
        // be related to failure to resolve paths or similar reasons, which are more likely to be
        // surprising and interesting.
        if self.attempt_match_node_children(pattern, code).is_ok() {
            return Ok(());
        }

        // Paths may contain paths. Find the first (left-most) path and work with that. It has the
        // greatest chance of being able to be resolved anyway.

        let path = ast::Path::cast(inner_most_path(code.clone()))
            .ok_or_else(|| match_error!("Failed to convert node to ast::Path"))?;
        if let Some(ra_hir::PathResolution::Def(resolved_def)) = self.sema.resolve_path(&path) {
            let module = resolved_def.module(self.sema.db).ok_or_else(|| {
                match_error!("Couldn't find module for '{}'", path.syntax().text())
            })?;
            self.attempt_match_resolved_path(pattern, &mut self.module_path(&module), code)?;
        } else {
            fail_match!("Couldn't resolve");
        }
        Ok(())
    }

    /// Finds the first token in `code`, then matches `resolved_path` against `pattern` before
    /// continuing with `code`.
    fn attempt_match_resolved_path(
        &mut self,
        pattern: &PatternNode,
        resolved_path: &[SmolStr],
        code: &SyntaxNode,
    ) -> Result<(), MatchFailed> {
        let mut pattern_children = pattern.children.iter();
        let mut code_children = code.children_with_tokens();
        match (pattern_children.next(), &code_children.next()) {
            (Some(PatternTree::Node(p)), Some(SyntaxElement::Node(c))) => {
                match (p.kind, c.kind()) {
                    (SyntaxKind::PATH, SyntaxKind::PATH) => {
                        self.attempt_match_resolved_path(p, resolved_path, &c)?;
                    }
                    (SyntaxKind::PATH, SyntaxKind::PATH_SEGMENT) => {
                        self.attempt_match_resolved_path_prefix(
                            p,
                            &mut resolved_path.iter().peekable(),
                        )?;
                        // Reset code back to the start of the path, since the PATH_SEGMENT will need to
                        // be consumed by subsequent parts of the pattern.
                        code_children = code.children_with_tokens();
                        // Advance pattern past the :: that should come next.
                        match pattern_children.next() {
                            Some(PatternTree::Token(Token {
                                kind: SyntaxKind::COLON2,
                                ..
                            })) => {}
                            Some(p) => {
                                fail_match!(
                                    "Unexpected element in pattern. Expected '::', found {}",
                                    p
                                );
                            }
                            None => {
                                fail_match!(
                                    "Unexpected end of pattern children while looking for '::'"
                                );
                            }
                        }
                    }
                    (p, c) => fail_match!("Unhandled pattern child pair {:?}, {:?}", p, c),
                }
            }
            (Some(PatternTree::Placeholder(_)), _) => {
                fail_match!("Placeholders in patterns aren't yet supported")
            }
            (p, c) => fail_match!("Unhandled pattern child pair {:?}, {:?}", p, c),
        }
        self.attempt_match_sequences(pattern_children, code_children)
    }

    fn attempt_match_resolved_path_prefix<'p>(
        &self,
        pattern: &'p PatternNode,
        path: &mut std::iter::Peekable<std::slice::Iter<SmolStr>>,
    ) -> Result<(), MatchFailed> {
        for p in &pattern.children {
            match p {
                PatternTree::Node(n) => self.attempt_match_resolved_path_prefix(&n, path)?,
                PatternTree::Token(t) => {
                    if t.kind == SyntaxKind::IDENT {
                        let path_next = path.next().ok_or_else(|| {
                            match_error!("Pattern '{}' didn't match to anything", t.text)
                        })?;
                        if t.text != *path_next {
                            fail_match!(
                                "Pattern had '{}', path resolved from code, had '{}'",
                                t.text,
                                path_next
                            )
                        }
                    }
                }
                PatternTree::Placeholder(_) => {
                    fail_match!("Matching placeholders to resolved paths is not supported")
                }
            }
        }
        Ok(())
    }

    /// We want to allow the records to match in any order, so we have special matching logic for
    /// them.
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
                        let code_record = fields_by_name.remove(ident).ok_or_else(|| {
                            match_error!(
                                "Placeholder has record field '{}', but code doesn't",
                                ident
                            )
                        })?;
                        self.attempt_match_node(p, &code_record)?;
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

    /// Outside of token trees, a placeholder can only match a single AST node, whereas in a token
    /// tree it can match a sequence of tokens. Note, that this code will only be used when the
    /// pattern matches the macro invocation. For matches within the macro call, we'll already have
    /// expanded the macro.
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
                    PlaceholderMatch::from_range(FileRange {
                        file_id: self.sema.original_range(code).file_id,
                        range: first_matched_token
                            .text_range()
                            .cover(last_matched_token.text_range()),
                    }),
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

/// Returns the left most path node in `path` (possibly `path`).
fn inner_most_path(path: SyntaxNode) -> SyntaxNode {
    if let Some(SyntaxElement::Node(first_child)) = path.first_child_or_token() {
        if first_child.kind() == SyntaxKind::PATH {
            return inner_most_path(first_child);
        }
    }
    path
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

impl PlaceholderMatch {
    fn new(node: &SyntaxNode, range: FileRange) -> Self {
        Self {
            node: Some(node.clone()),
            range,
            inner_matches: Vec::new(),
        }
    }

    fn from_range(range: FileRange) -> Self {
        Self {
            node: None,
            range,
            inner_matches: Vec::new(),
        }
    }
}

// Our search pattern, parsed as each different kind of syntax node we might encounter.
impl SearchTrees {
    pub(crate) fn new(tokens: &[PatternElement]) -> Self {
        Self {
            expr: patterns::create_pattern_tree(tokens, ra_parser::FragmentKind::Expr),
            type_ref: patterns::create_pattern_tree(tokens, ra_parser::FragmentKind::Type),
            item: patterns::create_pattern_tree(tokens, ra_parser::FragmentKind::Item),
            path: patterns::create_pattern_tree(tokens, ra_parser::FragmentKind::Path),
            pattern: patterns::create_pattern_tree(tokens, ra_parser::FragmentKind::Pattern),
        }
    }

    pub(crate) fn tree_for_kind(&self, kind: SyntaxKind) -> Result<&PatternNode, MatchFailed> {
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

impl patterns::NodeKind {
    fn matches(&self, node: &SyntaxNode) -> Result<(), MatchFailed> {
        let ok = match self {
            Self::Literal => ast::Literal::can_cast(node.kind()),
        };
        if !ok {
            fail_match!("Code '{}' isn't of kind {:?}", node.text(), self);
        }
        Ok(())
    }
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
