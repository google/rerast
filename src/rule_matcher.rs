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

use super::hir_id_from_path;
use crate::code_substitution::CodeSubstitution;
use crate::definitions::RerastDefinitions;
use crate::rule_finder::StartMatch;
use crate::rules::{Rule, Rules};
use crate::Config;
use rustc::hir::{self, intravisit, HirId};
use rustc::infer::{self, InferCtxt};
use rustc::traits::ObligationCause;
use rustc::ty::subst::Subst;
use rustc::ty::{self, TyCtxt};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::mem;
use syntax;
use syntax::ast;
use syntax::ast::NodeId;
use syntax::ptr::P;
use syntax::source_map::{self, Spanned};
use syntax::symbol::Symbol;
use syntax_pos::{Span, SpanSnippetError, DUMMY_SP};

#[macro_export]
macro_rules! debug {
    ($state:expr, $($args:expr),*) => {
        if $state.debug_active {
            println!($($args),*);
        }
    }
}

pub(crate) struct RuleMatcher<'r, 'a, 'gcx: 'r + 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rules: &'r Rules<'gcx>,
    matches: Matches<'r, 'gcx>,
    rule_mod_symbol: Symbol,
    parent_expr: Option<&'gcx hir::Expr>,
    body_id: Option<hir::BodyId>,
    rerast_definitions: RerastDefinitions<'gcx>,
    config: Config,
    debug_active: bool,
}

impl<'r, 'a, 'gcx> RuleMatcher<'r, 'a, 'gcx> {
    pub(crate) fn find_matches(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        rerast_definitions: RerastDefinitions<'gcx>,
        krate: &'gcx hir::Crate,
        rules: &'r Rules<'gcx>,
        config: Config,
    ) -> Matches<'r, 'gcx> {
        let mut matcher = RuleMatcher {
            tcx,
            rules,
            matches: Matches::new(),
            rule_mod_symbol: Symbol::intern(super::RULES_MOD_NAME),
            parent_expr: None,
            body_id: None,
            rerast_definitions,
            config,
            debug_active: false,
        };
        intravisit::walk_crate(&mut matcher, krate);
        matcher.matches
    }

    fn should_debug_node<T: StartMatch + 'gcx>(&self, node: &'gcx T) -> bool {
        if self.config.debug_snippet.is_empty() {
            return false;
        }
        self.tcx
            .sess
            .source_map()
            .span_to_snippet(node.span())
            .map(|snippet| {
                if self.config.debug_snippet == "list_all" {
                    println!("snippet: {}", snippet);
                }
                snippet == self.config.debug_snippet
            })
            .unwrap_or(false)
    }

    fn get_first_match<T: StartMatch + 'gcx>(
        &mut self,
        node: &'gcx T,
        parent_node: Option<&'gcx T>,
        rules: &'r [Rule<'gcx, T>],
    ) -> Option<Match<'r, 'gcx, T>> {
        self.debug_active = self.should_debug_node(node);
        debug!(self, "node: {:?}", node);
        for rule in rules {
            if let Some((_, original_span)) = get_original_spans(rule.search.span(), node.span()) {
                let m = self.get_match(node, parent_node, original_span, rule);
                if m.is_some() {
                    debug!(self, "Matched");
                    self.debug_active = false;
                    return m;
                }
            }
        }
        debug!(self, "Didn't match");
        self.debug_active = false;
        None
    }

    fn get_match<T: StartMatch + 'gcx>(
        &mut self,
        node: &'gcx T,
        parent_node: Option<&'gcx T>,
        original_span: Span,
        rule: &'r Rule<'gcx, T>,
    ) -> Option<Match<'r, 'gcx, T>> {
        let rule_fn_id = self.tcx.hir().body_owner_def_id(rule.body_id);
        let rule_tables = self.tcx.body_tables(rule.body_id);
        let rule_body = self.tcx.hir().body(rule.body_id);

        let maybe_match_placeholders = self.tcx.infer_ctxt().enter(|infcx| {
            let tcx = infcx.tcx;
            let substs = infcx.fresh_substs_for_item(tcx.def_span(rule_fn_id), rule_fn_id);
            let placeholder_types_by_id = rule_body
                .arguments
                .iter()
                .map(|arg| {
                    (arg.pat.hir_id, {
                        let ty = rule_tables.node_type(arg.hir_id);
                        ty.subst(tcx, substs)
                    })
                })
                .collect();

            let mut match_state = MatchState {
                tcx,
                infcx,
                body_id: self.body_id,
                rule_type_tables: rule_tables,
                match_placeholders: MatchPlaceholders::new(),
                placeholder_types_by_id,
                rerast_definitions: self.rerast_definitions,
                placeholder_ids: &rule.placeholder_ids,
                bindings_can_match_patterns: T::bindings_can_match_patterns(),
                debug_active: self.debug_active,
            };

            if rule.search.attempt_match(&mut match_state, node) {
                Some(match_state.match_placeholders)
            } else {
                None
            }
        });
        maybe_match_placeholders.map(|match_placeholders| Match {
            rule,
            node,
            match_placeholders,
            parent_node,
            original_span,
        })
    }

    fn process_children_of_expression(&mut self, expr: &'gcx hir::Expr) {
        let old_parent = self.parent_expr;
        self.parent_expr = Some(expr);
        intravisit::walk_expr(self, expr);
        self.parent_expr = old_parent;
    }

    // Called after we get a match. Looks for more matches to this and other rules within the
    // experssions/patterns etc bound to the placeholders of that match.
    fn find_matches_within_placeholders<T: StartMatch + 'gcx>(
        &mut self,
        m: &mut Match<'r, 'gcx, T>,
    ) {
        for placeholder in m.match_placeholders.placeholders_by_id.values_mut() {
            // We could create a new instance of RuleMatcher just for the finding
            // the matches within the placeholder, but all we care about is where new
            // matches get written, so we temporarily swap our matches with that of the
            // placeholder, then swap back when we're done.
            mem::swap(&mut placeholder.matches, &mut self.matches);
            match placeholder.contents {
                PlaceholderContents::Expr(placeholder_expr) => {
                    if placeholder_expr.hir_id == StartMatch::hir_id(m.node) {
                        // We've already matched this expression, don't match it again, but do
                        // try to find matches in its children.
                        self.process_children_of_expression(placeholder_expr);
                    } else {
                        intravisit::Visitor::visit_expr(self, placeholder_expr);
                    }
                }
                PlaceholderContents::Statements(placeholder_stmts) => {
                    for stmt in placeholder_stmts {
                        intravisit::Visitor::visit_stmt(self, stmt);
                    }
                }
                PlaceholderContents::Pattern(pattern) => {
                    // TODO: Check if it's possible for the entire pattern to be the
                    // placeholder. If it is, we might need to only process children like we do
                    // above for expressions.
                    intravisit::Visitor::visit_pat(self, pattern);
                }
            }
            mem::swap(&mut placeholder.matches, &mut self.matches);
        }
    }
}

impl<'r, 'a, 'gcx> intravisit::Visitor<'gcx> for RuleMatcher<'r, 'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_item(&mut self, item: &'gcx hir::Item) {
        if let hir::ItemKind::Mod(_) = item.node {
            // Avoid trying to find matches in the rules file.
            if item.ident.name == self.rule_mod_symbol {
                return;
            }
        }
        intravisit::walk_item(self, item);
    }

    fn visit_trait_ref(&mut self, trait_ref: &'gcx hir::TraitRef) {
        if let Some(m) = self.get_first_match(trait_ref, None, &self.rules.trait_ref_rules) {
            self.matches.trait_ref_matches.push(m);
        } else {
            intravisit::walk_trait_ref(self, trait_ref);
        }
    }

    fn visit_body(&mut self, body: &'gcx hir::Body) {
        let old_body_id = self.body_id;
        self.body_id = Some(body.id());
        match body.value.node {
            hir::ExprKind::Block(_, _) => {
                // We want to ensure that visit_expr is not called for the root expression of our
                // body (the block), since we don't want to replace it. But we still want to visit
                // the body arguments, so we do so explicitly.
                for arg in &body.arguments {
                    self.visit_id(arg.hir_id);
                    self.visit_pat(&arg.pat);
                }
                self.process_children_of_expression(&body.value);
            }
            _ => {
                // If our body isn't a block, we're a lambda expression without braces, treat out
                // body just like any other expression and allow it to match. See
                // tests::lambda_with_no_braces.
                intravisit::walk_body(self, body);
            }
        }
        self.body_id = old_body_id;
    }

    fn visit_expr(&mut self, expr: &'gcx hir::Expr) {
        let parent_expr = self.parent_expr;
        if let Some(mut m) = self.get_first_match(expr, parent_expr, &self.rules.expr_rules) {
            self.find_matches_within_placeholders(&mut m);
            self.matches.expr_matches.push(m);
        } else {
            // We only process the children of expressions that we didn't match. For matched
            // expressions, their placeholders are searched for futher matches and these matches are
            // stored on the placeholders.
            self.process_children_of_expression(expr);
        }
    }

    fn visit_ty(&mut self, ty: &'gcx hir::Ty) {
        if let Some(m) = self.get_first_match(ty, None, &self.rules.type_rules) {
            self.matches.type_matches.push(m);
            return;
        }
        intravisit::walk_ty(self, ty);
    }

    fn visit_pat(&mut self, pat: &'gcx hir::Pat) {
        if let Some(mut m) = self.get_first_match(pat, None, &self.rules.pattern_rules) {
            self.find_matches_within_placeholders(&mut m);
            self.matches.pattern_matches.push(m);
        } else {
            intravisit::walk_pat(self, pat);
        }
    }
}

pub(crate) struct MatchState<'r, 'a, 'gcx: 'r + 'a + 'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    infcx: InferCtxt<'a, 'gcx, 'tcx>,
    body_id: Option<hir::BodyId>,
    rule_type_tables: &'gcx ty::TypeckTables<'gcx>,
    match_placeholders: MatchPlaceholders<'r, 'gcx>,
    // This map should have all the same keys as the placeholders on match_placeholders. It's here
    // instead of on Match because it contains types that don't live as long as the match.
    placeholder_types_by_id: HashMap<HirId, ty::Ty<'tcx>>,
    rerast_definitions: RerastDefinitions<'gcx>,
    placeholder_ids: &'r HashSet<HirId>,
    // Whether bindings within a pattern are permitted to match any pattern. Otherwise, bindings are
    // only permitted to match bindings. This is enabled within replace_pattern, since the bindings
    // are only used within the pattern, not also as expressions, so binding to a pattern is
    // permissible.
    bindings_can_match_patterns: bool,
    debug_active: bool,
}

impl<'r, 'a, 'gcx: 'a + 'tcx, 'tcx: 'a> MatchState<'r, 'a, 'gcx, 'tcx> {
    fn attempt_to_bind_expr(&mut self, qpath: &hir::QPath, expr: &'gcx hir::Expr) -> bool {
        if let Some(hir_id) = hir_id_from_path(qpath) {
            if self.placeholder_ids.contains(&hir_id) {
                let p_ty = self.placeholder_types_by_id[&hir_id];
                let c_ty = self.code_type_tables().expr_ty(expr);
                // We check the type of the expression in our code both with and without
                // adjustment. It'd be nice if we didn't have to do this. I'm not sure it actually
                // covers all cases. The adjusted type includes autoderef, autoref etc, but since
                // p_ty is never adjusted similarly, we need to check the non-adjusted type as well.
                let c_ty_adjusted = self.code_type_tables().expr_ty_adjusted(expr);
                let cause = ObligationCause::dummy();
                let param_env = ty::ParamEnv::empty();
                if self.infcx.at(&cause, param_env).sub(p_ty, c_ty).is_err()
                    && self
                        .infcx
                        .at(&cause, param_env)
                        .sub(p_ty, c_ty_adjusted)
                        .is_err()
                {
                    debug!(self, "Types didn't match");
                    return false;
                }

                let old_placeholder = self
                    .match_placeholders
                    .placeholders_by_id
                    .insert(hir_id, Placeholder::new(PlaceholderContents::Expr(expr)));
                // Check that we don't already have a value for our placeholder. This shouldn't be
                // possible since SearchValidator checks that placeholders aren't used multiple
                // times. This is tested by error_multiple_bindings.
                assert!(old_placeholder.is_none());
                return true;
            }
        }
        false
    }

    fn can_sub<T>(&self, a: T, b: T) -> bool
    where
        T: infer::at::ToTrace<'tcx>,
    {
        self.infcx.can_sub(ty::ParamEnv::empty(), a, b).is_ok()
    }

    // Returns whether the supplied fn_expr (e.g. <Foo>::bar) is a reference to the same method as
    // is called by method_call_id (e.g. foo.bar()).
    fn fn_expr_equals_method_call(
        &self,
        fn_expr: &hir::Expr,
        fn_type_tables: &ty::TypeckTables<'gcx>,
        method_call_id: HirId,
        method_type_tables: &ty::TypeckTables<'gcx>,
    ) -> bool {
        if let Some(Ok((hir::def::DefKind::Method, method_id))) =
            fn_type_tables.type_dependent_defs().get(fn_expr.hir_id)
        {
            if let Ok((_, method_def_id)) = method_type_tables.type_dependent_defs()[method_call_id]
            {
                return method_def_id == *method_id;
            }
        }
        false
    }

    // Checks if the supplied statement is a placeholder for a sequence of statements. e.g. `a();`
    // where `a` is of type rerast::Statements. If it is, returns the HirId of the placeholder.
    fn opt_statements_placeholder_hir_id(&self, stmt: &hir::Stmt) -> Option<HirId> {
        if let hir::StmtKind::Semi(ref expr) = stmt.node {
            if let hir::ExprKind::Call(ref function, _) = expr.node {
                let fn_ty = self.rule_type_tables.expr_ty(function);
                if !self.can_sub(fn_ty, self.rerast_definitions.statements) {
                    return None;
                }
                if let hir::ExprKind::Path(ref path) = function.node {
                    if let Some(hir_id) = hir_id_from_path(path) {
                        if self.placeholder_ids.contains(&hir_id) {
                            return Some(hir_id);
                        }
                    }
                }
            }
        }
        None
    }

    fn code_type_tables(&self) -> &'gcx ty::TypeckTables<'gcx> {
        self.tcx.body_tables(self.body_id.unwrap())
    }

    fn span_to_snippet(&self, span: Span) -> Result<String, SpanSnippetError> {
        self.tcx.sess.source_map().span_to_snippet(span)
    }
}

pub(crate) trait Matchable: Debug {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool;
}

impl<T: Matchable> Matchable for Option<T> {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self.as_ref(), code.as_ref()) {
            (None, None) => true,
            (None, Some(_)) | (Some(_), None) => false,
            (Some(p), Some(c)) => p.attempt_match(state, c),
        }
    }
}

impl<T: Matchable> Matchable for [T] {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.len() == code.len()
            && self
                .iter()
                .zip(code.iter())
                .all(|(p, c)| p.attempt_match(state, c))
    }
}

impl<T: Matchable> Matchable for P<T> {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        (**self).attempt_match(state, &**code)
    }
}

impl<T: Matchable> Matchable for Spanned<T> {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.node.attempt_match(state, &code.node)
    }
}

impl Matchable for hir::Expr {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use rustc::hir::ExprKind;
        let result = match (&self.node, &code.node) {
            // TODO: ExprType, ExprInlineAsm (or more likely report that we don't support it).
            (&ExprKind::Call(ref p_fn, ref p_args), &ExprKind::Call(ref c_fn, ref c_args)) => {
                p_fn.attempt_match(state, c_fn) && p_args.attempt_match(state, c_args)
            }
            (
                &ExprKind::MethodCall(ref p_name, _, ref p_args),
                &ExprKind::MethodCall(ref c_name, _, ref c_args),
            ) => p_name.attempt_match(state, c_name) && p_args.attempt_match(state, c_args),
            (&ExprKind::MethodCall(_, _, ref p_args), &ExprKind::Call(ref c_fn, ref c_args)) => {
                state.fn_expr_equals_method_call(
                    c_fn,
                    state.code_type_tables(),
                    self.hir_id,
                    state.rule_type_tables,
                ) && p_args.attempt_match(state, c_args)
            }
            (&ExprKind::Call(ref p_fn, ref p_args), &ExprKind::MethodCall(_, _, ref c_args)) => {
                state.fn_expr_equals_method_call(
                    p_fn,
                    state.rule_type_tables,
                    code.hir_id,
                    state.code_type_tables(),
                ) && p_args.attempt_match(state, c_args)
            }
            (
                &ExprKind::Binary(ref p_op, ref p1, ref p2),
                &ExprKind::Binary(ref c_op, ref c1, ref c2),
            ) => {
                p_op.attempt_match(state, c_op)
                    && p1.attempt_match(state, c1)
                    && p2.attempt_match(state, c2)
            }
            (&ExprKind::Unary(p_op, ref p_expr), &ExprKind::Unary(c_op, ref c_expr)) => {
                p_op == c_op && p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::AddrOf(p_mut, ref p_expr), &ExprKind::AddrOf(c_mut, ref c_expr)) => {
                p_mut == c_mut && p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::Lit(ref p_lit), &ExprKind::Lit(ref c_lit)) => {
                p_lit.node == c_lit.node || {
                    if let Some((p_span, c_span)) = get_original_spans(self.span, code.span) {
                        // It's a bit unfortunate, but it seems that macros like file! and line!
                        // have no expansion info, so the only way we can tell if we've got the same
                        // macro invocation is to look at the code. Fortunately there aren't too
                        // many ways to invoke a macro like file! or line!.
                        state.span_to_snippet(p_span) == state.span_to_snippet(c_span)
                    } else {
                        false
                    }
                }
            }
            (
                &ExprKind::Loop(ref p_block, ref p_name, ref p_type),
                &ExprKind::Loop(ref c_block, ref c_name, ref c_type),
            ) => {
                p_type == c_type
                    && p_name.attempt_match(state, c_name)
                    && p_block.attempt_match(state, c_block)
            }
            (&ExprKind::Tup(ref p_vec), &ExprKind::Tup(ref c_vec))
            | (&ExprKind::Array(ref p_vec), &ExprKind::Array(ref c_vec)) => {
                p_vec.attempt_match(state, c_vec)
            }
            (
                &ExprKind::Repeat(ref p_expr, ref p_const),
                &ExprKind::Repeat(ref c_expr, ref c_const),
            ) => p_expr.attempt_match(state, c_expr) && p_const.attempt_match(state, c_const),
            (
                &ExprKind::Match(ref p_expr, ref p_arms, ref p_source),
                &ExprKind::Match(ref c_expr, ref c_arms, ref c_source),
            ) => {
                p_expr.attempt_match(state, c_expr)
                    && p_source == c_source
                    && p_arms.attempt_match(state, c_arms)
            }
            (
                &ExprKind::Struct(ref p_path, ref p_fields, ref p_expr),
                &ExprKind::Struct(ref c_path, ref c_fields, ref c_expr),
            ) => {
                p_path.attempt_match(state, c_path)
                    && p_fields.attempt_match(state, c_fields)
                    && p_expr.attempt_match(state, c_expr)
            }
            (
                &ExprKind::Block(ref p_block, ref p_label),
                &ExprKind::Block(ref c_block, ref c_label),
            ) => p_block.attempt_match(state, c_block) && p_label.attempt_match(state, c_label),
            (&ExprKind::Cast(ref p_expr, ref _p_ty), &ExprKind::Cast(ref c_expr, ref _c_ty)) => {
                p_expr.attempt_match(state, c_expr)
                    && state.can_sub(
                        state.rule_type_tables.expr_ty(self),
                        state.code_type_tables().expr_ty(code),
                    )
            }
            (
                &ExprKind::Index(ref p_expr, ref p_index),
                &ExprKind::Index(ref c_expr, ref c_index),
            ) => p_expr.attempt_match(state, c_expr) && p_index.attempt_match(state, c_index),
            (
                &ExprKind::Field(ref p_expr, ref p_name),
                &ExprKind::Field(ref c_expr, ref c_name),
            ) => p_expr.attempt_match(state, c_expr) && p_name.attempt_match(state, c_name),
            (&ExprKind::Assign(ref p_lhs, ref p_rhs), &ExprKind::Assign(ref c_lhs, ref c_rhs)) => {
                p_lhs.attempt_match(state, c_lhs) && p_rhs.attempt_match(state, c_rhs)
            }
            (
                &ExprKind::AssignOp(ref p_op, ref p_lhs, ref p_rhs),
                &ExprKind::AssignOp(ref c_op, ref c_lhs, ref c_rhs),
            ) => {
                p_op.attempt_match(state, c_op)
                    && p_lhs.attempt_match(state, c_lhs)
                    && p_rhs.attempt_match(state, c_rhs)
            }
            (
                &ExprKind::Break(ref p_label, ref p_expr),
                &ExprKind::Break(ref c_label, ref c_expr),
            ) => p_label.attempt_match(state, c_label) && p_expr.attempt_match(state, c_expr),
            (&ExprKind::Continue(ref p_label), &ExprKind::Continue(ref c_label)) => {
                p_label.attempt_match(state, c_label)
            }
            (
                &ExprKind::While(ref p_expr, ref p_block, ref p_name),
                &ExprKind::While(ref c_expr, ref c_block, ref c_name),
            ) => {
                p_expr.attempt_match(state, c_expr)
                    && p_block.attempt_match(state, c_block)
                    && p_name.attempt_match(state, c_name)
            }
            (
                &ExprKind::Closure(ref p_capture, _, ref p_body_id, _, ref p_gen),
                &ExprKind::Closure(ref c_capture, _, ref c_body_id, _, ref c_gen),
            ) => {
                p_capture.attempt_match(state, c_capture)
                    && p_body_id.attempt_match(state, c_body_id)
                    && p_gen == c_gen
            }
            (&ExprKind::Ret(ref p_expr), &ExprKind::Ret(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::Box(ref p_expr), &ExprKind::Box(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::DropTemps(ref p_expr), &ExprKind::DropTemps(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::Path(ref p_path), &ExprKind::Path(ref c_path)) => {
                // First check if the pattern is a placeholder and bind it if it is, otherwise try a
                // literal matching.
                if state.attempt_to_bind_expr(p_path, code) {
                    // For placeholders, return in order to bypass checking for identical macro
                    // expansion that would otherwise happen after the match.
                    return true;
                }
                p_path.attempt_match(state, c_path)
            }
            (&ExprKind::Path(ref path), _) => {
                // We've got a path and something that isn't a path (since we failed the previous
                // match arm). Check if the path is a placeholder and if it is, attempt to bind it
                // to our code.
                if state.attempt_to_bind_expr(path, code) {
                    // For placeholders, return in order to bypass checking for identical macro
                    // expansion that would otherwise happen after the match.
                    return true;
                }
                false
            }
            _ => {
                debug!(
                    state,
                    "Expression:   {:?}\ndidn't match: {:?}", code.node, self.node
                );
                false
            }
        };
        result && all_expansions_equal(self.span, code.span())
    }
}

impl Matchable for hir::Body {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.arguments.attempt_match(state, &code.arguments)
            && self.value.attempt_match(state, &code.value)
    }
}

impl Matchable for hir::Arg {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.pat.attempt_match(state, &code.pat)
    }
}

impl Matchable for hir::Ty {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.node.attempt_match(state, &code.node)
    }
}

impl Matchable for hir::TyKind {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use crate::hir::TyKind;
        match (self, code) {
            (&TyKind::Slice(ref p), &TyKind::Slice(ref c))
            | (&TyKind::Array(ref p, _), &TyKind::Array(ref c, _)) => p.attempt_match(state, c),
            (&TyKind::Ptr(ref p), &TyKind::Ptr(ref c)) => p.attempt_match(state, c),
            (&TyKind::Rptr(ref p_lifetime, ref p_ty), &TyKind::Rptr(ref c_lifetime, ref c_ty)) => {
                p_lifetime.attempt_match(state, c_lifetime) && p_ty.attempt_match(state, c_ty)
            }
            (&TyKind::BareFn(ref p), &TyKind::BareFn(ref c)) => p.attempt_match(state, c),
            (&TyKind::Never, &TyKind::Never) => true,
            (&TyKind::Tup(ref p), &TyKind::Tup(ref c)) => p.attempt_match(state, c),
            (&TyKind::Path(ref p), &TyKind::Path(ref c)) => p.attempt_match(state, c),
            (
                &TyKind::TraitObject(ref p, ref p_lifetime),
                &TyKind::TraitObject(ref c, ref c_lifetime),
            ) => p.attempt_match(state, c) && p_lifetime.attempt_match(state, c_lifetime),
            // TODO: TyKind::ImplTraitExistential
            // TODO: TyKind::ImplTraitUniversal
            // TODO: TyKind::TyKind::peOf
            _ => false,
        }
    }
}

impl Matchable for hir::MutTy {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.mutbl == code.mutbl && self.ty.attempt_match(state, &code.ty)
    }
}

impl Matchable for hir::Lifetime {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        _code: &'gcx Self,
    ) -> bool {
        // TODO: Probably want to check if both are 'static, otherwise attempt to bind with a
        // placeholder lifetime. Need to write test first.
        false
    }
}

impl Matchable for hir::BareFnTy {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        _code: &'gcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for hir::PolyTraitRef {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.trait_ref.attempt_match(state, &code.trait_ref)
    }
}

impl Matchable for hir::CaptureClause {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self, code) {
            (hir::CaptureClause::CaptureByValue, hir::CaptureClause::CaptureByValue)
            | (hir::CaptureClause::CaptureByRef, hir::CaptureClause::CaptureByRef) => true,
            _ => false,
        }
    }
}

impl Matchable for ast::CrateSugar {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self, code) {
            (ast::CrateSugar::PubCrate, ast::CrateSugar::PubCrate)
            | (ast::CrateSugar::JustCrate, ast::CrateSugar::JustCrate) => true,
            _ => false,
        }
    }
}

impl Matchable for hir::TraitRef {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.path.res == code.path.res
    }
}

impl Matchable for hir::GenericBound {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        _code: &'gcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for hir::Arm {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        // For now only accept if attrs is empty
        self.attrs.is_empty()
            && code.attrs.is_empty()
            && self.pats.attempt_match(state, &code.pats)
            && self.guard.attempt_match(state, &code.guard)
            && self.body.attempt_match(state, &code.body)
    }
}

impl Matchable for hir::Guard {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self, code) {
            (hir::Guard::If(ref p_expr), hir::Guard::If(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
        }
    }
}

impl Matchable for hir::Pat {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use crate::hir::PatKind::*;
        match (&self.node, &code.node) {
            (&Wild, &Wild) => true,
            (&Binding(p_mode, p_hir_id, ref _p_name, ref p_pat), _) => {
                if state.bindings_can_match_patterns {
                    state.match_placeholders.placeholders_by_id.insert(
                        p_hir_id,
                        Placeholder::new(PlaceholderContents::Pattern(code)),
                    );
                    true
                } else if let Binding(c_mode, c_hir_id, ref _c_name, ref c_pat) = code.node {
                    if p_mode == c_mode && p_pat.is_none() && c_pat.is_none() {
                        state
                            .match_placeholders
                            .matched_variable_decls
                            .insert(p_hir_id, c_hir_id);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (
                &Struct(ref p_qpath, ref p_pats, p_dotdot),
                &Struct(ref c_qpath, ref c_pats, c_dotdot),
            ) => {
                fn sorted_by_name(
                    pats: &hir::HirVec<Spanned<hir::FieldPat>>,
                ) -> Vec<&Spanned<hir::FieldPat>> {
                    let mut result: Vec<_> = pats.iter().collect();
                    result.sort_by_key(|pat| pat.node.ident.name);
                    result
                }

                p_qpath.attempt_match(state, c_qpath)
                    && p_dotdot == c_dotdot
                    && p_pats.len() == c_pats.len()
                    && sorted_by_name(p_pats)
                        .iter()
                        .zip(sorted_by_name(c_pats))
                        .all(|(p, c)| p.attempt_match(state, c))
            }
            (
                &TupleStruct(ref p_qpath, ref p_pats, ref p_dd_pos),
                &TupleStruct(ref c_qpath, ref c_pats, ref c_dd_pos),
            ) => {
                p_qpath.attempt_match(state, c_qpath)
                    && p_pats.attempt_match(state, c_pats)
                    && p_dd_pos.attempt_match(state, c_dd_pos)
            }
            (&Box(ref p_pat), &Box(ref c_pat)) => p_pat.attempt_match(state, c_pat),
            (&Tuple(ref p_patterns, ref p_dd_pos), &Tuple(ref c_patterns, ref c_dd_pos)) => {
                p_patterns.attempt_match(state, c_patterns) && p_dd_pos == c_dd_pos
            }
            (&Ref(ref p_pat, ref p_mut), &Ref(ref c_pat, ref c_mut)) => {
                p_pat.attempt_match(state, c_pat) && p_mut == c_mut
            }
            (
                &Slice(ref p_pats_a, ref p_op_pat, ref p_pats_b),
                &Slice(ref c_pats_a, ref c_op_pat, ref c_pats_b),
            ) => {
                p_pats_a.attempt_match(state, c_pats_a)
                    && p_op_pat.attempt_match(state, c_op_pat)
                    && p_pats_b.attempt_match(state, c_pats_b)
            }
            (&Lit(ref p_expr), &Lit(ref c_expr)) => p_expr.attempt_match(state, c_expr),
            (
                &Range(ref p_ex1, ref p_ex2, ref p_incl),
                &Range(ref c_ex1, ref c_ex2, ref c_incl),
            ) => {
                p_ex1.attempt_match(state, c_ex1)
                    && p_ex2.attempt_match(state, c_ex2)
                    && p_incl == c_incl
            }
            (&Path(ref p), &Path(ref c)) => p.attempt_match(state, c),
            _ => false,
        }
    }
}

impl Matchable for hir::Field {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.ident.attempt_match(state, &code.ident) && self.expr.attempt_match(state, &code.expr)
    }
}

impl Matchable for hir::FieldPat {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.ident.attempt_match(state, &code.ident) && self.pat.attempt_match(state, &code.pat)
    }
}

impl Matchable for hir::BinOp {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.node == code.node
    }
}

impl Matchable for Symbol {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self == code
    }
}

impl Matchable for usize {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self == code
    }
}

impl Matchable for hir::Destination {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.label.attempt_match(state, &code.label)
    }
}

impl Matchable for syntax::ast::Label {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.ident.name.attempt_match(state, &code.ident.name)
    }
}

impl Matchable for ast::Ident {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.name.attempt_match(state, &code.name)
    }
}

impl Matchable for hir::QPath {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        // TODO: Consider using TypeckTables::qpath_def, then passing the two defs to the match
        // currently for hir::Path below.
        use crate::hir::QPath::*;
        match (self, code) {
            (&Resolved(ref p_ty, ref p_path), &Resolved(ref c_ty, ref c_path)) => {
                p_ty.attempt_match(state, c_ty) && p_path.attempt_match(state, c_path)
            }
            (&TypeRelative(ref p_ty, ref p_segment), &TypeRelative(ref c_ty, ref c_segment)) => {
                p_ty.attempt_match(state, c_ty) && p_segment.attempt_match(state, c_segment)
            }
            _ => false,
        }
    }
}

impl Matchable for hir::Path {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self.res, code.res) {
            (hir::def::Res::Local(p_hir_id), hir::def::Res::Local(c_hir_id)) => {
                state
                    .match_placeholders
                    .matched_variable_decls
                    .get(&p_hir_id)
                    == Some(&c_hir_id)
            }
            _ => self.res == code.res,
        }
    }
}

impl Matchable for hir::PathSegment {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.ident.name == code.ident.name && self.args.attempt_match(state, &code.args)
    }
}

impl Matchable for hir::Stmt {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use rustc::hir::StmtKind;
        match (&self.node, &code.node) {
            (&StmtKind::Expr(ref p), &StmtKind::Expr(ref c))
            | (&StmtKind::Semi(ref p), &StmtKind::Semi(ref c)) => p.attempt_match(state, c),
            (&StmtKind::Local(ref p), &StmtKind::Local(ref c)) => p.attempt_match(state, c),
            (&StmtKind::Item(ref p), &StmtKind::Item(ref c)) => {
                let krate = state.tcx.hir().krate();
                krate.item(p.id).attempt_match(state, krate.item(c.id))
            }
            _ => false,
        }
    }
}

impl Matchable for hir::Local {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.pat.attempt_match(state, &code.pat)
            && self.ty.attempt_match(state, &code.ty)
            && self.init.attempt_match(state, &code.init)
            && self.attrs.attempt_match(state, &code.attrs)
    }
}

impl Matchable for hir::Item {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        state
            .match_placeholders
            .matched_variable_decls
            .insert(self.hir_id, code.hir_id);
        self.attrs.attempt_match(state, &*code.attrs)
            && self.vis.attempt_match(state, &code.vis)
            && self.node.attempt_match(state, &code.node)
    }
}

impl Matchable for hir::ItemKind {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use crate::hir::ItemKind;
        match (self, code) {
            (
                &ItemKind::Static(ref p_ty, p_mut, ref p_body_id),
                &ItemKind::Static(ref c_ty, c_mut, ref c_body_id),
            ) => {
                p_ty.attempt_match(state, c_ty)
                    && p_mut == c_mut
                    && p_body_id.attempt_match(state, c_body_id)
            }
            // TODO: Others
            _ => false,
        }
    }
}

impl Matchable for hir::AnonConst {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.body.attempt_match(state, &code.body)
    }
}

impl Matchable for hir::BodyId {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        let p_body = state.tcx.hir().body(*self);
        let c_body = state.tcx.hir().body(*code);
        p_body.attempt_match(state, c_body)
    }
}

impl Matchable for hir::Visibility {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use crate::hir::VisibilityKind::*;
        match (&self.node, &code.node) {
            (
                Restricted {
                    path: ref p_path, ..
                },
                Restricted {
                    path: ref c_path, ..
                },
            ) => p_path.attempt_match(state, c_path),
            (Crate(ref p_sugar), Crate(ref c_sugar)) => p_sugar.attempt_match(state, c_sugar),
            (Public, Public) | (Inherited, Inherited) => true,
            _ => false,
        }
    }
}

impl Matchable for ast::Attribute {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        _code: &'gcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for hir::Block {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        // The trailing expression in a block, if present, is never consumed by a placeholder since
        // it's not a statement, so match it first.
        if !self.expr.attempt_match(state, &code.expr) {
            return false;
        }
        // Ideally we should do what regex matching does and build an FSA or something. For now we
        // just apply a more basic algorithm. Look for matches at the start, if we find a
        // placeholder, look for matches at the end, then the placeholder takes whatever is left in
        // the middle. This means that we only support a single placeholder in a block.
        for (i, stmt) in self.stmts.iter().enumerate() {
            if let Some(hir_id) = state.opt_statements_placeholder_hir_id(stmt) {
                if code.stmts.len() < self.stmts.len() + 1 {
                    return false;
                }
                let p_after = &self.stmts[i + 1..];
                let c_after = &code.stmts[code.stmts.len() - p_after.len()..];
                if self.stmts[..i].attempt_match(state, &code.stmts[..i])
                    && p_after.attempt_match(state, c_after)
                    && state.placeholder_ids.contains(&hir_id)
                {
                    // TODO: Refactor this insert and the other one to a common location so
                    // that both check there isn't already something there.
                    state.match_placeholders.placeholders_by_id.insert(
                        hir_id,
                        Placeholder::new(PlaceholderContents::Statements(
                            &code.stmts[i..code.stmts.len() - p_after.len()],
                        )),
                    );
                    return true;
                }
                return false;
            }
        }
        // No placeholder was found, just match statements 1:1
        self.stmts.attempt_match(state, &code.stmts)
    }
}

impl Matchable for hir::GenericArgs {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.parenthesized == code.parenthesized
            && self.args.attempt_match(state, &*code.args)
            && self.bindings.attempt_match(state, &*code.bindings)
    }
}

impl Matchable for hir::GenericArg {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        match (self, code) {
            (
                hir::GenericArg::Lifetime(ref p_lifetime),
                hir::GenericArg::Lifetime(ref c_lifetime),
            ) => p_lifetime.attempt_match(state, c_lifetime),
            (hir::GenericArg::Type(ref p_type), hir::GenericArg::Type(ref c_type)) => {
                p_type.attempt_match(state, c_type)
            }
            _ => false,
        }
    }
}

impl Matchable for hir::TypeBinding {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.ident.name.attempt_match(state, &code.ident.name)
            && self.ty.attempt_match(state, &code.ty)
    }
}

#[derive(Debug)]
pub(crate) struct Matches<'r, 'gcx: 'r> {
    expr_matches: Vec<Match<'r, 'gcx, hir::Expr>>,
    pattern_matches: Vec<Match<'r, 'gcx, hir::Pat>>,
    type_matches: Vec<Match<'r, 'gcx, hir::Ty>>,
    trait_ref_matches: Vec<Match<'r, 'gcx, hir::TraitRef>>,
}

impl<'r, 'gcx> Matches<'r, 'gcx> {
    fn new() -> Matches<'r, 'gcx> {
        Matches {
            expr_matches: Vec::new(),
            pattern_matches: Vec::new(),
            type_matches: Vec::new(),
            trait_ref_matches: Vec::new(),
        }
    }
}

#[derive(Debug)]
struct Match<'r, 'gcx: 'r, T: StartMatch> {
    rule: &'r Rule<'gcx, T>,
    node: &'gcx T,
    // Parent of the patched expression if the parent is also an expression. Used to determine if we
    // need to insert parenthesis.
    // TODO: For nested matches, this might not be quite what we want. We want to know what the
    // parent of the replacement will be. For a top-level match, the parent will always be the
    // parent of the matched code, but for a match within a placeholder, if the the top-level of the
    // placeholder matches, then the new parent will be from the replacement expression in the
    // parent rule.
    parent_node: Option<&'gcx T>,
    match_placeholders: MatchPlaceholders<'r, 'gcx>,
    original_span: Span,
}

impl<'r, 'a, 'gcx, 'tcx, T: StartMatch> Match<'r, 'gcx, T> {
    fn get_replacement_source(&self, tcx: TyCtxt<'a, 'gcx, 'gcx>) -> String {
        let replacement = self.rule.replace;
        let mut replacement_visitor = ReplacementVisitor {
            tcx,
            result: vec![],
            current_match: self,
            parent_expr: None,
            substitute_hir_ids: HashMap::new(),
        };
        let source_map = tcx.sess.source_map();
        T::walk(&mut replacement_visitor, replacement);
        let substitutions = replacement_visitor.result;
        //Replacer::print_macro_backtrace("SPAN_BT", source_map, replacement.span());
        CodeSubstitution::apply_with_source_map(
            &substitutions,
            source_map,
            replacement.span().source_callsite(),
        )
    }
}

#[derive(Debug)]
pub(crate) struct MatchPlaceholders<'r, 'gcx: 'r> {
    // Maps the IDs of placeholders in arguments, to their state (unbound, bound to expression
    // etc).
    placeholders_by_id: HashMap<HirId, Placeholder<'r, 'gcx>>,
    // Maps from variables declared in the search pattern to variables declared in the code.
    matched_variable_decls: HashMap<HirId, HirId>,
}

impl<'r, 'a, 'gcx, 'tcx> MatchPlaceholders<'r, 'gcx> {
    fn new() -> MatchPlaceholders<'r, 'gcx> {
        MatchPlaceholders {
            placeholders_by_id: HashMap::new(),
            matched_variable_decls: HashMap::new(),
        }
    }

    fn get_placeholder<'this>(&'this self, hir_id: HirId) -> Option<&'this Placeholder<'r, 'gcx>> {
        self.placeholders_by_id.get(&hir_id)
    }
}

#[derive(Debug, Copy, Clone)]
enum PlaceholderContents<'gcx> {
    Expr(&'gcx hir::Expr),
    Statements(&'gcx [hir::Stmt]),
    Pattern(&'gcx hir::Pat),
}

impl<'gcx> PlaceholderContents<'gcx> {
    fn get_span(&self, target: Span) -> Span {
        use self::PlaceholderContents::*;
        match *self {
            Expr(expr) => span_within_span(expr.span, target),
            Statements(stmts) => {
                if let Some(stmt) = stmts.get(0) {
                    let result = span_within_span(stmt.span, target);
                    let last_span = span_within_span(stmts[stmts.len() - 1].span, target);
                    result.with_hi(last_span.hi())
                } else {
                    DUMMY_SP
                }
            }
            Pattern(pattern) => pattern.span,
        }
    }

    // Returns whether we need to add parenthesis around this contents of this placeholder when
    // inserted as a child of parent_expr in order to preserve order of operations.
    fn needs_parenthesis(&self, parent_expr: Option<&hir::Expr>) -> bool {
        if let PlaceholderContents::Expr(expr) = *self {
            OperatorPrecedence::needs_parenthesis(parent_expr, expr)
        } else {
            false
        }
    }
}

#[derive(Debug)]
struct Placeholder<'r, 'gcx: 'r> {
    contents: PlaceholderContents<'gcx>,
    // Matches found within contents. Populated if and only if the rule that owns this placeholder
    // succeeds.
    matches: Matches<'r, 'gcx>,
}

impl<'r, 'gcx: 'r> Placeholder<'r, 'gcx> {
    fn new(contents: PlaceholderContents<'gcx>) -> Placeholder<'r, 'gcx> {
        Placeholder {
            contents,
            matches: Matches::new(),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum OperatorPrecedence {
    Unary,      // All unary operators
    MulDivMod,  // * / %
    AddSub,     // + -
    BitShift,   // << >>
    BitAnd,     // &
    BitXor,     // ^
    BitOr,      // |
    Comparison, // == != < > <= >=
    LogicalAnd, // &&
    LogicalOr,  // ||
    Assignment, // =
}

impl OperatorPrecedence {
    fn from_expr(expr: &hir::Expr) -> Option<OperatorPrecedence> {
        use rustc::hir::ExprKind;
        Some(match expr.node {
            ExprKind::Unary(..) => OperatorPrecedence::Unary,
            ExprKind::Binary(op, ..) => {
                use rustc::hir::BinOpKind;
                match op.node {
                    BinOpKind::Add | BinOpKind::Sub => OperatorPrecedence::AddSub,
                    BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem => {
                        OperatorPrecedence::MulDivMod
                    }
                    BinOpKind::And => OperatorPrecedence::LogicalAnd,
                    BinOpKind::Or => OperatorPrecedence::LogicalOr,
                    BinOpKind::BitXor => OperatorPrecedence::BitXor,
                    BinOpKind::BitAnd => OperatorPrecedence::BitAnd,
                    BinOpKind::BitOr => OperatorPrecedence::BitOr,
                    BinOpKind::Shl | BinOpKind::Shr => OperatorPrecedence::BitShift,
                    BinOpKind::Eq
                    | BinOpKind::Lt
                    | BinOpKind::Le
                    | BinOpKind::Ne
                    | BinOpKind::Ge
                    | BinOpKind::Gt => OperatorPrecedence::Comparison,
                }
            }
            ExprKind::Assign(..) => OperatorPrecedence::Assignment,
            _ => return None,
        })
    }

    // Returns whether parenthsis are needed around the child expression in order to maintain
    // structure. i.e the child expression has weaker precedence than the parent.
    pub(crate) fn needs_parenthesis(
        maybe_parent_expr: Option<&hir::Expr>,
        child_expr: &hir::Expr,
    ) -> bool {
        if let (Some(parent), Some(child)) = (
            maybe_parent_expr.and_then(OperatorPrecedence::from_expr),
            OperatorPrecedence::from_expr(child_expr),
        ) {
            child >= parent
        } else {
            false
        }
    }
}

// Recursively searches the expansion of search_span and code_span in parallel. If at any point the
// expansions performed by the two spans are different, then that means the search pattern and the
// code invoked different macros, so returns None. If both reach the top (no expansions remaining)
// together, then returns their spans.
fn get_original_spans(search_span: Span, code_span: Span) -> Option<(Span, Span)> {
    match (
        search_span.ctxt().outer().expn_info(),
        code_span.ctxt().outer().expn_info(),
    ) {
        (Some(search_expn), Some(code_expn)) => {
            if is_same_expansion(&search_expn, &code_expn) {
                get_original_spans(search_expn.call_site, code_expn.call_site)
            } else {
                None
            }
        }
        (None, None) => Some((search_span, code_span)),
        _ => None,
    }
}

fn is_same_expansion(a: &source_map::ExpnInfo, b: &source_map::ExpnInfo) -> bool {
    use crate::source_map::ExpnFormat::*;
    a.format == b.format
        && match a.format {
            MacroBang(_) => a.def_site == b.def_site,
            // Not sure what we want to do here
            MacroAttribute(_) => unimplemented!(),
            // For desugaring, we ignore the span since it seems to just duplicate the span of the
            // caller which definitely won't be the same for two separate occurences.
            CompilerDesugaring(_) => true,
        }
}

// Searches the callsites of the first span until it finds one that is contained within the second
// span.
fn span_within_span(span: Span, target: Span) -> Span {
    if target.contains(span) {
        span
    } else if let Some(expn_info) = span.ctxt().outer().expn_info() {
        span_within_span(expn_info.call_site, target)
    } else {
        // TODO: Better error handling here.
        panic!("We never found a span within the target span");
    }
}

// Returns whether following the expansions of `rule_span` and `code_span` results in the same
// sequence of expansions.
fn all_expansions_equal(rule_span: Span, code_span: Span) -> bool {
    get_original_spans(rule_span, code_span).is_some()
}

// Visits the replacement AST looking for variables that need to be replaced with their bound values
// from the matched source then recording the spans for said replacement.
struct ReplacementVisitor<'r, 'a: 'r, 'gcx: 'a, T: StartMatch> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    result: Vec<CodeSubstitution<Span>>,
    current_match: &'r Match<'r, 'gcx, T>,
    parent_expr: Option<&'gcx hir::Expr>,
    // Map from HirIds of variables declared in the replacement pattern to HirIds declared in the
    // code that should replace them.
    substitute_hir_ids: HashMap<HirId, HirId>,
}

impl<'r, 'a, 'gcx, T: StartMatch> ReplacementVisitor<'r, 'a, 'gcx, T> {
    // Returns a snippet of code for the supplied definition.
    fn node_id_snippet(&self, node_id: NodeId) -> String {
        let source_map = self.tcx.sess.source_map();
        source_map
            .span_to_snippet(self.tcx.hir().span(node_id))
            .unwrap()
    }

    fn hir_id_snippet(&self, hir_id: HirId) -> String {
        self.node_id_snippet(self.tcx.hir().hir_to_node_id(hir_id))
    }

    // Check if the supplied expression is a placeholder variable. If it is, replace the supplied
    // span with whatever was bound to the placeholder and return true.
    fn process_expr(&mut self, expr: &'gcx hir::Expr, placeholder_span: Span) -> bool {
        if let hir::ExprKind::Path(ref path) = expr.node {
            if let Some(hir_id) = hir_id_from_path(path) {
                if let Some(placeholder) = self
                    .current_match
                    .match_placeholders
                    .get_placeholder(hir_id)
                {
                    self.process_placeholder(placeholder, placeholder_span);
                    return true;
                } else if let Some(code_hir_id) = self.substitute_hir_ids.get(&hir_id) {
                    let code = self.hir_id_snippet(*code_hir_id);
                    self.result.push(CodeSubstitution::new(expr.span, code));
                    return true;
                }
            }
        }
        false
    }

    fn process_placeholder(&mut self, placeholder: &Placeholder<'r, 'gcx>, placeholder_span: Span) {
        let source_map = self.tcx.sess.source_map();
        let span = placeholder
            .contents
            .get_span(self.current_match.original_span);
        let substitutions = substitions_for_matches(self.tcx, &placeholder.matches);
        let new_code = CodeSubstitution::apply_with_source_map(&substitutions, source_map, span);

        self.result.push(
            CodeSubstitution::new(placeholder_span, new_code)
                .needs_parenthesis(placeholder.contents.needs_parenthesis(self.parent_expr)),
        );
    }
}

impl<'r, 'a, 'gcx, T: StartMatch> intravisit::Visitor<'gcx>
    for ReplacementVisitor<'r, 'a, 'gcx, T>
{
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_expr(&mut self, expr: &'gcx hir::Expr) {
        self.process_expr(expr, expr.span);
        let old_parent = self.parent_expr;
        self.parent_expr = Some(expr);
        intravisit::walk_expr(self, expr);
        self.parent_expr = old_parent;
    }

    fn visit_stmt(&mut self, stmt: &'gcx hir::Stmt) {
        if let hir::StmtKind::Semi(ref expr) = stmt.node {
            if let hir::ExprKind::Call(ref expr_fn, _) = expr.node {
                if self.process_expr(expr_fn, stmt.span) {
                    return;
                }
            }
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_pat(&mut self, pat: &'gcx hir::Pat) {
        if let hir::PatKind::Binding(_, hir_id, ref ident, _) = pat.node {
            if let Some(search_hir_id) = self
                .current_match
                .rule
                .declared_name_hir_ids
                .get(&ident.name)
            {
                if let Some(placeholder) = self
                    .current_match
                    .match_placeholders
                    .get_placeholder(*search_hir_id)
                {
                    self.process_placeholder(placeholder, pat.span);
                } else if let Some(&code_hir_id) = self
                    .current_match
                    .match_placeholders
                    .matched_variable_decls
                    .get(search_hir_id)
                {
                    // TODO: Would the above be clearer if the RHS was extracted to a method on
                    // Match?

                    // Record the mapping so that we can replace references to the variable as well.
                    self.substitute_hir_ids.insert(hir_id, code_hir_id);
                    let code = self.hir_id_snippet(code_hir_id);
                    self.result.push(CodeSubstitution::new(ident.span, code));
                }
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

pub(crate) fn substitions_for_matches<'r, 'a, 'gcx>(
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    matches: &Matches<'r, 'gcx>,
) -> Vec<CodeSubstitution<Span>> {
    fn add_substitions_for_matches<'r, 'a, 'gcx, T: StartMatch>(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        matches: &[Match<'r, 'gcx, T>],
        substitutions: &mut Vec<CodeSubstitution<Span>>,
    ) {
        for m in matches {
            let replacement_src = m.get_replacement_source(tcx);
            substitutions.push(
                CodeSubstitution::new(m.original_span, replacement_src)
                    .needs_parenthesis(T::needs_parenthesis(m.parent_node, &*m.rule.replace)),
            );
        }
    }

    let mut substitutions = vec![];
    add_substitions_for_matches(tcx, &matches.expr_matches, &mut substitutions);
    add_substitions_for_matches(tcx, &matches.pattern_matches, &mut substitutions);
    add_substitions_for_matches(tcx, &matches.type_matches, &mut substitutions);
    add_substitions_for_matches(tcx, &matches.trait_ref_matches, &mut substitutions);
    substitutions.sort();
    substitutions
}
