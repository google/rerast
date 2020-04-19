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
use rustc_ast::{self, ast};
use rustc_hir;
use rustc_hir::intravisit;
use rustc_hir::HirId;
use rustc_infer::infer::{self, InferCtxt, TyCtxtInferExt};
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::subst::Subst;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::source_map::{self, Spanned};
use rustc_span::symbol::Symbol;
use rustc_span::{Span, SpanSnippetError, DUMMY_SP};
use std::collections::HashMap;
use std::fmt::Debug;
use std::mem;

#[macro_export]
macro_rules! debug {
    ($state:expr, $($args:expr),*) => {
        if $state.debug_active {
            println!($($args),*);
        }
    }
}

pub(crate) struct RuleMatcher<'r, 'tcx: 'r> {
    tcx: TyCtxt<'tcx>,
    rules: &'r Rules<'tcx>,
    matches: Matches<'r, 'tcx>,
    rule_mod_symbol: Symbol,
    parent_expr: Option<&'tcx rustc_hir::Expr<'tcx>>,
    body_id: Option<rustc_hir::BodyId>,
    rerast_definitions: RerastDefinitions<'tcx>,
    config: Config,
    debug_active: bool,
}

impl<'r, 'tcx> RuleMatcher<'r, 'tcx> {
    pub(crate) fn find_matches(
        tcx: TyCtxt<'tcx>,
        rerast_definitions: RerastDefinitions<'tcx>,
        krate: &'tcx rustc_hir::Crate,
        rules: &'r Rules<'tcx>,
        config: Config,
    ) -> Matches<'r, 'tcx> {
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

    fn should_debug_node<T: StartMatch<'tcx> + 'tcx>(&self, node: &'tcx T) -> bool {
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

    fn get_first_match<T: StartMatch<'tcx> + 'tcx>(
        &mut self,
        node: &'tcx T,
        parent_node: Option<&'tcx T>,
        rules: &'r [Rule<'tcx, T>],
    ) -> Option<Match<'r, 'tcx, T>> {
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

    fn get_match<T: StartMatch<'tcx> + 'tcx>(
        &mut self,
        node: &'tcx T,
        parent_node: Option<&'tcx T>,
        original_span: Span,
        rule: &'r Rule<'tcx, T>,
    ) -> Option<Match<'r, 'tcx, T>> {
        let rule_fn_id = self.tcx.hir().body_owner_def_id(rule.body_id).to_def_id();
        let rule_tables = self.tcx.body_tables(rule.body_id);

        let maybe_match_placeholders = self.tcx.infer_ctxt().enter(|infcx| {
            let tcx = infcx.tcx;
            let substs = infcx.fresh_substs_for_item(tcx.def_span(rule_fn_id), rule_fn_id);
            let placeholder_types_by_id = rule
                .placeholder_ids
                .iter()
                .map(|hir_id| {
                    (*hir_id, {
                        let ty = rule_tables.node_type(*hir_id);
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

    fn process_children_of_expression(&mut self, expr: &'tcx rustc_hir::Expr) {
        let old_parent = self.parent_expr;
        self.parent_expr = Some(expr);
        intravisit::walk_expr(self, expr);
        self.parent_expr = old_parent;
    }

    // Called after we get a match. Looks for more matches to this and other rules within the
    // experssions/patterns etc bound to the placeholders of that match.
    fn find_matches_within_placeholders<T: StartMatch<'tcx> + 'tcx>(
        &mut self,
        m: &mut Match<'r, 'tcx, T>,
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

impl<'r, 'tcx> intravisit::Visitor<'tcx> for RuleMatcher<'r, 'tcx> {
    type Map = rustc_middle::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.tcx.hir())
    }

    fn visit_item(&mut self, item: &'tcx rustc_hir::Item) {
        if let rustc_hir::ItemKind::Mod(_) = item.kind {
            // Avoid trying to find matches in the rules file.
            if item.ident.name == self.rule_mod_symbol {
                return;
            }
        }
        intravisit::walk_item(self, item);
    }

    fn visit_trait_ref(&mut self, trait_ref: &'tcx rustc_hir::TraitRef) {
        if let Some(m) = self.get_first_match(trait_ref, None, &self.rules.trait_ref_rules) {
            self.matches.trait_ref_matches.push(m);
        } else {
            intravisit::walk_trait_ref(self, trait_ref);
        }
    }

    fn visit_body(&mut self, body: &'tcx rustc_hir::Body) {
        let old_body_id = self.body_id;
        self.body_id = Some(body.id());
        match body.value.kind {
            rustc_hir::ExprKind::Block(_, _) => {
                // We want to ensure that visit_expr is not called for the root expression of our
                // body (the block), since we don't want to replace it. But we still want to visit
                // the body arguments, so we do so explicitly.
                for param in body.params {
                    self.visit_id(param.hir_id);
                    self.visit_pat(&param.pat);
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

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr) {
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

    fn visit_ty(&mut self, ty: &'tcx rustc_hir::Ty) {
        if let Some(m) = self.get_first_match(ty, None, &self.rules.type_rules) {
            self.matches.type_matches.push(m);
            return;
        }
        intravisit::walk_ty(self, ty);
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat) {
        if let Some(mut m) = self.get_first_match(pat, None, &self.rules.pattern_rules) {
            self.find_matches_within_placeholders(&mut m);
            self.matches.pattern_matches.push(m);
        } else {
            intravisit::walk_pat(self, pat);
        }
    }
}

pub(crate) struct MatchState<'r, 'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'a, 'tcx>,
    body_id: Option<rustc_hir::BodyId>,
    rule_type_tables: &'tcx ty::TypeckTables<'tcx>,
    match_placeholders: MatchPlaceholders<'r, 'tcx>,
    // This map should have all the same keys as the placeholders on match_placeholders. It's here
    // instead of on Match because it contains types that don't live as long as the match.
    placeholder_types_by_id: HashMap<HirId, ty::Ty<'tcx>>,
    rerast_definitions: RerastDefinitions<'tcx>,
    // Whether bindings within a pattern are permitted to match any pattern. Otherwise, bindings are
    // only permitted to match bindings. This is enabled within replace_pattern, since the bindings
    // are only used within the pattern, not also as expressions, so binding to a pattern is
    // permissible.
    bindings_can_match_patterns: bool,
    debug_active: bool,
}

impl<'r, 'a, 'tcx: 'a> MatchState<'r, 'a, 'tcx> {
    fn attempt_to_bind_expr(
        &mut self,
        qpath: &rustc_hir::QPath,
        expr: &'tcx rustc_hir::Expr,
    ) -> bool {
        if let Some(hir_id) = hir_id_from_path(qpath) {
            if let Some(&p_ty) = self.placeholder_types_by_id.get(&hir_id) {
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
        fn_expr: &rustc_hir::Expr,
        fn_type_tables: &ty::TypeckTables<'tcx>,
        method_call_id: HirId,
        method_type_tables: &ty::TypeckTables<'tcx>,
    ) -> bool {
        if let Some(Ok((rustc_hir::def::DefKind::Fn, method_id))) =
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
    fn opt_statements_placeholder_hir_id(&self, stmt: &rustc_hir::Stmt) -> Option<HirId> {
        if let rustc_hir::StmtKind::Semi(ref expr) = stmt.kind {
            if let rustc_hir::ExprKind::Call(ref function, _) = expr.kind {
                let fn_ty = self.rule_type_tables.expr_ty(function);
                if !self.can_sub(fn_ty, self.rerast_definitions.statements) {
                    return None;
                }
                if let rustc_hir::ExprKind::Path(ref path) = function.kind {
                    if let Some(hir_id) = hir_id_from_path(path) {
                        if self.placeholder_types_by_id.contains_key(&hir_id) {
                            return Some(hir_id);
                        }
                    }
                }
            }
        }
        None
    }

    fn code_type_tables(&self) -> &'tcx ty::TypeckTables<'tcx> {
        self.tcx.body_tables(self.body_id.unwrap())
    }

    fn span_to_snippet(&self, span: Span) -> Result<String, SpanSnippetError> {
        self.tcx.sess.source_map().span_to_snippet(span)
    }
}

pub(crate) trait Matchable: Debug {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool;
}

fn attempt_match_option<'r, 'a, 'tcx, T: Matchable>(
    state: &mut MatchState<'r, 'a, 'tcx>,
    pattern: Option<&T>,
    code: Option<&'tcx T>,
) -> bool {
    match (pattern, code) {
        (None, None) => true,
        (None, Some(_)) | (Some(_), None) => false,
        (Some(p), Some(c)) => p.attempt_match(state, c),
    }
}

fn attempt_match_all<'r, 'a, 'tcx, T: Matchable>(
    state: &mut MatchState<'r, 'a, 'tcx>,
    pattern: &[&T],
    code: &[&'tcx T],
) -> bool {
    pattern.len() == code.len()
        && pattern
            .iter()
            .zip(code.iter())
            .all(|(p, c)| p.attempt_match(state, c))
}

impl<T: Matchable> Matchable for Option<T> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self.as_ref(), code.as_ref()) {
            (None, None) => true,
            (None, Some(_)) | (Some(_), None) => false,
            (Some(p), Some(c)) => p.attempt_match(state, c),
        }
    }
}

impl<T: Matchable> Matchable for [T] {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.len() == code.len()
            && self
                .iter()
                .zip(code.iter())
                .all(|(p, c)| p.attempt_match(state, c))
    }
}

impl<T: Matchable> Matchable for rustc_ast::ptr::P<T> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        (**self).attempt_match(state, &**code)
    }
}

impl<T: Matchable> Matchable for Spanned<T> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.node.attempt_match(state, &code.node)
    }
}

impl Matchable for rustc_hir::Expr<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use rustc_hir::ExprKind;
        let result = match (&self.kind, &code.kind) {
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
            (
                &ExprKind::AddrOf(p_kind, p_mut, ref p_expr),
                &ExprKind::AddrOf(c_kind, c_mut, ref c_expr),
            ) => p_kind == c_kind && p_mut == c_mut && p_expr.attempt_match(state, c_expr),
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
                    && attempt_match_option(state, *p_expr, *c_expr)
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
            (
                &ExprKind::Assign(ref p_lhs, ref p_rhs, _),
                &ExprKind::Assign(ref c_lhs, ref c_rhs, _),
            ) => p_lhs.attempt_match(state, c_lhs) && p_rhs.attempt_match(state, c_rhs),
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
            ) => {
                p_label.attempt_match(state, c_label)
                    && attempt_match_option(state, *p_expr, *c_expr)
            }
            (&ExprKind::Continue(ref p_label), &ExprKind::Continue(ref c_label)) => {
                p_label.attempt_match(state, c_label)
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
                attempt_match_option(state, *p_expr, *c_expr)
            }
            (&ExprKind::Box(ref p_expr), &ExprKind::Box(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::DropTemps(ref p_expr), &ExprKind::DropTemps(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
            (&ExprKind::Yield(ref p_expr, _), &ExprKind::Yield(ref c_expr, _)) => {
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
            _ => false,
        };
        if !result {
            debug!(
                state,
                "Expression:   {:?}\ndidn't match: {:?}", code.kind, self.kind
            );
        }
        result && all_expansions_equal(self.span, code.span())
    }
}

impl Matchable for rustc_hir::Body<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.params.attempt_match(state, &code.params)
            && self.value.attempt_match(state, &code.value)
    }
}

impl Matchable for rustc_hir::Param<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.pat.attempt_match(state, &code.pat)
    }
}

impl Matchable for rustc_hir::Ty<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.kind.attempt_match(state, &code.kind)
    }
}

impl Matchable for rustc_hir::TyKind<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use crate::rustc_hir::TyKind;
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

impl Matchable for rustc_hir::MutTy<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.mutbl == code.mutbl && self.ty.attempt_match(state, &code.ty)
    }
}

impl Matchable for rustc_hir::Lifetime {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        _code: &'tcx Self,
    ) -> bool {
        // TODO: Probably want to check if both are 'static, otherwise attempt to bind with a
        // placeholder lifetime. Need to write test first.
        false
    }
}

impl Matchable for rustc_hir::BareFnTy<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        _code: &'tcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for rustc_hir::PolyTraitRef<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.trait_ref.attempt_match(state, &code.trait_ref)
    }
}

impl Matchable for rustc_hir::CaptureBy {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self, code) {
            (rustc_hir::CaptureBy::Value, rustc_hir::CaptureBy::Value)
            | (rustc_hir::CaptureBy::Ref, rustc_hir::CaptureBy::Ref) => true,
            _ => false,
        }
    }
}

impl Matchable for ast::CrateSugar {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self, code) {
            (ast::CrateSugar::PubCrate, ast::CrateSugar::PubCrate)
            | (ast::CrateSugar::JustCrate, ast::CrateSugar::JustCrate) => true,
            _ => false,
        }
    }
}

impl Matchable for rustc_hir::TraitRef<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.path.res == code.path.res
    }
}

impl Matchable for rustc_hir::GenericBound<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        _code: &'tcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for rustc_hir::Arm<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        // For now only accept if attrs is empty
        self.attrs.is_empty()
            && code.attrs.is_empty()
            && self.pat.attempt_match(state, &code.pat)
            && self.guard.attempt_match(state, &code.guard)
            && self.body.attempt_match(state, &code.body)
    }
}

impl Matchable for rustc_hir::Guard<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self, code) {
            (rustc_hir::Guard::If(ref p_expr), rustc_hir::Guard::If(ref c_expr)) => {
                p_expr.attempt_match(state, c_expr)
            }
        }
    }
}

impl Matchable for rustc_hir::Pat<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use crate::rustc_hir::PatKind::*;
        match (&self.kind, &code.kind) {
            (&Wild, &Wild) => true,
            (&Binding(p_mode, p_hir_id, ref _p_name, ref p_pat), _) => {
                if state.bindings_can_match_patterns {
                    state.match_placeholders.placeholders_by_id.insert(
                        p_hir_id,
                        Placeholder::new(PlaceholderContents::Pattern(code)),
                    );
                    true
                } else if let Binding(c_mode, c_hir_id, ref c_name, ref c_pat) = code.kind {
                    if p_mode == c_mode && p_pat.is_none() && c_pat.is_none() {
                        state.match_placeholders.matched_variable_decls.insert(
                            p_hir_id,
                            MatchedVariableDecl {
                                code_hir_id: c_hir_id,
                                name: c_name.to_string(),
                            },
                        );
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
                fn sorted_by_name<'a>(
                    pats: &'a [rustc_hir::FieldPat<'a>],
                ) -> Vec<&'a rustc_hir::FieldPat<'a>> {
                    let mut result: Vec<_> = pats.iter().collect();
                    result.sort_by_key(|pat| pat.ident.name);
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
                    && attempt_match_all(state, p_pats, c_pats)
                    && p_dd_pos.attempt_match(state, c_dd_pos)
            }
            (&Box(ref p_pat), &Box(ref c_pat)) => p_pat.attempt_match(state, c_pat),
            (&Tuple(ref p_patterns, ref p_dd_pos), &Tuple(ref c_patterns, ref c_dd_pos)) => {
                attempt_match_all(state, p_patterns, c_patterns) && p_dd_pos == c_dd_pos
            }
            (&Ref(ref p_pat, ref p_mut), &Ref(ref c_pat, ref c_mut)) => {
                p_pat.attempt_match(state, c_pat) && p_mut == c_mut
            }
            (
                &Slice(ref p_pats_a, ref p_op_pat, ref p_pats_b),
                &Slice(ref c_pats_a, ref c_op_pat, ref c_pats_b),
            ) => {
                attempt_match_all(state, p_pats_a, c_pats_a)
                    && attempt_match_option(state, *p_op_pat, *c_op_pat)
                    && attempt_match_all(state, p_pats_b, c_pats_b)
            }
            (&Lit(ref p_expr), &Lit(ref c_expr)) => p_expr.attempt_match(state, c_expr),
            (
                &Range(ref p_ex1, ref p_ex2, ref p_incl),
                &Range(ref c_ex1, ref c_ex2, ref c_incl),
            ) => {
                attempt_match_option(state, *p_ex1, *c_ex1)
                    && attempt_match_option(state, *p_ex2, *c_ex2)
                    && p_incl == c_incl
            }
            (&Path(ref p), &Path(ref c)) => p.attempt_match(state, c),
            _ => false,
        }
    }
}

impl Matchable for rustc_hir::Field<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.ident.attempt_match(state, &code.ident) && self.expr.attempt_match(state, &code.expr)
    }
}

impl Matchable for rustc_hir::FieldPat<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.ident.attempt_match(state, &code.ident) && self.pat.attempt_match(state, &code.pat)
    }
}

impl Matchable for rustc_hir::BinOp {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.node == code.node
    }
}

impl Matchable for Symbol {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self == code
    }
}

impl Matchable for usize {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self == code
    }
}

impl Matchable for rustc_hir::Destination {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        attempt_match_option(state, self.label.as_ref(), code.label.as_ref())
    }
}

impl Matchable for rustc_ast::ast::Label {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.ident.name.attempt_match(state, &code.ident.name)
    }
}

impl Matchable for ast::Ident {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.name.attempt_match(state, &code.name)
    }
}

impl Matchable for rustc_hir::QPath<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        // TODO: Consider using TypeckTables::qpath_def, then passing the two defs to the match
        // currently for rustc_hir::Path below.
        use crate::rustc_hir::QPath::*;
        match (self, code) {
            (&Resolved(p_ty, ref p_path), &Resolved(c_ty, ref c_path)) => {
                attempt_match_option(state, p_ty, c_ty) && p_path.attempt_match(state, c_path)
            }
            (&TypeRelative(ref p_ty, ref p_segment), &TypeRelative(ref c_ty, ref c_segment)) => {
                p_ty.attempt_match(state, c_ty) && p_segment.attempt_match(state, c_segment)
            }
            _ => false,
        }
    }
}

impl Matchable for rustc_hir::Path<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self.res, code.res) {
            (rustc_hir::def::Res::Local(p_hir_id), rustc_hir::def::Res::Local(c_hir_id)) => state
                .match_placeholders
                .matched_variable_decls
                .get(&p_hir_id)
                .map(|matched_var_decl| matched_var_decl.code_hir_id == c_hir_id)
                .unwrap_or(false),
            _ => self.res == code.res,
        }
    }
}

impl Matchable for rustc_hir::PathSegment<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.ident.name == code.ident.name && attempt_match_option(state, self.args, code.args)
    }
}

impl Matchable for rustc_hir::Stmt<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use rustc_hir::StmtKind;
        match (&self.kind, &code.kind) {
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

impl Matchable for rustc_hir::Local<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.pat.attempt_match(state, &code.pat)
            && attempt_match_option(state, self.ty, code.ty)
            && attempt_match_option(state, self.init, code.init)
            && self.attrs.attempt_match(state, &code.attrs)
    }
}

impl Matchable for rustc_hir::Item<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        state.match_placeholders.matched_variable_decls.insert(
            self.hir_id,
            MatchedVariableDecl {
                code_hir_id: code.hir_id,
                name: code.ident.to_string(),
            },
        );
        self.attrs.attempt_match(state, &*code.attrs)
            && self.vis.attempt_match(state, &code.vis)
            && self.kind.attempt_match(state, &code.kind)
    }
}

impl Matchable for rustc_hir::ItemKind<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use crate::rustc_hir::ItemKind;
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

impl Matchable for rustc_hir::AnonConst {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.body.attempt_match(state, &code.body)
    }
}

impl Matchable for rustc_hir::BodyId {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        let p_body = state.tcx.hir().body(*self);
        let c_body = state.tcx.hir().body(*code);
        p_body.attempt_match(state, c_body)
    }
}

impl Matchable for rustc_hir::Visibility<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        use crate::rustc_hir::VisibilityKind::*;
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
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'tcx>,
        _code: &'tcx Self,
    ) -> bool {
        // TODO
        false
    }
}

impl Matchable for rustc_hir::Block<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        if !self.stmts.attempt_match(state, &code.stmts) {
            return false;
        }
        // The trailing expression in a block, if present, is never consumed by a placeholder since
        // it's not a statement, so match it separately.
        if !attempt_match_option(state, self.expr, code.expr) {
            return false;
        }
        true
    }
}

impl Matchable for Vec<rustc_hir::Stmt<'_>> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        // Ideally we should do what regex matching does and build an FSA or something. For now we
        // just apply a more basic algorithm. Look for matches at the start, if we find a
        // placeholder, look for matches at the end, then the placeholder takes whatever is left in
        // the middle. This means that we only support a single placeholder in a block.
        for (i, stmt) in self.iter().enumerate() {
            if let Some(hir_id) = state.opt_statements_placeholder_hir_id(stmt) {
                if code.len() < self.len() + 1 {
                    return false;
                }
                let p_after = &self[i + 1..];
                let c_after = &code[code.len() - p_after.len()..];
                if self[..i].attempt_match(state, &code[..i])
                    && p_after.attempt_match(state, c_after)
                    && state.placeholder_types_by_id.contains_key(&hir_id)
                {
                    // TODO: Refactor this insert and the other one to a common location so
                    // that both check there isn't already something there.
                    state.match_placeholders.placeholders_by_id.insert(
                        hir_id,
                        Placeholder::new(PlaceholderContents::Statements(
                            &code[i..code.len() - p_after.len()],
                        )),
                    );
                    return true;
                }
                return false;
            }
        }
        // No placeholder was found, just match statements 1:1
        self.attempt_match(state, &code)
    }
}

impl Matchable for rustc_hir::GenericArgs<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.parenthesized == code.parenthesized
            && self.args.attempt_match(state, &*code.args)
            && self.bindings.attempt_match(state, &*code.bindings)
    }
}

impl Matchable for rustc_hir::GenericArg<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self, code) {
            (
                rustc_hir::GenericArg::Lifetime(ref p_lifetime),
                rustc_hir::GenericArg::Lifetime(ref c_lifetime),
            ) => p_lifetime.attempt_match(state, c_lifetime),
            (rustc_hir::GenericArg::Type(ref p_type), rustc_hir::GenericArg::Type(ref c_type)) => {
                p_type.attempt_match(state, c_type)
            }
            _ => false,
        }
    }
}

impl Matchable for rustc_hir::TypeBinding<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        self.ident.name.attempt_match(state, &code.ident.name)
            && self.kind.attempt_match(state, &code.kind)
    }
}

impl Matchable for rustc_hir::TypeBindingKind<'_> {
    fn attempt_match<'r, 'a, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'tcx>,
        code: &'tcx Self,
    ) -> bool {
        match (self, code) {
            (
                rustc_hir::TypeBindingKind::Equality { ty: p_ty },
                rustc_hir::TypeBindingKind::Equality { ty: c_ty },
            ) => p_ty.attempt_match(state, c_ty),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Matches<'r, 'tcx: 'r> {
    expr_matches: Vec<Match<'r, 'tcx, rustc_hir::Expr<'tcx>>>,
    pattern_matches: Vec<Match<'r, 'tcx, rustc_hir::Pat<'tcx>>>,
    type_matches: Vec<Match<'r, 'tcx, rustc_hir::Ty<'tcx>>>,
    trait_ref_matches: Vec<Match<'r, 'tcx, rustc_hir::TraitRef<'tcx>>>,
}

impl<'r, 'tcx> Matches<'r, 'tcx> {
    fn new() -> Matches<'r, 'tcx> {
        Matches {
            expr_matches: Vec::new(),
            pattern_matches: Vec::new(),
            type_matches: Vec::new(),
            trait_ref_matches: Vec::new(),
        }
    }
}

#[derive(Debug)]
struct Match<'r, 'tcx: 'r, T: StartMatch<'tcx>> {
    rule: &'r Rule<'tcx, T>,
    node: &'tcx T,
    // Parent of the patched expression if the parent is also an expression. Used to determine if we
    // need to insert parenthesis.
    // TODO: For nested matches, this might not be quite what we want. We want to know what the
    // parent of the replacement will be. For a top-level match, the parent will always be the
    // parent of the matched code, but for a match within a placeholder, if the the top-level of the
    // placeholder matches, then the new parent will be from the replacement expression in the
    // parent rule.
    parent_node: Option<&'tcx T>,
    match_placeholders: MatchPlaceholders<'r, 'tcx>,
    original_span: Span,
}

impl<'r, 'a, 'tcx, T: StartMatch<'tcx>> Match<'r, 'tcx, T> {
    fn get_replacement_source(&self, tcx: TyCtxt<'tcx>) -> String {
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
pub(crate) struct MatchedVariableDecl {
    // The ID of the variable in the user code.
    code_hir_id: HirId,
    name: String,
}

#[derive(Debug)]
pub(crate) struct MatchPlaceholders<'r, 'tcx: 'r> {
    // Maps the IDs of placeholders in arguments, to their state (unbound, bound to expression
    // etc).
    placeholders_by_id: HashMap<HirId, Placeholder<'r, 'tcx>>,
    // Maps from variables declared in the search pattern to variables declared in the code.
    matched_variable_decls: HashMap<HirId, MatchedVariableDecl>,
}

impl<'r, 'a, 'tcx> MatchPlaceholders<'r, 'tcx> {
    fn new() -> MatchPlaceholders<'r, 'tcx> {
        MatchPlaceholders {
            placeholders_by_id: HashMap::new(),
            matched_variable_decls: HashMap::new(),
        }
    }

    fn get_placeholder<'this>(&'this self, hir_id: HirId) -> Option<&'this Placeholder<'r, 'tcx>> {
        self.placeholders_by_id.get(&hir_id)
    }
}

#[derive(Debug, Copy, Clone)]
enum PlaceholderContents<'tcx> {
    Expr(&'tcx rustc_hir::Expr<'tcx>),
    Statements(&'tcx [rustc_hir::Stmt<'tcx>]),
    Pattern(&'tcx rustc_hir::Pat<'tcx>),
}

impl<'tcx> PlaceholderContents<'tcx> {
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
    fn needs_parenthesis(&self, parent_expr: Option<&rustc_hir::Expr>) -> bool {
        if let PlaceholderContents::Expr(expr) = *self {
            OperatorPrecedence::needs_parenthesis(parent_expr, expr)
        } else {
            false
        }
    }
}

#[derive(Debug)]
struct Placeholder<'r, 'tcx: 'r> {
    contents: PlaceholderContents<'tcx>,
    // Matches found within contents. Populated if and only if the rule that owns this placeholder
    // succeeds.
    matches: Matches<'r, 'tcx>,
}

impl<'r, 'tcx: 'r> Placeholder<'r, 'tcx> {
    fn new(contents: PlaceholderContents<'tcx>) -> Placeholder<'r, 'tcx> {
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
    fn from_expr(expr: &rustc_hir::Expr) -> Option<OperatorPrecedence> {
        use rustc_hir::ExprKind;
        Some(match expr.kind {
            ExprKind::Unary(..) => OperatorPrecedence::Unary,
            ExprKind::Binary(op, ..) => {
                use rustc_hir::BinOpKind;
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
        maybe_parent_expr: Option<&rustc_hir::Expr>,
        child_expr: &rustc_hir::Expr,
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
    match (search_span.from_expansion(), code_span.from_expansion()) {
        (true, true) => {
            let search_expn = search_span.ctxt().outer_expn().expn_data();
            let code_expn = code_span.ctxt().outer_expn().expn_data();
            if is_same_expansion(&search_expn, &code_expn) {
                get_original_spans(search_expn.call_site, code_expn.call_site)
            } else {
                None
            }
        }
        (false, false) => Some((search_span, code_span)),
        _ => None,
    }
}

fn is_same_expansion(a: &source_map::ExpnData, b: &source_map::ExpnData) -> bool {
    use crate::source_map::ExpnKind::*;
    match (&a.kind, &b.kind) {
        (Root, Root) => true,
        (Macro(a_kind, a_descr), Macro(b_kind, b_descr)) => a_kind == b_kind && a_descr == b_descr,
        (Desugaring(a_kind), Desugaring(b_kind)) => a_kind == b_kind,
        _ => false,
    }
}

// Searches the callsites of the first span until it finds one that is contained within the second
// span.
fn span_within_span(span: Span, target: Span) -> Span {
    if target.contains(span) {
        span
    } else {
        let expn_info = span.ctxt().outer_expn().expn_data();
        span_within_span(expn_info.call_site, target)
    }
}

// Returns whether following the expansions of `rule_span` and `code_span` results in the same
// sequence of expansions.
fn all_expansions_equal(rule_span: Span, code_span: Span) -> bool {
    get_original_spans(rule_span, code_span).is_some()
}

// Visits the replacement AST looking for variables that need to be replaced with their bound values
// from the matched source then recording the spans for said replacement.
struct ReplacementVisitor<'r, 'tcx, T: StartMatch<'tcx>> {
    tcx: TyCtxt<'tcx>,
    result: Vec<CodeSubstitution<Span>>,
    current_match: &'r Match<'r, 'tcx, T>,
    parent_expr: Option<&'tcx rustc_hir::Expr<'tcx>>,
    // Map from HirIds of variables declared in the replacement pattern to HirIds declared in the
    // code that should replace them.
    substitute_hir_ids: HashMap<HirId, HirId>,
}

impl<'r, 'tcx, T: StartMatch<'tcx>> ReplacementVisitor<'r, 'tcx, T> {
    // Returns a snippet of code for the supplied definition.
    fn hir_id_snippet(&self, hir_id: HirId) -> String {
        let source_map = self.tcx.sess.source_map();
        source_map
            .span_to_snippet(self.tcx.hir().span(hir_id))
            .unwrap()
    }

    // Check if the supplied expression is a placeholder variable. If it is, replace the supplied
    // span with whatever was bound to the placeholder and return true.
    fn process_expr(&mut self, expr: &'tcx rustc_hir::Expr, placeholder_span: Span) -> bool {
        if let rustc_hir::ExprKind::Path(ref path) = expr.kind {
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

    fn process_placeholder(&mut self, placeholder: &Placeholder<'r, 'tcx>, placeholder_span: Span) {
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

impl<'r, 'tcx, T: StartMatch<'tcx>> intravisit::Visitor<'tcx> for ReplacementVisitor<'r, 'tcx, T> {
    type Map = rustc_middle::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.tcx.hir())
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr) {
        self.process_expr(expr, expr.span);
        let old_parent = self.parent_expr;
        self.parent_expr = Some(expr);
        intravisit::walk_expr(self, expr);
        self.parent_expr = old_parent;
    }

    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt) {
        if let rustc_hir::StmtKind::Semi(ref expr) = stmt.kind {
            if let rustc_hir::ExprKind::Call(ref expr_fn, _) = expr.kind {
                if self.process_expr(expr_fn, stmt.span) {
                    return;
                }
            }
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat) {
        if let rustc_hir::PatKind::Binding(_, hir_id, ref ident, _) = pat.kind {
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
                } else if let Some(matched_var_decl) = self
                    .current_match
                    .match_placeholders
                    .matched_variable_decls
                    .get(search_hir_id)
                {
                    // TODO: Would the above be clearer if the RHS was extracted to a method on
                    // Match?

                    let code = self.hir_id_snippet(matched_var_decl.code_hir_id);
                    // We only replace variable names if their code snippet
                    // matches their name. Otherwise we risk trying to replace
                    // variables in compiler generated code, which generally has
                    // large spans that encompas the whole expression. We also
                    // don't treat variable declarations as placeholders if they
                    // originate from macros.
                    if code == matched_var_decl.name
                        && !self
                            .tcx
                            .hir()
                            .span(matched_var_decl.code_hir_id)
                            .from_expansion()
                    {
                        // Record the mapping so that we can replace references
                        // to the variable as well.
                        self.substitute_hir_ids
                            .insert(hir_id, matched_var_decl.code_hir_id);
                        self.result.push(CodeSubstitution::new(ident.span, code));
                    }
                }
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

pub(crate) fn substitions_for_matches<'r, 'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    matches: &Matches<'r, 'tcx>,
) -> Vec<CodeSubstitution<Span>> {
    fn add_substitions_for_matches<'r, 'a, 'tcx, T: StartMatch<'tcx>>(
        tcx: TyCtxt<'tcx>,
        matches: &[Match<'r, 'tcx, T>],
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
