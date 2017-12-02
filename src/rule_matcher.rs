use std::collections::{HashMap, HashSet};
use syntax_pos::SpanSnippetError;
use rustc::ty::subst::Subst;
use syntax::codemap::{self, CodeMap, Spanned};
use syntax::ast;
use syntax::ptr::P;
use syntax::ast::NodeId;
use rustc::hir::{self, intravisit};
use rustc::ty::{self, TyCtxt};
use syntax::ext::quote::rt::Span;
use rules::{Rules, Rule};
use rustc::infer::{self, InferCtxt};
use syntax::symbol::Symbol;
use ::std::mem;
use std::fmt::Debug;
use rustc::traits::{ObligationCause, Reveal};
use definitions::RerastDefinitions;
use ::syntax;
use rule_finder::StartMatch;
use ::Config;
use super::node_id_from_path;

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
            tcx: tcx,
            rules: rules,
            matches: Matches::new(),
            rule_mod_symbol: Symbol::intern(super::RULES_MOD_NAME),
            parent_expr: None,
            body_id: None,
            rerast_definitions: rerast_definitions,
            config: config,
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
            .codemap()
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
        let rule_fn_id = self.tcx.hir.body_owner_def_id(rule.body_id);
        let rule_tables = self.tcx.body_tables(rule.body_id);
        let rule_body = self.tcx.hir.body(rule.body_id);

        let maybe_match_placeholders = self.tcx.infer_ctxt().enter(|infcx| {
            let tcx = infcx.tcx;
            let substs = infcx.fresh_substs_for_item(tcx.def_span(rule_fn_id), rule_fn_id);
            let placeholder_types_by_id = rule_body
                .arguments
                .iter()
                .map(|arg| {
                    (arg.pat.id, {
                        let ty = rule_tables.node_id_to_type(self.tcx.hir.node_to_hir_id(arg.id));
                        ty.subst(tcx, substs)
                    })
                })
                .collect();

            let mut match_state = MatchState {
                tcx: tcx,
                infcx: infcx,
                body_id: self.body_id,
                rule_type_tables: rule_tables,
                match_placeholders: MatchPlaceholders::new(),
                placeholder_types_by_id: placeholder_types_by_id,
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
        maybe_match_placeholders.map(|match_placeholders| {
            Match {
                rule: rule,
                node: node,
                match_placeholders: match_placeholders,
                parent_node: parent_node,
                original_span: original_span,
            }
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
                    if placeholder_expr.id == StartMatch::node_id(m.node) {
                        // We've already matched this expression, don't match it again, but do
                        // try to find matches in its children.
                        self.process_children_of_expression(placeholder_expr);
                    } else {
                        intravisit::Visitor::visit_expr(self, placeholder_expr);
                    }
                }
                PlaceholderContents::Statements(placeholder_stmts) => for stmt in placeholder_stmts
                {
                    intravisit::Visitor::visit_stmt(self, stmt);
                },
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
        intravisit::NestedVisitorMap::All(&self.tcx.hir)
    }

    fn visit_item(&mut self, item: &'gcx hir::Item) {
        if let hir::Item_::ItemMod(_) = item.node {
            // Avoid trying to find matches in the rules file.
            if item.name == self.rule_mod_symbol {
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
            hir::Expr_::ExprBlock(_) => {
                // We want to ensure that visit_expr is not called for the root expression of our
                // body (the block), since we don't want to replace it. But we still want to visit
                // the body arguments, so we do so explicitly.
                for arg in &body.arguments {
                    self.visit_id(arg.id);
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
    placeholder_types_by_id: HashMap<NodeId, ty::Ty<'tcx>>,
    rerast_definitions: RerastDefinitions<'gcx>,
    placeholder_ids: &'r HashSet<NodeId>,
    // Whether bindings within a pattern are permitted to match any pattern. Otherwise, bindings are
    // only permitted to match bindings. This is enabled within replace_pattern, since the bindings
    // are only used within the pattern, not also as expressions, so binding to a pattern is
    // permissible.
    bindings_can_match_patterns: bool,
    debug_active: bool,
}

impl<'r, 'a, 'gcx: 'a + 'tcx, 'tcx: 'a> MatchState<'r, 'a, 'gcx, 'tcx> {
    fn attempt_to_bind_expr(&mut self, qpath: &hir::QPath, expr: &'gcx hir::Expr) -> bool {
        if let Some(node_id) = node_id_from_path(qpath) {
            if self.placeholder_ids.contains(&node_id) {
                let p_ty = self.placeholder_types_by_id[&node_id];
                let c_ty = self.code_type_tables().expr_ty(expr);
                // We check the type of the expression in our code both with and without
                // adjustment. It'd be nice if we didn't have to do this. I'm not sure it actually
                // covers all cases. The adjusted type includes autoderef, autoref etc, but since
                // p_ty is never adjusted similarly, we need to check the non-adjusted type as well.
                let c_ty_adjusted = self.code_type_tables().expr_ty_adjusted(expr);
                let cause = ObligationCause::dummy();
                let param_env = ty::ParamEnv::empty(Reveal::All);
                if self.infcx.at(&cause, param_env).sub(p_ty, c_ty).is_err()
                    && self.infcx
                        .at(&cause, param_env)
                        .sub(p_ty, c_ty_adjusted)
                        .is_err()
                {
                    debug!(self, "Types didn't match");
                    return false;
                }

                let old_placeholder = self.match_placeholders
                    .placeholders_by_id
                    .insert(node_id, Placeholder::new(PlaceholderContents::Expr(expr)));
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
        self.infcx
            .can_sub(ty::ParamEnv::empty(Reveal::All), a, b)
            .is_ok()
    }

    // Returns whether the supplied fn_expr (e.g. <Foo>::bar) is a reference to the same method as
    // is called by method_call_id (e.g. foo.bar()).
    fn fn_expr_equals_method_call(
        &self,
        fn_expr: &hir::Expr,
        fn_type_tables: &ty::TypeckTables<'gcx>,
        method_call_id: NodeId,
        method_type_tables: &ty::TypeckTables<'gcx>,
    ) -> bool {
        if let Some(&hir::def::Def::Method(method_id)) = fn_type_tables
            .type_dependent_defs()
            .get(self.tcx.hir.node_to_hir_id(fn_expr.id))
        {
            return method_type_tables.type_dependent_defs()
                [self.tcx.hir.node_to_hir_id(method_call_id)]
                .def_id() == method_id;
        }
        false
    }

    // Checks if the supplied statement is a placeholder for a sequence of statements. e.g. `a();`
    // where `a` is of type rerast::Statements. If it is, returns the NodeId of the placeholder.
    fn opt_statements_placeholder_node_id(&self, stmt: &hir::Stmt) -> Option<NodeId> {
        if let hir::Stmt_::StmtSemi(ref expr, _) = stmt.node {
            if let hir::Expr_::ExprCall(ref function, _) = expr.node {
                let fn_ty = self.rule_type_tables.expr_ty(function);
                if !self.can_sub(fn_ty, self.rerast_definitions.statements) {
                    return None;
                }
                if let hir::Expr_::ExprPath(ref path) = function.node {
                    if let Some(node_id) = node_id_from_path(path) {
                        if self.placeholder_ids.contains(&node_id) {
                            return Some(node_id);
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
        self.tcx.sess.codemap().span_to_snippet(span)
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
            && self.iter()
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
        use rustc::hir::Expr_::*;
        let result = match (&self.node, &code.node) {
            // TODO: ExprType, ExprInlineAsm (or more likely report that we don't support it).
            (&ExprCall(ref p_fn, ref p_args), &ExprCall(ref c_fn, ref c_args)) => {
                p_fn.attempt_match(state, c_fn) && p_args.attempt_match(state, c_args)
            }
            (
                &ExprMethodCall(ref p_name, _, ref p_args),
                &ExprMethodCall(ref c_name, _, ref c_args),
            ) => p_name.attempt_match(state, c_name) && p_args.attempt_match(state, c_args),
            (&ExprMethodCall(_, _, ref p_args), &ExprCall(ref c_fn, ref c_args)) => {
                state.fn_expr_equals_method_call(
                    c_fn,
                    state.code_type_tables(),
                    self.id,
                    state.rule_type_tables,
                ) && p_args.attempt_match(state, c_args)
            }
            (&ExprCall(ref p_fn, ref p_args), &ExprMethodCall(_, _, ref c_args)) => {
                state.fn_expr_equals_method_call(
                    p_fn,
                    state.rule_type_tables,
                    code.id,
                    state.code_type_tables(),
                ) && p_args.attempt_match(state, c_args)
            }
            (&ExprBinary(ref p_op, ref p1, ref p2), &ExprBinary(ref c_op, ref c1, ref c2)) => {
                p_op.attempt_match(state, c_op) && p1.attempt_match(state, c1)
                    && p2.attempt_match(state, c2)
            }
            (&ExprUnary(p_op, ref p_expr), &ExprUnary(c_op, ref c_expr)) => {
                p_op == c_op && p_expr.attempt_match(state, c_expr)
            }
            (&ExprAddrOf(p_mut, ref p_expr), &ExprAddrOf(c_mut, ref c_expr)) => {
                p_mut == c_mut && p_expr.attempt_match(state, c_expr)
            }
            (&ExprLit(ref p_lit), &ExprLit(ref c_lit)) => {
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
                &ExprLoop(ref p_block, ref p_name, ref p_type),
                &ExprLoop(ref c_block, ref c_name, ref c_type),
            ) => {
                p_type == c_type && p_name.attempt_match(state, c_name)
                    && p_block.attempt_match(state, c_block)
            }
            (&ExprTup(ref p_vec), &ExprTup(ref c_vec)) |
            (&ExprArray(ref p_vec), &ExprArray(ref c_vec)) => p_vec.attempt_match(state, c_vec),
            (&ExprRepeat(ref p_expr, ref p_body_id), &ExprRepeat(ref c_expr, ref c_body_id)) => {
                p_expr.attempt_match(state, c_expr) && p_body_id.attempt_match(state, c_body_id)
            }
            (
                &ExprIf(ref p_cond, ref p_block, ref p_else),
                &ExprIf(ref c_cond, ref c_block, ref c_else),
            ) => {
                p_cond.attempt_match(state, c_cond) && p_block.attempt_match(state, c_block)
                    && p_else.attempt_match(state, c_else)
            }
            (
                &ExprMatch(ref p_expr, ref p_arms, ref p_source),
                &ExprMatch(ref c_expr, ref c_arms, ref c_source),
            ) => {
                p_expr.attempt_match(state, c_expr) && p_source == c_source
                    && p_arms.attempt_match(state, c_arms)
            }
            (
                &ExprStruct(ref p_path, ref p_fields, ref p_expr),
                &ExprStruct(ref c_path, ref c_fields, ref c_expr),
            ) => {
                p_path.attempt_match(state, c_path) && p_fields.attempt_match(state, c_fields)
                    && p_expr.attempt_match(state, c_expr)
            }
            (&ExprBlock(ref p_block), &ExprBlock(ref c_block)) => {
                p_block.attempt_match(state, c_block)
            }
            (&ExprCast(ref p_expr, ref _p_ty), &ExprCast(ref c_expr, ref _c_ty)) => {
                p_expr.attempt_match(state, c_expr)
                    && state.can_sub(
                        state.rule_type_tables.expr_ty(self),
                        state.code_type_tables().expr_ty(code),
                    )
            }
            (&ExprIndex(ref p_expr, ref p_index), &ExprIndex(ref c_expr, ref c_index)) => {
                p_expr.attempt_match(state, c_expr) && p_index.attempt_match(state, c_index)
            }
            (&ExprField(ref p_expr, ref p_name), &ExprField(ref c_expr, ref c_name)) => {
                p_expr.attempt_match(state, c_expr) && p_name.attempt_match(state, c_name)
            }
            (&ExprTupField(ref p_expr, ref p_index), &ExprTupField(ref c_expr, ref c_index)) => {
                p_expr.attempt_match(state, c_expr) && p_index.attempt_match(state, c_index)
            }
            (&ExprAssign(ref p_lhs, ref p_rhs), &ExprAssign(ref c_lhs, ref c_rhs)) => {
                p_lhs.attempt_match(state, c_lhs) && p_rhs.attempt_match(state, c_rhs)
            }
            (
                &ExprAssignOp(ref p_op, ref p_lhs, ref p_rhs),
                &ExprAssignOp(ref c_op, ref c_lhs, ref c_rhs),
            ) => {
                p_op.attempt_match(state, c_op) && p_lhs.attempt_match(state, c_lhs)
                    && p_rhs.attempt_match(state, c_rhs)
            }
            (&ExprBreak(ref p_label, ref p_expr), &ExprBreak(ref c_label, ref c_expr)) => {
                p_label.attempt_match(state, c_label) && p_expr.attempt_match(state, c_expr)
            }
            (&ExprAgain(ref p_label), &ExprAgain(ref c_label)) => {
                p_label.attempt_match(state, c_label)
            }
            (
                &ExprWhile(ref p_expr, ref p_block, ref p_name),
                &ExprWhile(ref c_expr, ref c_block, ref c_name),
            ) => {
                p_expr.attempt_match(state, c_expr) && p_block.attempt_match(state, c_block)
                    && p_name.attempt_match(state, c_name)
            }
            (
                &ExprClosure(p_capture, _, ref p_body_id, _, ref p_gen),
                &ExprClosure(c_capture, _, ref c_body_id, _, ref c_gen),
            ) => {
                p_capture == c_capture && p_body_id.attempt_match(state, c_body_id)
                    && p_gen == c_gen
            }
            (&ExprRet(ref p_expr), &ExprRet(ref c_expr)) => p_expr.attempt_match(state, c_expr),
            (&ExprBox(ref p_expr), &ExprBox(ref c_expr)) => p_expr.attempt_match(state, c_expr),
            (&ExprPath(ref p_path), &ExprPath(ref c_path)) => {
                // First check if the pattern is a placeholder and bind it if it is, otherwise try a
                // literal matching.
                if state.attempt_to_bind_expr(p_path, code) {
                    // For placeholders, return in order to bypass checking for identical macro
                    // expansion that would otherwise happen after the match.
                    return true;
                }
                p_path.attempt_match(state, c_path)
            }
            (&ExprPath(ref path), _) => {
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
                    "Expression:   {:?}\ndidn't match: {:?}",
                    code.node,
                    self.node
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

impl Matchable for hir::Ty_ {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use hir::Ty_::*;
        match (self, code) {
            (&TySlice(ref p), &TySlice(ref c)) | (&TyArray(ref p, _), &TyArray(ref c, _)) => {
                p.attempt_match(state, c)
            }
            (&TyPtr(ref p), &TyPtr(ref c)) => p.attempt_match(state, c),
            (&TyRptr(ref p_lifetime, ref p_ty), &TyRptr(ref c_lifetime, ref c_ty)) => {
                p_lifetime.attempt_match(state, c_lifetime) && p_ty.attempt_match(state, c_ty)
            }
            (&TyBareFn(ref p), &TyBareFn(ref c)) => p.attempt_match(state, c),
            (&TyNever, &TyNever) => true,
            (&TyTup(ref p), &TyTup(ref c)) => p.attempt_match(state, c),
            (&TyPath(ref p), &TyPath(ref c)) => p.attempt_match(state, c),
            (&TyTraitObject(ref p, ref p_lifetime), &TyTraitObject(ref c, ref c_lifetime)) => {
                p.attempt_match(state, c) && p_lifetime.attempt_match(state, c_lifetime)
            }
            // TODO: TyImplTraitExistential
            // TODO: TyImplTraitUniversal
            // TODO: TyTypeOf
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

impl Matchable for hir::TraitRef {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        _state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.path.def == code.path.def
    }
}

impl Matchable for hir::TyParamBound {
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
        self.attrs.is_empty() && code.attrs.is_empty() && self.pats.attempt_match(state, &code.pats)
            && self.guard.attempt_match(state, &code.guard)
            && self.body.attempt_match(state, &code.body)
    }
}

impl Matchable for hir::Pat {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use hir::PatKind::*;
        match (&self.node, &code.node) {
            (&Wild, &Wild) => true,
            (&Binding(p_mode, p_node_id, ref _p_name, ref p_pat), _) => {
                if state.bindings_can_match_patterns {
                    state.match_placeholders.placeholders_by_id.insert(
                        p_node_id,
                        Placeholder::new(PlaceholderContents::Pattern(code)),
                    );
                    true
                } else if let Binding(c_mode, c_node_id, ref _c_name, ref c_pat) = code.node {
                    if p_mode == c_mode && p_pat.is_none() && c_pat.is_none() {
                        state
                            .match_placeholders
                            .matched_variable_decls
                            .insert(p_node_id, c_node_id);
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
                    result.sort_by_key(|pat| pat.node.name);
                    result
                }

                p_qpath.attempt_match(state, c_qpath) && p_dotdot == c_dotdot
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
                p_qpath.attempt_match(state, c_qpath) && p_pats.attempt_match(state, c_pats)
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
                p_pats_a.attempt_match(state, c_pats_a) && p_op_pat.attempt_match(state, c_op_pat)
                    && p_pats_b.attempt_match(state, c_pats_b)
            }
            (&Lit(ref p_expr), &Lit(ref c_expr)) => p_expr.attempt_match(state, c_expr),
            (
                &Range(ref p_ex1, ref p_ex2, ref p_incl),
                &Range(ref c_ex1, ref c_ex2, ref c_incl),
            ) => {
                p_ex1.attempt_match(state, c_ex1) && p_ex2.attempt_match(state, c_ex2)
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
        self.name.attempt_match(state, &code.name) && self.expr.attempt_match(state, &code.expr)
    }
}

impl Matchable for hir::FieldPat {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.name.attempt_match(state, &code.name) && self.pat.attempt_match(state, &code.pat)
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
        self.ident.attempt_match(state, &code.ident)
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
        use hir::QPath::*;
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
        match (self.def, code.def) {
            (hir::def::Def::Local(p_def_id), hir::def::Def::Local(c_def_id)) => {
                state
                    .match_placeholders
                    .matched_variable_decls
                    .get(&p_def_id) == Some(&c_def_id)
            }
            _ => self.def == code.def,
        }
    }
}

impl Matchable for hir::PathSegment {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.name == code.name && self.parameters.attempt_match(state, &code.parameters)
    }
}

impl Matchable for hir::Stmt {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use rustc::hir::Stmt_::*;
        match (&self.node, &code.node) {
            (&StmtExpr(ref p, _), &StmtExpr(ref c, _)) |
            (&StmtSemi(ref p, _), &StmtSemi(ref c, _)) => p.attempt_match(state, c),
            (&StmtDecl(ref p, _), &StmtDecl(ref c, _)) => p.attempt_match(state, c),
            _ => false,
        }
    }
}

impl Matchable for hir::Decl_ {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use hir::Decl_::*;
        match (self, code) {
            (&DeclLocal(ref p), &DeclLocal(ref c)) => p.attempt_match(state, c),
            (&DeclItem(ref p), &DeclItem(ref c)) => {
                let krate = state.tcx.hir.krate();
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
        self.pat.attempt_match(state, &code.pat) && self.ty.attempt_match(state, &code.ty)
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
            .insert(self.id, code.id);
        self.attrs.attempt_match(state, &*code.attrs) && self.vis.attempt_match(state, &code.vis)
            && self.node.attempt_match(state, &code.node)
    }
}

impl Matchable for hir::Item_ {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use hir::Item_::*;
        match (self, code) {
            (
                &ItemStatic(ref p_ty, p_mut, ref p_body_id),
                &ItemStatic(ref c_ty, c_mut, ref c_body_id),
            ) => {
                p_ty.attempt_match(state, c_ty) && p_mut == c_mut
                    && p_body_id.attempt_match(state, c_body_id)
            }
            // TODO: Others
            _ => false,
        }
    }
}

impl Matchable for hir::BodyId {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        let p_body = state.tcx.hir.body(*self);
        let c_body = state.tcx.hir.body(*code);
        p_body.attempt_match(state, c_body)
    }
}

impl Matchable for hir::Visibility {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        use hir::Visibility::*;
        match (self, code) {
            (
                &Restricted {
                    path: ref p_path, ..
                },
                &Restricted {
                    path: ref c_path, ..
                },
            ) => p_path.attempt_match(state, c_path),
            (&Public, &Public) | (&Crate, &Crate) | (&Inherited, &Inherited) => true,
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
            if let Some(node_id) = state.opt_statements_placeholder_node_id(stmt) {
                if code.stmts.len() < self.stmts.len() + 1 {
                    return false;
                }
                let p_after = &self.stmts[i + 1..];
                let c_after = &code.stmts[code.stmts.len() - p_after.len()..];
                if self.stmts[..i].attempt_match(state, &code.stmts[..i])
                    && p_after.attempt_match(state, c_after)
                    && state.placeholder_ids.contains(&node_id)
                {
                    // TODO: Refactor this insert and the other one to a common location so
                    // that both check there isn't already something there.
                    state.match_placeholders.placeholders_by_id.insert(
                        node_id,
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

impl Matchable for hir::PathParameters {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.parenthesized == code.parenthesized
            && self.lifetimes.attempt_match(state, &*code.lifetimes)
            && self.types.attempt_match(state, &*code.types)
            && self.bindings.attempt_match(state, &*code.bindings)
    }
}

impl Matchable for hir::TypeBinding {
    fn attempt_match<'r, 'a, 'gcx, 'tcx>(
        &self,
        state: &mut MatchState<'r, 'a, 'gcx, 'tcx>,
        code: &'gcx Self,
    ) -> bool {
        self.name.attempt_match(state, &code.name) && self.ty.attempt_match(state, &code.ty)
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
struct Match<'r, 'gcx: 'r, T: StartMatch + 'gcx> {
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
            tcx: tcx,
            result: vec![],
            current_match: self,
            parent_expr: None,
            substitute_node_ids: HashMap::new(),
        };
        let codemap = tcx.sess.codemap();
        T::walk(&mut replacement_visitor, replacement);
        let mut substitutions = replacement_visitor.result;
        substitutions.sort();
        //Replacer::print_macro_backtrace("SPAN_BT", codemap, replacement.span());
        CodeSubstitution::apply(
            substitutions.into_iter(),
            codemap,
            replacement.span().source_callsite(),
        )
    }
}

#[derive(Debug)]
pub(crate) struct MatchPlaceholders<'r, 'gcx: 'r> {
    // Maps the node IDs of placeholders in arguments, to their state (unbound, bound to expression
    // etc).
    placeholders_by_id: HashMap<NodeId, Placeholder<'r, 'gcx>>,
    // Maps from variables declared in the search pattern to variables declared in the code.
    matched_variable_decls: HashMap<NodeId, NodeId>,
}

impl<'r, 'a, 'gcx, 'tcx> MatchPlaceholders<'r, 'gcx> {
    fn new() -> MatchPlaceholders<'r, 'gcx> {
        MatchPlaceholders {
            placeholders_by_id: HashMap::new(),
            matched_variable_decls: HashMap::new(),
        }
    }

    fn get_placeholder<'this>(
        &'this self,
        maybe_node_id: Option<NodeId>,
    ) -> Option<&'this Placeholder<'r, 'gcx>> {
        maybe_node_id.and_then(|node_id| self.placeholders_by_id.get(&node_id))
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
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
            Statements(stmts) => if let Some(stmt) = stmts.get(0) {
                let result = span_within_span(stmt.span, target);
                let last_span = span_within_span(stmts[stmts.len() - 1].span, target);
                result.with_hi(last_span.hi())
            } else {
                syntax::ext::quote::rt::DUMMY_SP
            },
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
            contents: contents,
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
        use rustc::hir::Expr_::*;
        Some(match expr.node {
            ExprUnary(..) => OperatorPrecedence::Unary,
            ExprBinary(op, ..) => {
                use rustc::hir::BinOp_::*;
                match op.node {
                    BiAdd | BiSub => OperatorPrecedence::AddSub,
                    BiMul | BiDiv | BiRem => OperatorPrecedence::MulDivMod,
                    BiAnd => OperatorPrecedence::LogicalAnd,
                    BiOr => OperatorPrecedence::LogicalOr,
                    BiBitXor => OperatorPrecedence::BitXor,
                    BiBitAnd => OperatorPrecedence::BitAnd,
                    BiBitOr => OperatorPrecedence::BitOr,
                    BiShl | BiShr => OperatorPrecedence::BitShift,
                    BiEq | BiLt | BiLe | BiNe | BiGe | BiGt => OperatorPrecedence::Comparison,
                }
            }
            ExprAssign(..) => OperatorPrecedence::Assignment,
            _ => return None,
        })
    }

    // Returns whether parenthsis are needed around the child expression in order to maintain
    // structure. i.e the child expression has weaker precedence than the parent.
    pub(crate) fn needs_parenthesis(maybe_parent_expr: Option<&hir::Expr>, child_expr: &hir::Expr) -> bool {
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
            if is_same_expansion(&search_expn.callee, &code_expn.callee) {
                get_original_spans(search_expn.call_site, code_expn.call_site)
            } else {
                None
            }
        }
        (None, None) => Some((search_span, code_span)),
        _ => None,
    }
}

fn is_same_expansion(a: &codemap::NameAndSpan, b: &codemap::NameAndSpan) -> bool {
    use codemap::ExpnFormat::*;
    a.format == b.format && match a.format {
        MacroBang(_) => a.span == b.span,
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
struct ReplacementVisitor<'r, 'a: 'r, 'gcx: 'a, T: StartMatch + 'gcx> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    result: Vec<CodeSubstitution>,
    current_match: &'r Match<'r, 'gcx, T>,
    parent_expr: Option<&'gcx hir::Expr>,
    // Map from NodeIds of variables declared in the replacement pattern to NodeIds declared in the
    // code that should replace them.
    substitute_node_ids: HashMap<NodeId, NodeId>,
}

impl<'r, 'a, 'gcx, T: StartMatch> ReplacementVisitor<'r, 'a, 'gcx, T> {
    // Returns a snippet of code for the supplied definition.
    fn node_id_snippet(&self, node_id: NodeId) -> String {
        let codemap = self.tcx.sess.codemap();
        codemap.span_to_snippet(self.tcx.hir.span(node_id)).unwrap()
    }

    // Check if the supplied expression is a placeholder variable. If it is, replace the supplied
    // span with whatever was bound to the placeholder and return true.
    fn process_expr(&mut self, expr: &'gcx hir::Expr, placeholder_span: Span) -> bool {
        if let hir::Expr_::ExprPath(ref path) = expr.node {
            if let Some(placeholder) = self.current_match
                .match_placeholders
                .get_placeholder(node_id_from_path(path))
            {
                self.process_placeholder(placeholder, placeholder_span);
                return true;
            } else if let Some(node_id) = node_id_from_path(path) {
                if let Some(code_node_id) = self.substitute_node_ids.get(&node_id) {
                    let code = self.node_id_snippet(*code_node_id);
                    self.result.push(CodeSubstitution {
                        span: expr.span,
                        new_code: code,
                        needs_parenthesis: false,
                    });
                    return true;
                }
            }
        }
        false
    }

    fn process_placeholder(&mut self, placeholder: &Placeholder<'r, 'gcx>, placeholder_span: Span) {
        let codemap = self.tcx.sess.codemap();
        let span = placeholder
            .contents
            .get_span(self.current_match.original_span);
        let substitutions =
            CodeSubstitution::sorted_substitions_for_matches(self.tcx, &placeholder.matches);
        let new_code = CodeSubstitution::apply(substitutions.into_iter(), codemap, span);

        self.result.push(CodeSubstitution {
            span: placeholder_span,
            new_code: new_code,
            needs_parenthesis: placeholder.contents.needs_parenthesis(self.parent_expr),
        });
    }
}

impl<'r, 'a, 'gcx, T: StartMatch> intravisit::Visitor<'gcx>
    for ReplacementVisitor<'r, 'a, 'gcx, T> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir)
    }

    fn visit_expr(&mut self, expr: &'gcx hir::Expr) {
        self.process_expr(expr, expr.span);
        let old_parent = self.parent_expr;
        self.parent_expr = Some(expr);
        intravisit::walk_expr(self, expr);
        self.parent_expr = old_parent;
    }

    fn visit_stmt(&mut self, stmt: &'gcx hir::Stmt) {
        if let hir::Stmt_::StmtSemi(ref expr, _) = stmt.node {
            if let hir::Expr_::ExprCall(ref expr_fn, _) = expr.node {
                if self.process_expr(expr_fn, stmt.span) {
                    return;
                }
            }
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_pat(&mut self, pat: &'gcx hir::Pat) {
        if let hir::PatKind::Binding(_, ref node_id, ref name, _) = pat.node {
            if let Some(search_node_id) = self.current_match
                .rule
                .declared_name_node_ids
                .get(&name.node)
            {
                if let Some(placeholder) = self.current_match
                    .match_placeholders
                    .get_placeholder(Some(*search_node_id))
                {
                    self.process_placeholder(placeholder, pat.span);
                } else if let Some(code_node_id) = self.current_match
                    .match_placeholders
                    .matched_variable_decls
                    .get(search_node_id)
                {
                    // TODO: Would the above be clearer if the RHS was extracted to a method on
                    // Match?

                    // Record the mapping so that we can replace references to the variable as well.
                    self.substitute_node_ids.insert(*node_id, *code_node_id);

                    let code = self.node_id_snippet(*code_node_id);
                    self.result.push(CodeSubstitution {
                        span: name.span,
                        new_code: code,
                        needs_parenthesis: false,
                    });
                }
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct CodeSubstitution {
    // The span to be replaced.
    pub(crate) span: Span,
    // New code to replace what's at span.
    pub(crate) new_code: String,
    // Whether parenthesis are needed around the substitution.
    pub(crate) needs_parenthesis: bool,
}

impl CodeSubstitution {
    pub(crate) fn sorted_substitions_for_matches<'r, 'a, 'gcx>(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        matches: &Matches<'r, 'gcx>,
    ) -> Vec<CodeSubstitution> {
        let mut substitutions = vec![];
        Self::add_substitions(tcx, &matches.expr_matches, &mut substitutions);
        Self::add_substitions(tcx, &matches.pattern_matches, &mut substitutions);
        Self::add_substitions(tcx, &matches.type_matches, &mut substitutions);
        Self::add_substitions(tcx, &matches.trait_ref_matches, &mut substitutions);
        substitutions.sort();
        substitutions
    }

    fn add_substitions<'r, 'a, 'gcx, T: StartMatch>(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        matches: &[Match<'r, 'gcx, T>],
        substitutions: &mut Vec<CodeSubstitution>,
    ) {
        for m in matches {
            let replacement_src = m.get_replacement_source(tcx);
            substitutions.push(CodeSubstitution {
                span: m.original_span,
                new_code: replacement_src,
                needs_parenthesis: T::needs_parenthesis(m.parent_node, &*m.rule.replace),
            });
        }
    }


    // Take the code represented by base_span and apply all the substitutions, returning the
    // resulting code.
    pub(crate) fn apply<T: Iterator<Item = CodeSubstitution>>(
        substitutions: T,
        codemap: &CodeMap,
        base_span: Span,
    ) -> String {
        let mut output = String::new();
        let mut span_lo = base_span.lo();
        for substitution in substitutions {
            output.push_str(&codemap
                .span_to_snippet(Span::new(span_lo, substitution.span.lo(), base_span.ctxt()))
                .unwrap());
            if substitution.needs_parenthesis {
                output.push('(');
            }
            output.push_str(&substitution.new_code);
            if substitution.needs_parenthesis {
                output.push(')');
            }
            span_lo = substitution.span.hi();
            // Macro invocations consume a ; that follows them. Check if the code we're replacing
            // ends with a ;. If it does and the new code doesn't then insert one. This may need to
            // be smarter, but hopefully this will do.
            let code_being_replaced = codemap.span_to_snippet(substitution.span).unwrap();
            if code_being_replaced.ends_with(';') && !substitution.new_code.ends_with(';') {
                output.push(';');
            }
        }
        output.push_str(&codemap
            .span_to_snippet(base_span.with_lo(span_lo))
            .unwrap());
        output
    }
}
