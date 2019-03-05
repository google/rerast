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

use super::DeclaredNamesFinder;
use crate::definitions::RerastDefinitions;
use crate::errors::ErrorWithSpan;
use crate::rule_matcher::{Matchable, OperatorPrecedence};
use crate::rules::{Rule, Rules};
use rustc::hir::{self, intravisit, HirId};
use rustc::ty::{self, TyCtxt};
use std::marker;
use std::vec::Vec;
use syntax::symbol::Symbol;
use syntax_pos::Span;

// Finds rules.
pub(crate) struct RuleFinder<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rerast_definitions: RerastDefinitions<'gcx>,
    rules_mod_symbol: Symbol,
    rules: Rules<'gcx>,
    body_id: Option<hir::BodyId>,
    in_rules_module: bool,
    errors: Vec<ErrorWithSpan>,
}

impl<'a, 'gcx> RuleFinder<'a, 'gcx> {
    pub(crate) fn find_rules(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        rerast_definitions: RerastDefinitions<'gcx>,
        krate: &'gcx hir::Crate,
    ) -> Result<Rules<'gcx>, Vec<ErrorWithSpan>> {
        let mut rule_finder = RuleFinder {
            tcx,
            rerast_definitions,
            rules_mod_symbol: Symbol::intern(super::RULES_MOD_NAME),
            rules: Rules::new(),
            body_id: None,
            in_rules_module: false,
            errors: Vec::new(),
        };
        intravisit::walk_crate(&mut rule_finder, krate);
        if rule_finder.errors.is_empty() {
            Ok(rule_finder.rules)
        } else {
            Err(rule_finder.errors)
        }
    }

    // Possibly add a rule.
    fn maybe_add_rule(
        &mut self,
        arg_ty: ty::Ty<'gcx>,
        arms: &'gcx [hir::Arm],
        body_id: hir::BodyId,
        arg_ty_span: Span,
    ) -> Result<(), Vec<ErrorWithSpan>> {
        if self.maybe_add_typed_rule::<hir::Expr>(arg_ty, arms, body_id)?
            || self.maybe_add_typed_rule::<hir::Pat>(arg_ty, arms, body_id)?
            || self.maybe_add_typed_rule::<hir::TraitRef>(arg_ty, arms, body_id)?
            || self.maybe_add_typed_rule::<hir::Ty>(arg_ty, arms, body_id)?
        {
            Ok(())
        } else {
            // TODO: Report proper span. Perhaps report other code - this will only report an
            // unexpected match.
            Err(vec![ErrorWithSpan::new(
                "Unexpected code found in rule function",
                arg_ty_span,
            )])
        }
    }

    fn maybe_add_typed_rule<T: 'gcx + StartMatch>(
        &mut self,
        arg_ty: ty::Ty<'gcx>,
        arms: &'gcx [hir::Arm],
        body_id: hir::BodyId,
    ) -> Result<bool, Vec<ErrorWithSpan>> {
        // Given some arms of a match statement, returns the block for arm_name if any.
        fn get_arm(arms: &[hir::Arm], arm_name: Symbol) -> Option<&hir::Block> {
            for arm in arms {
                if let hir::PatKind::Path(hir::QPath::Resolved(None, ref path)) = arm.pats[0].node {
                    if let Some(segment) = path.segments.last() {
                        if segment.ident.name == arm_name {
                            if let hir::ExprKind::Block(ref block, _) = arm.body.node {
                                return Some(block);
                            }
                        }
                    }
                }
            }
            None
        }

        if arg_ty != T::replace_marker_type(&self.rerast_definitions) {
            // This is a rule of a different type
            return Ok(false);
        }
        if let (Some(search_block), Some(replace_block)) = (
            get_arm(arms, self.rerast_definitions.search_symbol),
            get_arm(arms, self.rerast_definitions.replace_symbol),
        ) {
            let search = T::extract_root(search_block)?;
            let replace = T::extract_root(replace_block)?;
            let placeholder_ids = self
                .tcx
                .hir()
                .body(body_id)
                .arguments
                .iter()
                .map(|arg| arg.pat.hir_id)
                .collect();

            let rule = Rule {
                search,
                replace,
                body_id,
                declared_name_hir_ids: DeclaredNamesFinder::find(self.tcx, search),
                placeholder_ids,
            };
            rule.validate(self.tcx)?;
            T::add_rule(rule, &mut self.rules);
        } else {
            // Pretty sure this shouldn't be possible unless rerast internals are directly used.
            panic!("Missing search/replace pattern");
        }
        Ok(true)
    }
}

impl<'a, 'gcx, 'tcx> intravisit::Visitor<'gcx> for RuleFinder<'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_item(&mut self, item: &'gcx hir::Item) {
        if let hir::ItemKind::Mod(_) = item.node {
            if item.ident.name == self.rules_mod_symbol {
                self.in_rules_module = true;
                intravisit::walk_item(self, item);
                self.in_rules_module = false;
                return;
            } else if !self.in_rules_module {
                // Not the module we're interested in
                return;
            }
        }
        intravisit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &'gcx hir::Expr) {
        if !self.in_rules_module {
            return;
        }
        use crate::hir::ExprKind;
        if let ExprKind::Match(ref match_expr, ref arms, _) = expr.node {
            if let ExprKind::MethodCall(ref _name, ref _tys, ref args) = match_expr.node {
                if let Some(body_id) = self.body_id {
                    let type_tables = self
                        .tcx
                        .typeck_tables_of(self.tcx.hir().body_owner_def_id(body_id));
                    let arg0 = &args[0];
                    let arg_ty = type_tables.node_type(arg0.hir_id);
                    if let Err(errors) = self.maybe_add_rule(arg_ty, arms, body_id, arg0.span) {
                        self.errors.extend(errors);
                    }
                    // Don't walk deeper into this expression.
                    return;
                }
            }
        }
        intravisit::walk_expr(self, expr)
    }

    fn visit_body(&mut self, body: &'gcx hir::Body) {
        if !self.in_rules_module {
            return;
        }
        let old_body_id = self.body_id;
        self.body_id = Some(body.id());
        intravisit::walk_body(self, body);
        self.body_id = old_body_id;
    }
}

// Trait implemented by types that we can match (as opposed to be part of a match).
pub(crate) trait StartMatch: Matchable {
    fn span(&self) -> Span;
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self);
    fn needs_parenthesis(_parent: Option<&Self>, _child: &Self) -> bool {
        false
    }
    // Extract the root search/replace node from the supplied block.
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan>;
    // Adds the supplied rule to the appropriate typed collection in rules.
    fn add_rule<'gcx>(rule: Rule<'gcx, Self>, rules: &mut Rules<'gcx>)
    where
        Self: marker::Sized;
    // Get the type marker used to identify this type of search/replace.
    fn replace_marker_type<'gcx>(rerast_definitions: &RerastDefinitions<'gcx>) -> ty::Ty<'gcx>;
    // See comment on field of the same name on MatchState.
    fn bindings_can_match_patterns() -> bool {
        false
    }
    fn hir_id(&self) -> HirId;
}

impl StartMatch for hir::Expr {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        visitor.visit_expr(node);
    }
    fn needs_parenthesis(parent: Option<&Self>, child: &Self) -> bool {
        OperatorPrecedence::needs_parenthesis(parent, child)
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Semi(ref addr_expr) = block.stmts[0].node {
                if let hir::ExprKind::AddrOf(_, ref expr) = addr_expr.node {
                    return Ok(&**expr);
                }
            }
        }
        Err(ErrorWithSpan::new(
            "replace! macro didn't produce expected structure",
            block.span,
        ))
    }
    fn add_rule<'gcx>(rule: Rule<'gcx, Self>, rules: &mut Rules<'gcx>) {
        rules.expr_rules.push(rule);
    }
    fn replace_marker_type<'gcx>(rerast_definitions: &RerastDefinitions<'gcx>) -> ty::Ty<'gcx> {
        rerast_definitions.expr_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}

impl StartMatch for hir::Ty {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        visitor.visit_ty(node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Local(ref local) = block.stmts[0].node {
                if let Some(ref ref_ty) = local.ty {
                    if let hir::TyKind::Rptr(_, ref mut_ty) = ref_ty.node {
                        return Ok(&*mut_ty.ty);
                    }
                }
            }
        }
        Err(ErrorWithSpan::new(
            "replace_type! macro didn't produce expected structure",
            block.span,
        ))
    }
    fn add_rule<'gcx>(rule: Rule<'gcx, Self>, rules: &mut Rules<'gcx>) {
        rules.type_rules.push(rule);
    }
    fn replace_marker_type<'gcx>(rerast_definitions: &RerastDefinitions<'gcx>) -> ty::Ty<'gcx> {
        rerast_definitions.type_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}

impl StartMatch for hir::TraitRef {
    fn span(&self) -> Span {
        self.path.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        visitor.visit_trait_ref(node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        let ty = <hir::Ty as StartMatch>::extract_root(block)?;
        if let hir::TyKind::TraitObject(ref bounds, _) = ty.node {
            if bounds.len() == 1 {
                return Ok(&bounds[0].trait_ref);
            } else {
                return Err(ErrorWithSpan::new(
                    "replace_trait_ref! requires exactly one trait",
                    ty.span,
                ));
            }
        } else {
            return Err(ErrorWithSpan::new(
                "replace_trait_ref! requires a trait",
                ty.span,
            ));
        }
    }
    fn add_rule<'gcx>(rule: Rule<'gcx, Self>, rules: &mut Rules<'gcx>) {
        rules.trait_ref_rules.push(rule);
    }
    fn replace_marker_type<'gcx>(rerast_definitions: &RerastDefinitions<'gcx>) -> ty::Ty<'gcx> {
        rerast_definitions.trait_ref_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_ref_id
    }
}

impl StartMatch for hir::Pat {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        visitor.visit_pat(node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Semi(ref expr) = block.stmts[0].node {
                if let hir::ExprKind::Match(_, ref arms, _) = expr.node {
                    // The user's pattern is wrapped in Some(x) in order to make all patterns
                    // refutable. Otherwise we'd need the user to use a different macro for
                    // refutable and irrefutable patterns which wouldn't be very ergonomic.
                    if let hir::PatKind::TupleStruct(_, ref patterns, _) = arms[0].pats[0].node {
                        return Ok(&patterns[0]);
                    }
                }
            }
        }
        Err(ErrorWithSpan::new(
            "replace_pattern! macro didn't produce expected structure",
            block.span,
        ))
    }
    fn add_rule<'gcx>(rule: Rule<'gcx, Self>, rules: &mut Rules<'gcx>) {
        rules.pattern_rules.push(rule);
    }
    fn replace_marker_type<'gcx>(rerast_definitions: &RerastDefinitions<'gcx>) -> ty::Ty<'gcx> {
        rerast_definitions.pattern_rule_marker
    }
    fn bindings_can_match_patterns() -> bool {
        true
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}
