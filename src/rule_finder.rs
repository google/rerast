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
use rustc_span::symbol::Symbol;
use rustc_span::Span;
use std::marker;
use std::vec::Vec;

// Finds rules.
pub(crate) struct RuleFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    rerast_definitions: RerastDefinitions<'tcx>,
    rules_mod_symbol: Symbol,
    rules: Rules<'tcx>,
    body_ids: Vec<hir::BodyId>,
    in_rules_module: bool,
    errors: Vec<ErrorWithSpan>,
}

impl<'tcx> RuleFinder<'tcx> {
    pub(crate) fn find_rules(
        tcx: TyCtxt<'tcx>,
        rerast_definitions: RerastDefinitions<'tcx>,
        krate: &'tcx hir::Crate,
    ) -> Result<Rules<'tcx>, Vec<ErrorWithSpan>> {
        let mut rule_finder = RuleFinder {
            tcx,
            rerast_definitions,
            rules_mod_symbol: Symbol::intern(super::RULES_MOD_NAME),
            rules: Rules::new(),
            body_ids: Vec::new(),
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
        arg_ty: ty::Ty<'tcx>,
        arms: &'tcx [hir::Arm],
        arg_ty_span: Span,
    ) -> Result<(), Vec<ErrorWithSpan>> {
        if self.maybe_add_typed_rule::<hir::Expr>(arg_ty, arms)?
            || self.maybe_add_typed_rule::<hir::Pat>(arg_ty, arms)?
            || self.maybe_add_typed_rule::<hir::TraitRef>(arg_ty, arms)?
            || self.maybe_add_typed_rule::<hir::Ty>(arg_ty, arms)?
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

    fn maybe_add_typed_rule<T: 'tcx + StartMatch<'tcx>>(
        &mut self,
        arg_ty: ty::Ty<'tcx>,
        arms: &'tcx [hir::Arm],
    ) -> Result<bool, Vec<ErrorWithSpan>> {
        // Given some arms of a match statement, returns the block for arm_name if any.
        fn get_arm<'a>(arms: &'a [hir::Arm], arm_name: Symbol) -> Option<&'a hir::Block<'a>> {
            for arm in arms {
                if let hir::PatKind::Path(hir::QPath::Resolved(None, ref path)) = arm.pat.kind {
                    if let Some(segment) = path.segments.last() {
                        if segment.ident.name == arm_name {
                            if let hir::ExprKind::Block(ref block, _) = arm.body.kind {
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
        let mut placeholder_ids = Vec::new();
        for body_id in &self.body_ids {
            let body = self.tcx.hir().body(*body_id);
            for param in body.params {
                placeholder_ids.push(param.pat.hir_id);
            }
            // Allow any variable declarations at the start or the rule block to
            // serve as placeholders in addition to the funciton arguments. This
            // is necssary since async functions transform the supplied code
            // into this form. e.g. if the async function has an argument r,
            // then the function will contain a block with the first statement
            // being let r = r;
            if let hir::ExprKind::Block(block, ..) = &body.value.kind {
                for stmt in block.stmts.iter() {
                    if let hir::StmtKind::Local(local) = &stmt.kind {
                        if let hir::PatKind::Binding(_, hir_id, ..) = &local.pat.kind {
                            placeholder_ids.push(*hir_id);
                        }
                    } else {
                        break;
                    }
                }
            }
        }
        let body_id = match self.body_ids.last() {
            Some(x) => *x,
            None => return Ok(false),
        };
        if let (Some(search_block), Some(replace_block)) = (
            get_arm(arms, self.rerast_definitions.search_symbol),
            get_arm(arms, self.rerast_definitions.replace_symbol),
        ) {
            let search = T::extract_root(search_block)?;
            let replace = T::extract_root(replace_block)?;
            let rule = Rule {
                search,
                replace,
                body_id,
                placeholder_ids,
                declared_name_hir_ids: DeclaredNamesFinder::find(self.tcx, search),
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

impl<'tcx> intravisit::Visitor<'tcx> for RuleFinder<'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_item(&mut self, item: &'tcx hir::Item) {
        if let hir::ItemKind::Mod(_) = item.kind {
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

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        if !self.in_rules_module {
            return;
        }
        use crate::hir::ExprKind;
        if let ExprKind::Match(ref match_expr, ref arms, _) = expr.kind {
            if let ExprKind::MethodCall(ref _name, ref _tys, ref args) = match_expr.kind {
                if let Some(&body_id) = self.body_ids.last() {
                    let type_tables = self
                        .tcx
                        .typeck_tables_of(self.tcx.hir().body_owner_def_id(body_id));
                    let arg0 = &args[0];
                    let arg_ty = type_tables.node_type(arg0.hir_id);
                    if let Err(errors) = self.maybe_add_rule(arg_ty, arms, arg0.span) {
                        self.errors.extend(errors);
                    }
                    // Don't walk deeper into this expression.
                    return;
                }
            }
        }
        intravisit::walk_expr(self, expr)
    }

    fn visit_body(&mut self, body: &'tcx hir::Body) {
        if !self.in_rules_module {
            return;
        }
        self.body_ids.push(body.id());
        intravisit::walk_body(self, body);
        self.body_ids.pop();
    }
}

// Trait implemented by types that we can match (as opposed to be part of a match).
pub(crate) trait StartMatch<'tcx>: Matchable {
    fn span(&self) -> Span;
    fn walk<V: intravisit::Visitor<'tcx>>(visitor: &mut V, node: &'tcx Self);
    fn needs_parenthesis(_parent: Option<&Self>, _child: &Self) -> bool {
        false
    }
    // Extract the root search/replace node from the supplied block.
    fn extract_root(block: &'tcx hir::Block<'tcx>) -> Result<&'tcx Self, ErrorWithSpan>;
    // Adds the supplied rule to the appropriate typed collection in rules.
    fn add_rule(rule: Rule<'tcx, Self>, rules: &mut Rules<'tcx>)
    where
        Self: marker::Sized;
    // Get the type marker used to identify this type of search/replace.
    fn replace_marker_type(rerast_definitions: &RerastDefinitions<'tcx>) -> ty::Ty<'tcx>;
    // See comment on field of the same name on MatchState.
    fn bindings_can_match_patterns() -> bool {
        false
    }
    fn hir_id(&self) -> HirId;
}

impl<'tcx> StartMatch<'tcx> for hir::Expr<'tcx> {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<V: intravisit::Visitor<'tcx>>(visitor: &mut V, node: &'tcx Self) {
        visitor.visit_expr(node);
    }
    fn needs_parenthesis(parent: Option<&Self>, child: &Self) -> bool {
        OperatorPrecedence::needs_parenthesis(parent, child)
    }
    fn extract_root(block: &'tcx hir::Block<'tcx>) -> Result<&'tcx Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Semi(ref addr_expr) = block.stmts[0].kind {
                if let hir::ExprKind::AddrOf(_, _, ref expr) = addr_expr.kind {
                    return Ok(&**expr);
                }
            }
        }
        Err(ErrorWithSpan::new(
            "replace! macro didn't produce expected structure",
            block.span,
        ))
    }
    fn add_rule(rule: Rule<'tcx, Self>, rules: &mut Rules<'tcx>) {
        rules.expr_rules.push(rule);
    }
    fn replace_marker_type(rerast_definitions: &RerastDefinitions<'tcx>) -> ty::Ty<'tcx> {
        rerast_definitions.expr_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}

impl<'tcx> StartMatch<'tcx> for hir::Ty<'tcx> {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<V: intravisit::Visitor<'tcx>>(visitor: &mut V, node: &'tcx Self) {
        visitor.visit_ty(node);
    }
    fn extract_root(block: &'tcx hir::Block<'tcx>) -> Result<&'tcx Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Local(ref local) = block.stmts[0].kind {
                if let Some(ref ref_ty) = local.ty {
                    if let hir::TyKind::Rptr(_, ref mut_ty) = ref_ty.kind {
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
    fn add_rule(rule: Rule<'tcx, Self>, rules: &mut Rules<'tcx>) {
        rules.type_rules.push(rule);
    }
    fn replace_marker_type(rerast_definitions: &RerastDefinitions<'tcx>) -> ty::Ty<'tcx> {
        rerast_definitions.type_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}

impl<'tcx> StartMatch<'tcx> for hir::TraitRef<'tcx> {
    fn span(&self) -> Span {
        self.path.span
    }
    fn walk<V: intravisit::Visitor<'tcx>>(visitor: &mut V, node: &'tcx Self) {
        visitor.visit_trait_ref(node);
    }
    fn extract_root(block: &'tcx hir::Block<'tcx>) -> Result<&'tcx Self, ErrorWithSpan> {
        let ty = <hir::Ty as StartMatch>::extract_root(block)?;
        if let hir::TyKind::TraitObject(ref bounds, _) = ty.kind {
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
    fn add_rule(rule: Rule<'tcx, Self>, rules: &mut Rules<'tcx>) {
        rules.trait_ref_rules.push(rule);
    }
    fn replace_marker_type(rerast_definitions: &RerastDefinitions<'tcx>) -> ty::Ty<'tcx> {
        rerast_definitions.trait_ref_rule_marker
    }
    fn hir_id(&self) -> HirId {
        self.hir_ref_id
    }
}

impl<'tcx> StartMatch<'tcx> for hir::Pat<'tcx> {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<V: intravisit::Visitor<'tcx>>(visitor: &mut V, node: &'tcx Self) {
        visitor.visit_pat(node);
    }
    fn extract_root(block: &'tcx hir::Block<'tcx>) -> Result<&'tcx hir::Pat<'tcx>, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::StmtKind::Semi(ref expr) = block.stmts[0].kind {
                if let hir::ExprKind::Match(_, ref arms, _) = expr.kind {
                    // The user's pattern is wrapped in Some(x) in order to make all patterns
                    // refutable. Otherwise we'd need the user to use a different macro for
                    // refutable and irrefutable patterns which wouldn't be very ergonomic.
                    if let hir::PatKind::TupleStruct(_, ref patterns, _) = arms[0].pat.kind {
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
    fn add_rule(rule: Rule<'tcx, Self>, rules: &mut Rules<'tcx>) {
        rules.pattern_rules.push(rule);
    }
    fn replace_marker_type<'a>(rerast_definitions: &RerastDefinitions<'a>) -> ty::Ty<'a> {
        rerast_definitions.pattern_rule_marker
    }
    fn bindings_can_match_patterns() -> bool {
        true
    }
    fn hir_id(&self) -> HirId {
        self.hir_id
    }
}
