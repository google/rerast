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

use rustc::hir::{self, intravisit};
use rustc::ty::{self, TyCtxt};
use syntax::symbol::Symbol;

#[derive(Copy, Clone)]
pub(crate) struct RerastDefinitions<'gcx> {
    pub(crate) statements: ty::Ty<'gcx>,
    pub(crate) expr_rule_marker: ty::Ty<'gcx>,
    pub(crate) pattern_rule_marker: ty::Ty<'gcx>,
    pub(crate) type_rule_marker: ty::Ty<'gcx>,
    pub(crate) trait_ref_rule_marker: ty::Ty<'gcx>,
    pub(crate) search_symbol: Symbol,
    pub(crate) replace_symbol: Symbol,
}

// Visits the code in the rerast module, finding definitions we care about for later use.
pub(crate) struct RerastDefinitionsFinder<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rerast_mod_symbol: Symbol,
    inside_rerast_mod: bool,
    definitions: Option<RerastDefinitions<'gcx>>,
}

impl<'a, 'gcx> RerastDefinitionsFinder<'a, 'gcx> {
    /// Finds rerast's internal definitions. Returns none if they cannot be found. This happens for
    /// example if the root source file has a #![cfg(feature = "something")] where the "something"
    /// feature is not enabled.
    pub(crate) fn find_definitions(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        krate: &'gcx hir::Crate,
    ) -> Option<RerastDefinitions<'gcx>> {
        let mut finder = RerastDefinitionsFinder {
            tcx,
            rerast_mod_symbol: Symbol::intern(super::RERAST_INTERNAL_MOD_NAME),
            inside_rerast_mod: false,
            definitions: None,
        };
        intravisit::walk_crate(&mut finder, krate);
        finder.definitions
    }
}

// This would be a little easier if there were a way to find functions by name. There's probably
// something I've missed, but so far I haven't found one.
impl<'a, 'gcx, 'tcx> intravisit::Visitor<'gcx> for RerastDefinitionsFinder<'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir)
    }

    fn visit_item(&mut self, item: &'gcx hir::Item) {
        if self.inside_rerast_mod {
            intravisit::walk_item(self, item);
        } else {
            use hir::Item_::*;
            if let ItemMod(_) = item.node {
                if item.name == self.rerast_mod_symbol {
                    self.inside_rerast_mod = true;
                    intravisit::walk_item(self, item);
                    self.inside_rerast_mod = false;
                }
            }
        }
    }

    fn visit_body(&mut self, body: &'gcx hir::Body) {
        let fn_id = self.tcx.hir.body_owner_def_id(body.id());
        if self.tcx.item_name(fn_id) == "rerast_types" {
            let tables = self.tcx.typeck_tables_of(fn_id);
            let hir = &self.tcx.hir;
            let mut types = body
                .arguments
                .iter()
                .map(|arg| tables.node_id_to_type(hir.node_to_hir_id(arg.id)));
            self.definitions = Some(RerastDefinitions {
                statements: types
                    .next()
                    .expect("Internal error - missing type: statements"),
                expr_rule_marker: types
                    .next()
                    .expect("Internal error - missing type: expr_rule_marker"),
                pattern_rule_marker: types
                    .next()
                    .expect("Internal error - missing type: pattern_rule_marker"),
                type_rule_marker: types
                    .next()
                    .expect("Internal error - missing type: type_rule_marker"),
                trait_ref_rule_marker: types
                    .next()
                    .expect("Internal error - missing type: trait_ref_rule_marker"),
                search_symbol: Symbol::intern("Search"),
                replace_symbol: Symbol::intern("Replace"),
            })
        }
    }
}
