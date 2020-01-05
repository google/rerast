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

use crate::rule_finder::StartMatch;
use rustc::hir::{self, HirId};
use rustc_span::symbol::Symbol;
use std::collections::HashMap;
use std::vec::Vec;

#[derive(Debug)]
pub(crate) struct Rule<'tcx, T: StartMatch<'tcx>> {
    pub(crate) search: &'tcx T,
    pub(crate) replace: &'tcx T,
    // The method in which the rule is defined.
    pub(crate) body_id: hir::BodyId,
    pub(crate) placeholder_ids: Vec<HirId>,
    // Maps from the names of declared variables (which must be unique within the search pattern) to
    // their HirId. This is used to pair up variables in the search pattern with their counterparts
    // in the replacement pattern. This is necessary since as far as rustc is concerned, they're
    // completely unrelated definitions. It isn't needed for expression placeholders since they're
    // declared as arguments to the function, so the search and replace pattern can both reference
    // the same placeholder variable.
    pub(crate) declared_name_hir_ids: HashMap<Symbol, HirId>,
}

#[derive(Debug)]
pub(crate) struct Rules<'tcx> {
    pub(crate) expr_rules: Vec<Rule<'tcx, hir::Expr<'tcx>>>,
    pub(crate) pattern_rules: Vec<Rule<'tcx, hir::Pat<'tcx>>>,
    pub(crate) type_rules: Vec<Rule<'tcx, hir::Ty<'tcx>>>,
    pub(crate) trait_ref_rules: Vec<Rule<'tcx, hir::TraitRef<'tcx>>>,
}

impl<'tcx> Rules<'tcx> {
    pub(crate) fn new() -> Rules<'tcx> {
        Rules {
            expr_rules: Vec::new(),
            pattern_rules: Vec::new(),
            type_rules: Vec::new(),
            trait_ref_rules: Vec::new(),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.expr_rules.len()
            + self.pattern_rules.len()
            + self.type_rules.len()
            + self.trait_ref_rules.len()
    }
}
