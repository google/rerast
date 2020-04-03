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
use crate::errors::ErrorWithSpan;
use crate::rule_finder::StartMatch;
use crate::rules::Rule;
use rustc_hir::intravisit;
use rustc_hir::{self, HirId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::HashSet;

struct ValidatorState<'tcx> {
    tcx: TyCtxt<'tcx>,
    errors: Vec<ErrorWithSpan>,
    // Definitions that are defined as placeholders.
    placeholders: HashSet<HirId>,
    // Placeholders that have been bound.
    bound_placeholders: HashSet<HirId>,
}

impl<'tcx> ValidatorState<'tcx> {
    fn add_error<T: Into<String>>(&mut self, message: T, span: Span) {
        self.errors.push(ErrorWithSpan::new(message, span));
    }
}

impl<'tcx, T: StartMatch<'tcx> + 'tcx> Rule<'tcx, T> {
    pub(crate) fn validate<'a>(&self, tcx: TyCtxt<'tcx>) -> Result<(), Vec<ErrorWithSpan>> {
        let rule_body = tcx.hir().body(self.body_id);

        let mut search_validator = SearchValidator {
            state: ValidatorState {
                tcx,
                errors: Vec::new(),
                placeholders: rule_body.params.iter().map(|arg| arg.pat.hir_id).collect(),
                bound_placeholders: HashSet::new(),
            },
        };
        StartMatch::walk(&mut search_validator, self.search);
        let mut replacement_validator = ReplacementValidator {
            state: search_validator.state,
        };
        StartMatch::walk(&mut replacement_validator, self.replace);
        if !replacement_validator.state.errors.is_empty() {
            return Err(replacement_validator.state.errors);
        }
        Ok(())
    }
}

struct SearchValidator<'tcx> {
    state: ValidatorState<'tcx>,
}

impl<'tcx> intravisit::Visitor<'tcx> for SearchValidator<'tcx> {
    type Map = rustc_middle::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.state.tcx.hir())
    }

    fn visit_qpath(&mut self, qpath: &'tcx rustc_hir::QPath, id: rustc_hir::HirId, span: Span) {
        if let Some(hir_id) = hir_id_from_path(qpath) {
            if self.state.placeholders.contains(&hir_id)
                && !self.state.bound_placeholders.insert(hir_id)
            {
                self.state.add_error(
                    "Placeholder is bound multiple times. This is not currently permitted.",
                    span,
                );
            }
        }
        intravisit::walk_qpath(self, qpath, id, span);
    }
}

struct ReplacementValidator<'tcx> {
    state: ValidatorState<'tcx>,
}

impl<'tcx> intravisit::Visitor<'tcx> for ReplacementValidator<'tcx> {
    type Map = rustc_middle::hir::map::Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.state.tcx.hir())
    }

    fn visit_qpath(&mut self, qpath: &'tcx rustc_hir::QPath, id: rustc_hir::HirId, span: Span) {
        if let Some(hir_id) = hir_id_from_path(qpath) {
            if self.state.placeholders.contains(&hir_id)
                && !self.state.bound_placeholders.contains(&hir_id)
            {
                self.state.add_error(
                    "Placeholder used in replacement pattern, but never bound.",
                    span,
                );
            }
        }
        intravisit::walk_qpath(self, qpath, id, span);
    }
}
