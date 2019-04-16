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
use rustc::hir::{self, intravisit, HirId};
use rustc::ty::TyCtxt;
use std::collections::HashSet;
use syntax_pos::Span;

struct ValidatorState<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    errors: Vec<ErrorWithSpan>,
    // Definitions that are defined as placeholders.
    placeholders: HashSet<HirId>,
    // Placeholders that have been bound.
    bound_placeholders: HashSet<HirId>,
}

impl<'a, 'gcx: 'a> ValidatorState<'a, 'gcx> {
    fn add_error<T: Into<String>>(&mut self, message: T, span: Span) {
        self.errors.push(ErrorWithSpan::new(message, span));
    }
}

impl<'gcx, T: StartMatch + 'gcx> Rule<'gcx, T> {
    pub(crate) fn validate<'a>(
        &self,
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
    ) -> Result<(), Vec<ErrorWithSpan>> {
        let rule_body = tcx.hir().body(self.body_id);

        let mut search_validator = SearchValidator {
            state: ValidatorState {
                tcx,
                errors: Vec::new(),
                placeholders: rule_body
                    .arguments
                    .iter()
                    .map(|arg| arg.pat.hir_id)
                    .collect(),
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

struct SearchValidator<'a, 'gcx: 'a> {
    state: ValidatorState<'a, 'gcx>,
}

impl<'a, 'gcx: 'a> intravisit::Visitor<'gcx> for SearchValidator<'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.state.tcx.hir())
    }

    fn visit_qpath(&mut self, qpath: &'gcx hir::QPath, id: hir::HirId, span: Span) {
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

struct ReplacementValidator<'a, 'gcx: 'a> {
    state: ValidatorState<'a, 'gcx>,
}

impl<'a, 'gcx: 'a> intravisit::Visitor<'gcx> for ReplacementValidator<'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.state.tcx.hir())
    }

    fn visit_qpath(&mut self, qpath: &'gcx hir::QPath, id: hir::HirId, span: Span) {
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
