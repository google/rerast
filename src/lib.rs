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

// An overview of how this code works...
//
// We run the rust compiler on a crate up to the point where it has done analysis. This gives us a
// HIR tree - rustc's intermediate representation that comes after the tokens and the AST, but
// before MIR and LLVM. We use HIR because it has type information and we want to ensure that our
// placeholders only match expressions of their specified type. We inject the code for the rules
// that are to be applied into the crate, so these are processed as well.
//
// Next we locate the previously injected rules module within the HIR tree and extract some rules
// from it. This is done by RuleFinder.
//
// The rules are then given to RuleMatcher which traverses the crate. For each
// expression/type/statement etc that could match, it walks the HIR from the rule in parallel with
// the HIR from the code. This is done by implementations of the Matchable trait. Whenever
// expression placeholders are found in the rule, we attempt to make the type sub-type the type of
// the placeholder. If this succeeds, we bind the placeholder to the expression.
//
// Once an expression has been bound to a placeholder, we traverse the expression, looking for more
// matches to any of our rules within it. This allows us to handle nested matches. The nested
// matches are stored on the placeholder as this makes substitution easier.
//
// Once a match completes, we skip trying other rules on the same node. We also skip traversing
// deeper. We've already searched any placeholders for matches and if there were any other matches
// to be found they would overlap with the current match in ways that wouldn't allow us to do
// substitution.
//
// Next we take matches and produce CodeSubstitition instances for each top-level match. These are
// instructions to replace a particular span with some new code. Note that we never print syntax
// trees. All replacement code is produced by copying around spans from either the original code or
// the rule. The replacement code for a match is produced by taking the code from the rule that
// matched and copying in the code for any placeholders. The code for the placeholders is taken from
// the original code to which the placeholder was bound and substituting in any nested matches and
// so on recursively.
//
// We special-case addition of parenthesis around expressions (placeholders or replacements) where
// the precedence is less than or equal to the precedence of the parent expression. Search for
// "needs_parenthesis" to find this code.
//
// Since the HIR syntax tree is post-macro-expansion and post-desugaring, we need to take these into
// account, firstly in order to make sure we copy the appropriate spans and secondly because if a
// user asks to replace a macro invocation with something else, we don't want to match code that
// does the same thing as the macro, but without using the macro. To achieve this, we traverse the
// expanstion info for both the rule and the code in parallel. If at any point the two are applying
// different expansions, we reject the match. This is done by RuleMatcher::get_original_span.
//
// Note, everything is in this one file because I find it easier to work with. No need to switch
// files. Just do an incremental search for whatever I'm looking for. That said, I might be open to
// changing this at some point.

#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(conservative_impl_trait)]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

extern crate getopts;
extern crate itertools;
extern crate rerast_macros;
extern crate rustc;
extern crate rustc_driver;
extern crate syntax;
extern crate syntax_pos;

use std::marker;
use syntax::ast;
use syntax::ast::NodeId;
use syntax::symbol::Symbol;
use syntax::codemap::{self, CodeMap, Spanned};
use syntax::ptr::P;
use syntax::ext::quote::rt::Span;
use syntax_pos::{FileLinesResult, SpanLinesError, SyntaxContext};
use std::vec::Vec;
use std::collections::{HashMap, HashSet};
use rustc_driver::{driver, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc::session::Session;
use rustc::hir::{self, intravisit};
use rustc::ty::{self, TyCtxt};
use std::rc::Rc;
use std::cell::RefCell;
use itertools::Itertools;
use syntax::codemap::{FileLoader, RealFileLoader};
use std::path::{Path, PathBuf};
use std::io;
use rustc::traits::{ObligationCause, Reveal};
use rustc::ty::subst::Subst;
use rustc::infer::{self, InferCtxt};
use std::fmt::{self, Debug};

macro_rules! debug {
    ($state:expr, $($args:expr),*) => {
        if $state.debug_active {
            println!($($args),*);
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Config {
    pub debug_snippet: String,
}

#[derive(Clone, Debug, Default)]
pub struct ArgBuilder {
    args: Vec<String>,
}

impl ArgBuilder {
    pub fn new() -> ArgBuilder {
        ArgBuilder { args: Vec::new() }
    }

    pub fn from_args<T: Iterator<Item = String>>(args: T) -> ArgBuilder {
        ArgBuilder {
            args: args.collect(),
        }
    }

    pub fn arg<T: Into<String>>(mut self, full_arg: T) -> Self {
        self.args.push(full_arg.into());
        self
    }

    // TODO: Try removing this at some point - perhaps once impl trait has stabalized. Right now it
    // ICEs without these lifetimes. I did find the bug for this, but don't have it handy.
    #[allow(needless_lifetimes)]
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a String> {
        self.args.iter()
    }

    pub fn build(self) -> Vec<String> {
        self.args
    }

    pub fn has_arg(&self, s: &str) -> bool {
        self.iter().any(|a| a == s)
    }
}

// We inject our rules as a submodule of the root of the crate. We do this by just appending some
// content to the end of the file. It may be possible to inject our module(s) via a similar
// mechanism to what's used by maybe_inject_crates_ref in libsyntax/std_inject.rs. For now, we go
// with the easier/simpler mechanism.
const RULES_MOD_NAME: &'static str = "__rerast_rules";
const CODE_FOOTER: &'static str = stringify!(
    #[macro_use]
    pub mod __rerast_internal;
    pub mod __rerast_rules;
);

// This module is used to help us find the definitions for rerast types that we need.
const RERAST_INTERNAL_MOD_NAME: &'static str = "__rerast_internal";
const RERAST_INTERNAL: &'static str = stringify!(
    pub fn rerast_types(
        _: Statements,
        _: _ExprRuleMarker,
        _: _PatternRuleMarker,
        _: _TypeRuleMarker,
        _: _TraitRefRuleMarker) {}
);

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

// Recursively searches the expansion of search_span and code_span in parallel. Once the next
// expansion in search_span is the replace! macro, stop and return the current code_span. If at any
// point the expansions performed by the two spans are different, then that means the search pattern
// and the code invoked different macros, so we return None.
fn get_original_span(search_span: Span, code_span: Span) -> Option<Span> {
    if let Some(search_expn) = search_span.ctxt().outer().expn_info() {
        if let Some(code_expn) = code_span.ctxt().outer().expn_info() {
            if is_same_expansion(&search_expn.callee, &code_expn.callee) {
                get_original_span(search_expn.call_site, code_expn.call_site)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(code_span)
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


fn node_id_from_path(q_path: &hir::QPath) -> Option<NodeId> {
    use hir::def::Def::*;
    if let hir::QPath::Resolved(None, ref path) = *q_path {
        match path.def {
            Local(node_id) | Upvar(node_id, _, _) => Some(node_id),
            _ => None,
        }
    } else {
        None
    }
}

struct Replacer<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rerast_definitions: RerastDefinitions<'gcx>,
    rules: Rules<'gcx>,
    config: Config,
}

impl<'a, 'gcx> Replacer<'a, 'gcx> {
    fn new(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        rerast_definitions: RerastDefinitions<'gcx>,
        rules: Rules<'gcx>,
        config: Config,
    ) -> Replacer<'a, 'gcx> {
        Replacer {
            tcx: tcx,
            rerast_definitions: rerast_definitions,
            rules: rules,
            config: config,
        }
    }

    #[allow(dead_code)]
    fn print_macro_backtrace(msg: &str, codemap: &CodeMap, span: Span) {
        println!(
            "{}: {}",
            msg,
            codemap
                .span_to_snippet(span)
                .unwrap_or_else(|_| "<Span crosses file boundaries>".to_owned())
        );
        if span.ctxt() == SyntaxContext::empty() {
            println!("SyntaxContext::empty()");
        }
        for bt in span.macro_backtrace() {
            println!(
                "Expansion of {} from: {}",
                bt.macro_decl_name,
                codemap.span_to_snippet(bt.call_site).unwrap()
            );
        }
    }

    fn apply_to_crate(&self, krate: &'gcx hir::Crate) -> HashMap<String, String> {
        let codemap = self.tcx.sess.codemap();

        let matches = RuleMatcher::find_matches(
            self.tcx,
            self.rerast_definitions,
            krate,
            &self.rules,
            self.config.clone(),
        );
        let substitutions = CodeSubstitution::sorted_substitions_for_matches(self.tcx, &matches);
        let mut updated_files = HashMap::new();
        let substitutions_grouped_by_file = substitutions
            .into_iter()
            .group_by(|subst| codemap.span_to_filename(subst.span));
        for (filename, file_substitutions) in &substitutions_grouped_by_file {
            let filemap = codemap.get_filemap(&filename).unwrap();
            let mut output = CodeSubstitution::apply(
                file_substitutions,
                codemap,
                Span::new(filemap.start_pos, filemap.end_pos, SyntaxContext::empty()),
            );
            if output.ends_with(CODE_FOOTER) {
                output = output.trim_right_matches(CODE_FOOTER).to_owned();
            }
            updated_files.insert(filename, output);
        }
        updated_files
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
enum OperatorPrecedence {
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
    fn needs_parenthesis(maybe_parent_expr: Option<&hir::Expr>, child_expr: &hir::Expr) -> bool {
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

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
struct CodeSubstitution {
    // The span to be replaced.
    span: Span,
    // New code to replace what's at span.
    new_code: String,
    // Whether parenthesis are needed around the substitution.
    needs_parenthesis: bool,
}

impl CodeSubstitution {
    fn sorted_substitions_for_matches<'r, 'a, 'gcx>(
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
    fn apply<T: Iterator<Item = CodeSubstitution>>(
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

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum PlaceholderContents<'gcx> {
    Expr(&'gcx hir::Expr),
    Statements(&'gcx [hir::Stmt]),
    Pattern(&'gcx hir::Pat),
}

impl<'gcx> PlaceholderContents<'gcx> {
    fn get_span(&self, target: Span) -> Span {
        use PlaceholderContents::*;
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

#[derive(Debug)]
struct Matches<'r, 'gcx: 'r> {
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
struct MatchPlaceholders<'r, 'gcx: 'r> {
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

struct MatchState<'r, 'a, 'gcx: 'r + 'a + 'tcx, 'tcx: 'a> {
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
}

// Trait implemented by types that we can match (as opposed to be part of a match).
trait StartMatch: Matchable {
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
    fn node_id(&self) -> NodeId;
}

impl StartMatch for hir::Expr {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        intravisit::walk_expr(visitor, node);
    }
    fn needs_parenthesis(parent: Option<&Self>, child: &Self) -> bool {
        OperatorPrecedence::needs_parenthesis(parent, child)
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::Stmt_::StmtSemi(ref addr_expr, _) = block.stmts[0].node {
                if let hir::Expr_::ExprAddrOf(_, ref expr) = addr_expr.node {
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
    fn node_id(&self) -> NodeId {
        self.id
    }
}

impl StartMatch for hir::Ty {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        intravisit::walk_ty(visitor, node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::Stmt_::StmtDecl(ref decl, _) = block.stmts[0].node {
                if let hir::Decl_::DeclLocal(ref local) = decl.node {
                    if let Some(ref ref_ty) = local.ty {
                        if let hir::Ty_::TyRptr(_, ref mut_ty) = ref_ty.node {
                            return Ok(&*mut_ty.ty);
                        }
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
    fn node_id(&self) -> NodeId {
        self.id
    }
}

impl StartMatch for hir::TraitRef {
    fn span(&self) -> Span {
        self.path.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        intravisit::walk_trait_ref(visitor, node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        let ty = <hir::Ty as StartMatch>::extract_root(block)?;
        if let hir::Ty_::TyTraitObject(ref bounds, _) = ty.node {
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
    fn node_id(&self) -> NodeId {
        self.ref_id
    }
}

impl StartMatch for hir::Pat {
    fn span(&self) -> Span {
        self.span
    }
    fn walk<'gcx, V: intravisit::Visitor<'gcx>>(visitor: &mut V, node: &'gcx Self) {
        intravisit::walk_pat(visitor, node);
    }
    fn extract_root(block: &hir::Block) -> Result<&Self, ErrorWithSpan> {
        if block.stmts.len() == 1 && block.expr.is_none() {
            if let hir::Stmt_::StmtSemi(ref expr, _) = block.stmts[0].node {
                if let hir::Expr_::ExprMatch(_, ref arms, _) = expr.node {
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
    fn node_id(&self) -> NodeId {
        self.id
    }
}

trait Matchable: Debug {
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
            (&ExprLit(ref p_lit), &ExprLit(ref c_lit)) => p_lit.node == c_lit.node,
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
                debug!(state, "Expression:   {:?}\ndidn't match: {:?}", code.node, self.node);
                false
            }
        };
        if result {
            // A literal (non-placeholder expression) matched. Verify that our rule and our code
            // were derived from the same macro expansion or desugaring if any.
            if let Some(code_span) = get_original_span(self.span(), code.span()) {
                if code_span.ctxt().outer().expn_info().is_some() {
                    // The code had additional expansion(s) not found in the rule.
                    debug!(state, "Found expr");
                    return false;
                }
            } else {
                // The rule had additional or different expansion(s) not found in the code.
                return false;
            }
        }
        result
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
            (&TyImplTrait(ref p), &TyImplTrait(ref c)) => p.attempt_match(state, c),
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

#[derive(Debug)]
struct Rule<'gcx, T: StartMatch + 'gcx> {
    search: &'gcx T,
    replace: &'gcx T,
    // The method in which the rule is defined.
    body_id: hir::BodyId,
    // Maps from the names of declared variables (which must be unique within the search pattern) to
    // their NodeId. This is used to pair up variables in the search pattern with their counterparts
    // in the replacement pattern. This is necessary since as far as rustc is concerned, they're
    // completely unrelated definitions. It isn't needed for expression placeholders since they're
    // declared as arguments to the function, so the search and replace pattern can both reference
    // the same placeholder variable.
    declared_name_node_ids: HashMap<Symbol, NodeId>,
    // IDs of the arguments to the function in which the rule was declared. When references to these
    // NodeIds are encountered in the search pattern, they should be treated as placeholders.
    placeholder_ids: HashSet<NodeId>,
}

mod validation {
    use super::{node_id_from_path, ErrorWithSpan, Rule, StartMatch};
    use std::collections::HashSet;
    use syntax::ext::quote::rt::Span;
    use syntax::ast::NodeId;
    use rustc::hir::{self, intravisit};
    use rustc::ty::TyCtxt;

    struct ValidatorState<'a, 'gcx: 'a> {
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        errors: Vec<ErrorWithSpan>,
        // Definitions that are defined as placeholders.
        placeholders: HashSet<NodeId>,
        // Placeholders that have been bound.
        bound_placeholders: HashSet<NodeId>,
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
            let rule_body = tcx.hir.body(self.body_id);

            let mut search_validator = SearchValidator {
                state: ValidatorState {
                    tcx: tcx,
                    errors: Vec::new(),
                    placeholders: rule_body.arguments.iter().map(|arg| arg.pat.id).collect(),
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
            intravisit::NestedVisitorMap::All(&self.state.tcx.hir)
        }

        fn visit_qpath(&mut self, qpath: &'gcx hir::QPath, id: NodeId, span: Span) {
            if let Some(node_id) = node_id_from_path(qpath) {
                if self.state.placeholders.contains(&node_id)
                    && !self.state.bound_placeholders.insert(node_id)
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
            intravisit::NestedVisitorMap::All(&self.state.tcx.hir)
        }

        fn visit_qpath(&mut self, qpath: &'gcx hir::QPath, id: NodeId, span: Span) {
            if let Some(node_id) = node_id_from_path(qpath) {
                if self.state.placeholders.contains(&node_id)
                    && !self.state.bound_placeholders.contains(&node_id)
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
}

struct RuleMatcher<'r, 'a, 'gcx: 'r + 'a> {
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
    fn find_matches(
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
            rule_mod_symbol: Symbol::intern(RULES_MOD_NAME),
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
            if let Some(original_span) = get_original_span(rule.search.span(), node.span()) {
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
            std::mem::swap(&mut placeholder.matches, &mut self.matches);
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
            std::mem::swap(&mut placeholder.matches, &mut self.matches);
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

#[derive(Debug, PartialEq, Eq)]
struct ErrorWithSpan {
    message: String,
    span: Span,
}

impl ErrorWithSpan {
    fn new<T: Into<String>>(message: T, span: Span) -> ErrorWithSpan {
        ErrorWithSpan {
            message: message.into(),
            span: span,
        }
    }

    fn with_snippet<'a, 'gcx>(self, tcx: TyCtxt<'a, 'gcx, 'gcx>) -> RerastError {
        RerastError {
            message: self.message,
            file_lines: Some(tcx.sess.codemap().span_to_lines(self.span)),
        }
    }
}

impl From<ErrorWithSpan> for Vec<ErrorWithSpan> {
    fn from(error: ErrorWithSpan) -> Vec<ErrorWithSpan> {
        vec![error]
    }
}

struct RerastError {
    message: String,
    file_lines: Option<FileLinesResult>,
}

impl fmt::Display for RerastError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "error: {}", self.message)?;
        match self.file_lines {
            Some(Ok(ref file_lines)) => {
                if let Some(first_line) = file_lines.lines.get(0) {
                    writeln!(
                        f,
                        "    --> {}:{}:{}",
                        file_lines.file.name,
                        first_line.line_index,
                        first_line.start_col.0
                    )?;
                }
                for line_info in &file_lines.lines {
                    if let Some(line) = file_lines.file.get_line(line_info.line_index) {
                        writeln!(f, "{}", line)?;
                        writeln!(
                            f,
                            "{}{}",
                            " ".repeat(line_info.start_col.0),
                            "^".repeat(line_info.end_col.0 - line_info.start_col.0)
                        )?;
                    } else {
                        writeln!(
                            f,
                            "Error occurred on non-existent line {}",
                            line_info.line_index
                        )?;
                    }
                }
            }
            Some(Err(ref span_lines_error)) => match *span_lines_error {
                SpanLinesError::IllFormedSpan(span) => {
                    writeln!(f, "Unable to report location. Ill-formed span: {:?}", span)?;
                }
                SpanLinesError::DistinctSources(_) => {
                    writeln!(f, "Unable to report location. Spans distinct sources")?;
                }
            },
            None => {}
        }
        Ok(())
    }
}

pub struct RerastErrors(Vec<RerastError>);

impl RerastErrors {
    fn new<T: Into<String>>(message: T) -> RerastErrors {
        RerastErrors(vec![
            RerastError {
                message: message.into(),
                file_lines: None,
            },
        ])
    }
}

impl fmt::Debug for RerastErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for RerastErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.0 {
            write!(f, "{}\n", error)?;
        }
        Ok(())
    }
}

impl From<io::Error> for RerastErrors {
    fn from(err: io::Error) -> RerastErrors {
        RerastErrors::new(err.to_string())
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct RerastOutput {
    pub updated_files: HashMap<String, String>,
}

impl RerastOutput {
    fn new() -> RerastOutput {
        RerastOutput {
            updated_files: HashMap::new(),
        }
    }
}

struct RerastCompilerCalls {
    // This needs to be an Rc because rust CompilerCalls::build_controller doesn't (at the time of
    // writing) provide any relationship between the lifetime of self and the the lifetime of the
    // returned CompileController.
    output: Rc<RefCell<Result<RerastOutput, RerastErrors>>>,
    config: Config,
}

impl<'a> CompilerCalls<'a> for RerastCompilerCalls {
    fn build_controller(
        &mut self,
        sess: &Session,
        matches: &getopts::Matches,
    ) -> driver::CompileController<'a> {
        let mut defaults = RustcDefaultCalls;
        let mut control = defaults.build_controller(sess, matches);
        let output = Rc::clone(&self.output);
        let config = self.config.clone();
        control.after_analysis.callback =
            Box::new(move |state| after_analysis(state, &output, &config));
        control.after_analysis.stop = Compilation::Stop;
        control
    }
}

fn after_analysis<'a, 'gcx>(
    state: &mut driver::CompileState<'a, 'gcx>,
    output: &Rc<RefCell<Result<RerastOutput, RerastErrors>>>,
    config: &Config,
) {
    state.session.abort_if_errors();
    *output.borrow_mut() = find_and_apply_rules(state, config.clone());
}

fn find_and_apply_rules<'a, 'gcx>(
    state: &mut driver::CompileState<'a, 'gcx>,
    config: Config,
) -> Result<RerastOutput, RerastErrors> {
    let tcx = state.tcx.unwrap();
    let krate = tcx.hir.krate();
    let rerast_definitions = RerastDefinitionsFinder::find_definitions(tcx, krate);
    let rules = RuleFinder::find_rules(tcx, rerast_definitions, krate).map_err(|errors| {
        RerastErrors(
            errors
                .into_iter()
                .map(|error| error.with_snippet(tcx))
                .collect(),
        )
    })?;
    println!("Found {} rule(s)", rules.len());
    let replacer = Replacer::new(tcx, rerast_definitions, rules, config);
    Ok(RerastOutput {
        updated_files: replacer.apply_to_crate(krate),
    })
}

#[derive(Copy, Clone)]
struct RerastDefinitions<'gcx> {
    statements: ty::Ty<'gcx>,
    expr_rule_marker: ty::Ty<'gcx>,
    pattern_rule_marker: ty::Ty<'gcx>,
    type_rule_marker: ty::Ty<'gcx>,
    trait_ref_rule_marker: ty::Ty<'gcx>,
    search_symbol: Symbol,
    replace_symbol: Symbol,
}

// Visits the code in the rerast module, finding definitions we care about for later use.
struct RerastDefinitionsFinder<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rerast_mod_symbol: Symbol,
    inside_rerast_mod: bool,
    definitions: Option<RerastDefinitions<'gcx>>,
}

impl<'a, 'gcx> RerastDefinitionsFinder<'a, 'gcx> {
    fn find_definitions(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        krate: &'gcx hir::Crate,
    ) -> RerastDefinitions<'gcx> {
        let mut finder = RerastDefinitionsFinder {
            tcx: tcx,
            rerast_mod_symbol: Symbol::intern(RERAST_INTERNAL_MOD_NAME),
            inside_rerast_mod: false,
            definitions: None,
        };
        intravisit::walk_crate(&mut finder, krate);
        finder
            .definitions
            .expect("Internal error, failed to find rerast type definitions")
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
            let mut types = body.arguments
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

#[derive(Debug)]
struct Rules<'gcx> {
    expr_rules: Vec<Rule<'gcx, hir::Expr>>,
    pattern_rules: Vec<Rule<'gcx, hir::Pat>>,
    type_rules: Vec<Rule<'gcx, hir::Ty>>,
    trait_ref_rules: Vec<Rule<'gcx, hir::TraitRef>>,
}

impl<'gcx> Rules<'gcx> {
    fn new() -> Rules<'gcx> {
        Rules {
            expr_rules: Vec::new(),
            pattern_rules: Vec::new(),
            type_rules: Vec::new(),
            trait_ref_rules: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.expr_rules.len() + self.pattern_rules.len() + self.type_rules.len()
            + self.trait_ref_rules.len()
    }
}

// Given some arms of a match statement, returns the block for arm_name if any.
fn get_arm(arms: &[hir::Arm], arm_name: Symbol) -> Option<&hir::Block> {
    for arm in arms {
        if let hir::PatKind::Path(hir::QPath::Resolved(None, ref path)) = arm.pats[0].node {
            if let Some(segment) = path.segments.last() {
                if segment.name == arm_name {
                    if let hir::Expr_::ExprBlock(ref block) = arm.body.node {
                        return Some(block);
                    }
                }
            }
        }
    }
    None
}

// Finds rules.
struct RuleFinder<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    rerast_definitions: RerastDefinitions<'gcx>,
    rules_mod_symbol: Symbol,
    rules: Rules<'gcx>,
    body_id: Option<hir::BodyId>,
    in_rules_module: bool,
    errors: Vec<ErrorWithSpan>,
}

impl<'a, 'gcx> RuleFinder<'a, 'gcx> {
    fn find_rules(
        tcx: TyCtxt<'a, 'gcx, 'gcx>,
        rerast_definitions: RerastDefinitions<'gcx>,
        krate: &'gcx hir::Crate,
    ) -> Result<Rules<'gcx>, Vec<ErrorWithSpan>> {
        let mut rule_finder = RuleFinder {
            tcx: tcx,
            rerast_definitions: rerast_definitions,
            rules_mod_symbol: Symbol::intern(RULES_MOD_NAME),
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
            Err(vec![
                ErrorWithSpan::new("Unexpected code found in rule function", arg_ty_span),
            ])
        }
    }

    fn maybe_add_typed_rule<T: 'gcx + StartMatch>(
        &mut self,
        arg_ty: ty::Ty<'gcx>,
        arms: &'gcx [hir::Arm],
        body_id: hir::BodyId,
    ) -> Result<bool, Vec<ErrorWithSpan>> {
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
            let placeholder_ids = self.tcx
                .hir
                .body(body_id)
                .arguments
                .iter()
                .map(|arg| arg.pat.id)
                .collect();

            let rule = Rule {
                search: search,
                replace: replace,
                body_id: body_id,
                declared_name_node_ids: DeclaredNamesFinder::find(self.tcx, search),
                placeholder_ids: placeholder_ids,
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
        intravisit::NestedVisitorMap::All(&self.tcx.hir)
    }

    fn visit_item(&mut self, item: &'gcx hir::Item) {
        use hir::Item_::*;
        if let ItemMod(_) = item.node {
            if item.name == self.rules_mod_symbol {
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
        use hir::Expr_::*;
        if let ExprMatch(ref match_expr, ref arms, _) = expr.node {
            if let ExprMethodCall(ref _name, ref _tys, ref args) = match_expr.node {
                if let Some(body_id) = self.body_id {
                    let type_tables = self.tcx
                        .typeck_tables_of(self.tcx.hir.body_owner_def_id(body_id));
                    let arg0 = &args[0];
                    let arg_ty = type_tables.node_id_to_type(self.tcx.hir.node_to_hir_id(arg0.id));
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

// Searches for variables declared within the search code. For example in the pattern Some(a), "a"
// will be found.
struct DeclaredNamesFinder<'a, 'gcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'gcx>,
    names: HashMap<Symbol, NodeId>,
}

impl<'a, 'gcx> DeclaredNamesFinder<'a, 'gcx> {
    fn find<T: StartMatch>(tcx: TyCtxt<'a, 'gcx, 'gcx>, node: &'gcx T) -> HashMap<Symbol, NodeId> {
        let mut finder = DeclaredNamesFinder {
            tcx: tcx,
            names: HashMap::new(),
        };
        T::walk(&mut finder, node);
        finder.names
    }
}

impl<'a, 'gcx, 'tcx> intravisit::Visitor<'gcx> for DeclaredNamesFinder<'a, 'gcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'gcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir)
    }

    fn visit_pat(&mut self, pat: &'gcx hir::Pat) {
        if let hir::PatKind::Binding(_, node_id, ref name, _) = pat.node {
            if self.names.insert(name.node, node_id).is_some() {
                // TODO: Proper error reporting
                panic!(
                    "Variables declared in the search pattern must all use distinct \
                     names, even in different scopes. The variable {:?} was declared more \
                     than once.",
                    name
                );
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

// TODO: Consider renaming to OverlayFileLoader
struct InMemoryFileLoader<T: FileLoader> {
    files: HashMap<PathBuf, String>,
    inner_file_loader: T,
}

impl<T: FileLoader> InMemoryFileLoader<T> {
    fn new(inner: T) -> InMemoryFileLoader<T> {
        InMemoryFileLoader {
            files: HashMap::new(),
            inner_file_loader: inner,
        }
    }

    fn add_file<P: Into<PathBuf>>(&mut self, file_name: P, contents: String) {
        self.files.insert(file_name.into(), contents);
    }
}

impl<T: FileLoader> FileLoader for InMemoryFileLoader<T> {
    fn file_exists(&self, path: &Path) -> bool {
        self.files.contains_key(path) || self.inner_file_loader.file_exists(path)
    }

    fn abs_path(&self, _: &Path) -> Option<PathBuf> {
        None
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if let Some(contents) = self.files.get(path) {
            return Ok(contents.to_string());
        }
        self.inner_file_loader.read_file(path)
    }
}

// Currently we require use of rustup
fn rustup_sysroot() -> String {
    env!("RUSTUP_HOME").to_owned() + "/toolchains/" + env!("RUSTUP_TOOLCHAIN")
}

fn run_compiler(
    file_loader: Option<Box<FileLoader + 'static>>,
    args: &[String],
    config: Config,
) -> Result<RerastOutput, RerastErrors> {
    let mut compiler_calls = RerastCompilerCalls {
        output: Rc::new(RefCell::new(Ok(RerastOutput::new()))),
        config: config,
    };
    let (_, _) = rustc_driver::run_compiler(args, &mut compiler_calls, file_loader, None);
    Rc::try_unwrap(compiler_calls.output)
        .map_err(|_| {
            RerastErrors::new(
                "Internal error: rustc_driver unexpectedly kept a reference to our data",
            )
        })?
        .into_inner()
}

pub struct RerastCompilerDriver {
    args: ArgBuilder,
}

impl RerastCompilerDriver {
    pub fn new(args: ArgBuilder) -> RerastCompilerDriver {
        RerastCompilerDriver { args: args }
    }

    pub fn args(&self) -> &ArgBuilder {
        &self.args
    }

    pub fn is_compiling_dependency(&self) -> bool {
        if let Some(path) = self.code_filename() {
            // For now we determine if we're compiling a dependent crate by whether the path is
            // absolute or not. This is unfortunate. It'd be better if we could just ask Cargo to
            // compile all dependent crates, then ask it for the rustc commandline to compile our
            // crate, then we wouldn't have to do this.
            Path::new(path).is_absolute()
        } else {
            false
        }
    }

    fn code_filename(&self) -> Option<&str> {
        self.args
            .iter()
            .skip(1)
            .find(|arg| arg.ends_with(".rs"))
            .map(|s| s.as_ref())
    }

    // Apply rules from `rules`, or if that is empty, read `rules_file`.
    pub fn apply_rules_from_string_or_file(
        &self,
        rules: String,
        rules_file: &str,
        config: Config,
    ) -> Result<RerastOutput, RerastErrors> {
        let file_loader = RealFileLoader;
        let rules = if rules.is_empty() {
            file_loader
                .read_file(&PathBuf::from(rules_file))
                .map_err(|e| {
                    RerastErrors::new(format!("Error opening {}: {}", rules_file, e))
                })?
        } else {
            rules
        };
        self.apply_rules_to_code(file_loader, rules, config)
    }

    fn apply_rules_to_code<T: FileLoader + 'static>(
        &self,
        file_loader: T,
        rules: String,
        config: Config,
    ) -> Result<RerastOutput, RerastErrors> {
        let args_vec = self.args
            .clone()
            .arg("--sysroot")
            .arg(rustup_sysroot())
            .arg("--allow")
            .arg("dead_code")
            .build();
        let mut file_loader = box InMemoryFileLoader::new(file_loader);
        // In an ideal world we might get rust to parse the arguments then ask it what the root code
        // filename is. In the absence of being able to do that, this will have to do.
        let code_filename = self.code_filename().ok_or_else(|| {
            RerastErrors::new(
                "Couldn't find source filename with .rs extension in the supplied arguments",
            )
        })?;
        let code_path = PathBuf::from(code_filename);
        file_loader.add_file(
            code_path.with_file_name(RULES_MOD_NAME.to_owned() + ".rs"),
            rules,
        );
        file_loader.add_file(
            code_path.with_file_name(RERAST_INTERNAL_MOD_NAME.to_owned() + ".rs"),
            rerast_macros::_RERAST_MACROS_SRC
                .replace(r#"include_str!("lib.rs")"#, r#""""#)
                .replace("$crate", &("::".to_owned() + RERAST_INTERNAL_MOD_NAME))
                + RERAST_INTERNAL,
        );
        let code_with_footer = file_loader.read_file(&code_path)? + CODE_FOOTER;

        file_loader.add_file(code_path, code_with_footer);
        run_compiler(Some(file_loader), &args_vec, config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map;

    const CODE_FILE_NAME: &'static str = "code.rs";

    struct NullFileLoader;

    impl FileLoader for NullFileLoader {
        fn file_exists(&self, _: &Path) -> bool {
            false
        }

        fn abs_path(&self, _: &Path) -> Option<PathBuf> {
            None
        }

        fn read_file(&self, path: &Path) -> io::Result<String> {
            match path.to_str() {
                Some(path_str) => Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    path_str.to_string() + " not found",
                )),
                None => Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "Path is not valid UTF8",
                )),
            }
        }
    }

    fn maybe_apply_rule_to_test_code(
        common: &str,
        rule: &str,
        code: &str,
    ) -> Result<RerastOutput, RerastErrors> {
        let mut file_loader = InMemoryFileLoader::new(NullFileLoader);
        file_loader.add_file("common.rs".to_owned(), common.to_owned());
        let header1 = r#"#![allow(unused_imports)]
                         #![allow(unused_variables)]
                         "#;
        let header2 = "use common::*;\n";
        let code_header = r#"
               #![feature(box_syntax)]
               #![feature(box_patterns)]
               #![feature(slice_patterns)]
               #![feature(exclusive_range_pattern)]
               #![feature(conservative_impl_trait)]
               "#.to_owned() + header1 + "#[macro_use]\nmod common;\n"
            + header2;
        let rule_header = header1.to_owned() + "use common;\n" + header2;
        file_loader.add_file(CODE_FILE_NAME.to_owned(), code_header.clone() + code);
        let args = ArgBuilder::new()
            .arg("rerast_test")
            .arg("--crate-type")
            .arg("lib")
            .arg(CODE_FILE_NAME);
        let driver = RerastCompilerDriver::new(args);
        let mut output =
            driver.apply_rules_to_code(file_loader, rule_header + rule, Config::default())?;
        if let hash_map::Entry::Occupied(mut entry) =
            output.updated_files.entry(CODE_FILE_NAME.to_owned())
        {
            let contents = entry.get_mut();
            assert!(contents.starts_with(&code_header));
            *contents = contents[code_header.len()..].to_owned();
        }
        Ok(output)
    }

    fn apply_rule_to_test_code(common: &str, rule: &str, code: &str) -> RerastOutput {
        match maybe_apply_rule_to_test_code(common, rule, code) {
            Ok(output) => output,
            Err(errors) => {
                panic!("Got unexpected errors.\n{}\n", errors);
            }
        }
    }

    fn check(common: &str, rule: &str, input: &str, expected: &str) {
        let updated_files = apply_rule_to_test_code(common, &rule.to_string(), input).updated_files;
        let is_other_filename = |filename| filename != CODE_FILE_NAME && filename != "common.rs";
        if updated_files.keys().any(is_other_filename) {
            panic!(
                "Unexpected updates to other files: {:?}",
                updated_files.keys()
            );
        }
        let new_code = updated_files
            .get(CODE_FILE_NAME)
            .expect("File not updated. No match?");
        if new_code != expected {
            println!("result: {}", new_code);
            println!("expect: {}", expected);
        }
        assert_eq!(new_code, expected);
    }

    fn check_no_match(common: &str, rule: &str, input: &str) {
        let updated_files = apply_rule_to_test_code(common, rule, input).updated_files;
        if !updated_files.is_empty() {
            println!("Unexpected: {:?}", updated_files);
        }
        assert!(updated_files.is_empty());
    }

    fn check_error(rule: &str, expected_message: &str, expected_snippet: &str) {
        match maybe_apply_rule_to_test_code("", rule, "") {
            Ok(result) => panic!("Expected error, got:\n{:?}", result),
            Err(errors) => {
                if errors.0.len() > 1 {
                    panic!(
                        "Unexpectedly got multiple errors ({}).\n{}",
                        errors.0.len(),
                        errors
                    );
                }
                assert_eq!(expected_message, errors.0[0].message);
                match errors.0[0].file_lines {
                    Some(Ok(ref file_lines)) => {
                        assert_eq!(1, file_lines.lines.len());
                        let line_info = &file_lines.lines[0];
                        if let Some(line) = file_lines.file.get_line(line_info.line_index) {
                            let snippet: String = line.chars()
                                .skip(line_info.start_col.0)
                                .take(line_info.end_col.0 - line_info.start_col.0)
                                .collect();
                            assert_eq!(expected_snippet, snippet);
                        } else {
                            panic!(
                                "Error reported on non-existent line {}",
                                line_info.line_index
                            );
                        }
                    }
                    Some(Err(ref error)) => {
                        panic!("Expected error with file lines, but error: {:?}", error)
                    }
                    None => panic!("Expected error with lines, but got error without lines"),
                }
            }
        }
    }

    // Check that we can match and replace a binary operand with placeholders on both sides.
    #[test]
    fn addition_swap_order() {
        check(
            "",
            "fn r(x: i64, y: i64) {replace!(x + y => y + x);}",
            "fn bar() -> i64 {return (41 + 2) - (9 + 1);}",
            "fn bar() -> i64 {return (2 + 41) - (1 + 9);}",
        );
    }

    // Check that we can match an expression that's more than just a literal against a placeholder
    // in the pattern.
    #[test]
    fn swap_complex_expr() {
        check(
            "",
            "fn r(x: i64, y: i64) {replace!(x - y => y / x);}",
            "fn bar() -> i64 {return (41 + 2) - (9 + 1);}",
            "fn bar() -> i64 {return (9 + 1) / (41 + 2);}",
        );
    }

    #[test]
    fn no_whitespace() {
        check(
            "",
            "fn r(x: i64, y: i64) {replace!(x-y => y/x);}",
            "fn bar() -> i64 {return (41+2)-(9+1);}",
            "fn bar() -> i64 {return (9+1)/(41+2);}",
        );
    }

    // Check that we can match a literal value with the same literal value in the pattern.
    #[test]
    fn integer_literal() {
        check(
            "",
            "fn r(x: i64, y: i64) {replace!(x - y + 1 => x + 1 - y);}",
            "fn bar() -> i64 {return 10 - 5 + 1;}",
            "fn bar() -> i64 {return 10 + 1 - 5;}",
        );
    }

    // Ensure that we can replace an expression in a function that isn't the first function in the
    // file.
    #[test]
    fn match_in_second_fn() {
        check(
            "",
            "fn bar(x: bool, y: bool) {replace!(x && y => x || y);}",
            "fn f1() -> bool {return true;} fn f2() -> bool {return true && false;}",
            "fn f1() -> bool {return true;} fn f2() -> bool {return true || false;}",
        );
    }

    // Check that we can match a loop.
    #[test]
    fn match_loop() {
        check(
            "",
            r#"#[allow(while_true)]
                 fn bar() {replace!(loop {break;} => while true {break;});}"#,
            "#[allow(while_true)]\n fn f1() {loop {break;}}",
            "#[allow(while_true)]\n fn f1() {while true {break;}}",
        );
    }

    // Check that we can match a continue statement.
    #[test]
    fn match_continue() {
        check(
            "",
            "fn r1() {replace!(loop {continue;} => loop {break;});}",
            "fn f1() {loop {continue;}}",
            "fn f1() {loop {break;}}",
        );
    }

    // Check that we can match a repeated array initialization.
    #[test]
    fn match_repeat() {
        check(
            "pub fn foo(_: &[i32]) {}",
            "fn r1(x: i32) {replace!([x; 3] => [x; 5]);}",
            "fn f1() {foo(&[0; 3]);}",
            "fn f1() {foo(&[0; 5]);}",
        );
    }

    // A more complex example where we replace various different kinds of field access with
    // different method calls.
    #[test]
    fn abstract_field() {
        check(
            stringify!(
            pub struct Point {
                pub x: i32,
                pub y: i32,
            }

            impl Point {
                pub fn new(x: i32, y: i32) -> Point {
                    Point {
                        x: x,
                        y: y,
                    }
                }

                pub fn get_x(&self) -> i32 {
                    self.x
                }

                pub fn get_mut_x(&mut self) -> &mut i32 {
                    &mut self.x
                }

                pub fn set_x(&mut self, x: i32) {
                    self.x = x;
                }
            }

            pub fn process_i32(v: i32) {}),
            r#"fn r(mut p: Point, x: i32, y: i32) {
                     replace!(Point{ x: x, y: y } => Point::new(x, y));
                     replace!(p.x = x => p.set_x(x));
                     replace!(&mut p.x => p.get_mut_x());
                     replace!(p.x => p.get_x());
                 }"#,
            r#"fn f1(point: Point, point_ref: &Point, mut_point_ref: &mut Point) {
                     let p2 = Point { x: 1, y: 2 };
                     process_i32(point.x);
                     mut_point_ref.x = 1;
                     let x = &mut mut_point_ref.x;
                     *x = 42;
                     process_i32(point_ref.x);
                 }"#,
            r#"fn f1(point: Point, point_ref: &Point, mut_point_ref: &mut Point) {
                     let p2 = Point::new(1, 2);
                     process_i32(point.get_x());
                     mut_point_ref.set_x(1);
                     let x = mut_point_ref.get_mut_x();
                     *x = 42;
                     process_i32(point_ref.get_x());
                 }"#,
        );
    }

    // Check that we can match a while loop and multiple statements within its block.
    #[test]
    // Disabled because the import of rerast::Statements doesn't work any more. Consider using a
    // macro instead of using a type. e.g. statements!(s1);
    #[ignore]
    fn match_while() {
        check(
            "",
            r#"use rerast;
                 fn r1(b: bool, s: rerast::Statements) {
                     replace!(while b {s();} => loop {
                         if !b {break}
                         s();
                     });}"#,
            r#"fn f1() -> i32 {
                     let mut v = 0;
                     while v < 10 {
                         v += 1;
                         v += 2;
                     }
                     v
                 }"#,
            r#"fn f1() -> i32 {
                     let mut v = 0;
                     loop {
                         if !(v < 10) {break}
                         v += 1;
                         v += 2;
                     }
                     v
                 }"#,
        );
    }

    #[test]
    #[ignore]
    fn error_multiple_statement_placeholders() {
        check_error(
            r#"use rerast;
                 fn r1(s1: rerast::Statements, s2: rerast::Statements) {
                     replace!(
                         loop {
                             s1();
                             if false {break;}
                             s2();
                          } => loop {
                             s1();
                             s2();
                     });}"#,
            "Multiple statement placeholders within a block is not supported",
            "",
        );
    }

    // Replace a call to a function.
    #[test]
    fn replace_function_call() {
        check(
            "pub fn f1(_: i32, _: i32) {} pub fn f2(_: i32, _: i32) {}",
            r#"pub fn pat1(x: i32, y: i32) {
                     replace!(f1(x, y) => f2(y, x));}"#,
            "pub fn bar() {f1(1, 2);}",
            "pub fn bar() {f2(2, 1);}",
        );
    }

    // Check that we can match an array.
    #[test]
    fn match_array() {
        check(
            "pub fn sum(_: &[i32]) -> i32 {42}",
            "fn bar(x: i32, y: i32) {replace!(sum(&[x, y]) => x + y);}",
            "fn f1() -> i32 {sum(&[1, 2])}",
            "fn f1() -> i32 {1 + 2}",
        );
    }

    // Check that we can match a tuple.
    #[test]
    fn match_tuple() {
        check(
            "pub fn sum(_: (i32, i32)) -> i32 {42} pub fn f2(_: i32) {}",
            "fn bar(x: i32, y: i32) {replace!(sum((x, y)) => x + y);}",
            "fn f1() {f2(sum((1, 2)));}",
            "fn f1() {f2(1 + 2);}",
        );
    }

    // Check that we can match an if-else. Also checks unary expression and parenthesis.
    // TODO: Can we remove the redundant parens on the output?
    #[test]
    fn match_if_else() {
        check(
            "",
            r#"fn bar(x: i32, y: i32, b: bool) {
                     replace!(if !b {x} else {y} => if b {y} else {x});}"#,
            "fn f1(a: i32, b: i32) -> i32 {if !(a < b) {a + 1} else {a - 1}}",
            "fn f1(a: i32, b: i32) -> i32 {if (a < b) {a - 1} else {a + 1}}",
        );
    }

    // Mostly a sanity-check for the subsequent test where the type doesn't match.
    #[test]
    fn primitive_type_match() {
        check(
            "",
            "fn bar(x: i32) {replace!(x == 0 => 0 == x);}",
            "fn f1(a: i32) -> i32 {if a == 0 {a + 1} else {a - 1}}",
            "fn f1(a: i32) -> i32 {if 0 == a {a + 1} else {a - 1}}",
        );
    }

    // Check that we don't match an i32 value against an i64 placeholder.
    #[test]
    fn primitive_type_no_match() {
        check_no_match(
            "",
            "fn bar(x: i64) {replace!(x == 0 => 0 == x);}",
            "fn f1(a: i32) -> i32 {if a == 0 {a + 1} else {a - 1}}",
        );
    }

    // Make sure a regular method call matches a regular method call.
    #[test]
    fn match_method_call() {
        check(
            "",
            "fn bar(x: i16) {replace!(x.count_ones() => x.count_zeros());}",
            "fn f1() -> u32 {let a = 42i16; a.count_ones()}",
            "fn f1() -> u32 {let a = 42i16; a.count_zeros()}",
        )
    }

    // Make sure a UFCS method call matches a UFCS method call.
    #[test]
    fn ufcs_search_ufcs_code() {
        check(
            "",
            "fn bar(x: i16) {replace!(i16::count_ones(x) => i16::count_zeros(x));}",
            "fn f1() -> u32 {let a = 42i16; i16::count_ones(a)}",
            "fn f1() -> u32 {let a = 42i16; i16::count_zeros(a)}",
        )
    }

    // Make sure a UFCS search pattern matches non-UFCS code.
    #[test]
    fn ufcs_search_non_ufcs_code() {
        check(
            "",
            "fn bar(x: i16) {replace!(i16::count_ones(x) => x.count_zeros());}",
            "fn f1() -> u32 {let a = 42i16; a.count_ones()}",
            "fn f1() -> u32 {let a = 42i16; a.count_zeros()}",
        )
    }

    // Make sure a non-UFCS search pattern matches UFCS code.
    #[test]
    fn non_ufcs_search_ufcs_code() {
        check(
            "",
            "fn bar(x: i16) {replace!(x.count_ones() => x.count_zeros());}",
            "fn f1() -> u32 {let a = 42i16; i16::count_ones(a)}",
            "fn f1() -> u32 {let a = 42i16; a.count_zeros()}",
        )
    }

    #[test]
    fn match_cast() {
        check(
            "",
            r#"fn bar(x: i16) {
                     replace!(x as i32 => x as i64);
                 }"#,
            r#"fn f1(a: i16) {println!("{}", a as i32);}"#,
            r#"fn f1(a: i16) {println!("{}", a as i64);}"#,
        );
    }

    #[test]
    fn no_match_cast_different_type() {
        check_no_match(
            "",
            r#"fn bar(x: i16) {
                     replace!(x as i32 => x as i64);
                 }"#,
            r#"fn f1(a: i16) {println!("{}", a as u32);}"#,
        );
    }

    #[test]
    fn match_return() {
        check(
            "",
            r#"fn bar(x: i16) -> i32 {
                     replace!(return x as i32 => return x.into());
                     unreachable!();
                 }"#,
            "fn f1(a: i16) -> i32 {return a as i32}",
            "fn f1(a: i16) -> i32 {return a.into()}",
        );
    }

    // TODO: Do we want to enforce this? If so, I think we need to check that the rule return type
    // unifies with the function return type. Doing it at the return expression doesn't work so
    // well.
    #[test]
    #[ignore]
    fn no_match_return_wrong_type() {
        check_no_match(
            "",
            r#"fn bar(x: i16) -> i32 {
                              replace!(return x.into() => return (x + 1).into());}"#,
            "fn f1(a: i16) -> i64 {return a.into();}",
        );
    }

    // Verify that we can use a type parameter with a bound (and use it multiple times).
    #[test]
    fn match_trait_bound() {
        check(
            "",
            r#"fn bar<T: Ord>(x: T, y: T, r1: T, r2: T) {
                   replace!(if x < y {r1} else {r2}
                       => if y > x {r2} else {r1});}"#,
            "fn f1(a: i32, b: i32, c1: i32, c2: i32) {if a < b {c1} else {c2};}",
            "fn f1(a: i32, b: i32, c1: i32, c2: i32) {if b > a {c2} else {c1};}",
        );
    }

    // Match destructuring of a struct.
    #[test]
    fn match_destructure_struct() {
        check(
            r#"pub struct Size { pub w: i32, pub h: i32 }
               impl Size { pub fn area(&self) -> i32 { self.w * self.h }}
               pub fn do_stuff(_: i32) {}"#,
            r#"use common::*;
                 fn bar(op: Option<Size>, d: i32) {
                   replace!(if let Some(Size {w, h}) = op {w * h} else {d}
                       => op.map(|p| p.area()).unwrap_or_else(|| d));}"#,
            r#"use common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(if let Some(Size {w: w1, h: h1}) = sz {w1 * h1} else {42});
                 }"#,
            r#"use common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(sz.map(|p| p.area()).unwrap_or_else(|| 42));
                 }"#,
        );
    }

    // Match destructuring of a struct where the order is changed.
    #[test]
    fn match_destructure_struct_out_of_order() {
        check(
            r#"pub struct Size { pub w: i32, pub h: i32 }
               impl Size { pub fn area(&self) -> i32 { self.w * self.h }}
               pub fn do_stuff(_: i32) {}"#,
            r#"use common::*;
                 fn bar(op: Option<Size>, d: i32) {
                   replace!(if let Some(Size {w, h}) = op {w * h} else {d}
                       => op.map(|p| p.area()).unwrap_or_else(|| d));}"#,
            r#"use common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(if let Some(Size {h: h1, w: w1}) = sz {w1 * h1} else {42});
                 }"#,
            r#"use common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(sz.map(|p| p.area()).unwrap_or_else(|| 42));
                 }"#,
        );
    }

    // Check that we both match and substitute placeholders inside lambdas.
    #[test]
    fn placeholder_in_lambda() {
        check(
            "",
            r#"fn rule(a: Option<i32>, d: i32) {
                     replace!(a.unwrap_or_else(|| d) => a.unwrap_or_else(|| d + 1));}"#,
            r#"fn foo() {None.unwrap_or_else(|| 41i32);}"#,
            r#"fn foo() {None.unwrap_or_else(|| 41i32 + 1);}"#,
        );
    }

    // Check that we substitute matched argument names in lambda expressions in place of those in
    // the replace pattern.
    #[test]
    fn lambda_arg_name_substitution() {
        check(
            "",
            r#"fn rule(a: Option<i32>) {
                     replace!(a.map(|v| v + 1) => a.map(|v| v + 2));}"#,
            r#"fn foo() {Some(41i32).map(|aaa| aaa + 1);}"#,
            r#"fn foo() {Some(41i32).map(|aaa| aaa + 2);}"#,
        );
    }

    // Check that if we match an expression that is an argument to a macro, we don't do the wrong
    // thing. (e.g. replace the whole macro invocation).
    #[test]
    fn match_macro_argument() {
        check(
            "",
            r#"fn rule(a: bool, b: bool) {replace!(a || b => b || a);}"#,
            r#"fn foo(x: i32, y: i32) {println!("{}", x == 1 || y == 2);}"#,
            r#"fn foo(x: i32, y: i32) {println!("{}", y == 2 || x == 1);}"#,
        );
    }

    #[test]
    fn fully_qualified() {
        check(
            "pub fn bar() {} pub fn foo() {}",
            "fn rule() {replace!(bar() => foo());}",
            "fn f1() {common::bar();}",
            "fn f1() {foo();}",
        );
        check(
            "pub fn bar() {} pub fn foo() {}",
            "fn rule() {replace!(common::bar() => common::foo());}",
            "fn f1() {bar();}",
            "fn f1() {common::foo();}",
        );
    }

    // Check that we don't match when the same type parameter is bound to multiple different types.
    #[test]
    fn conflicting_type_bounds() {
        check_no_match(
            "",
            r#"fn bar<T: Ord>(x: T, y: T, r1: T, r2: T) {
                   replace!(if x < y {r1} else {r2}
                       => if y > x {r2} else {r1});}"#,
            "fn f1(a: i32, b: i32, c1: i64, c2: i64) {if a < b {c1} else {c2};}",
        );
    }

    // Check that we insert parenthesis if required due to equal operator precedence.
    #[test]
    fn insert_parenthesis_equal_precedence() {
        check(
            "",
            "fn bar() {replace!(42 => 40 + 2);}",
            "fn f1() -> i32 {100 - 42}",
            "fn f1() -> i32 {100 - (40 + 2)}",
        );
    }

    // Check that we insert parenthesis if required due to lower operator precedence.
    #[test]
    fn insert_parenthesis_lower_precedence() {
        check(
            "",
            "fn bar() {replace!(42 => 40 + 2);}",
            "fn f1() -> i32 {100 / 42}",
            "fn f1() -> i32 {100 / (40 + 2)}",
        );
    }

    // Check that we don't insert parenthesis not required due to operator precedence.
    #[test]
    fn no_insert_parenthesis() {
        check(
            "",
            "fn bar() {replace!(20 => 40 / 2);}",
            "fn f1() -> i32 {100 - 20}",
            "fn f1() -> i32 {100 - 40 / 2}",
        );
    }

    // Check that we can match a macro invocation.  Note: If this test ever starts failing with an
    // extra ; - search this crate for ends_with(";") - there's a workaround for macros consuming
    // semicolons that follow them and the workaround may no longer be necessary.
    #[test]
    fn match_macro() {
        check(
            "pub fn foo() -> Result<i32, i32> {Ok(42)}",
            "use std::fmt::Debug; \
                 fn bar<T, E: Debug>(r: Result<T, E>) -> Result<T, E> {\
                     replace!(try!(r) => r.unwrap());
                     unreachable!();
                 }",
            "fn f1() -> Result<i32, i32> {try!(foo()); Ok(1)}",
            "fn f1() -> Result<i32, i32> {foo().unwrap(); Ok(1)}",
        )
    }

    // Check that when a placeholder matches an expression that is the result of a macro expansion,
    // we correctly take the call-site of that macro.
    #[test]
    fn placeholder_takes_macro_invocation() {
        check(
            r#"pub fn get_result() -> Result<i32, i32> {Ok(42)}
                 pub fn foo(_: i32) {}
                 pub fn bar(_: i32) {}"#,
            "fn rule(a: i32) {replace!(foo(a) => bar(a));}",
            "fn f1() -> Result<i32, i32> {foo(try!(get_result())); Ok(1)}",
            "fn f1() -> Result<i32, i32> {bar(try!(get_result())); Ok(1)}",
        );
    }

    // Check that we can match a macro invocation that contains a placeholder that is also a macro
    // invocation.
    #[test]
    fn macro_placeholder_within_matched_macro() {
        check(
            r#"#[macro_export]
                 macro_rules! add {($e1:expr, $e2:expr) => {$e1 + $e2}}
                 pub fn foo() -> Result<i32, i32> {Ok(41)}"#,
            r#"use std::ops::Add;
                 fn rule<T: Add>(a: T, b: T) {
                     replace!(add!(a, b) => a + b);
                 }"#,
            "fn f1() -> Result<i32, i32> {Ok(add!(1, try!(foo())))}",
            "fn f1() -> Result<i32, i32> {Ok(1 + try!(foo()))}",
        );
    }

    // Check that comments before and after a placeholder are preserved
    #[test]
    #[ignore] // TODO
    fn comments_next_to_placeholder() {
        check(
            "",
            "fn rule(a: i32, b: i32) {replace!(a + b => b + a);}",
            r#"fn foo() {
                     println!("{}", /* <a */ 1i32 /* a> */ + /* <b */ 2 /* b> */);
                 }"#,
            r#"fn foo() {
                     println!("{}", /* <b */ 2 /* b> */ + /* <a */ 1i32 /* a> */);
                 }"#,
        );
    }

    // Check that we can match indexing.
    #[test]
    fn match_index() {
        check(
            "",
            "fn bar(x: &[i32], y: usize) {replace!(x[y] => *x.get(y + 1).unwrap());}",
            "fn f1(a: &[i32]) -> i32 {a[42]}",
            "fn f1(a: &[i32]) -> i32 {*a.get(42 + 1).unwrap()}",
        );
    }

    // Check that we can match a range
    #[test]
    fn match_range() {
        check(
            "",
            "use std::ops::Range; pub fn bar(x: i32, y: i32) {\
             replace!(x..y => Range{ start: x, end: y });}",
            "use std::ops::Range; pub fn f1() -> Range<i32> {2..42}",
            "use std::ops::Range; pub fn f1() -> Range<i32> {Range{ start: 2, end: 42 }}",
        );
    }

    #[test]
    fn nested_expression_match() {
        check(
            "pub fn foo(a: i32) -> i32 {a}",
            "fn rule(x: i32) {replace!(foo(x) => foo(x + 1));}",
            "fn f1() -> i32 {foo(foo(foo(0)))}",
            "fn f1() -> i32 {foo(foo(foo(0 + 1) + 1) + 1)}",
        );
    }

    // Checks that we can match something that auto-dereferences to the placeholder type (&mut Point
    // where the rule just has Point). Also checks use of multiple replace! calls in the one
    // function and field references.
    #[test]
    fn auto_dereference() {
        check(
            "pub struct Point { pub x: i32, pub y: i32 }",
            r#"pub fn rule(p: Point) {
                 replace!(p.x => p.y);
                 replace!(p.y => p.x);
               }"#,
            r#"pub fn f1(point: &mut Point) {
                     point.x = point.x + 1;
                     point.y = point.y - 1;
                 }"#,
            r#"pub fn f1(point: &mut Point) {
                     point.y = point.y + 1;
                     point.x = point.x - 1;
                 }"#,
        )
    }

    #[test]
    fn match_box() {
        check(
            "",
            "fn rule(x: i32) {replace!(box x => Box::new(x));}",
            "fn f1() -> Box<i32> {box 42}",
            "fn f1() -> Box<i32> {Box::new(42)}",
        );
    }

    #[test]
    fn match_box_pattern() {
        check(
            r#"pub fn get_boxed_op() -> Box<Option<i32>> {box Some(42)}
                 pub fn get_op_box() -> Option<Box<i32>> {Some(box 42)}"#,
            r#"fn r<T>(p1: Box<Option<T>>, p2: Option<Box<T>>) {
                   replace!(get_boxed_op() => get_op_box());
                   replace_pattern!(box Some(a) = p1 => Some(box a) = p2);
                 }"#,
            "fn f1() -> i32 {if let box Some(v) = get_boxed_op() {v} else {0}}",
            "fn f1() -> i32 {if let Some(box v) = get_op_box() {v} else {0}}",
        );
    }

    #[test]
    fn match_addr_of() {
        check(
            r#"pub fn foo(_: &(i32, bool)) {}
                 pub fn bar(_: (i32, bool)) {}"#,
            "fn rule(x: (i32, bool)) {replace!(foo(&x) => bar(x));}",
            "fn f1(v: (i32, bool)) {foo(&v)}",
            "fn f1(v: (i32, bool)) {bar(v)}",
        );
    }

    #[test]
    fn match_assign() {
        check(
            r#"pub fn assign(_: &mut i32, _: i32) {}
                 pub fn bar(_: (i32, bool)) {}"#,
            "fn rule(x: &mut i32, v: i32) {replace!(*x = v => assign(x, v));}",
            "fn f1(b: &mut i32) {*b = 42;}",
            "fn f1(b: &mut i32) {assign(b, 42);}",
        );
    }

    #[test]
    fn match_assign_op() {
        check(
            r#"pub fn add(_: &mut i32, _: i32) {}
                 pub fn bar(_: (i32, bool)) {}"#,
            "fn rule(x: &mut i32, v: i32) {replace!(*x += v => add(x, v));}",
            "fn f1(b: &mut i32) {*b += 42;}",
            "fn f1(b: &mut i32) {add(b, 42);}",
        );
    }

    #[test]
    fn match_tuple_field() {
        check(
            r#"pub fn add(_: &mut i32, _: i32) {}
                 pub fn bar(_: (i32, bool)) {}"#,
            r#"fn r1(x: (i32, i32)) {replace!(x.0 => x.1);}
                 fn r2(x: (i32, i32)) {replace!(x.1 => x.0);}"#,
            "fn f1(b: (i32, i32)) -> i32 {b.0 + b.1}",
            "fn f1(b: (i32, i32)) -> i32 {b.1 + b.0}",
        );
    }

    // At the moment, matching println! is not practical. Its expansion includes a reference to a
    // static format string. Each invocation of the macro references a different static. If there
    // were a compelling reason for wanting to do this, we could possibly compare the definitions of
    // those statics, but the usefulness of this at the moment seems pretty limited.
    #[test]
    #[ignore]
    fn match_println() {
        check(
            "",
            r#"fn r(a: i32) {replace!(println!("{}", a); => println!("{}", a + 1);)}"#,
            r#"fn foo(x: i32) {println!("{}", x * 2);}"#,
            r#"fn foo(x: i32) {println!("{}", x * 2 + 1);}"#,
        );
    }

    #[test]
    fn struct_init() {
        check(
            stringify!(
            pub struct Point {pub x: i32, pub y: i32}
            impl Point {
                pub fn new(x: i32, y: i32) -> Point {
                    Point {x: x, y: y}
                }
            }),
            r#"fn rule(x: i32, y: i32) {
                     replace!(Point {x: x, y: y} => Point::new(x, y))}"#,
            "fn f1() -> Point {Point {x: 1 + 2, y: 3 + 4}}",
            "fn f1() -> Point {Point::new(1 + 2, 3 + 4)}",
        );
    }

    // Search for an expression that is nothing more than a placeholder. Checks that we don't
    // recurse infinitely in submatching logic. This test also checks that we don't mistakenly match
    // the function's block (since that is of type i32 as well). If this happened, then instead of
    // "... -> i32 {0i32}" we'd get "... -> i32 0i32".
    #[test]
    fn just_a_placeholder_no_subst() {
        check(
            "",
            "fn rule(x: i32) {replace!(x => 0i32);}",
            "fn f1(a: i32) -> i32 {(a + 1) * 2}",
            "fn f1(a: i32) -> i32 {0i32}",
        );
    }

    // While we don't want to match block that are function bodies as expressions, we do want to
    // match a lambda bodies where the expression isn't a block - i.e. lambda expressions without
    // braces.
    #[test]
    fn lambda_with_no_braces() {
        check(
            "",
            "fn r1(i: i32) {replace!(i + 1 => i - 2);}",
            "fn f1(o: Option<i32>) -> Option<i32> {o.map(|v| v + 1)}",
            "fn f1(o: Option<i32>) -> Option<i32> {o.map(|v| v - 2)}");
    }

    // Check that we can still replace nested matches within a placeholder-only expression.
    // TODO: There are some extra parenthesis in here. See if we can avoid them.
    #[test]
    fn just_a_placeholder_nested_matches() {
        check(
            "pub fn foo(v: i32) -> i32 {v}",
            "fn rule(x: i32) {replace!(x => foo(x));}",
            "fn f1(a: i32) -> i32 {(a + 1) * 2}",
            "fn f1(a: i32) -> i32 {foo(foo((foo(a) + foo(1))) * foo(2))}",
        );
    }

    // Check that we can replace a call to a trait method.
    #[test]
    fn match_trait_method() {
        check(
            stringify!(
                pub trait Foo {
                    fn foo1(self);
                    fn foo2(self);
                }

                impl Foo for i32 {
                    fn foo1(self) {}
                    fn foo2(self) {}
                }
            ),
            "fn rule<T: Foo>(x: T) {replace!(x.foo1() => x.foo2());}",
            "fn f1(a: i32) {a.foo1()}",
            "fn f1(a: i32) {a.foo2()}",
        );
    }

    // Checks matching of ?. Also checks that the replacement can be a macro invocation.
    #[test]
    fn match_question_mark() {
        check(
            "pub fn get_result() -> Result<i32, i32> {Ok(42)}",
            r#"fn r<T, E>(x: Result<T, E>) -> Result<T, E> {
                     replace!(x? => try!(x));
                     unreachable!();
                 }"#,
            "fn f1() -> Result<i32, i32> {get_result()?; Ok(1)}",
            "fn f1() -> Result<i32, i32> {try!(get_result()); Ok(1)}",
        );
    }

    #[test]
    fn match_crate_root_reference() {
        check(
            "",
            "fn r() {replace!(::foo::bar() => ::foo::bar2());}",
            r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {::foo::bar();}"#,
            r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {::foo::bar2();}"#,
        );
    }

    #[test]
    fn replace_type_in_argument_and_return() {
        check(
            "pub struct T1; pub struct T2;",
            "fn r() {replace_type!(T1 => T2); replace!(T1 => T2);}",
            "fn f1() -> T1 { let t: T1 = T1; t }",
            "fn f1() -> T2 { let t: T2 = T2; t }",
        );
    }

    #[test]
    fn replace_type_in_function_argument() {
        check(
            "pub struct T1; pub struct T2;",
            "fn r() {replace_type!(T1 => T2);}",
            "fn f1(t: T1) -> T1 { t }",
            "fn f1(t: T2) -> T2 { t }",
        );
    }

    #[test]
    fn replace_type_in_static() {
        check(
            "pub struct T1; pub struct T2;",
            "fn r() {replace_type!(T1 => T2);}",
            "static T: Option<T1> = None;",
            "static T: Option<T2> = None;",
        );
    }

    #[test]
    fn replace_type_nested() {
        check(
            "pub struct T1; pub struct T2;",
            "fn r() {replace_type!(T1 => T2);}",
            "fn f1(t: Option<T1>) -> Option<T1> { t }",
            "fn f1(t: Option<T2>) -> Option<T2> { t }",
        );
    }

    #[test]
    fn replace_trait_ref_in_type() {
        check(
            "pub trait T1 {} pub trait T2 {}",
            "fn r() {replace_trait_ref!(T1 => T2);}",
            "fn f1(_t: Box<T1>) {let _x: Box<T1>;}",
            "fn f1(_t: Box<T2>) {let _x: Box<T2>;}",
        );
    }

    #[test]
    fn replace_trait_ref_returned_impl_trait() {
        check(
            r#"pub trait T1 {}
               pub trait T2 {}
               pub struct S1();
               impl T1 for S1 {}
               impl T2 for S1 {}"#,
            "fn r() {replace_trait_ref!(T1 => T2);}",
            "fn f1() -> impl T1 {S1()}",
            "fn f1() -> impl T2 {S1()}",
        );
    }

    #[test]
    fn replace_trait_ref_in_impl() {
        check(
            "pub trait T1 {} pub trait T2 {}",
            "fn r() {replace_trait_ref!(T1 => T2);}",
            "struct Foo {} impl T1 for Foo {}",
            "struct Foo {} impl T2 for Foo {}",
        );
    }

    #[test]
    fn replace_trait_ref_in_where_clause() {
        check(
            "pub trait T1 {} pub trait T2 {}",
            "fn r() {replace_trait_ref!(T1 => T2);}",
            "fn f1<T>(t: Option<T>) -> Option<T> where T: Clone + T1 { t }",
            "fn f1<T>(t: Option<T>) -> Option<T> where T: Clone + T2 { t }",
        );
    }

    #[test]
    fn replace_trait_ref_in_type_bound() {
        check(
            "pub trait T1 {} pub trait T2 {}",
            "fn r() {replace_trait_ref!(T1 => T2);}",
            "fn f1<T: Clone + T1>(t: Option<T>) -> Option<T> { t }",
            "fn f1<T: Clone + T2>(t: Option<T>) -> Option<T> { t }",
        );
    }

    #[test]
    fn replace_trait_ref_with_non_trait_type() {
        check_error(
            r#"pub trait T1 {}
               pub struct T2 {}
               fn r() {replace_trait_ref!(T1 => T2);}"#,
            "replace_trait_ref! requires a trait",
            "T2",
        );
    }

    #[test]
    fn no_match_trait_with_same_name() {
        check_no_match(
            "pub trait T1 {} pub trait T2 {}",
            "fn r() {replace_trait_ref!(T1 => T2);}",
            r#"mod foo {
                   trait T1 {}
                   fn bar(_: Box<T1>) {}
               }"#,
        );
    }

    // Tests matching of tuple and reference patterns
    #[test]
    fn tuple_pattern() {
        check(
            stringify!(
                pub struct Foo(pub i32);
                pub struct Bar(pub i32, pub i32);
                pub fn get_foo_tuple() -> (Foo, i32) {(Foo(1), 2)}
                pub fn get_bar() -> Bar {Bar(1, 2)}
            ),
            r#"fn r1(t: &(Foo, i32), b: Bar) {
                     replace!(&get_foo_tuple() => get_bar());
                     replace_pattern!(&(Foo(f), v) = t => Bar(f, v) = b);
                 }"#,
            "fn f1() -> i32 {let &(Foo(x), y) = &get_foo_tuple(); x + y}",
            "fn f1() -> i32 {let Bar(x, y) = get_bar(); x + y}",
        );
    }

    // Checks matching of slice patterns and literals.
    #[test]
    fn slice_pattern() {
        check(
            "",
            "fn r1(s: &[i32]) {replace_pattern!(&[1, x] = s => &[x, 2] = s);}",
            "fn f1(v: &[i32]) -> i32 {if let &[1, a] = v {a} else {42}}",
            "fn f1(v: &[i32]) -> i32 {if let &[a, 2] = v {a} else {42}}",
        );
    }

    // Checks matching of inclusive and exclusive ended ranges.
    #[test]
    fn range_pattern() {
        check(
            "",
            r#"fn r1(i: i32) {
                     replace_pattern!(1 ... 5 = i => 1 .. 6 = i);
                     replace_pattern!(8 .. 10 = i => 8 ... 9 = i);
                 }"#,
            r#"fn f1(v: i32) -> i32 {
                     match v {
                         1 ... 5 => {42}
                         8 .. 10 => {41}
                         _ => {40}
                     }
                 }"#,
            r#"fn f1(v: i32) -> i32 {
                     match v {
                         1 .. 6 => {42}
                         8 ... 9 => {41}
                         _ => {40}
                     }
                 }"#,
        );
    }

    #[test]
    fn pattern_as_fn_argument() {
        check(
            "pub struct Point {pub x: i32, pub y: i32}",
            r#"fn r1(p: Point) {
                     replace_pattern!(Point {x: x1, y: y1} = p => Point {x: x1, y: y1, ..} = p);
               }"#,
            "fn f1(Point {x: x2, y: y2}: Point) -> i32 {x2 + y2}",
            "fn f1(Point {x: x2, y: y2, ..}: Point) -> i32 {x2 + y2}",
        );
    }

    // A match arm that contains a path to some constant.
    #[test]
    fn pattern_path() {
        check(
            "pub const FORTY_TWO: i32 = 42;",
            "fn r1(v: i32) {replace_pattern!(FORTY_TWO = v => 42 = v);}",
            r#"fn f1(v: Option<i32>) -> i32 {
                     match v {
                         Some(FORTY_TWO) => 1,
                         Some(_) => 2,
                         None => 3,
                     }
                 }"#,
            r#"fn f1(v: Option<i32>) -> i32 {
                     match v {
                         Some(42) => 1,
                         Some(_) => 2,
                         None => 3,
                     }
                 }"#,
        );
    }

    // Check that replace_pattern! allows a placeholder to match a pattern other than a binding.
    // This is also a copy of the example from the documentation in lib.rs for replace_pattern!
    #[test]
    fn pattern_placeholder_matches_non_binding() {
        check(
            r#"
                pub struct Foo(pub i32);
                pub fn f() -> Option<Foo> {Some(Foo(42))}
              "#,
            r#"fn some_foo_to_result_foo(p1: Option<Foo>, p2: Result<Foo, ()>) {
                    replace_pattern!(Some(f1) = p1 => Result::Ok(f1) = p2);
                    replace_pattern!(None = p1 => Result::Err(()) = p2);
                }"#,
            r#"fn m() -> i32 {
                match f() {
                    Some(Foo(x)) => x,
                    None => 0,
                }
            }"#,
            r#"fn m() -> i32 {
                match f() {
                    Result::Ok(Foo(x)) => x,
                    Result::Err(()) => 0,
                }
            }"#,
        );
    }

    #[test]
    fn rule_in_nested_module() {
        check(
            "pub fn foo(_: i32) {}",
            "mod s1 {use common::*; fn r1() {replace!(foo(1) => foo(2));}}",
            "fn f1() {foo(1);}",
            "fn f1() {foo(2);}",
        );
    }

    // Verify that using a placeholder multiple times in a search pattern is an error.
    #[test]
    fn error_multiple_bindings() {
        check_error(
            "fn r1(a: i32) {replace!(a + a => 42);}",
            "Placeholder is bound multiple times. This is not currently permitted.",
            "a",
        );
    }

    // Verify that using a placeholder in a replacement pattern that was never used in the search
    // pattern is an error.
    #[test]
    fn error_unbound_placeholder() {
        check_error(
            "fn r1(a: i32) {replace!(42 => a);}",
            "Placeholder used in replacement pattern, but never bound.",
            "a",
        );
    }

    // Check that when part of the matched AST comes from a macro (the +) and part comes from the
    // caller of the macro (x and y) that we reject the match.
    #[test]
    fn placeholder_bound_to_part_of_macro() {
        check_no_match(
            r#"macro_rules! add {
                  ($v1:expr, $v2:expr) => {$v1 + $v2}
               }
            "#,
            "fn r1(a: i32, b: i32) {replace!(a + b => b + a);}",
            "fn f1(x: i32, y: i32) -> i32 {add!(x, y)}",
        );
    }

    // Verify that an expression, part of which is a macro invocation isn't matched by an equivalent
    // expression without said macro invocation.
    #[test]
    fn subexpression_bound_to_part_of_macro() {
        check_no_match(
            "macro_rules! forty_two {() => {42}}",
            "fn r1() {replace!(1 + 42 + 1 => 1 + 40 + 1);}",
            "fn f1() -> i32 {1 + forty_two!() + 1}",
        );
    }

    // Verify that an invocation of a macro doesn't match an invocation of a different macro that
    // happens to produce the same code.
    #[test]
    fn invoke_two_identical_macros() {
        check_no_match(
            r#"macro_rules! forty_two_a {() => {42}}
                          macro_rules! forty_two_b {() => {42}}"#,
            "fn r1() {replace!(forty_two_a!() => 42);}",
            "fn f1() -> i32 {forty_two_b!()}",
        );
    }

    #[test]
    fn same_name_in_multiple_contexts() {
        check(
            "pub fn f(x: i32) -> i32 {42 + x}",
            "fn r1(f: i32) {replace!(f + 1 => f * 2);}",
            "fn f1() -> i32 {f(f(3)) + 1 + f(4)}",
            "fn f1() -> i32 {f(f(3)) * 2 + f(4)}",
        );
    }

    #[test]
    fn nested_patterns() {
        check(
            r#"pub fn f() -> Option<Option<Option<i32>>> {None}
               pub fn g() -> Result<Result<Result<i32, ()>, ()>, ()> {Err(())}"#,
            r#"fn r1<T>(o1: Option<T>, r1: Result<T, ()>) {
                   replace!(f() => g());
                   replace_pattern!(Some(x) = o1 => Ok(x) = r1);
                   replace_pattern!(None = o1 => Err(()) = r1);
               }"#,
            r#"fn f1() -> i32 {
                  match f() {
                      Some(Some(Some(v))) => v,
                      Some(Some(None)) => 1,
                      _ => 0,
                  }
               }"#,
            r#"fn f1() -> i32 {
                  match g() {
                      Ok(Ok(Ok(v))) => v,
                      Ok(Ok(Err(()))) => 1,
                      _ => 0,
                  }
               }"#,
        );
    }

    // Change code that calls Rc::clone to use UFCS, but make sure we don't also change code that's
    // calling clone on something else (a String).
    #[test]
    fn make_rc_clone_use_ufcs() {
        check(
            "pub use std::rc::Rc;",
            "fn r1<T>(r: Rc<T>) {replace!(r.clone() => Rc::clone(&r))}",
            "fn f1(n: Rc<Vec<String>>) {n[0].clone(); n.clone();}",
            "fn f1(n: Rc<Vec<String>>) {n[0].clone(); Rc::clone(&n);}",
        );
    }

    // Check that use-statements are added as required.
    #[test]
    #[ignore]
    fn add_use_statement() {
        check(
            r#"pub fn process_i32(i: i32) {}
                 pub mod foo {
                     pub struct Bar(pub i32);
                     pub fn process_bar(b: Bar) {}
                 }"#,
            r#"use ::common::foo::{process_bar, Bar};
                 fn r(a: i32) {replace!(process_i32(a) => process_bar(Bar(a)));}"#,
            r#"fn f1(x: i32) {process_i32(x + 1);}"#,
            r#"use ::common::foo::process_bar;
                 use ::common::foo::Bar;
                 fn f1(x: i32) {process_bar(Bar(x + 1));}"#,
        );
    }

    // Ensure that we don't go looking for rules outside of the rules module.
    #[test]
    // Disabled since replace! is no longer defined prior to our code. Need to figure out a new way
    // to write this test.
    #[ignore]
    fn rule_outside_of_rules_module() {
        check_no_match(
            "",
            "",
            r#"fn r1() {replace!(1i64 => 42i64);}
               fn f1() -> i64 {1i64} "#,
        );
    }

    // Expression containing two &str - one 'static and one not. Only the &'static str should match.
    // Currently however, both match. I'm guessing lifetimes are not included when we check if we
    // can subtype. Lifetime checking must be a separate step. It's possible it isn't worth trying
    // to make this pass.
    #[test]
    #[ignore]
    fn static_and_non_static_refs() {
        check(
            "pub fn im_a_static_str(s: &str) -> &str {s}",
            "fn r3(s: &'static str) {replace!(s => im_a_static_str(s));}",
            r#"fn f1() -> String {
                     "static".to_string() + 2.to_string().as_ref()
                 }"#,
            r#"fn f1() -> String {
                     im_a_static_str("static").to_string() + 2.to_string().as_ref()
                 }"#,
        );
    }

    // The expansion of the panic! macro includes a string literal containing the filename.
    #[test]
    // We currently match that string literal with a span of the whole macro invocation. Guessing
    // the span that's put on the literal is a bit strange. It might be possible to detect "strange"
    // spans and just refuse to match them.
    #[ignore]
    fn panic_doesnt_match_str_placeholder() {
        check_no_match(
            "",
            "fn r3(s: &str) {replace!(s => drop(s));}",
            "fn f1() {panic!(42);}",
        );
    }

    #[test]
    fn indexed_context() {
        check(
            "",
            "fn rule<T>(v: &[T], i: usize) {replace!(v[i] => v.get(i).unwrap());}",
            "fn f(data: &[i32]) -> i32 {data[0]}",
            "fn f(data: &[i32]) -> i32 {data.get(0).unwrap()}",
        );
    }
}
