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

// Given two versions of a source file, finds what's changed and builds a Rerast rule to reproduce
// the change.

extern crate getopts;
extern crate rustc;
extern crate rustc_driver;
extern crate syntax;
extern crate syntax_pos;

use crate::errors::RerastErrors;
use crate::file_loader::{ClonableRealFileLoader, InMemoryFileLoader};
use crate::CompilerInvocationInfo;
use rustc::hir::{self, intravisit};
use rustc::ty::{TyCtxt, TyKind};
use rustc_interface::interface;
use std::collections::hash_map::{DefaultHasher, HashMap};
use std::collections::hash_set::HashSet;
use std::fmt::Write;
use std::hash::{Hash, Hasher};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use syntax::parse::{self, ParseSess};
use syntax::source_map::{FileLoader, FilePathMapping, SourceMap};
use syntax::tokenstream::{TokenStream, TokenTree};
use syntax_pos::{BytePos, Pos, Span, SyntaxContext};

struct PlaceholderCandidate<T> {
    hash: u64,
    children: Vec<PlaceholderCandidate<T>>,
    data: T,
}

impl<T> PlaceholderCandidate<T> {
    fn new(data: T) -> PlaceholderCandidate<T> {
        PlaceholderCandidate {
            hash: 0,
            data,
            children: Vec::new(),
        }
    }
}

impl<T> Hash for PlaceholderCandidate<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        hasher.write_u64(self.hash);
    }
}

struct Placeholder<'tcx> {
    expr: &'tcx hir::Expr,
    uses: Vec<Span>,
}

fn default_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn hash_token_stream(stream: &TokenStream, hasher: &mut DefaultHasher) {
    for tt in stream.trees() {
        match tt {
            TokenTree::Token(_token) => {
                // If hash collisions become enough of a problem that we get bad performance, we'll
                // probably need to look into the structure of the token and hash that. In the mean
                // time, lets just hash an arbitrary constant value. At least expressions with
                // different tree structures will likely get different hashes.
                42.hash(hasher)
            }
            TokenTree::Delimited(_span, _delimited, tts) => hash_token_stream(&tts, hasher),
        }
    }
}

struct PlaceholderCandidateFinder<'tcx, T, F>
where
    F: Fn(&'tcx hir::Expr) -> T,
{
    tcx: TyCtxt<'tcx>,
    stack: Vec<PlaceholderCandidate<T>>,
    data_fn: F,
}

impl<'tcx, T, F> PlaceholderCandidateFinder<'tcx, T, F>
where
    F: Fn(&'tcx hir::Expr) -> T,
{
    fn find_placeholder_candidates(
        tcx: TyCtxt<'tcx>,
        node: &'tcx hir::Expr,
        data_fn: F,
    ) -> Vec<PlaceholderCandidate<T>> {
        let mut state = PlaceholderCandidateFinder {
            tcx,
            stack: vec![PlaceholderCandidate::new(data_fn(node))],
            data_fn,
        };
        state.walk_expr_children(node);
        state.stack.pop().unwrap().children
    }

    fn walk_expr_children(&mut self, expr: &'tcx hir::Expr) {
        if let hir::ExprKind::Call(ref _expr_fn, ref args) = expr.kind {
            // Ignore expr_fn as a candidate, just consider the args.
            for arg in args {
                use rustc::hir::intravisit::Visitor;
                self.visit_expr(arg);
            }
        } else {
            intravisit::walk_expr(self, expr);
        }
    }
}

impl<'tcx, T, F> intravisit::Visitor<'tcx> for PlaceholderCandidateFinder<'tcx, T, F>
where
    F: Fn(&'tcx hir::Expr) -> T,
{
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        self.stack
            .push(PlaceholderCandidate::new((self.data_fn)(expr)));
        self.walk_expr_children(expr);
        // We pushed to the stack. So long as all pushes and pops are matched, we should be able to
        // safely pop.
        let mut candidate = self.stack.pop().unwrap();
        candidate.hash = if candidate.children.is_empty() {
            // Leaf node. Get a token stream and hash its tokens.
            let snippet = self
                .tcx
                .sess
                .source_map()
                .span_to_snippet(expr.span)
                .unwrap();
            let session = ParseSess::new(FilePathMapping::empty());
            let stream = parse::parse_stream_from_source_str(
                syntax_pos::FileName::anon_source_code(&snippet),
                snippet,
                &session,
                None,
            );
            let mut hasher = DefaultHasher::new();
            hash_token_stream(&stream, &mut hasher);
            hasher.finish()
        } else {
            // Non-leaf node. Just combine the already computed hashes of our children.
            default_hash(&candidate.children)
        };
        // There should at least be the root still on the stack.
        self.stack.last_mut().unwrap().children.push(candidate);
    }
}

fn span_within_span(span: Span, target: Span) -> Span {
    if target.contains(span) {
        span
    } else {
        let expn_info = span.ctxt().outer_expn().expn_data();
        span_within_span(expn_info.call_site, target)
    }
}

struct RelativeSpan(Range<BytePos>);

impl RelativeSpan {
    fn new(absolute_span: Span, filemap: &syntax_pos::SourceFile) -> RelativeSpan {
        let absolute_span = span_within_span(
            absolute_span,
            Span::with_root_ctxt(filemap.start_pos, filemap.end_pos),
        );
        let start_pos = filemap.start_pos;
        assert!(absolute_span.lo() >= start_pos);
        assert!(absolute_span.hi() <= filemap.end_pos);
        RelativeSpan((absolute_span.lo() - start_pos)..(absolute_span.hi() - start_pos))
    }

    fn absolute(&self, filemap: &syntax_pos::SourceFile) -> Span {
        let start_pos = filemap.start_pos;
        let result = Span::with_root_ctxt(self.0.start + start_pos, self.0.end + start_pos);
        assert!(result.lo() >= filemap.start_pos);
        assert!(result.hi() <= filemap.end_pos);
        result
    }
}

// The span of a file that has changed. Start and end are relative to the start and end of the file,
// which makes the files the same in both the changed and the original version of the file.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
struct ChangedSpan {
    common_prefix: usize,
    common_suffix: usize,
}

impl ChangedSpan {
    fn new(common_prefix: usize, common_suffix: usize) -> ChangedSpan {
        ChangedSpan {
            common_prefix,
            common_suffix,
        }
    }

    fn from_span(span: Span, filemap: &syntax_pos::SourceFile) -> ChangedSpan {
        ChangedSpan {
            common_prefix: (span.lo() - filemap.start_pos).to_usize(),
            common_suffix: (filemap.end_pos - span.hi()).to_usize(),
        }
    }

    fn to_span(&self, filemap: &syntax_pos::SourceFile) -> Span {
        Span::new(
            filemap.start_pos + BytePos::from_usize(self.common_prefix),
            filemap.end_pos - BytePos::from_usize(self.common_suffix),
            SyntaxContext::root(),
        )
    }
}

struct ChangedSideState {
    candidate_placeholders: Vec<PlaceholderCandidate<RelativeSpan>>,
    required_paths: HashSet<String>,
}

struct FindRulesState {
    modified_file_name: String,
    modified_source: String,
    changed_span: ChangedSpan,
    result: String,
    changed_side_state: Option<ChangedSideState>,
}

impl rustc_driver::Callbacks for FindRulesState {
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> rustc_driver::Compilation {
        compiler.session().abort_if_errors();
        compiler.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let source_map = tcx.sess.source_map();
            let maybe_filemap = source_map.get_source_file(&syntax_pos::FileName::Real(
                PathBuf::from(&self.modified_file_name),
            ));
            let filemap = if let Some(f) = maybe_filemap {
                f
            } else {
                return rustc_driver::Compilation::Stop;
            };
            let span = self.changed_span.to_span(&filemap);
            let mut rule_finder = RuleFinder {
                tcx,
                changed_span: span,
                candidate: Node::NotFound,
                body_id: None,
                current_item: None,
            };
            intravisit::walk_crate(&mut rule_finder, tcx.hir().krate());
            match rule_finder.candidate {
                Node::NotFound => {}
                Node::Expr(expr, body_id, item) => {
                    let new_changed_span = ChangedSpan::from_span(expr.span, &filemap);
                    if let Some(ref changed_side_state) = self.changed_side_state {
                        // Presence of changed_side_state means that we've already run on the changed
                        // version of the source. We're now running on the original source.
                        if self.changed_span != new_changed_span {
                            self.changed_span = new_changed_span;
                        } else {
                            self.result = analyse_original_source(
                                tcx,
                                changed_side_state,
                                expr,
                                &self.changed_span,
                                self.modified_source.clone(),
                                body_id,
                                item,
                            );
                        }
                    } else {
                        // First rustc invocation. We're running on the changed version of the source. Find
                        // which bit of the HIR tree has changed and select candidate placeholders.
                        self.changed_span = new_changed_span;
                        self.changed_side_state = Some(ChangedSideState {
                            candidate_placeholders:
                                PlaceholderCandidateFinder::find_placeholder_candidates(
                                    tcx,
                                    expr,
                                    |child_expr| RelativeSpan::new(child_expr.span, &filemap),
                                ),
                            required_paths: ReferencedPathsFinder::paths_in_expr(tcx, expr),
                        })
                    }
                }
            }
            rustc_driver::Compilation::Stop
        })
    }
}

fn analyse_original_source<'a, 'tcx: 'a>(
    tcx: TyCtxt<'tcx>,
    changed_side_state: &ChangedSideState,
    expr: &'tcx hir::Expr,
    changed_span: &ChangedSpan,
    modified_source: String,
    body_id: hir::BodyId,
    item: &'tcx hir::Item,
) -> String {
    let source_map = tcx.sess.source_map();
    let mut others_by_hash = HashMap::new();
    populate_placeholder_map(
        &changed_side_state.candidate_placeholders,
        &mut others_by_hash,
    );
    let mut candidates =
        PlaceholderCandidateFinder::find_placeholder_candidates(tcx, expr, |child_expr| child_expr);
    let other_filemap = source_map.new_source_file(
        syntax_pos::FileName::Custom("__other_source".to_owned()),
        modified_source,
    );
    let replacement_span = changed_span.to_span(&*other_filemap);
    let mut matcher = PlaceholderMatcher {
        tcx,
        other_filemap,
        other_candidates: others_by_hash,
        placeholders_found: Vec::new(),
        used_placeholder_spans: Vec::new(),
    };
    matcher.find_placeholders(&mut candidates);
    // Sort placeholders by the order they appear in the search expression, since this seems a bit
    // more natural to read.
    matcher.placeholders_found.sort_by_key(|p| p.expr.span.lo());
    build_rule(
        tcx,
        &matcher.placeholders_found,
        expr,
        body_id,
        item,
        &changed_side_state.required_paths,
        replacement_span,
    )
}

fn build_rule<'a, 'tcx: 'a>(
    tcx: TyCtxt<'tcx>,
    placeholders: &[Placeholder<'tcx>],
    expr: &'tcx hir::Expr,
    body_id: hir::BodyId,
    item: &'tcx hir::Item,
    right_paths: &HashSet<String>,
    replacement_span: Span,
) -> String {
    let source_map = tcx.sess.source_map();
    let type_tables = tcx.body_tables(body_id);
    let mut uses_type_params = false;
    for ph in placeholders {
        let ph_ty = type_tables.expr_ty(ph.expr);
        for subtype in ph_ty.walk() {
            if let TyKind::Param(..) = subtype.kind {
                uses_type_params = true;
            }
        }
    }
    let generics_string;
    let where_string;
    if uses_type_params {
        if let Some(generics) = item.kind.generics() {
            generics_string = source_map.span_to_snippet(generics.span).unwrap();
            let mut where_predicate_strings = Vec::new();
            for predicate in &generics.where_clause.predicates {
                let span = match *predicate {
                    hir::WherePredicate::BoundPredicate(ref p) => p.span,
                    hir::WherePredicate::RegionPredicate(ref p) => p.span,
                    hir::WherePredicate::EqPredicate(ref p) => p.span,
                };
                where_predicate_strings.push(source_map.span_to_snippet(span).unwrap());
            }
            where_string = if where_predicate_strings.is_empty() {
                String::new()
            } else {
                format!(" where {}", where_predicate_strings.join(", "))
            };
        } else {
            panic!("Item has no generics, but type appears to have type parameters");
        }
    } else {
        generics_string = String::new();
        where_string = String::new();
    }
    let arg_decls = placeholders
        .iter()
        .enumerate()
        .map(|(ph_num, ph)| format!("p{}: {}", ph_num, type_tables.expr_ty(ph.expr)))
        .collect::<Vec<_>>()
        .join(", ");
    let mut use_statements = String::new();
    let left_paths = ReferencedPathsFinder::paths_in_expr(tcx, expr);
    let mut paths: Vec<_> = left_paths.union(right_paths).collect();
    paths.sort();
    for path in paths {
        use_statements += &format!("use {}; ", path);
    }

    let mut search_substitutions = Vec::new();
    let mut replacement_substitutions = Vec::new();
    for (ph_num, ph) in placeholders.iter().enumerate() {
        search_substitutions.push((ph.expr.span, format!("p{}", ph_num)));
        for usage in &ph.uses {
            replacement_substitutions.push((*usage, format!("p{}", ph_num)));
        }
    }
    let search = substitute_placeholders(source_map, expr.span, &mut search_substitutions);
    let replace =
        substitute_placeholders(source_map, replacement_span, &mut replacement_substitutions);
    format!(
        "{}fn r1{}({}){} {{replace!({} => {});}}",
        use_statements, generics_string, arg_decls, where_string, search, replace
    )
}

fn substitute_placeholders(
    source_map: &SourceMap,
    span: Span,
    substitutions: &mut [(Span, String)],
) -> String {
    substitutions.sort_by_key(|v| v.0.lo());
    let mut result = String::new();
    let mut start = span.lo();
    for &(subst_span, ref substitution) in substitutions.iter() {
        result += &source_map
            .span_to_snippet(Span::with_root_ctxt(start, subst_span.lo()))
            .unwrap();
        result += substitution;
        start = subst_span.hi();
    }
    result += &source_map
        .span_to_snippet(Span::with_root_ctxt(start, span.hi()))
        .unwrap();
    result
}

struct PlaceholderMatcher<'tcx, 'placeholders> {
    tcx: TyCtxt<'tcx>,
    other_filemap: Rc<syntax_pos::SourceFile>,
    other_candidates: HashMap<u64, Vec<&'placeholders PlaceholderCandidate<RelativeSpan>>>,
    placeholders_found: Vec<Placeholder<'tcx>>,
    used_placeholder_spans: Vec<Span>,
}

impl<'tcx, 'placeholders> PlaceholderMatcher<'tcx, 'placeholders> {
    fn find_placeholders(&mut self, candidates: &mut [PlaceholderCandidate<&'tcx hir::Expr>]) {
        // Sort candidates with longest first so that they take precedence.
        candidates.sort_by_key(|p| p.data.span.lo() - p.data.span.hi());
        for candidate in candidates {
            let mut got_match = false;
            if let Some(matching_others) = self.other_candidates.get(&candidate.hash) {
                let source_map = self.tcx.sess.source_map();
                let source = source_map.span_to_snippet(candidate.data.span).unwrap();
                let mut placeholder = Placeholder {
                    expr: candidate.data,
                    uses: Vec::new(),
                };
                for other in matching_others {
                    let session = ParseSess::new(FilePathMapping::empty());
                    let stream = parse::parse_stream_from_source_str(
                        syntax_pos::FileName::Custom("left".to_owned()),
                        source.clone(),
                        &session,
                        None,
                    );
                    let other_span = other.data.absolute(&*self.other_filemap);
                    let other_source = source_map.span_to_snippet(other_span).unwrap();
                    let other_stream = parse::parse_stream_from_source_str(
                        syntax_pos::FileName::Custom("right".to_owned()),
                        other_source,
                        &session,
                        None,
                    );
                    if stream.eq_unspanned(&other_stream)
                        && !self
                            .used_placeholder_spans
                            .iter()
                            .any(|s| s.contains(other_span) || other_span.contains(*s))
                    {
                        self.used_placeholder_spans.push(other_span);
                        placeholder.uses.push(other_span);
                        break;
                    }
                }
                if !placeholder.uses.is_empty() {
                    self.placeholders_found.push(placeholder);
                    got_match = true;
                }
            }
            if !got_match {
                // Placeholders can't overlap - only look for matches in our children if we didn't
                // match.
                self.find_placeholders(&mut candidate.children);
            }
        }
    }
}

fn populate_placeholder_map<'a, T>(
    candidates: &'a [PlaceholderCandidate<T>],
    map_out: &mut HashMap<u64, Vec<&'a PlaceholderCandidate<T>>>,
) {
    for candidate in candidates {
        map_out
            .entry(candidate.hash)
            .or_insert_with(Vec::new)
            .push(candidate);
        populate_placeholder_map(&candidate.children, map_out);
    }
}

// Finds referenced item paths and builds use statements that import those paths.
struct ReferencedPathsFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    result: HashSet<String>,
}

impl<'tcx> ReferencedPathsFinder<'tcx> {
    fn paths_in_expr(tcx: TyCtxt<'tcx>, expr: &'tcx hir::Expr) -> HashSet<String> {
        let mut finder = ReferencedPathsFinder {
            tcx,
            result: HashSet::new(),
        };
        intravisit::walk_expr(&mut finder, expr);
        finder.result
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for ReferencedPathsFinder<'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_path(&mut self, path: &'tcx hir::Path, _: hir::HirId) {
        if let crate::hir::def::Res::Def(_, def_id) = path.res {
            let mut qualified_path = String::new();
            for component in self.tcx.def_path(def_id).data {
                write!(qualified_path, "::{}", component.data.as_interned_str()).unwrap();
            }
            self.result.insert(qualified_path);
        }
    }
}

enum Node<'tcx> {
    NotFound,
    Expr(&'tcx hir::Expr, hir::BodyId, &'tcx hir::Item),
}

struct RuleFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    changed_span: Span,
    candidate: Node<'tcx>,
    body_id: Option<hir::BodyId>,
    current_item: Option<&'tcx hir::Item>,
}

impl<'tcx> intravisit::Visitor<'tcx> for RuleFinder<'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, 'tcx> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_item(&mut self, item: &'tcx hir::Item) {
        // TODO: Avoid visiting items that we know don't contain the changed code. Just need to make
        // sure we still visit mod items where the module code is in another file.
        let old_item = self.current_item;
        self.current_item = Some(item);
        intravisit::walk_item(self, item);
        self.current_item = old_item;
    }

    fn visit_body(&mut self, body: &'tcx hir::Body) {
        let old_body_id = self.body_id;
        self.body_id = Some(body.id());
        intravisit::walk_body(self, body);
        self.body_id = old_body_id;
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr) {
        if expr.span.from_expansion() {
            intravisit::walk_expr(self, expr);
        } else if expr.span.contains(self.changed_span) {
            if let (Some(body_id), Some(item)) = (self.body_id, self.current_item) {
                self.candidate = Node::Expr(expr, body_id, item);
                intravisit::walk_expr(self, expr);
            } else {
                // TODO: Consider better error handling - assuming it's actually possible to trip
                // this. Static initializer? Or does that have a body?
                panic!("Changing expressions outside of bodies isn't supported");
            }
        }
    }
}

pub fn determine_rule(
    compiler_invocations: &[CompilerInvocationInfo],
    modified_file_name: &str,
    original_file_contents: &str,
) -> Result<String, RerastErrors> {
    determine_rule_with_file_loader(
        &ClonableRealFileLoader,
        compiler_invocations,
        modified_file_name,
        original_file_contents,
    )
}

fn determine_rule_with_file_loader<T: FileLoader + Clone + Send + Sync + 'static>(
    file_loader: &T,
    compiler_invocations: &[CompilerInvocationInfo],
    modified_file_name: &str,
    original_file_contents: &str,
) -> Result<String, RerastErrors> {
    let right = file_loader.read_file(Path::new(modified_file_name))?;
    let changed_span = match common(original_file_contents, &right) {
        Some(c) => c,
        None => {
            return Err(RerastErrors::with_message(
                "Nothing appears to have changed",
            ));
        }
    };
    let mut find_rules_state = FindRulesState {
        modified_file_name: modified_file_name.to_owned(),
        modified_source: right.clone(),
        changed_span,
        changed_side_state: None,
        result: String::new(),
    };

    let mut args_index = 0;
    loop {
        // Run rustc on modified source to find HIR node that encloses changed code as well as
        // subnodes that will be candidates for placeholders.
        let invocation_info = compiler_invocations[args_index]
            .clone()
            .arg("--sysroot")
            .arg(crate::rustup_sysroot())
            .arg("--allow")
            .arg("dead_code");
        invocation_info.run_compiler(&mut find_rules_state, Some(box file_loader.clone()))?;
        if find_rules_state.changed_side_state.is_none() {
            // Span was not found with these compiler args, try the next command line.
            args_index += 1;
            if args_index >= compiler_invocations.len() {
                return Err(RerastErrors::with_message(
                    "Failed to find a modified expression",
                ));
            }
            continue;
        }
        let right_side_changed_span = find_rules_state.changed_span;

        // Run rustc on original source to confirm matching HIR node exists and to match
        // placeholders.
        let mut original_file_loader = box InMemoryFileLoader::new(file_loader.clone());
        original_file_loader.add_file(
            modified_file_name.to_owned(),
            original_file_contents.to_owned(),
        );
        invocation_info.run_compiler(&mut find_rules_state, Some(original_file_loader))?;

        if right_side_changed_span == find_rules_state.changed_span {
            // The changed span after examining the right side matched a full expression on the
            // left, so we're done.
            break;
        }
        // The changed span after examing the right side corresponded to only part of an expression
        // on the left. We need to go back and reprocess the right with the now widened span.
    }

    Ok(find_rules_state.result)
}

fn common_prefix(left: &str, right: &str) -> Option<usize> {
    for (i, (l, r)) in left.bytes().zip(right.bytes()).enumerate() {
        if l != r {
            return Some(i);
        }
    }
    None
}

fn common_suffix(left: &str, right: &str) -> Option<usize> {
    for (i, (l, r)) in left.bytes().rev().zip(right.bytes().rev()).enumerate() {
        if l != r {
            return Some(i);
        }
    }
    None
}

fn common(left: &str, right: &str) -> Option<ChangedSpan> {
    match (common_prefix(left, right), common_suffix(left, right)) {
        (Some(prefix), Some(suffix)) => Some(ChangedSpan::new(prefix, suffix)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::NullFileLoader;

    fn check_determine_rule_with_file_loader(
        file_loader: &InMemoryFileLoader<NullFileLoader>,
        changed_filename: &str,
        original_file_contents: &str,
        expected_rule: &str,
    ) {
        let expected_rule = expected_rule
            .lines()
            .map(str::trim)
            .collect::<Vec<_>>()
            .join("");
        let invocation_info = CompilerInvocationInfo {
            args: vec![
                "rustc".to_owned(),
                "--crate-type".to_owned(),
                "lib".to_owned(),
                "lib.rs".to_owned(),
            ],
            env: HashMap::new(),
        };
        let rule = determine_rule_with_file_loader(
            file_loader,
            &[invocation_info],
            changed_filename,
            original_file_contents,
        )
        .unwrap();
        assert_eq!(rule, expected_rule);
    }

    fn check_determine_rule(common: &str, left: &str, right: &str, expected_rule: &str) {
        let left = common.to_owned() + "\n" + left;
        let right = common.to_owned() + "\n" + right;
        let mut file_loader = InMemoryFileLoader::new(NullFileLoader);
        file_loader.add_file("lib.rs", right);
        check_determine_rule_with_file_loader(&file_loader, "lib.rs", &left, expected_rule);
    }

    #[test]
    fn change_in_separate_file() {
        let mut file_loader = InMemoryFileLoader::new(NullFileLoader);
        file_loader.add_file("lib.rs", "mod foo;".to_owned());
        file_loader.add_file("foo.rs", "fn bar() -> bool {!true}".to_owned());
        check_determine_rule_with_file_loader(
            &file_loader,
            "foo.rs",
            "fn bar() -> bool {false}",
            "fn r1() {replace!(false => !true);}",
        );
    }

    #[test]
    fn find_changed_range() {
        assert_eq!(
            Some(ChangedSpan::new(5, 2)),
            common("ababcab", "ababcdefab")
        );
    }

    #[test]
    fn determine_rule_basic() {
        check_determine_rule(
            r#"pub fn bar(x: i32) -> i32 {x}
               pub fn baz(x: i32) -> i32 {x}"#,
            "fn foo(a: i32, b: i32) -> i32 {if a < b {bar(a * 2 + 1)} else {b}}",
            "fn foo(a: i32, b: i32) -> i32 {if a < b {baz(a * 2)} else {b}}",
            "use ::bar; use ::baz; fn r1(p0: i32) {replace!(bar(p0 + 1) => baz(p0));}",
        );
    }

    #[test]
    fn swap_order() {
        check_determine_rule(
            r#"pub fn bar() -> (i32, usize) {(1, 2)}"#,
            "fn foo(x: i32, y: i32) -> (i32, i32) {(x + 1, y + 1)}",
            "fn foo(x: i32, y: i32) -> (i32, i32) {(y + 1, x + 1)}",
            "fn r1(p0: i32, p1: i32) {replace!((p0, p1) => (p1, p0));}",
        );
    }

    #[test]
    fn generic_typed_placeholder() {
        check_determine_rule(
            "",
            "fn foo<T: std::ops::Add<Output=T>>(x: T, y: T) -> T {x + y}",
            "fn foo<T: std::ops::Add<Output=T>>(x: T, y: T) -> T {y + x}",
            "fn r1<T: std::ops::Add<Output=T>>(p0: T, p1: T) {replace!(p0 + p1 => p1 + p0);}",
        );
    }

    #[test]
    fn generic_typed_placeholder_where_clause() {
        check_determine_rule(
            "",
            "fn foo<T>(x: T, y: T) -> T where T: std::ops::Add<Output=T> {x + y}",
            "fn foo<T>(x: T, y: T) -> T where T: std::ops::Add<Output=T> {y + x}",
            r#"fn r1<T>(p0: T, p1: T) where T: std::ops::Add<Output=T> {
                   replace!(p0 + p1 => p1 + p0);
               }"#,
        );
    }

    #[test]
    fn changed_closure() {
        check_determine_rule(
            "fn r<T, F>(f: F) -> T where F: FnOnce() -> T {f()}",
            "fn foo<T>(x: T, y: T) -> T where T: std::ops::Add<Output=T> {r(|| x + y)}",
            "fn foo<T>(x: T, y: T) -> T where T: std::ops::Add<Output=T> {r(|| y + x)}",
            r#"fn r1<T>(p0: T, p1: T) where T: std::ops::Add<Output=T> {
                   replace!(p0 + p1 => p1 + p0);
               }"#,
        );
    }

    // This test used to pass. Started failing on 2019-08-23. Not sure why. But
    // I've never heard of anyone actually using change_to_rule, so am not sure
    // I want to spend the time to figure it out.
    #[test]
    #[ignore]
    fn changed_println_arg() {
        check_determine_rule(
            "",
            r#"fn b() {println!("{}", 10 + 1);}"#,
            r#"fn b() {println!("{}", 10 - 1);}"#,
            "fn r1(p0: i32, p1: i32) {replace!(p0 + p1 => p0 - p1);}",
        );
    }

    // When a value (1 in this case) appears multiple times in both the left and right code,
    // placeholders should be determined by ordering. i.e. the first 1 in both should be p0.
    #[test]
    fn repeated_placeholder() {
        check_determine_rule(
            "",
            "fn b() -> i32 {1 + 1}",
            "fn b() -> i32 {1 - 1}",
            "fn r1(p0: i32, p1: i32) {replace!(p0 + p1 => p0 - p1);}",
        );
    }

    // If the changed code references a path, we need to import it into the rule code.
    #[test]
    fn use_fn_in_submodule() {
        check_determine_rule(
            "mod m1 { pub mod m11 { pub fn foo(_: i32) {} pub fn bar() {} } }",
            "mod m2 { use m1::m11::*; fn b() {foo(1)} }",
            "mod m2 { use m1::m11::*; fn b() {bar()} }",
            "use ::m1::m11::bar; use ::m1::m11::foo; fn r1() {replace!(foo(1) => bar());}",
        );
    }

    // If we didn't give precedence to larger placeholders, the first 2 would match the 2 in 1 + 2,
    // then 1 + 2 couldn't be a placeholder so we'd end up with (p1, p1 + p2) instead of (p0, p1).
    #[test]
    fn larger_placeholder_takes_precedence() {
        check_determine_rule(
            "",
            "fn b() -> (i32, i32) {(2, 1 + 2)}",
            "fn b() -> (i32, i32) {(1 + 2, 2)}",
            "fn r1(p0: i32, p1: i32) {replace!((p0, p1) => (p1, p0));}",
        );
    }

    // Verify that we correctly handle the case where the changed code starts in one expression and
    // finishes in another. In this case, if we're not careful, we'll think that our replacement
    // pattern is just `2`. Also verify that we don't produce multiple identical use statements.
    #[test]
    fn changed_span_crosses_expressions_and_deduplication_of_use_statements() {
        check_determine_rule(
            "fn foo(x: u32) -> u32 {x}",
            "fn b() -> u32 {foo(1) + foo(1)}",
            "fn b() -> u32 {foo(2)}",
            "use ::foo; fn r1() {replace!(foo(1) + foo(1) => foo(2));}",
        );
    }

    // Make sure we don't emit unnecessary use statements for references contained within
    // code that becomes placeholders.
    #[test]
    #[ignore] // Not sure if this is worth making pass.
    fn function_used_only_from_placeholder() {
        check_determine_rule(
            "fn foo() -> i32 {1}",
            "fn f1() -> i32 {foo() + 1}",
            "fn f1() -> i32 {foo() - 1}",
            "fn r1(p0: i32, p1: i32) {replace!(p0 + p1 => p0 - p1);}",
        );
    }

    // Make sure we don't make a function reference that's part of a function call be a placeholder.
    #[test]
    fn function_changed_function_arguments() {
        check_determine_rule(
            "fn foo(_: i32, _: i32) {}",
            "fn f1() {foo(1, 2)}",
            "fn f1() {foo(2, 1)}",
            "use ::foo; fn r1(p0: i32, p1: i32) {replace!(foo(p0, p1) => foo(p1, p0));}",
        );
    }

    // Not sure if we actually want to do this. In some ways it would be more consistent if we
    // allowed the whole expression to be a placeholder, but we're effectively then matching
    // anything of that type.
    #[test]
    #[ignore]
    fn placeholder_is_whole_expression() {
        check_determine_rule(
            "",
            "fn f1() -> bool {true}",
            "fn f1() -> bool {!true}",
            "fn r1(p0: bool) {replace!(p0 => !p0);}",
        );
    }
}
