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
// different expansions, we reject the match. This is done by RuleMatcher::get_original_spans.
//
// Note, everything is in this one file because initially I found it easier to work with. No need to
// switch files. Just do an incremental search for whatever I'm looking for. I'm in the process of
// moving some bits out in the hopes that this will improve compilation times (not that they're that
// bad).

//! Very little thought has gone into the public interface of this library. Things that are pub are
//! mostly that way so they can be accessed from cargo-rerast. If you have a use-case for using this
//! library, it's probably best to discuss it so that we can nail down a more thought-out interface.

#![feature(rustc_private)]
#![feature(box_syntax)]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

extern crate getopts;

use rerast_macros;
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate syntax;

pub mod change_to_rule;
pub mod chunked_diff;
pub mod code_substitution;
mod definitions;
pub mod errors;
mod file_loader;
mod rule_finder;
mod rule_matcher;
mod rules;
mod validation;

use crate::code_substitution::FileRelativeSubstitutions;
use crate::definitions::{RerastDefinitions, RerastDefinitionsFinder};
use crate::errors::RerastErrors;
use crate::file_loader::InMemoryFileLoader;
use crate::rule_finder::StartMatch;
use crate::rules::Rules;
use rustc::ty::TyCtxt;
use rustc_hir::intravisit;
use rustc_hir::HirId;
use rustc_interface::interface;
use rustc_span::source_map::FileLoader;
use rustc_span::source_map::{self, SourceMap};
use rustc_span::symbol::Symbol;
use rustc_span::{Span, SyntaxContext};
use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::vec::Vec;

#[derive(Debug, Clone, Default)]
pub struct Config {
    pub verbose: bool,
    pub debug_snippet: String,
    pub files: Option<Vec<String>>,
}

#[derive(Debug, Clone, Default)]
pub struct CompilerInvocationInfo {
    pub args: Vec<String>,
    pub env: HashMap<String, String>,
}

impl CompilerInvocationInfo {
    pub fn from_args<T: Iterator<Item = S>, S: Into<String>>(args: T) -> CompilerInvocationInfo {
        CompilerInvocationInfo {
            args: args.map(std::convert::Into::into).collect(),
            env: HashMap::new(),
        }
    }

    pub fn arg<T: Into<String>>(mut self, full_arg: T) -> Self {
        self.args.push(full_arg.into());
        self
    }

    fn args_iter(&self) -> std::slice::Iter<'_, String> {
        self.args.iter()
    }

    pub fn build_args(self) -> Vec<String> {
        self.args
    }

    pub fn has_arg(&self, s: &str) -> bool {
        self.args_iter().any(|a| a == s)
    }

    pub(crate) fn run_compiler<'a>(
        &self,
        callbacks: &mut (dyn rustc_driver::Callbacks + Send),
        file_loader: Option<Box<dyn FileLoader + Send + Sync + 'static>>,
    ) -> interface::Result<()> {
        for (k, v) in &self.env {
            std::env::set_var(k, v);
        }
        syntax::with_default_globals(|| {
            rustc_driver::run_compiler(&self.args, callbacks, file_loader, None)
        })?;
        for k in self.env.keys() {
            std::env::set_var(k, "");
        }
        Ok(())
    }
}

// Allow rules files to contain extern crate rerast_macros and a corresponding
// #[macro_use]. Replace these lines if present with empty lines so that the
// rule compiles once it's in the context of a submodule.
fn remove_extern_crate_rerast_from_rules(rules: &str) -> String {
    let mut result = String::new();
    let mut opt_pending_line = None;
    for line in rules.lines() {
        if line.trim() == "#[macro_use] extern crate rerast_macros;" {
            result.push('\n');
        } else if line.trim() == "extern crate rerast_macros;" {
            result.push('\n');
            if opt_pending_line.is_some() {
                result.push('\n');
            }
            opt_pending_line = None;
        } else {
            if let Some(pending_line) = opt_pending_line.take() {
                result.push_str(pending_line);
                result.push('\n');
            }
            if line.trim() == "#[macro_use]" {
                opt_pending_line = Some(line);
            } else {
                result.push_str(line);
                result.push('\n');
            }
        }
    }
    result
}

// We inject our rules as a submodule of the root of the crate. We do this by just appending some
// content to the end of the file. It may be possible to inject our module(s) via a similar
// mechanism to what's used by maybe_inject_crates_ref in libsyntax/std_inject.rs. For now, we go
// with the easier/simpler mechanism.
const RULES_MOD_NAME: &str = "__rerast_rules";
const CODE_FOOTER: &str = stringify!(
    #[macro_use]
    pub mod __rerast_internal;
    #[doc(hidden)]
    pub mod __rerast_rules;
);

// This module is used to help us find the definitions for rerast types that we need.
const RERAST_INTERNAL_MOD_NAME: &str = "__rerast_internal";
const RERAST_INTERNAL: &str = stringify!(
    pub fn rerast_types(
        _: Statements,
        _: _ExprRuleMarker,
        _: _PatternRuleMarker,
        _: _TypeRuleMarker,
        _: _TraitRefRuleMarker,
    ) {
    }
);

pub(crate) fn hir_id_from_path(q_path: &rustc_hir::QPath) -> Option<HirId> {
    use crate::rustc_hir::def::Res;
    if let rustc_hir::QPath::Resolved(None, ref path) = *q_path {
        match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        }
    } else {
        None
    }
}

struct Replacer<'tcx> {
    tcx: TyCtxt<'tcx>,
    rerast_definitions: RerastDefinitions<'tcx>,
    rules: Rules<'tcx>,
    config: Config,
}

impl<'tcx> Replacer<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        rerast_definitions: RerastDefinitions<'tcx>,
        rules: Rules<'tcx>,
        config: Config,
    ) -> Replacer<'tcx> {
        Replacer {
            tcx,
            rerast_definitions,
            rules,
            config,
        }
    }

    #[allow(dead_code)]
    fn print_macro_backtrace(msg: &str, codemap: &SourceMap, span: Span) {
        println!(
            "{}: {}",
            msg,
            codemap
                .span_to_snippet(span)
                .unwrap_or_else(|_| "<Span crosses file boundaries>".to_owned())
        );
        if span.ctxt() == SyntaxContext::root() {
            println!("SyntaxContext::root()");
        }
        for bt in span.macro_backtrace() {
            println!(
                "Expansion of {} from: {}",
                bt.kind.descr(),
                codemap.span_to_snippet(bt.call_site).unwrap()
            );
        }
    }

    fn apply_to_crate(&self, krate: &'tcx rustc_hir::Crate) -> FileRelativeSubstitutions {
        let codemap = self.tcx.sess.source_map();

        let matches = rule_matcher::RuleMatcher::find_matches(
            self.tcx,
            self.rerast_definitions,
            krate,
            &self.rules,
            self.config.clone(),
        );
        let codemap_relative_substitutions =
            rule_matcher::substitions_for_matches(self.tcx, &matches);
        FileRelativeSubstitutions::new(codemap_relative_substitutions, codemap)
    }
}

#[derive(Debug, Default)]
pub struct RerastOutput {
    pub(crate) file_relative_substitutions: FileRelativeSubstitutions,
}

impl RerastOutput {
    pub fn updated_files(
        self,
        file_loader: &dyn FileLoader,
    ) -> io::Result<HashMap<PathBuf, String>> {
        self.file_relative_substitutions.updated_files(file_loader)
    }

    pub fn merge(&mut self, other: RerastOutput) {
        self.file_relative_substitutions
            .merge(other.file_relative_substitutions);
    }
}

struct RerastCompilerCallbacks {
    // This needs to be an Rc because rust CompilerCalls::build_controller doesn't (at the time of
    // writing) provide any relationship between the lifetime of self and the the lifetime of the
    // returned CompileController.
    output: Result<RerastOutput, RerastErrors>,
    config: Config,
    diagnostic_output: errors::DiagnosticOutput,
}

impl rustc_driver::Callbacks for RerastCompilerCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.diagnostic_output =
            rustc::session::DiagnosticOutput::Raw(Box::new(self.diagnostic_output.clone()));
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.session().abort_if_errors();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            self.output = find_and_apply_rules(tcx, &self.config);
        });
        rustc_driver::Compilation::Stop
    }
}

fn find_and_apply_rules<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    config: &Config,
) -> Result<RerastOutput, RerastErrors> {
    let krate = tcx.hir().krate();
    let rerast_definitions = match RerastDefinitionsFinder::find_definitions(tcx, krate) {
        Some(r) => r,
        None => {
            if config.verbose {
                if let rustc_span::FileName::Real(filename) =
                    tcx.sess.source_map().span_to_filename(krate.module.inner)
                {
                    println!(
                        "A build target was skipped due to apparently being empty: {:?}",
                        filename
                    );
                }
            }
            // Most likely the entire compilation target is empty due to a cfg attribute at the
            // root.
            return Ok(RerastOutput::default());
        }
    };
    let rules =
        rule_finder::RuleFinder::find_rules(tcx, rerast_definitions, krate).map_err(|errors| {
            RerastErrors::new(
                errors
                    .into_iter()
                    .map(|error| error.with_snippet(tcx))
                    .collect(),
            )
        })?;
    if config.verbose {
        println!("Found {} rule(s)", rules.len());
    }
    let replacer = Replacer::new(tcx, rerast_definitions, rules, config.clone());
    Ok(RerastOutput {
        file_relative_substitutions: replacer.apply_to_crate(krate),
    })
}

// Searches for variables declared within the search code. For example in the pattern Some(a), "a"
// will be found.
struct DeclaredNamesFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    names: HashMap<Symbol, HirId>,
}

impl<'tcx> DeclaredNamesFinder<'tcx> {
    fn find<T: StartMatch<'tcx>>(tcx: TyCtxt<'tcx>, node: &'tcx T) -> HashMap<Symbol, HirId> {
        let mut finder = DeclaredNamesFinder {
            tcx,
            names: HashMap::new(),
        };
        T::walk(&mut finder, node);
        finder.names
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for DeclaredNamesFinder<'tcx> {
    type Map = rustc::hir::map::Map<'tcx>;

    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<'this, Self::Map> {
        intravisit::NestedVisitorMap::All(&self.tcx.hir())
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat) {
        if let rustc_hir::PatKind::Binding(_, hir_id, ref ident, _) = pat.kind {
            if self.names.insert(ident.name, hir_id).is_some() {
                // TODO: Proper error reporting
                panic!(
                    "Variables declared in the search pattern must all use distinct \
                     names, even in different scopes. The variable {:?} was declared more \
                     than once.",
                    ident
                );
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

fn rust_sysroot() -> Result<String, RerastErrors> {
    // We either compute the sysroot based on the compile-time values of the
    // rustup environment variables RUSTUP_HOME and RUSTUP_TOOLCHAIN, or failing
    // that, we run `rustc --print sysroot` at runtime.
    if let (Some(rustup_home), Some(toolchain)) =
        (option_env!("RUSTUP_HOME"), option_env!("RUSTUP_TOOLCHAIN"))
    {
        Ok((rustup_home.to_owned() + "/toolchains/" + toolchain).into())
    } else {
        match std::process::Command::new("rustc")
            .arg("--print")
            .arg("sysroot")
            .output()
        {
            Ok(out) => {
                // -1 is to remove trailing newline.
                match std::str::from_utf8(&out.stdout[0..out.stdout.len() - 1]) {
                    Ok(sysroot) => Ok(sysroot.to_owned()),
                    Err(err) => Err(RerastErrors::with_message(format!(
                        "`rustc --print sysroot` returned invalid UTF8: {:?}",
                        err
                    ))),
                }
            }
            Err(err) => Err(RerastErrors::with_message(format!(
                "`rustc --print sysroot` failed: {:?}",
                err
            ))),
        }
    }
}

fn run_compiler(
    file_loader: Option<Box<dyn FileLoader + Send + Sync + 'static>>,
    invocation_info: &CompilerInvocationInfo,
    config: Config,
) -> Result<RerastOutput, RerastErrors> {
    let mut callbacks = RerastCompilerCallbacks {
        output: Ok(RerastOutput::default()),
        config,
        diagnostic_output: errors::DiagnosticOutput::new(),
    };
    if invocation_info
        .run_compiler(&mut callbacks, file_loader)
        .is_err()
    {
        return Err(callbacks.diagnostic_output.errors());
    }
    callbacks.output
}

pub struct RerastCompilerDriver {
    invocation_info: CompilerInvocationInfo,
}

impl RerastCompilerDriver {
    pub fn new(invocation_info: CompilerInvocationInfo) -> RerastCompilerDriver {
        RerastCompilerDriver { invocation_info }
    }

    pub fn args(&self) -> &CompilerInvocationInfo {
        &self.invocation_info
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

    pub fn code_filename(&self) -> Option<&str> {
        self.invocation_info
            .args_iter()
            .skip(1)
            .find(|arg| arg.ends_with(".rs"))
            .map(std::convert::AsRef::as_ref)
    }

    // TODO: Consider just removing this method.
    pub fn apply_rules_from_string<T: FileLoader + Send + Sync + 'static>(
        &self,
        rules: String,
        config: Config,
        file_loader: T,
    ) -> Result<RerastOutput, RerastErrors> {
        let rules = remove_extern_crate_rerast_from_rules(&rules);
        self.apply_rules_to_code(file_loader, rules, config)
    }

    fn apply_rules_to_code<T: FileLoader + Send + Sync + 'static>(
        &self,
        file_loader: T,
        rules: String,
        config: Config,
    ) -> Result<RerastOutput, RerastErrors> {
        let sysroot = crate::rust_sysroot()?;
        let invocation_info = self
            .invocation_info
            .clone()
            .arg("--sysroot")
            .arg(sysroot)
            .arg("--allow")
            .arg("dead_code")
            .arg("--allow")
            .arg("deprecated");
        let mut file_loader = box InMemoryFileLoader::new(file_loader);
        // In an ideal world we might get rust to parse the arguments then ask it what the root code
        // filename is. In the absence of being able to do that, this will have to do.
        let code_filename = self.code_filename().ok_or_else(|| {
            RerastErrors::with_message(
                "Couldn't find source filename with .rs extension in the supplied arguments",
            )
        })?;
        if let Some(ref restrict_files) = config.files {
            if !restrict_files.iter().any(|e| e == code_filename) {
                if config.verbose {
                    println!("Skipping {} due to --files", code_filename);
                }
                return Ok(RerastOutput::default());
            }
        }
        let code_path = PathBuf::from(code_filename);
        file_loader.add_file(
            code_path.with_file_name(RULES_MOD_NAME.to_owned() + ".rs"),
            rules,
        );
        file_loader.add_file(
            code_path.with_file_name(RERAST_INTERNAL_MOD_NAME.to_owned() + ".rs"),
            rerast_macros::_RERAST_MACROS_SRC
                .replace(r#"include_str!("lib.rs")"#, r#""""#)
                .replace("$crate", &("crate::".to_owned() + RERAST_INTERNAL_MOD_NAME))
                + RERAST_INTERNAL,
        );
        let code_with_footer = file_loader.read_file(&code_path)? + CODE_FOOTER;

        file_loader.add_file(code_path, code_with_footer);
        run_compiler(Some(file_loader), &invocation_info, config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map;
    use std::io;

    const CODE_FILE_NAME: &str = "code.rs";

    #[derive(Clone)]
    pub(crate) struct NullFileLoader;

    struct TestBuilder {
        common: String,
        rule: String,
        input: String,
        edition: String,
    }

    impl TestBuilder {
        fn new() -> TestBuilder {
            TestBuilder {
                common: String::new(),
                rule: String::new(),
                input: String::new(),
                edition: "2018".to_owned(),
            }
        }

        fn common(mut self, common: &str) -> TestBuilder {
            self.common = common.to_owned();
            self
        }

        fn rule(mut self, rule: &str) -> TestBuilder {
            self.rule = rule.to_owned();
            self
        }

        fn input(mut self, input: &str) -> TestBuilder {
            self.input = input.to_owned();
            self
        }

        fn edition(mut self, edition: &str) -> TestBuilder {
            self.edition = edition.to_owned();
            self
        }

        fn expect(self, expected: &str) {
            let updated_files = self.apply_rule_to_test_code();
            let is_other_filename = |filename| {
                filename != Path::new(CODE_FILE_NAME) && filename != Path::new("common.rs")
            };
            if updated_files.keys().any(is_other_filename) {
                panic!(
                    "Unexpected updates to other files: {:?}",
                    updated_files.keys()
                );
            }
            let new_code = updated_files
                .get(Path::new(CODE_FILE_NAME))
                .expect("File not updated. No match?");
            if new_code != expected {
                println!("result: {}", new_code);
                println!("expect: {}", expected);
            }
            assert_eq!(new_code, expected);
        }

        fn maybe_apply_rule_to_test_code(self) -> Result<HashMap<PathBuf, String>, RerastErrors> {
            let mut file_loader = InMemoryFileLoader::new(NullFileLoader);
            file_loader.add_file("common.rs".to_owned(), self.common);
            let header1 = r#"#![allow(unused_imports)]
                         #![allow(unused_variables)]
                         #![allow(unused_must_use)]
                         #![allow(bare_trait_objects)]
                         "#;
            let header2 = "use crate::common::*;\n";
            let code_header = r#"
               #![feature(box_syntax)]
               #![feature(box_patterns)]
               #![feature(slice_patterns)]
               #![feature(exclusive_range_pattern)]
               #![feature(generators)]
               "#
            .to_owned()
                + header1
                + "#[macro_use]\nmod common;\n"
                + header2;
            let rule_header = header1.to_owned() + "use crate::common;\n" + header2;
            file_loader.add_file(CODE_FILE_NAME.to_owned(), code_header.clone() + &self.input);
            let args = CompilerInvocationInfo::default()
                .arg("rerast_test")
                .arg("--crate-type")
                .arg("lib")
                .arg("--edition")
                .arg(self.edition)
                .arg(CODE_FILE_NAME);
            let driver = RerastCompilerDriver::new(args);
            let output = driver.apply_rules_to_code(
                file_loader.clone(),
                rule_header + &self.rule,
                Config::default(),
            )?;
            let mut updated_files = output.updated_files(&file_loader)?;
            if let hash_map::Entry::Occupied(mut entry) =
                updated_files.entry(PathBuf::from(CODE_FILE_NAME))
            {
                let contents = entry.get_mut();
                assert!(contents.starts_with(&code_header));
                *contents = contents[code_header.len()..].to_owned();
            }
            Ok(updated_files)
        }

        fn apply_rule_to_test_code(self) -> HashMap<PathBuf, String> {
            match self.maybe_apply_rule_to_test_code() {
                Ok(output) => output,
                Err(errors) => {
                    panic!("Got unexpected errors.\n{}\n", errors);
                }
            }
        }

        fn expect_no_match(self) {
            let updated_files = self.apply_rule_to_test_code();
            if !updated_files.is_empty() {
                println!("Unexpected: {:?}", updated_files);
            }
            assert!(updated_files.is_empty());
        }

        fn expect_error(self, expected_message: &str, expected_snippet: &str) {
            match self.maybe_apply_rule_to_test_code() {
                Ok(result) => panic!("Expected error, got:\n{:?}", result),
                Err(errors) => {
                    let errors_vec: Vec<_> = errors.iter().collect();
                    if errors_vec.len() > 1 {
                        panic!(
                            "Unexpectedly got multiple errors ({}).\n{}",
                            errors_vec.len(),
                            errors
                        );
                    }
                    assert_eq!(expected_message, errors_vec[0].message);
                    match errors_vec[0].file_lines {
                        Some(Ok(ref file_lines)) => {
                            assert_eq!(1, file_lines.lines.len());
                            let line_info = &file_lines.lines[0];
                            if let Some(line) = &line_info.code {
                                let snippet: String = line
                                    .chars()
                                    .skip(line_info.start_col)
                                    .take(line_info.end_col - line_info.start_col)
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
                            panic!("Expected error with file lines, but error: {}", error)
                        }
                        None => panic!("Expected error with lines, but got error without lines"),
                    }
                }
            }
        }
    }

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

    fn check(common: &str, rule: &str, input: &str, expected: &str) {
        TestBuilder::new()
            .common(common)
            .rule(rule)
            .input(input)
            .expect(expected);
    }

    fn check_no_match(common: &str, rule: &str, input: &str) {
        TestBuilder::new()
            .common(common)
            .rule(rule)
            .input(input)
            .expect_no_match();
    }

    // Check that we can match and replace a binary operand with placeholders on both sides.
    #[test]
    fn addition_swap_order() {
        TestBuilder::new()
            .rule("fn r(x: i64, y: i64) {replace!(x + y => y + x);}")
            .input("fn bar() -> i64 {return (41 + 2) - (9 + 1);}")
            .expect("fn bar() -> i64 {return (2 + 41) - (1 + 9);}");
    }

    // Make sure things still work on 2015 edition.
    #[test]
    fn addition_swap_order_2015() {
        TestBuilder::new()
            .edition("2015")
            .rule("fn r(x: i64, y: i64) {replace!(x + y => y + x);}")
            .input("fn bar() -> i64 {return (41 + 2) - (9 + 1);}")
            .expect("fn bar() -> i64 {return (2 + 41) - (1 + 9);}");
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
                 fn bar() {replace!(loop {break;} => while true {});}"#,
            "#[allow(while_true)]\n fn f1() {loop {break;}}",
            "#[allow(while_true)]\n fn f1() {while true {}}",
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
        TestBuilder::new()
            .rule(
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
            )
            .expect_error(
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
            r#"use crate::common::*;
                 fn bar(op: Option<Size>, d: i32) {
                   replace!(if let Some(Size {w, h}) = op {w * h} else {d}
                       => op.map(|p| p.area()).unwrap_or_else(|| d));}"#,
            r#"use crate::common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(if let Some(Size {w: w1, h: h1}) = sz {w1 * h1} else {42});
                 }"#,
            r#"use crate::common::*;
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
            r#"use crate::common::*;
                 fn bar(op: Option<Size>, d: i32) {
                   replace!(if let Some(Size {w, h}) = op {w * h} else {d}
                       => op.map(|p| p.area()).unwrap_or_else(|| d));}"#,
            r#"use crate::common::*;
                 fn f1(sz: Option<Size>) {
                     do_stuff(if let Some(Size {h: h1, w: w1}) = sz {w1 * h1} else {42});
                 }"#,
            r#"use crate::common::*;
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

    // Make sure we can't be tricked into not adding parenthesis.
    #[test]
    fn insert_parenthesis_lower_precedence_already_starts_and_ends_with_parenthesis() {
        check(
            "",
            "fn bar() {replace!(42 => (50 - 10) + (1 + 1));}",
            "fn f1() -> i32 {100 / 42}",
            "fn f1() -> i32 {100 / ((50 - 10) + (1 + 1))}",
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
    fn match_macro_replace_question_mark() {
        TestBuilder::new()
            .edition("2015") // try is a keyword in 2018
            .common("pub fn foo() -> Result<i32, i32> {Ok(42)}")
            .rule(
                "use std::fmt::Debug; \
                 fn bar<T, E: Debug>(r: Result<T, E>) -> Result<T, E> {\
                     replace!(try!(r) => r?);
                     unreachable!();
                 }",
            )
            .input("fn f1() -> Result<i32, i32> {try!(foo()); Ok(1)}")
            .expect("fn f1() -> Result<i32, i32> {foo()?; Ok(1)}");
    }

    #[test]
    fn replace_try_2018() {
        TestBuilder::new()
            .edition("2018")
            .common("pub fn foo() -> Result<i32, i32> {Ok(42)}")
            .rule(
                "use std::fmt::Debug; \
                 fn bar<T, E: Debug>(r: Result<T, E>) -> Result<T, E> {\
                     replace!(r#try!(r) => r?);
                     unreachable!();
                 }",
            )
            .input("fn f1() -> Result<i32, i32> {r#try!(foo()); Ok(1)}")
            .expect("fn f1() -> Result<i32, i32> {foo()?; Ok(1)}");
    }

    // Check that when a placeholder matches an expression that is the result of a macro expansion,
    // we correctly take the call-site of that macro.
    #[test]
    fn placeholder_takes_macro_invocation() {
        TestBuilder::new()
            .edition("2015")
            .common(
                r#"pub fn get_result() -> Result<i32, i32> {Ok(42)}
                 pub fn foo(_: i32) {}
                 pub fn bar(_: i32) {}"#,
            )
            .rule("fn rule(a: i32) {replace!(foo(a) => bar(a));}")
            .input("fn f1() -> Result<i32, i32> {foo(try!(get_result())); Ok(1)}")
            .expect("fn f1() -> Result<i32, i32> {bar(try!(get_result())); Ok(1)}");
    }

    // Check that we can match a macro invocation that contains a placeholder that is also a macro
    // invocation.
    #[test]
    fn macro_placeholder_within_matched_macro() {
        TestBuilder::new()
            .edition("2015")
            .common(
                r#"#[macro_export]
                 macro_rules! add {($e1:expr, $e2:expr) => {$e1 + $e2}}
                 pub fn foo() -> Result<i32, i32> {Ok(41)}"#,
            )
            .rule(
                r#"use std::ops::Add;
                 fn rule<T: Add>(a: T, b: T) {
                     replace!(add!(a, b) => a + b);
                 }"#,
            )
            .input("fn f1() -> Result<i32, i32> {Ok(add!(1, try!(foo())))}")
            .expect("fn f1() -> Result<i32, i32> {Ok(1 + try!(foo()))}");
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
            "fn f1(o: Option<i32>) -> Option<i32> {o.map(|v| v - 2)}",
        );
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

    // Checks matching of ?.
    #[test]
    fn match_question_mark() {
        TestBuilder::new()
            .common("pub fn get_result() -> Result<i32, i32> {Ok(42)}")
            .rule(
                r#"fn r<T, E: std::fmt::Debug>(x: Result<T, E>) -> Result<T, E> {
                     replace!(x? => x.unwrap());
                     unreachable!();
                 }"#,
            )
            .input("fn f1() -> Result<i32, i32> {get_result()?; Ok(1)}")
            .expect("fn f1() -> Result<i32, i32> {get_result().unwrap(); Ok(1)}");
    }

    #[test]
    fn replace_with_old_try_macro() {
        TestBuilder::new()
            .edition("2015")
            .common("pub fn get_result() -> Result<i32, i32> {Ok(42)}")
            .rule(
                r#"fn r<T, E>(x: Result<T, E>) -> Result<T, E> {
                     replace!(x? => try!(x));
                     unreachable!();
                 }"#,
            )
            .input("fn f1() -> Result<i32, i32> {get_result()?; Ok(1)}")
            .expect("fn f1() -> Result<i32, i32> {try!(get_result()); Ok(1)}");
    }

    // Makes sure the replacement can be a macro invocation and that it can
    // still contain placeholders.
    #[test]
    fn replace_with_macro_invocation() {
        TestBuilder::new()
            .common("macro_rules! ff { ($e:expr) => {$e + 2}; }")
            .rule("fn r(i: i32) { replace!(i + 2 => ff!(i)); }")
            .input(r#"fn f() {println!("Answer is: {}", 40 + 2);}"#)
            .expect(r#"fn f() {println!("Answer is: {}", ff!(40));}"#)
    }

    #[test]
    fn match_crate_root_reference_2015() {
        TestBuilder::new()
            .edition("2015")
            .rule("fn r() {replace!(::foo::bar() => ::foo::bar2());}")
            .input(
                r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {::foo::bar();}"#,
            )
            .expect(
                r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {::foo::bar2();}"#,
            );
    }

    #[test]
    fn match_crate_root_reference_2018() {
        TestBuilder::new()
            .edition("2018")
            .rule("fn r() {replace!(crate::foo::bar() => crate::foo::bar2());}")
            .input(
                r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {crate::foo::bar();}"#,
            )
            .expect(
                r#"pub mod foo {
                   pub fn bar() {}
                   pub fn bar2() {}
                 }
                 fn f1() {crate::foo::bar2();}"#,
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
        TestBuilder::new()
            .rule(
                r#"pub trait T1 {}
               pub struct T2 {}
               fn r() {replace_trait_ref!(T1 => T2);}"#,
            )
            .expect_error("replace_trait_ref! requires a trait", "T2");
    }

    #[test]
    fn no_match_trait_with_same_name() {
        TestBuilder::new()
            .common("pub trait T1 {} pub trait T2 {}")
            .rule("fn r() {replace_trait_ref!(T1 => T2);}")
            .input(
                r#"mod foo {
                   trait T1 {}
                   fn bar(_: Box<T1>) {}
               }"#,
            )
            .expect_no_match();
    }

    // Tests matching of tuple and reference patterns
    #[test]
    fn tuple_pattern() {
        check(
            stringify!(
                pub struct Foo(pub i32);
                pub struct Bar(pub i32, pub i32);
                pub fn get_foo_tuple() -> (Foo, i32) {
                    (Foo(1), 2)
                }
                pub fn get_bar() -> Bar {
                    Bar(1, 2)
                }
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
                     replace_pattern!(1 ..= 5 = i => 1 .. 6 = i);
                     replace_pattern!(8 .. 10 = i => 8 ..= 9 = i);
                 }"#,
            r#"fn f1(v: i32) -> i32 {
                     match v {
                         1 ..= 5 => {42}
                         8 .. 10 => {41}
                         _ => {40}
                     }
                 }"#,
            r#"fn f1(v: i32) -> i32 {
                     match v {
                         1 .. 6 => {42}
                         8 ..= 9 => {41}
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
            "mod s1 {use crate::common::*; fn r1() {replace!(foo(1) => foo(2));}}",
            "fn f1() {foo(1);}",
            "fn f1() {foo(2);}",
        );
    }

    // If a macro emits an expression twice and we match that expression, we should discard one of
    // the matches.
    #[test]
    fn test_macro_emits_code_twice() {
        check(
            "macro_rules! dupe {($a:expr) => (($a, $a))}",
            "fn r1() {replace!(41 => 42);}",
            "fn f() -> (i32, i32) {dupe!(41)}",
            "fn f() -> (i32, i32) {dupe!(42)}",
        );
    }

    // Verify that using a placeholder multiple times in a search pattern is an error.
    #[test]
    fn error_multiple_bindings() {
        TestBuilder::new()
            .rule("fn r1(a: i32) {replace!(a + a => 42);}")
            .expect_error(
                "Placeholder is bound multiple times. This is not currently permitted.",
                "a",
            );
    }

    // Verify that using a placeholder in a replacement pattern that was never used in the search
    // pattern is an error.
    #[test]
    fn error_unbound_placeholder() {
        TestBuilder::new()
            .rule("fn r1(a: i32) {replace!(42 => a);}")
            .expect_error(
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

    // Match a block where the final expression contains a reference to a
    // variable defined earlier in the block. We used to get this wrong by
    // processing the final expression before the contents of the block. This is
    // kind of rule is not especially likely to be written by a user, but can
    // easily result from macro expansion.
    #[test]
    fn defined_var_referenced_in_block_expr() {
        check(
            "",
            "fn rule() {replace!({let a = 0; a + 1} => {let a = 0; a + 2});}",
            "fn c() -> i32 {{let x = 0;x + 1}}",
            "fn c() -> i32 {{let x = 0; x + 2}}",
        );
    }

    // Functions declared async get restructured, even if they don't contain any
    // actual async code. In particular all the arguments get shadowed by locals
    // with the same name. If we don't handle these locals properly then
    // placeholders won't function.
    #[test]
    fn rule_in_async_fn() {
        check(
            "",
            "pub async fn rule1(r: i32) {replace!(r * 2 => 2 * r);}",
            "fn c(x: i32) -> i32 {x * 2}",
            "fn c(x: i32) -> i32 {2 * x}",
        );
    }

    #[test]
    fn file_and_line_macros() {
        check(
            "macro_rules! foo {() => {file!()}}",
            r#"fn rule() {
                 replace!(file!() => "filename");
                 replace!(line!() => 42);
                 replace!(foo!() => "foo-filename");
               }"#,
            r#"fn f1() {println!("{}{}{}", file!(), line!(), foo!());}"#,
            r#"fn f1() {println!("{}{}{}", "filename", 42, "foo-filename");}"#,
        );
    }

    // Checks that we can match yield expressions. Also checks that a rule
    // declared inside a generator can still make use of placeholders out in the
    // function declaration.
    #[test]
    fn yeild_and_rule_in_generator() {
        check(
            "",
            "fn r1(x: i32) {let _ = || {replace!(yield x => yield x + 1);};}",
            "fn f1() {let _ = || {yield 1i32;};}",
            "fn f1() {let _ = || {yield 1i32 + 1;};}",
        );
    }

    #[test]
    fn entire_replacement_is_placeholder() {
        check(
            "pub fn foo(o: Option<i32>) -> Option<i32> {o}",
            "fn rule(o: Option<i32>) {replace!(foo(o) => o);}",
            "fn f1(opt_i32: Option<i32>) -> Option<i32> {foo(opt_i32)}",
            "fn f1(opt_i32: Option<i32>) -> Option<i32> {opt_i32}",
        );
    }

    #[test]
    fn test_remove_extern_crate_rerast_from_rules() {
        let rules = r#"
            // foo
            #[macro_use] extern crate rerast_macros;
            #[macro_use]
            extern crate foo;
            #[macro_use]
            extern crate rerast_macros;
            // bar"#;
        let rules = remove_extern_crate_rerast_from_rules(rules);
        assert_eq!(
            rules,
            r#"
            // foo

            #[macro_use]
            extern crate foo;


            // bar"#
                .to_owned()
                + "\n"
        );
    }
}
