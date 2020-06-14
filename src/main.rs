// Copyright 2020 Google Inc.
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

use argh::FromArgs;
use fmt::Debug;
use ra_db::{FileId, FileRange};
use ra_syntax::ast::{self, AstNode};
use ra_syntax::{SyntaxNode, TextSize};
use std::fmt;

mod matching;
mod patterns;
mod replacing;

use matching::{Match, SearchTrees};

#[derive(Debug, Eq, PartialEq)]
struct Error {
    message: String,
}

/// Searches a crate for pattern matches and possibly replaces them with something else.
struct MatchFinder<'db> {
    /// If set, any nodes that match this string exactly will be considered as nodes that we
    /// expected to match. For such nodes, we'll print additional debugging information and if
    /// matching fails, we'll collect and report the reason why.
    debug_snippet: Option<String>,
    /// Our source of information about the user's code.
    sema: ra_hir::Semantics<'db, ra_ide_db::RootDatabase>,
}

/// Information about the search we're currently doing. We enter a nested scope each time we encounter a macro call. The inner scope
struct SearchScope<'a> {
    search: &'a SearchTrees,
    root_module: &'a ra_hir::Module,
    restrict_range: Option<FileRange>,
}

impl Error {
    fn new(message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl<'db> MatchFinder<'db> {
    fn new(debug_snippet: Option<String>, db: &'db ra_ide_db::RootDatabase) -> MatchFinder<'db> {
        MatchFinder {
            debug_snippet,
            sema: ra_hir::Semantics::new(db),
        }
    }

    fn root_module(&self, node: &SyntaxNode) -> Result<ra_hir::Module, Error> {
        self.sema
            .scope(node)
            .module()
            .ok_or_else(|| Error::new("Failed to get root module"))
    }

    fn find_matches(
        &self,
        search_scope: &SearchScope,
        code: &SyntaxNode,
        matches_out: &mut Vec<Match>,
    ) {
        let debug_active =
            self.debug_snippet.is_some() && Some(code.text().to_string()) == self.debug_snippet;
        if debug_active {
            if let Ok(tree) = search_scope.search.tree_for_kind(code.kind()) {
                println!("========= PATTERN ==========\n{:#?}", tree);
            }

            println!(
                "\n============ AST ===========\n\
                {:#?}\n============================",
                code
            );
        }
        if let Some(mut m) = matching::get_match(debug_active, search_scope, &code, &self.sema) {
            // Continue searching in each of our placeholders.
            for placeholder_value in m.placeholder_values.values_mut() {
                if let Some(placeholder_node) = &placeholder_value.node {
                    // Don't search our placeholder if it's the entire matched node, otherwise we'd
                    // find the same match over and over until we got a stack overflow.
                    if placeholder_node != code {
                        self.find_matches(
                            search_scope,
                            placeholder_node,
                            &mut placeholder_value.inner_matches,
                        );
                    }
                }
            }
            matches_out.push(m);
            return;
        }
        // If we've got a macro call, we already tried matching it pre-expansion, which is the only
        // way to match the whole macro, now try expanding it and matching the expansion.
        if let Some(macro_call) = ast::MacroCall::cast(code.clone()) {
            if let Some(expanded) = self.sema.expand(&macro_call) {
                if let Some(tt) = macro_call.token_tree() {
                    // When matching within a macro expansion, we only want to allow matches of
                    // nodes that originated entirely from within the token tree of the macro call.
                    // i.e. we don't want to match something that came from the macro itself.
                    self.find_matches(
                        &SearchScope {
                            restrict_range: Some(self.sema.original_range(tt.syntax())),
                            ..*search_scope
                        },
                        &expanded,
                        matches_out,
                    );
                }
            }
        }
        for child in code.children() {
            self.find_matches(search_scope, &child, matches_out);
        }
    }

    fn find_match_str(&self, pattern_str: &str, file_id: FileId) -> Result<Vec<String>, Error> {
        let mut matches = Vec::new();
        let file = self.sema.parse(file_id);
        let code = file.syntax();
        self.find_matches(
            &SearchScope {
                search: &SearchTrees::new(&patterns::parse_pattern(pattern_str, true)?),
                root_module: &self.root_module(code)?,
                restrict_range: None,
            },
            code,
            &mut matches,
        );
        let mut flattened_matches = Vec::new();
        flatten_matches(&matches, &mut flattened_matches);
        return Ok(flattened_matches);
    }

    fn apply_str(
        &self,
        search: &str,
        replacement: &str,
        file_id: FileId,
    ) -> Result<Option<String>, Error> {
        let search = patterns::parse_pattern(search, true)?;
        let replacement = patterns::parse_pattern(replacement, false)?;
        patterns::validate_rule(&search, &replacement)?;
        let file = self.sema.parse(file_id);
        let code = file.syntax();
        let mut matches = Vec::new();
        self.find_matches(
            &SearchScope {
                search: &SearchTrees::new(&search),
                root_module: &self.root_module(code)?,
                restrict_range: None,
            },
            code,
            &mut matches,
        );
        if matches.is_empty() {
            return Ok(None);
        }
        use ra_db::FileLoader;
        let mut file_source = self.sema.db.file_text(file_id).to_string();
        let edit =
            replacing::matches_to_edit(&matches, &replacement, &file_source, TextSize::from(0));
        edit.apply(&mut file_source);
        Ok(Some(file_source))
    }
}

fn flatten_matches(matches: &[Match], flattened_matches: &mut Vec<String>) {
    for m in matches {
        println!("M: {}", m.matched_node.text());
        flattened_matches.push(m.matched_node.text().to_string());
        for p in m.placeholder_values.values() {
            if let Some(n) = &p.node {
                println!("  P: {}", n.text());
            }
            flatten_matches(&p.inner_matches, flattened_matches);
        }
    }
}

/// Searches for and replaces code based on token trees.
#[derive(FromArgs)]
struct RerastConfig {
    /// pattern to search for.
    #[argh(option, short = 's')]
    search: String,

    /// what to replace matches with.
    #[argh(option)]
    replace: Option<String>,

    /// code in which to search.
    #[argh(option)]
    code: String,

    /// a snippet of code that you expect to match. When exactly this snippet is encountered, debug
    /// information will be printed during matching.
    #[argh(option)]
    debug_snippet: Option<String>,
}

fn single_file(code: &str) -> (ra_ide_db::RootDatabase, FileId) {
    use ra_db::fixture::WithFixture;
    ra_ide_db::RootDatabase::with_single_file(code)
}

fn main() -> Result<(), Error> {
    let config: RerastConfig = argh::from_env();
    let (db, file_id) = single_file(&config.code);
    let match_finder = MatchFinder::new(config.debug_snippet, &db);
    if let Some(replace) = &config.replace {
        if let Some(rewritten) = match_finder.apply_str(&config.search, replace, file_id)? {
            println!("OUT: {}", rewritten);
        } else {
            println!("No replacement occurred");
        }
    } else {
        let matches = match_finder.find_match_str(&config.search, file_id)?;
        if matches.is_empty() {
            println!("No match found");
        } else {
            println!("Matches:");
            for m in matches {
                println!("{}", m);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find(pattern: &str, code: &str) -> Vec<String> {
        let (db, file_id) = single_file(code);
        let match_finder = MatchFinder::new(None, &db);
        match_finder.find_match_str(pattern, file_id).unwrap()
    }

    fn assert_matches(pattern: &str, code: &str, expected: &[&str]) {
        if !expected.is_empty() {
            println!(
                "If this test fails, run the following to debug it:\
                    \n  cargo run -- --code '{}' --search '{}' --debug-snippet '{}'",
                code, pattern, &expected[0]
            );
        }
        let r = find(pattern, code);
        assert_eq!(r, expected);
    }

    fn assert_no_match(pattern: &str, code: &str) {
        assert_matches(pattern, code, &[]);
    }

    fn apply(search: &str, replace: &str, code: &str) -> Result<Option<String>, Error> {
        let (db, file_id) = single_file(code);
        let match_finder = MatchFinder::new(None, &db);
        match_finder.apply_str(search, replace, file_id)
    }

    fn assert_replace(search: &str, replace: &str, code: &str, expected: &str) {
        let out = apply(search, replace, code).unwrap();
        if out != Some(expected.to_owned()) {
            println!(
                "Test is about to fail, to debug run (ideally with --debug-snippet set as well):\
                \n  cargo run -- --search '{}' --replace '{}' --code '{}'",
                search, replace, code,
            );
            if let Some(out) = out {
                println!("Expected:\n{}\n\nActual:\n{}\n", expected, out);
            } else {
                panic!("No replacement occurred");
            }
            panic!("Test failed, see above for details");
        }
    }

    #[test]
    fn ignores_whitespace() {
        assert_matches("1+2", "fn f() -> i32 {1  +  2}", &["1  +  2"]);
        assert_matches("1 + 2", "fn f() -> i32 {1+2}", &["1+2"]);
    }

    #[test]
    fn no_match() {
        assert_no_match("1 + 3", "fn f() -> i32 {1  +  2}");
    }

    #[test]
    fn match_fn_definition() {
        assert_matches(
            "fn $a($b: $t) {$c}",
            "fn f(a: i32) {bar()}",
            &["fn f(a: i32) {bar()}"],
        );
    }

    #[test]
    fn match_struct_definition() {
        assert_matches(
            "struct $n {$f: Option<String>}",
            "struct Bar {} struct Foo {name: Option<String>}",
            &["struct Foo {name: Option<String>}"],
        );
    }

    #[test]
    fn match_expr() {
        let code = "fn f() -> i32 {foo(40 + 2, 42)}";
        assert_matches("foo($a, $b)", code, &["foo(40 + 2, 42)"]);
        assert_no_match("foo($a, $b, $c)", code);
        assert_no_match("foo($a)", code);
    }

    // Make sure that when a placeholder has a choice of several nodes that it could consume, that
    // it doesn't consume too early and then fail the rest of the match.
    #[test]
    fn match_nested_method_calls() {
        assert_matches(
            "$a.z().z().z()",
            "fn f() {h().i().j().z().z().z().d().e()}",
            &["h().i().j().z().z().z()"],
        );
    }

    // Make sure that our node matching semantics don't differ within macro calls.
    #[test]
    fn match_nested_method_calls_with_macro_call() {
        assert_matches(
            "$a.z().z().z()",
            r#"
                macro_rules! m1 { ($a:expr) => {$a}; }
                fn f() {m1!(h().i().j().z().z().z().d().e())}"#,
            &["h().i().j().z().z().z()"],
        );
    }

    #[test]
    fn match_complex_expr() {
        let code = "fn f() -> i32 {foo(bar(40, 2), 42)}";
        assert_matches("foo($a, $b)", code, &["foo(bar(40, 2), 42)"]);
        assert_no_match("foo($a, $b, $c)", code);
        assert_no_match("foo($a)", code);
        assert_matches("bar($a, $b)", code, &["bar(40, 2)"]);
    }

    // Trailing commas in the code should be ignored.
    #[test]
    fn match_with_trailing_commas() {
        // Code has comma, pattern doesn't.
        assert_matches("foo($a, $b)", "fn f() {foo(1, 2,);}", &["foo(1, 2,)"]);
        assert_matches("Foo{$a, $b}", "fn f() {Foo{1, 2,};}", &["Foo{1, 2,}"]);

        // Pattern has comma, code doesn't.
        assert_matches("foo($a, $b,)", "fn f() {foo(1, 2);}", &["foo(1, 2)"]);
        assert_matches("Foo{$a, $b,}", "fn f() {Foo{1, 2};}", &["Foo{1, 2}"]);
    }

    #[test]
    fn match_type() {
        assert_matches("i32", "fn f() -> i32 {1  +  2}", &["i32"]);
        assert_matches("Option<$a>", "fn f() -> Option<i32> {42}", &["Option<i32>"]);
        assert_no_match("Option<$a>", "fn f() -> Result<i32, ()> {42}");
    }

    #[test]
    fn match_struct_instantiation() {
        assert_matches(
            "Foo {bar: 1, baz: 2}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            &["Foo {bar: 1, baz: 2}"],
        );
        // Now with placeholders for all parts of the struct. If we're not careful here, then $a
        // will consume the whole record field (`bar: 1`) then the `:` in the pattern will fail to
        // match.
        assert_matches(
            "Foo {$a: $b, $c: $d}",
            "fn f() {Foo {bar: 1, baz: 2}}",
            &["Foo {bar: 1, baz: 2}"],
        );
        assert_matches("Foo {}", "fn f() {Foo {}}", &["Foo {}"]);
    }

    #[test]
    fn match_path() {
        assert_matches("foo::bar", "fn f() {foo::bar(42)}", &["foo::bar"]);
        assert_matches("$a::bar", "fn f() {foo::bar(42)}", &["foo::bar"]);
        assert_matches("foo::$b", "fn f() {foo::bar(42)}", &["foo::bar"]);
    }

    #[test]
    fn match_pattern() {
        assert_matches(
            "Some($a)",
            "fn f() {if let Some(x) = foo() {}}",
            &["Some(x)"],
        );
    }

    // If our pattern has a full path, e.g. a::b::c() and the code has c(), but c resolves to
    // a::b::c, then we should match.
    #[test]
    fn match_fully_qualified_fn_path() {
        let code = r#"
            mod a {
                mod b {
                    fn c() {}
                }
            }
            use a::b::c;
            fn f1() {
                c(42);
            }
            "#;
        assert_matches("a::b::c($a)", code, &["c(42)"]);
    }

    #[test]
    fn match_resolved_type_name() {
        let code = r#"
            mod m1 {
                pub mod m2 {
                    pub trait Foo<T> {}
                }
            }
            mod m3 {
                trait Foo<T> {}
                fn f1(f: Option<&dyn Foo<bool>>) {}
            }
            mod m4 {
                use crate::m1::m2::Foo;
                fn f1(f: Option<&dyn Foo<i32>>) {}
            }
            "#;
        assert_matches("m1::m2::Foo<$t>", code, &["Foo<i32>"]);
    }

    #[test]
    fn match_resolved_pat_type() {
        let code = r#"
            mod m1 {
                pub mod m2 {
                    pub enum Animal {Cat, Dog(i32)}
                }
            }
            mod m3 {
                pub enum Animal {Cat, Dog(i32)}
                fn f1(a1: Animal) {
                    if let Animal::Dog(5) = a1 {}
                }
            }
            mod m4 {
                use crate::m1::m2::Animal;
                fn f1(a2: Animal) {
                    if let Animal::Dog(42) = a2 {}
                }
            }
            "#;
        // The matches all from from m4, since the more or less identical code in m3 has a different
        // Animal type. We match the function argument `a2`, the destructuring pattern and the
        // variable reference.
        assert_matches(
            "${a:type(m1::m2::Animal)}",
            code,
            &["a2", "Animal::Dog(42)", "a2"],
        );
    }

    #[test]
    fn literal_constraint() {
        let code = r#"
            fn f1() {
                let x1 = Some(42);
                let x2 = Some("foo");
                let x3 = Some(x1);
                let x4 = Some(40 + 2);
                let x5 = Some(true);
            }
            "#;
        assert_matches(
            "Some(${a:kind(literal)})",
            code,
            &["Some(42)", "Some(\"foo\")", "Some(true)"],
        );
        assert_matches(
            "Some(${a:not(kind(literal))})",
            code,
            &["Some(x1)", "Some(40 + 2)"],
        );
    }

    #[test]
    fn match_reordered_struct_instantiation() {
        assert_matches(
            "Foo {aa: 1, b: 2, ccc: 3}",
            "fn f() {Foo {b: 2, ccc: 3, aa: 1}}",
            &["Foo {b: 2, ccc: 3, aa: 1}"],
        );
        assert_no_match("Foo {a: 1}", "fn f() {Foo {b: 1}}");
        assert_no_match("Foo {a: 1}", "fn f() {Foo {a: 2}}");
        assert_no_match("Foo {a: 1, b: 2}", "fn f() {Foo {a: 1}}");
        assert_no_match("Foo {a: 1, b: 2}", "fn f() {Foo {b: 2}}");
        assert_no_match("Foo {a: 1, }", "fn f() {Foo {a: 1, b: 2}}");
        assert_no_match("Foo {a: 1, z: 9}", "fn f() {Foo {a: 1}}");
    }

    #[test]
    fn match_macro_invocation() {
        assert_matches("foo!($a)", "fn() {foo(foo!(foo()))}", &["foo!(foo())"]);
        assert_matches(
            "foo!(41, $a, 43)",
            "fn() {foo!(41, 42, 43)}",
            &["foo!(41, 42, 43)"],
        );
        assert_no_match("foo!(50, $a, 43)", "fn() {foo!(41, 42, 43}");
        assert_no_match("foo!(41, $a, 50)", "fn() {foo!(41, 42, 43}");
        assert_matches("foo!($a())", "fn() {foo!(bar())}", &["foo!(bar())"]);
    }

    // When matching within a macro expansion, we only allow matches of nodes that originated from
    // the macro call, not from the macro definition.
    #[test]
    fn no_match_expression_from_macro() {
        assert_no_match(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    () => {42.clone()}
                }
                fn f1() {m1!()}
                "#,
        );
    }

    // We definitely don't want to allow matching of an expression that part originates from the
    // macro call `42` and part from the macro definition `.clone()`.
    #[test]
    fn no_match_split_expression() {
        assert_no_match(
            "${a:type(i32)}.clone()",
            r#"
                macro_rules! m1 {
                    ($x:expr) => {$x.clone()}
                }
                fn f1() {m1!(42)}
                "#,
        );
    }

    #[test]
    fn expression_type_constraints() {
        let code = r#"
            mod m1 {
                pub mod m2 {
                    #[derive(Clone)]
                    struct Foo {}
                }
                fn f1() -> m2::Foo {
                    m2::Foo {}
                }
            }
            fn f2() {
                String::new().clone();
                true.clone();
                m1::f1().clone();
            }
            "#;
        assert_matches(
            "${a:type(m1::m2::Foo)}.clone()",
            code,
            &["m1::f1().clone()"],
        );
        assert_no_match("${a:type(m1::m2::Bar)}.clone()", code);
        assert_matches("${a:type(bool)}.clone()", code, &["true.clone()"]);
    }

    #[test]
    fn replace_function_call() {
        assert_replace(
            "foo()",
            "bar()",
            "fn f1() {foo(); foo();}",
            "fn f1() {bar(); bar();}",
        );
    }

    #[test]
    fn replace_function_call_with_placeholders() {
        assert_replace(
            "foo($a, $b)",
            "bar($b, $a)",
            "fn f1() {foo(5, 42)}",
            "fn f1() {bar(42, 5)}",
        );
    }

    #[test]
    fn replace_nested_function_calls() {
        assert_replace(
            "foo($a)",
            "bar($a)",
            "fn f1() {foo(foo(42))}",
            "fn f1() {bar(bar(42))}",
        );
    }

    #[test]
    fn replace_type() {
        assert_replace(
            "Result<(), $a>",
            "Option<$a>",
            "fn f1() -> Result<(), Vec<Error>> {foo()}",
            "fn f1() -> Option<Vec<Error>> {foo()}",
        );
    }

    #[test]
    fn replace_struct_init() {
        assert_replace(
            "Foo {a: $a, b: $b}",
            "Foo::new($a, $b)",
            "fn f1() {Foo{b: 1, a: 2}}",
            "fn f1() {Foo::new(2, 1)}",
        );
    }

    #[test]
    fn replace_macro_invocations() {
        assert_replace(
            "try!($a)",
            "$a?",
            "fn f1() -> Result<(), E> {bar(try!(foo()));}",
            "fn f1() -> Result<(), E> {bar(foo()?);}",
        );
        assert_replace(
            "foo!($a($b))",
            "foo($b, $a)",
            "fn f1() {foo!(abc(def() + 2));}",
            "fn f1() {foo(def() + 2, abc);}",
        );
    }

    #[test]
    fn match_within_macro_invocation() {
        let code = r#"
                macro_rules! foo {
                    ($a:stmt; $b:expr) => {
                        $b    
                    };
                }
                struct A {}
                impl A {
                    fn bar() {}
                }
                fn f1() {
                    let aaa = A {};
                    foo!(macro_ignores_this(); aaa.bar());
                }
            "#;
        assert_matches("$a.bar()", code, &["aaa.bar()"]);
    }

    // We support matching of whole macros pre-expansion. We also support matching nodes
    // post-expansion. However post expansion, no macro calls are present, so if there's a macro
    // call within a macro call, we currently can't match it. It would probably be possible to
    // implement provided the search pattern didn't start or end with a placeholder.
    #[test]
    #[ignore]
    fn match_nested_macro_invocations() {
        assert_matches(
            "try!($a)",
            "fn f1() {other_macro!(bar(try!(foo())));",
            &["try!(foo())"],
        );
    }

    #[test]
    #[ignore]
    fn replace_nested_macro_invocations() {
        assert_replace(
            "try!($a)",
            "$a?",
            "fn f1() {try!(bar(try!(foo())));",
            "fn f1() {bar(foo()?)?;}",
        );
    }

    #[test]
    fn undefined_placeholder_in_replacement() {
        assert_eq!(
            apply("42", "$a", "fn f() ->i32 {42}"),
            Err(Error::new(
                "Replacement contains undefined placeholders: $a"
            ))
        );
        assert_eq!(
            apply("43", "$a", "fn f() ->i32 {42}"),
            Err(Error::new(
                "Replacement contains undefined placeholders: $a"
            ))
        );
    }

    #[test]
    fn replace_within_macro_invocation() {
        let code = r#"
                macro_rules! foo {
                    ($a:stmt; $b:expr) => {
                        $b
                    };
                }
                struct A {}
                impl A {
                    fn bar() {}
                }
                fn f1() -> i32 {
                    let aaa = A {};
                    foo!(macro_ignores_this(); aaa.bar());
                    foo!(macro_ignores_this(); 1 + 2 + 3);
                    1 + 2 + 3
                }
            "#;
        assert_replace(
            "$a.bar()",
            "bar2($a)",
            code,
            &code.replace("aaa.bar()", "bar2(aaa)"),
        );
        assert_replace(
            "$a + $b",
            "$b - $a",
            code,
            &code.replace("1 + 2 + 3", "3 - 2 - 1"),
        );
    }

    #[test]
    fn duplicate_placeholders() {
        assert_eq!(
            apply("foo($a, $a)", "42", "fn f() {}"),
            Err(Error::new("Duplicate placeholder: $a"))
        );
    }

    #[test]
    fn replace_binary_op() {
        assert_replace(
            "$a + $b",
            "$b + $a",
            "fn f() {2 * 3 + 4 * 5}",
            "fn f() {4 * 5 + 2 * 3}",
        );
        assert_replace(
            "$a + $b",
            "$b + $a",
            "fn f() {1 + 2 + 3 + 4}",
            "fn f() {4 + 3 + 2 + 1}",
        );
    }

    #[test]
    fn match_binary_op() {
        assert_matches(
            "$a + $b",
            "fn f() {1 + 2 + 3 + 4}",
            &["1 + 2 + 3 + 4", "1 + 2 + 3", "1 + 2"],
        );
    }
}
