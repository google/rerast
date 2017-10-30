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

/// Invocations of this macro instruct Rerast to replace the first expression/statement with the one
/// after the =>. For example replace!(5 => 6) says to replace all occurences of the literal 5 with
/// the literal 6.
///
/// The macro should be invoked inside a function definition. The arguments to the function
/// represent placeholders within the search and replace expressions.
#[macro_export]
macro_rules! replace {
    ($a:expr => $b:expr) => {
        // Suppress warnings about unused values in case we're replacing something like a Result.
        #[allow(unused_must_use)]
        // If we have a search or replacement pattern that is just a placeholder then this macro
        // will turn that into a statement. Normally a reference to a variable is not permitted as a
        // statement, allow it.
        #[allow(path_statements)]
        #[allow(unreachable_code)]
        {
            if false {
                use $crate::GetMode;
                match $crate::_ExprRuleMarker.get_mode() {
                    $crate::Mode::Search => {&$a;}
                    $crate::Mode::Replace => {&$b;}
                }
                // Some of the placeholders used in this replace! invocation might have been
                // moved. To avoid use-after-move errors, we mark this as unreachable.
                unreachable!();
            }
        }
    };
}

/// Replaces one type with another. This will not match trait bounds (e.g. in where clauses), since
/// they are not types. If you want to replace all references to a trait, use `replace_trait_ref!`
/// instead.
#[macro_export]
macro_rules! replace_type {
    ($a:ty => $b:ty) => {
        {
            use $crate::GetMode;
            match $crate::_TypeRuleMarker.get_mode() {
                $crate::Mode::Search => {
                    let _t: &$a;
                }
                $crate::Mode::Replace => {
                    let _t: &$b;
                }
            }
        }
    };
}

#[macro_export]
macro_rules! replace_trait_ref {
    ($a:ty => $b:ty) => {
        {
            use $crate::GetMode;
            match $crate::_TraitRefRuleMarker.get_mode() {
                $crate::Mode::Search => {
                    let _t: &$a;
                }
                $crate::Mode::Replace => {
                    let _t: &$b;
                }
            }
        }
    };
}

/// Replaces a pattern with another pattern. A placeholder is required in order to specify the types
/// of the search and replacement pattern. Although they can be the same if you're replacing a
/// pattern with another of the same type.
///
/// # Examples
/// ```
/// # #[macro_use] extern crate rerast;
/// # struct Foo(i32);
/// fn some_foo_to_result_foo(p1: Option<Foo>, p2: Result<Foo, ()>) {
///     replace_pattern!(Some(f1) = p1 => Result::Ok(f1) = p2);
///     replace_pattern!(None = p1 => Result::Err(()) = p2);
/// }
/// # fn main () {}
/// ```
///
/// This will transform:
/// ```
/// # #[derive(Copy, Clone)] struct Foo(i32);
/// # fn f() -> Option<Foo> {Some(Foo(42))}
/// match f() {
///     Some(Foo(x)) => x,
///     None => 0,
/// }
/// ```
/// Into:
/// ```
/// # fn f() -> Foo {Foo(42)}
/// match f() {
///     Result::Ok(Foo(x)) => x,
///     Result::Err(()) => 0,
/// }
/// ```
#[macro_export]
macro_rules! replace_pattern {
    ($a:pat = $at:ident => $b:pat = $bt:ident) => {
        if false {
            use $crate::GetMode;
            match $crate::_PatternRuleMarker.get_mode() {
                $crate::Mode::Search => {
                    if let Some($a) = Some($at) {};
                }
                $crate::Mode::Replace => {
                    if let Some($b) = Some($bt) {};
                }
            }
            // Some of the placeholders used in this replace_pattern! invocation might have been
            // moved. To avoid use-after-move errors, we mark this as unreachable.
            unreachable!();
        }
    }
}

/// A placeholder that matches zero or more statements
/// IMPORTANT: This is currently broken and will most likely be replaced with a macro.
pub type Statements = &'static Fn() -> _Statements;

// These types are internal markers to help rerast find and identify things in rules. They're not
// intended to be referenced directly.
pub enum Mode {
    Search,
    Replace,
}
pub struct _Statements;
pub trait GetMode {
    fn get_mode(&self) -> Mode {
        Mode::Search
    }
}
pub struct _TypeRuleMarker;
impl GetMode for _TypeRuleMarker {}
pub struct _ExprRuleMarker;
impl GetMode for _ExprRuleMarker {}
pub struct _PatternRuleMarker;
impl GetMode for _PatternRuleMarker {}
pub struct _TraitRefRuleMarker;
impl GetMode for _TraitRefRuleMarker {}

pub const _RERAST_MACROS_SRC: &'static str = include_str!("lib.rs");
