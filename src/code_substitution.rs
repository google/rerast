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

use syntax::ext::quote::rt::Span;
use syntax::codemap::CodeMap;

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct CodeSubstitution {
    // The span to be replaced.
    pub(crate) span: Span,
    // New code to replace what's at span.
    pub(crate) new_code: String,
    // Whether parenthesis are needed around the substitution.
    pub(crate) needs_parenthesis: bool,
}

impl CodeSubstitution {
    // Take the code represented by base_span and apply all the substitutions, returning the
    // resulting code. Substitutions must be sorted and non-overlapping.
    pub(crate) fn apply<T: Iterator<Item = CodeSubstitution>>(
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
        output.push_str(&codemap.span_to_snippet(base_span.with_lo(span_lo)).unwrap());
        output
    }
}
