//! Sample input file.

#![deny(missing_docs, warnings)]

/// A well documented function.
pub fn foo(a: i32, b: i32) -> i32 {
    if a > b {
        42
    } else {
        b
    }
}

#[cfg(test)]
mod tests {
    fn bar(a: i32, b: i32) -> i32 {
        if a > b {
            42
        } else {
            b
        }
    }

    #[test]
    fn x() {
        assert_eq!(super::foo(1, 2), bar(1, 2));
    }
}
