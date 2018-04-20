//! Sample input file.

#![deny(missing_docs, warnings)]

// We have two cfg(test) modules to make sure that matches in both get merged correctly with matches
// in the main module.
#[cfg(test)]
mod tests2 {
    #[test]
    fn x() {
        if 1 > 42 {
            assert!(false);
        }
    }
}

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

    #[test]
    fn env() {
        // Make sure some environment variables are set. See issue #9.
        //env!("OUT_DIR");
        env!("CARGO_PKG_VERSION");
        env!("CARGO_PKG_VERSION");
        env!("CARGO_PKG_VERSION_MAJOR");
        env!("CARGO_PKG_VERSION_MINOR");
        env!("CARGO_PKG_VERSION_PATCH");
    }
}
