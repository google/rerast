use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::process::Command;

fn cargo_rerast(crate_root: &str) -> Command {
    // We can't use Assert.current_dir, because then Assert::cargo_binary doesn't work, instead we
    // pass the crate root as an argument and get our binary to change directories once it's
    // running.
    let mut cmd = Command::cargo_bin("cargo-rerast").unwrap();
    cmd.arg("rerast").arg("--crate_root").arg(crate_root);
    cmd
}

#[test]
fn test_help() {
    cargo_rerast(".")
        .arg("--help")
        .assert()
        .success()
        .stdout(predicate::str::contains("cargo rerast"));
}

#[test]
fn test_simple_diff() {
    cargo_rerast("tests/crates/simple")
        // TODO: Remove once #10 is fixed.
        .env("RERAST_FULL_CARGO_CLEAN", "1")
        .arg("-p")
        .arg("p0: i32, p1: i32")
        .arg("-s")
        .arg("p0 > p1")
        .arg("-r")
        .arg("p1 < p0")
        .arg("--diff")
        .arg("--color=never")
        .assert()
        .stdout(predicate::eq(
            r#"--- src/lib.rs
+++ src/lib.rs
@@ -8,7 +8,7 @@
 mod tests2 {
     #[test]
     fn x() {
-        if 1 > 42 {
+        if 42 < 1 {
             assert!(false);
         }
     }

@@ -16,7 +16,7 @@
 
 /// A well documented function.
 pub fn foo(a: i32, b: i32) -> i32 {
-    if a > b {
+    if b < a {
         42
     } else {
         b

@@ -26,7 +26,7 @@
 #[cfg(test)]
 mod tests {
     fn bar(a: i32, b: i32) -> i32 {
-        if a > b {
+        if b < a {
             42
         } else {
             b

"#,
        ));
}

#[test]
fn test_invalid_cargo_toml() {
    cargo_rerast("tests/crates/invalid_cargo_toml")
        .args(&["-s", "file!()", "-r", "\"foo\""])
        .args(&["--diff", "--color=never"])
        .assert()
        .failure()
        .stderr(
            predicate::str::contains("cargo metadata failed")
                .and(predicate::str::contains("could not parse input as TOML")),
        );
}

#[test]
fn test_compilation_error() {
    cargo_rerast("tests/crates/compilation_error")
        .args(&["-s", "file!()", "-r", "\"foo\""])
        .args(&["--diff", "--color=never"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("this is not an i32"));
}
