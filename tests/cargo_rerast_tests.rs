extern crate assert_cli;

fn cargo_rerast(crate_root: &str) -> assert_cli::Assert {
    // We can't use Assert.current_dir, because then Assert::cargo_binary doesn't work, instead we
    // pass the crate root as an argument and get our binary to change directories once it's
    // running.
    assert_cli::Assert::cargo_binary("cargo-rerast").with_args(&[
        "rerast",
        "--crate_root",
        crate_root,
    ])
}

#[test]
fn test_help() {
    cargo_rerast(".")
        .with_args(&["--help"])
        .stdout()
        .contains("cargo rerast")
        .execute()
        .unwrap();
}

#[test]
fn test_simple_diff() {
    cargo_rerast("tests/crates/simple")
        .with_args(&["-p", "p0: i32, p1: i32"])
        .with_args(&["-s", "p0 > p1"])
        .with_args(&["-r", "p1 < p0"])
        .with_args(&["--diff", "--color=never"])
        .stdout()
        .is(r#"
--- src/lib.rs
+++ src/lib.rs
@@ -1,5 +1,5 @@
 pub fn foo(a: i32, b: i32) -> i32 {
-    if a > b {
+    if b < a {
         42
     } else {
         b

@@ -9,7 +9,7 @@
 #[cfg(test)]
 mod tests {
     fn bar(a: i32, b: i32) -> i32 {
-        if a > b {
+        if b < a {
             42
         } else {
             b


"#)
        .unwrap();
}

#[test]
fn test_invalid_cargo_toml() {
    cargo_rerast("tests/crates/invalid_cargo_toml")
        .with_args(&["-s", "file!()", "-r", "\"foo\""])
        .with_args(&["--diff", "--color=never"])
        .stderr()
        .contains("cargo metadata failed")
        .stderr()
        .contains("could not parse input as TOML")
        .fails()
        .unwrap();
}

#[test]
fn test_compilation_error() {
    cargo_rerast("tests/crates/compilation_error")
        .with_args(&["-s", "file!()", "-r", "\"foo\""])
        .with_args(&["--diff", "--color=never"])
        .stderr()
        .contains("this is not an i32")
        .fails()
        .unwrap();
}
