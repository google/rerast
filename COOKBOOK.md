# Rerast cookbook
Here we've got some examples of things you can do with rerast. If you've got any
more examples, please feel free to send pull requests.

### Replace ```try!(something)``` with ```something?```

```rust
fn rule1<T,E,X: From<E>>(r: Result<T,E>) -> Result<T,X> {
    replace!(try!(r) => r?);
    unreachable!()
}
```
This will change:
```rust
fn get_file_contents(filename: &Path) -> io::Result<String> {
    let mut result = String::new();
    try!(try!(File::open(filename)).read_to_string(&mut result));
    Ok(result)
}
```
Into this:
```rust
fn get_file_contents(filename: &Path) -> io::Result<String> {
    let mut result = String::new();
    File::open(filename)?.read_to_string(&mut result)?;
    Ok(result)
}
```

This rule also shows how to handle rules that have return statements in
them. i.e. specify a return type for your rule function. ```unreachable!()```
can then be used to avoid having to construct an actual value.

### Use accessors instead of direct field access

```rust
fn r(mut p: Point, x: i32, y: i32) {
    replace!(Point{ x: x, y: y } => Point::new(x, y));
    replace!(p.x = x => p.set_x(x));
    replace!(&mut p.x => p.get_mut_x());
    replace!(p.x => p.get_x());
}
```
This will change:

```rust
fn f1(point: Point, point_ref: &Point, mut_point_ref: &mut Point) {
    let p2 = Point { x: 1, y: 2 };
    process_i32(point.x);
    mut_point_ref.x = 1;
    let x = &mut mut_point_ref.x;
    *x = 42;
    process_i32(point_ref.x);
}
```
Into:

```rust
fn f1(point: Point, point_ref: &Point, mut_point_ref: &mut Point) {
    let p2 = Point::new(1, 2);
    process_i32(point.get_x());
    mut_point_ref.set_x(1);
    let x = mut_point_ref.get_mut_x();
    *x = 42;
    process_i32(point_ref.get_x());
}
```

### Remove the argument from a function

[cargo-issue]: https://github.com/rust-lang/cargo/issues/5746
[cargo-pr]: https://github.com/rust-lang/cargo/pull/5752

This is a real world example from the Cargo project ([issue][cargo-issue], [PR][cargo-pr]).

```rust
use cargotest::support::{ project, project_foo };

fn rule1(a: &'static str) {
   replace!(project("foo") => project_foo());
   replace!(project(a) => project_foo().at(a));
}
```

Changes:

```rust
let p = project("foo")
    .file("Cargo.toml", &basic_bin_manifest("foo"))
    .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
    .build();
let _p2 = project("bar")
    .file("Cargo.toml", &basic_bin_manifest("bar"))
    .file("src/bar.rs", &main_file(r#""i am bar""#, &[]))
    .build();
```

Into:

```rust
let p = project_foo()
    .file("Cargo.toml", &basic_bin_manifest("foo"))
    .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
    .build();
let _p2 = project_foo().at("bar")
    .file("Cargo.toml", &basic_bin_manifest("bar"))
    .file("src/bar.rs", &main_file(r#""i am bar""#, &[]))
    .build();
```

When run like this:

```terminal
cargo +nightly rerast --rules_file=rewrite.rs --force --targets tests --file tests/testsuite/main.rs
```

Afterwhich a simple search and replace can rename `project_foo` back to `project` and the argument
can be dropped.
