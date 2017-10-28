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

#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

extern crate clap;
extern crate json;
extern crate rerast;

use std::io::{self, Write};
use rerast::{ArgBuilder, Config, RerastCompilerDriver};

// Environment variables that we use to pass data from the outer invocation of cargo-rerast through
// to the inner invocation (where it acts as the rust compiler). Eventually we'll hopefully be able
// to query cargo as to what rustc commands are needed to build, then we can use those
// directly. Possibly we could just run "cargo check -v" and collect its output. Either way, we'd
// like to get rid of these as they add unnecessary complexity.
mod var_names {
    pub const RULES_FILE: &'static str = "RERAST_RULES_FILE";
    pub const RULES: &'static str = "RERAST_RULES";
    pub const DIFF_CMD: &'static str = "RERAST_DIFF_CMD";
    pub const DEBUG_SNIPPET: &'static str = "RERAST_DEBUG_SNIPPET";
}

// Queries cargo to find the name of the current crate, then runs cargo clean to
// clean up artifacts for that package (but not dependencies). This is necessary
// in order to ensure that all the files in the current crate actually get built
// when we run cargo check. Hopefully eventually there'll be a nicer way to
// integrate with cargo such that we won't need to do this.
fn clean_local_targets() -> io::Result<()> {
    let output = std::process::Command::new("cargo")
        .args(vec!["metadata", "--no-deps", "--format-version=1"])
        .stdout(std::process::Stdio::piped())
        .output()?;
    let metadata_str = std::str::from_utf8(output.stdout.as_slice()).map_err(|e| {
        io::Error::new(io::ErrorKind::InvalidData, e.to_string())
    })?;
    let parsed = json::parse(metadata_str).map_err(|e| {
        io::Error::new(io::ErrorKind::InvalidData, e.to_string())
    })?;
    for package in parsed["packages"].members() {
        if let Some(name) = package["name"].as_str() {
            std::process::Command::new("cargo")
                .args(vec!["clean", "--package", name])
                .status()?;
        }
    }
    Ok(())
}

fn cargo_rerast() {
    let matches = clap::App::new("Rerast")
        .version("0.1")
        .author("David Lattimore <dml@google.com>")
        .subcommand(
            clap::SubCommand::with_name("rerast")
                .about("Replace Rust code based on typed, syntactic patterns")
                .args_from_usage(
                    "--rules_file=[FILE] 'Path to a rule file'
                     --use_statements=[USE_STATEMENTS] 'Use statements required by rule'
                     --placeholders=[PLACEHOLDERS] 'e.g. <T>(o: option<T>)'
                     --replace=[PATTERN] 'Pattern to search for'
                     --with=[PATTERN] 'Replacement code'
                     --debug_snippet=[CODE_SNIPPET] 'A snippet of code that you think should \
                                                     match or list_all to list all checked \
                                                     snippets.'
                                      \
                     --diff 'Diff changes'
                     --colordiff 'Diff changes with colordiff'",
                ),
        )
        .get_matches();
    if let Some(matches) = matches.subcommand_matches("rerast") {
        // User ran "cargo rerast", invoke cargo build with us as "rustc"
        let rules = if let (Some(search), Some(replacement)) =
            (matches.value_of("replace"), matches.value_of("with"))
        {
            let mut placeholders = matches.value_of("placeholders").unwrap_or("").to_owned();
            if !placeholders.contains('(') {
                placeholders = "(".to_owned() + &placeholders + ")";
            }
            matches.value_of("use_statements").unwrap_or("").to_owned() + "pub fn rule"
                + &placeholders + "{replace!(" + search + " => " + replacement + ");}"
        } else {
            "".to_owned()
        };
        let rules_file = matches.value_of("rules_file").unwrap_or("");
        if rules_file.is_empty() == rules.is_empty() {
            eprintln!("Must specify either --rules_file or both of --search and --replacement");
            std::process::exit(1);
        }
        if matches.is_present("diff") == matches.is_present("colordiff") {
            eprintln!("Currently either --diff or --colordiff must be specified");
            std::process::exit(1);
        }
        // We run cargo with RUSTC_WRAPPER set, so that it then uses us as the compiler. Really what
        // we'd like is to run cargo, asking it to build all the crate dependencies, then tell us
        // the commandline(s) to build all the targets in the current crate. This is pretty
        // ugly. Clippy does something similar, so there probably isn't a better way at the moment.
        // Unfortunately this hack has several consequences. (1) We're invoked separately for each
        // target, which precludes, or would at least make it hard to produce a summary of all
        // matches. (2) Cargo won't run us if the crate has already been built, requiring that we
        // touch the main source file in order to force it to actually run us. (3) If our
        // dependencies haven't already been built, we'll try to look for matches in them - not
        // really what we want. (4) Cargo sometimes prints messages that are either not helpful or
        // outright confusing - e.g. asking the user to add --verbose.
        clean_local_targets().unwrap();
        let cargo_exit_status = std::process::Command::new("cargo")
            .env(
                "RUSTC_WRAPPER",
                std::env::current_exe().expect("env::current_exe() failed"),
            )
            .env(
                var_names::DEBUG_SNIPPET,
                matches.value_of("debug_snippet").unwrap_or(""),
            )
            .env(
                var_names::DIFF_CMD,
                if matches.is_present("diff") {
                    "diff"
                } else if matches.is_present("colordiff") {
                    "colordiff"
                } else {
                    ""
                },
            )
            .env(var_names::RULES, rules)
            .env(var_names::RULES_FILE, rules_file)
            .args(vec!["check"])
            .status()
            .expect("Failed to invoke cargo");
        // Return whatever exit code we got back from cargo or -1 if it was terminated by a signal.
        std::process::exit(cargo_exit_status.code().unwrap_or(-1));
    } else {
        panic!("Unknown mode");
    }
}

pub fn main() {
    let driver = RerastCompilerDriver::new(ArgBuilder::from_args(std::env::args().skip(1)));
    // If cargo is calling us to get compiler configuration or is compiling a dependent crate, then
    // just run the compiler normally.
    if driver.args().has_arg("--print=cfg") || driver.is_compiling_dependency() {
        let args: Vec<_> = std::env::args().skip(2).collect();
        std::process::Command::new("rustc")
            .args(args)
            .status()
            .expect("Failed to run rustc");
    } else if let (Ok(rules_filename), Ok(rules), Ok(debug_snippet)) = (
        std::env::var(var_names::RULES_FILE),
        std::env::var(var_names::RULES),
        std::env::var(var_names::DEBUG_SNIPPET),
    ) {
        let config = Config {
            debug_snippet: debug_snippet,
        };
        match driver.apply_rules_from_string_or_file(rules, &rules_filename, config) {
            Ok(output) => {
                if output.updated_files.is_empty() {
                    println!("No matches found");
                }
                for (filename, new_contents) in output.updated_files {
                    // rustfmt has a native diff built-in. If that were extracted into a separate
                    // crate, we could reuse that instead of calling out to an external diff.
                    if let Ok(diff_cmd) = std::env::var(var_names::DIFF_CMD) {
                        let mut diff_process = std::process::Command::new(diff_cmd)
                            .args(ArgBuilder::new().arg("-u").arg(filename).arg("-").build())
                            .stdin(std::process::Stdio::piped())
                            .spawn()
                            .expect("Failed to run diff command");
                        diff_process
                            .stdin
                            .as_mut()
                            .unwrap()
                            .write_all(new_contents.as_bytes())
                            .expect("Failed to pipe file contents to diff command");
                        diff_process
                            .wait()
                            .expect("Failed waiting for diff command");
                    } else {
                        println!("--- Updated {} ---", filename);
                        println!("{}", new_contents);
                    }
                }
            }
            Err(errors) => {
                eprintln!("{}", errors);
                std::process::exit(1);
            }
        }
    } else if let Some(arg1) = std::env::args().nth(1) {
        if arg1 == "rerast" {
            cargo_rerast();
        }
    }
}
