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

use json::{JsonError, JsonValue};
use std::io::{self, Write};
use rerast::{ArgBuilder, Config, RerastCompilerDriver};
use std::str::Utf8Error;
use std::fs;
use clap::ArgMatches;

#[derive(Clone, Debug)]
struct Error {
    message: String,
}

impl Error {
    fn new<T: Into<String>>(message: T) -> Error {
        Error {
            message: message.into(),
        }
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Error {
        Error::new(error.to_string())
    }
}

impl From<JsonError> for Error {
    fn from(error: JsonError) -> Error {
        Error::new(error.to_string())
    }
}

impl From<Utf8Error> for Error {
    fn from(error: Utf8Error) -> Error {
        Error::new(error.to_string())
    }
}

// Environment variables that we use to pass data from the outer invocation of cargo-rerast through
// to the inner invocation which runs within cargo check.
mod var_names {
    // Environment variable name, which if set, indicates that we should write our arguments out as
    // JSON before running the actual rust compiler. Hopefully eventually cargo will have a way for
    // us to query the compile commandlines without doing this sort of thing.
    pub const PRINT_ARGS_JSON: &'static str = "RERAST_PRINT_ARGS_JSON";
}

const JSON_ARGS_MARKER: &'static str = "RUSTC_ARGS_AS_JSON: ";

// Queries cargo to find the name of the current crate, then runs cargo clean to
// clean up artifacts for that package (but not dependencies). This is necessary
// in order to ensure that all the files in the current crate actually get built
// when we run cargo check. Hopefully eventually there'll be a nicer way to
// integrate with cargo such that we won't need to do this.
fn clean_local_targets() -> Result<(), Error> {
    let output = std::process::Command::new("cargo")
        .args(vec!["metadata", "--no-deps", "--format-version=1"])
        .stdout(std::process::Stdio::piped())
        .output()?;
    let metadata_str = std::str::from_utf8(output.stdout.as_slice())?;
    let parsed = json::parse(metadata_str)?;
    for package in parsed["packages"].members() {
        if let Some(name) = package["name"].as_str() {
            std::process::Command::new("cargo")
                .args(vec!["clean", "--package", name])
                .status()?;
        }
    }
    Ok(())
}

fn get_rustc_commandlines_for_local_package() -> Result<Vec<Vec<String>>, Error> {
    clean_local_targets()?;
    let current_exe = std::env::current_exe().expect("env::current_exe() failed");
    let cargo_check_output = std::process::Command::new("cargo")
        .env(var_names::PRINT_ARGS_JSON, "yes")
        .env("RUSTC_WRAPPER", current_exe)
        .args(vec!["check", "-v"])
        .stdout(std::process::Stdio::piped())
        .output()
        .expect("Failed to invoke cargo");
    let output_str = std::str::from_utf8(cargo_check_output.stdout.as_slice())
        .map_err(|e| Error::new(e.to_string()))?;
    if cargo_check_output.status.code() != Some(0) {
        return Err(Error::new(format!(
            "cargo check failed (exit code = {}). Output follows:\n{}",
            cargo_check_output
                .status
                .code()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "signal".to_owned()),
            output_str
        )));
    }
    let mut result: Vec<Vec<String>> = Vec::new();
    for line in output_str.lines() {
        if line.starts_with(JSON_ARGS_MARKER) {
            let parsed = json::parse(&line[JSON_ARGS_MARKER.len()..]).map_err(|e| {
                io::Error::new(io::ErrorKind::InvalidData, e.to_string())
            })?;
            if let JsonValue::Array(values) = parsed {
                let args: Result<Vec<String>, Error> = values
                    .into_iter()
                    .map(|v| if let Some(s) = v.as_str() {
                        Ok(s.to_owned())
                    } else {
                        Err(Error::new(format!("Expected JSON string, got: {:?}", v)))
                    })
                    .collect();
                result.push(args?);
            }
        }
    }
    Ok(result)
}

enum Action {
    Diff(String),
    ForceWrite { backup: bool },
}

impl Action {
    fn from_matches(matches: &ArgMatches) -> Result<Action, Error> {
        let mut actions = Vec::new();
        if matches.is_present("diff") {
            actions.push(Action::Diff("diff -u".to_owned()))
        }
        if let Some(diff_cmd) = matches.value_of("diff_cmd") {
            actions.push(Action::Diff(diff_cmd.to_owned()));
        }
        if matches.is_present("force") {
            actions.push(Action::ForceWrite {
                backup: matches.is_present("backup"),
            })
        }
        if actions.len() > 1 {
            actions.clear();
        }
        actions.into_iter().next().ok_or_else(|| {
            Error::new("Exactly one of --diff, --diff_cmd or --force is currently required")
        })
    }

    fn process(&self, filename: &str, new_contents: &str) -> Result<(), Error> {
        match *self {
            Action::Diff(ref diff_cmd) => {
                // rustfmt has a native diff built-in. If that were extracted into a separate crate,
                // we could reuse that instead of calling out to an external diff.
                let mut diff_cmd_iter = diff_cmd.split(" ");
                let command = diff_cmd_iter.next().unwrap_or("diff");
                let mut diff_process = std::process::Command::new(command)
                    .args(
                        ArgBuilder::from_args(diff_cmd_iter)
                            .arg(filename)
                            .arg("-")
                            .build(),
                    )
                    .stdin(std::process::Stdio::piped())
                    .spawn()
                    .map_err(|e| {
                        io::Error::new(e.kind(), format!("Error running '{}': {}", diff_cmd, e))
                    })?;
                diff_process
                    .stdin
                    .as_mut()
                    .unwrap()
                    .write_all(new_contents.as_bytes())?;
                diff_process.wait()?;
            }
            Action::ForceWrite { backup } => {
                // Write to a temporary file so that we don't truncate the file if writing fails.
                let tmp_file = "rerast-tmp";
                fs::File::create(tmp_file)?.write_all(new_contents.as_bytes())?;
                if backup {
                    fs::rename(filename, filename.to_owned() + ".bk")?;
                }
                fs::rename(tmp_file, filename)?;
            }
        }
        Ok(())
    }
}

fn cargo_rerast() -> Result<(), Error> {
    let matches = clap::App::new("Rerast")
        .version("0.1")
        .author("David Lattimore <dml@google.com>")
        .subcommand(
            clap::SubCommand::with_name("rerast")
                .about("Replace Rust code based on typed, syntactic patterns")
                .args_from_usage(
                    "--rules_file=[FILE] 'Path to a rule file'
                     --use=[USE_STATEMENT]... 'Use statements required by rule'
                     --placeholders=[PLACEHOLDERS] 'e.g. <T>(o: option<T>)'
                     --replace=[PATTERN] 'Pattern to search for'
                     --with=[PATTERN] 'Replacement code'
                     --diff_cmd=[COMMAND] 'Diff changes with the specified diff command'
                     --debug_snippet=[CODE_SNIPPET] 'A snippet of code that you think should \
                                                     match or list_all to list all checked \
                                                     snippets.'
                                      \
                     --diff 'Diff changes'
                     --force 'Overwrite files',
                     --backup 'Rename old files with a .bk extension',
                     --verbose 'Print additional information about what's happening'",
                ),
        )
        .get_matches();
    if let Some(matches) = matches.subcommand_matches("rerast") {
        let config = Config {
            verbose: matches.is_present("verbose"),
            debug_snippet: matches.value_of("debug_snippet").unwrap_or("").to_owned(),
        };
        let rules = if let (Some(search), Some(replacement)) =
            (matches.value_of("replace"), matches.value_of("with"))
        {
            let mut placeholders = matches.value_of("placeholders").unwrap_or("").to_owned();
            if !placeholders.contains('(') {
                placeholders = "(".to_owned() + &placeholders + ")";
            }
            let mut rules = String::new();
            if let Some(deps) = matches.values_of("use") {
                for dependency in deps {
                    rules.push_str("use ");
                    rules.push_str(dependency);
                    rules.push_str(";\n");
                }
            }
            rules.push_str("pub fn rule");
            rules.push_str(&placeholders);
            rules.push_str("{replace!(");
            rules.push_str(search);
            rules.push_str(" => ");
            rules.push_str(replacement);
            rules.push_str(");}");
            rules
        } else {
            "".to_owned()
        };
        let rules_file = matches.value_of("rules_file").unwrap_or("");
        if rules_file.is_empty() == rules.is_empty() {
            eprintln!("Must specify either --rules_file or both of --search and --replacement");
            std::process::exit(1);
        }
        let action = Action::from_matches(matches)?;
        if config.verbose {
            println!("Running cargo check in order to build dependencies and get rustc commands");
        }
        let rustc_command_lines = get_rustc_commandlines_for_local_package()?;

        for rustc_args in &rustc_command_lines {
            let driver = RerastCompilerDriver::new(
                ArgBuilder::from_args(rustc_args.iter().skip(1).cloned()),
            );
            let code_filename = driver.code_filename().ok_or_else(|| {
                Error::new(format!(
                    "Failed to determine code filename from: {:?}",
                    &rustc_args[2..]
                ))
            })?;
            if config.verbose {
                println!("Processing {}", code_filename);
            }
            match driver.apply_rules_from_string_or_file(rules.clone(), &rules_file, config.clone())
            {
                Ok(output) => {
                    if config.verbose && output.updated_files.is_empty() {
                        println!("No matches found in {} or submodules", code_filename);
                    }
                    for (filename, new_contents) in output.updated_files {
                        action.process(&filename, &new_contents)?;
                    }
                }
                Err(errors) => {
                    eprintln!("{}", errors);
                    std::process::exit(1);
                }
            }
        }
    } else {
        panic!("Unknown mode");
    }
    Ok(())
}

fn pass_through_to_actual_compiler() {
    let args: Vec<_> = std::env::args().skip(2).collect();
    std::process::Command::new("rustc")
        .args(args)
        .status()
        .expect("Failed to run rustc");
}

pub fn main() {
    let driver = RerastCompilerDriver::new(ArgBuilder::from_args(std::env::args().skip(1)));
    // If cargo is calling us to get compiler configuration or is compiling a dependent crate, then
    // just run the compiler normally.
    if driver.args().has_arg("--print=cfg") || driver.is_compiling_dependency() {
        pass_through_to_actual_compiler();
    } else if let Ok(_) = std::env::var(var_names::PRINT_ARGS_JSON) {
        let json_args: Vec<JsonValue> = std::env::args().map(|a| JsonValue::String(a)).collect();
        println!("{}{}", JSON_ARGS_MARKER, JsonValue::Array(json_args).dump());
        pass_through_to_actual_compiler();
    } else if let Some(arg1) = std::env::args().nth(1) {
        if arg1 == "rerast" {
            if let Err(error) = cargo_rerast() {
                eprintln!("{}", error.message);
            }
        }
    }
}
