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

#![feature(rustc_private)]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

#[macro_use]
extern crate clap;
extern crate colored;
#[macro_use]
extern crate failure;
extern crate json;
extern crate rerast;
extern crate syntax;

use json::JsonValue;
use std::io::Write;
use rerast::{ArgBuilder, Config, RerastCompilerDriver, RerastOutput};
use rerast::chunked_diff;
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::Path;
use clap::ArgMatches;
use failure::Error;
use syntax::codemap::RealFileLoader;

// Environment variables that we use to pass data from the outer invocation of cargo-rerast through
// to the inner invocation which runs within cargo check.
mod var_names {
    // Environment variable name, which if set, indicates that we should write our arguments out as
    // JSON before running the actual rust compiler. Hopefully eventually cargo will have a way for
    // us to query the compile commandlines without doing this sort of thing.
    pub const PRINT_ARGS_JSON: &str = "RERAST_PRINT_ARGS_JSON";
}

const JSON_ARGS_MARKER: &str = "RUSTC_ARGS_AS_JSON: ";

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
    ensure!(
        output.status.success(),
        "cargo metadata failed:\n{}",
        std::str::from_utf8(output.stderr.as_slice())?
    );
    let metadata_str = std::str::from_utf8(output.stdout.as_slice())?;
    let parsed = json::parse(metadata_str)?;
    for package in parsed["packages"].members() {
        if let Some(name) = package["name"].as_str() {
            // TODO: Remove once #10 is fixed.
            if std::env::var("RERAST_FULL_CARGO_CLEAN") == Ok("1".to_string()) {
                std::process::Command::new("cargo")
                    .args(vec!["clean"])
                    .status()?;
            } else {
                std::process::Command::new("cargo")
                    .args(vec!["clean", "--package", name])
                    .status()?;
            }
        }
    }
    Ok(())
}

fn read_file_as_string(path: &Path) -> Result<String, Error> {
    fn read_file_internal(path: &Path) -> std::io::Result<String> {
        let mut contents = String::new();
        File::open(path)?.read_to_string(&mut contents)?;
        Ok(contents)
    }
    read_file_internal(path).map_err(|error| format_err!("Error opening {:?}: {}", path, error))
}

fn get_rustc_commandlines_for_local_package() -> Result<Vec<Vec<String>>, Error> {
    clean_local_targets()?;
    let current_exe = std::env::current_exe().expect("env::current_exe() failed");
    let cargo_check_output = std::process::Command::new("cargo")
        .env(var_names::PRINT_ARGS_JSON, "yes")
        .env("RUSTC_WRAPPER", current_exe)
        .args(vec!["check", "-v", "--tests", "--benches", "--examples"])
        .stdout(std::process::Stdio::piped())
        .output()
        .expect("Failed to invoke cargo");
    let output_str = std::str::from_utf8(cargo_check_output.stdout.as_slice())?;
    ensure!(
        cargo_check_output.status.code() == Some(0),
        "cargo check failed (exit code = {}). Output follows:\n{}",
        cargo_check_output
            .status
            .code()
            .map(|c| c.to_string())
            .unwrap_or_else(|| "signal".to_owned()),
        output_str
    );
    let mut result: Vec<Vec<String>> = Vec::new();
    for line in output_str.lines() {
        if line.starts_with(JSON_ARGS_MARKER) {
            let parsed = json::parse(&line[JSON_ARGS_MARKER.len()..])?;
            if let JsonValue::Array(values) = parsed {
                let args: Result<Vec<String>, Error> = values
                    .into_iter()
                    .map(|v| {
                        if let Some(s) = v.as_str() {
                            Ok(s.to_owned())
                        } else {
                            bail!("Expected JSON string, got: {:?}", v);
                        }
                    })
                    // First value will be the path to cargo-rerast, skip it.
                    .skip(1)
                    .collect();
                result.push(args?);
            }
        }
    }
    Ok(result)
}

enum Action {
    Diff,
    DiffCmd(String),
    ForceWrite { backup: bool },
}

impl Action {
    fn from_matches(matches: &ArgMatches) -> Result<Action, Error> {
        let mut actions = Vec::new();
        if matches.is_present("diff") {
            actions.push(Action::Diff)
        }
        if let Some(diff_cmd) = matches.value_of("diff_cmd") {
            actions.push(Action::DiffCmd(diff_cmd.to_owned()));
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
            format_err!("Exactly one of --diff, --diff_cmd or --force is currently required")
        })
    }

    fn process(&self, path: &Path, new_contents: &str) -> Result<(), Error> {
        let filename = path.to_str()
            .ok_or_else(|| format_err!("Path wasn't valid UTF-8"))?;
        match *self {
            Action::Diff => {
                let current_contents = read_file_as_string(path)?;
                chunked_diff::print_diff(filename, &current_contents, new_contents);
            }
            Action::DiffCmd(ref diff_cmd) => {
                // rustfmt has a native diff built-in. If that were extracted into a separate crate,
                // we could reuse that instead of calling out to an external diff.
                let mut diff_cmd_iter = diff_cmd.split(' ');
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
                    .map_err(|e| format_err!("Error running '{}': {}", diff_cmd, e))?;
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

fn get_replacement_kind_and_arg(matches: &ArgMatches) -> Result<(&'static str, String), Error> {
    let mut result = Vec::new();
    if let Some(s) = matches.value_of("search") {
        result.push(("replace", s.to_owned()));
    }
    if let Some(s) = matches.value_of("search_type") {
        result.push(("replace_type", s.to_owned()));
    }
    if let Some(s) = matches.value_of("search_pattern") {
        result.push(("replace_pattern", s.to_owned()));
    }
    if let Some(s) = matches.value_of("search_trait_ref") {
        result.push(("replace_trait_ref", s.to_owned()));
    }
    if result.len() > 1 {
        result.clear();
    }
    result.into_iter().next().ok_or_else(|| {
        format_err!("--replace_with requires exactly one kind of --search* argument is required.")
    })
}

fn cargo_rerast() -> Result<(), Error> {
    let mut args: Vec<String> = std::env::args().collect();
    // We want the help message to say "cargo rerast" not "cargo-rerast rerast".
    args[0] = "cargo".to_owned();
    let matches = clap::App::new("Rerast")
        .subcommand(
            clap::SubCommand::with_name("rerast")
                .about("Replace Rust code based on typed, syntactic patterns")
                .args_from_usage(
                    "--rules_file=[FILE] 'Path to a rule file'
                     --use=[USE_STATEMENT]... 'Use statements required by rule'
                     -p, --placeholders=[PLACEHOLDERS] 'e.g. <T>(o: option<T>)'
                     -s, --search=[CODE] 'Expression to search for'
                     --search_type=[CODE] 'Type to search for'
                     --search_pattern=[CODE] 'Pattern to search for'
                     --search_trait_ref=[TRAIT] 'Trait to search for'
                     -r, --replace_with=[CODE] 'Replacement code'
                     --file=[FILE]... 'Only apply to these root files and their submodules'
                     --diff_cmd=[COMMAND] 'Diff changes with the specified diff command'
                     --color=[always/never] 'Force color on or off'
                     --debug_snippet=[CODE_SNIPPET] 'A snippet of code that you think should \
                                                     match or list_all to list all checked \
                                                     snippets.'
                     --crate_root=[DIR] 'Root directory of crate. Defaults to current directory.'
                                      \
                     --diff 'Diff changes'
                     --force 'Overwrite files',
                     --backup 'Rename old files with a .bk extension',
                     --replay_git 'Detect and replay existing unstaged git change',
                     --verbose 'Print additional information about what's happening'",
                ),
        )
        .get_matches_from(&args);
    let matches = matches.subcommand_matches("rerast").ok_or_else(|| {
        format_err!("This binary is intended to be run as `cargo rerast` not run directly.")
    })?;
    let config = Config {
        verbose: matches.is_present("verbose"),
        debug_snippet: matches.value_of("debug_snippet").unwrap_or("").to_owned(),
        files: values_t!(matches.values_of("file"), String).ok(),
    };
    match matches.value_of("color") {
        Some("always") => colored::control::set_override(true),
        Some("never") => colored::control::set_override(false),
        Some(v) => bail!("Invalid value for --color: {}", v),
        _ => {}
    }
    if let Some(crate_root) = matches.value_of("crate_root") {
        std::env::set_current_dir(crate_root)?;
    }
    let mut maybe_rustc_command_lines = None;
    let rules = if let Some(replacement) = matches.value_of("replace_with") {
        let (replace_kind, search) = get_replacement_kind_and_arg(matches)?;
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
        rules.push_str("{");
        rules.push_str(replace_kind);
        rules.push_str("!(");
        rules.push_str(&search);
        rules.push_str(" => ");
        rules.push_str(replacement);
        rules.push_str(");}");
        rules
    } else if matches.is_present("replay_git") {
        let rustc_command_lines = get_rustc_commandlines_for_local_package()?;
        let rule_from_change = derive_rule_from_git_change(&rustc_command_lines)?;
        maybe_rustc_command_lines = Some(rustc_command_lines);
        println!("Generated rule:\n{}\n", rule_from_change);
        rule_from_change
    } else if matches.is_present("search") || matches.is_present("search_type")
        || matches.is_present("search_pattern")
        || matches.is_present("search_trait_ref")
    {
        bail!("Searching without --replace_with is not yet implemented");
    } else if let Some(rules_file) = matches.value_of("rules_file") {
        read_file_as_string(Path::new(rules_file))?
    } else {
        bail!("Must specify either --rules_file or both of --search and --replacement");
    };
    let action = Action::from_matches(matches)?;
    if config.verbose {
        println!("Running cargo check in order to build dependencies and get rustc commands");
    }
    // Get rustc command lines if we haven't already gotten them.
    let rustc_command_lines = if let Some(existing_value) = maybe_rustc_command_lines {
        existing_value
    } else {
        get_rustc_commandlines_for_local_package()?
    };

    let mut updates_to_apply = RerastOutput::new();
    for rustc_args in &rustc_command_lines {
        let driver = RerastCompilerDriver::new(ArgBuilder::from_args(rustc_args.iter().cloned()));
        let code_filename = driver.code_filename().ok_or_else(|| {
            format_err!(
                "Failed to determine code filename from: {:?}",
                &rustc_args[2..]
            )
        })?;
        if config.verbose {
            println!("Processing {}", code_filename);
        }

        let output_or_error =
            driver.apply_rules_from_string(rules.clone(), config.clone(), RealFileLoader);
        match output_or_error {
            Ok(output) => {
                updates_to_apply.merge(output);
            }
            Err(errors) => {
                bail!("{}", errors);
            }
        }
    }
    let updated_files = updates_to_apply.updated_files(&RealFileLoader)?;
    if config.verbose && updated_files.is_empty() {
        println!("No matches found");
    }
    for (filename, new_contents) in updated_files {
        action.process(&filename, &new_contents)?;
    }
    Ok(())
}

fn derive_rule_from_git_change(command_lines: &[Vec<String>]) -> Result<String, Error> {
    let git_diff_output = std::process::Command::new("git")
        .arg("diff")
        .arg("--name-only")
        .arg("--relative")
        .arg(".")
        .stdout(std::process::Stdio::piped())
        .output()?;

    let changed_files: Vec<&str> = std::str::from_utf8(&git_diff_output.stdout)?
        .lines()
        .collect();
    ensure!(
        !changed_files.is_empty(),
        "According to git diff, no files have been changed"
    );
    ensure!(
        changed_files.len() == 1,
        "According to git diff, multiple have been changed"
    );
    let changed_filename = changed_files[0];

    let git_show_output = std::process::Command::new("git")
        .arg("show")
        .arg(format!(":{}", changed_filename))
        .stdout(std::process::Stdio::piped())
        .output()?;
    let original_file_contents = std::str::from_utf8(&git_show_output.stdout)?;

    match rerast::change_to_rule::determine_rule(
        command_lines,
        changed_filename,
        original_file_contents,
    ) {
        Ok(rule) => Ok(rule),
        Err(errors) => bail!("{}", errors),
    }
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
    if std::env::var(var_names::PRINT_ARGS_JSON).is_ok() {
        // If cargo is calling us to get compiler configuration or is compiling
        // a dependent crate, thenp just run the compiler normally.
        if driver.args().has_arg("--print=cfg") || driver.is_compiling_dependency() {
            pass_through_to_actual_compiler();
        } else {
            let json_args: Vec<JsonValue> = std::env::args().map(JsonValue::String).collect();
            println!("{}{}", JSON_ARGS_MARKER, JsonValue::Array(json_args).dump());
            pass_through_to_actual_compiler();
        }
    } else if let Err(error) = cargo_rerast() {
        eprintln!("{}", error);
        std::process::exit(-1);
    }
}
