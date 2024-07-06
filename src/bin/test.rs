//! Parses test expectations and checks the given virtual machine against them.

#![warn(
    rustdoc::all,
    clippy::pedantic,
    clippy::nursery,
    missing_debug_implementations
)]
#![deny(clippy::all, missing_docs, rust_2018_idioms, rust_2021_compatibility)]

use std::{
    collections::{HashSet, VecDeque},
    fmt,
    fs::{self, File},
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
};

use clap::{command, Parser};
use regex::{Captures, Regex};

fn make_regex(pattern: &str) -> Regex {
    Regex::new(pattern).expect("Invalid regular expression")
}

fn parse_expected_output(s: &str) -> Option<Captures<'_>> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN
        .get_or_init(|| make_regex(r"// expect: ?(.*)"))
        .captures(s)
}

fn parse_expected_compile_error(s: &str) -> Option<Captures<'_>> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN
        .get_or_init(|| make_regex(r"// (\[((java|c) )?line (\d+)\] )?(Error.*)"))
        .captures(s)
}

fn parse_expected_runtime_error(s: &str) -> Option<Captures<'_>> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN
        .get_or_init(|| make_regex(r"// expect runtime error: (.+)"))
        .captures(s)
}

fn parse_syntax_error(s: &str) -> Option<Captures<'_>> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN
        .get_or_init(|| make_regex(r"\[.*line (\d+)\] (Error.+)"))
        .captures(s)
}

fn parse_stack_trace(s: &str) -> Option<Captures<'_>> {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN
        .get_or_init(|| make_regex(r"\[line (\d+)\]"))
        .captures(s)
}

fn is_non_test(s: &str) -> bool {
    s.contains("// nontest")
}

#[derive(Debug)]
enum Error {
    IO(std::io::Error),
    ParseInt(std::num::ParseIntError),
    ParseTest(String),
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IO(err) => write!(f, "{err}"),
            Self::ParseInt(err) => write!(f, "{err}"),
            Self::ParseTest(msg) => write!(f, "{msg}"),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self::IO(value)
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(value: std::num::ParseIntError) -> Self {
        Self::ParseInt(value)
    }
}

#[derive(Debug)]
struct ExpectedLine {
    data: String,
    number: usize,
}

impl ExpectedLine {
    fn new(data: &str, number: usize) -> Self {
        Self {
            data: data.to_string(),
            number,
        }
    }
}

#[derive(Debug)]
struct Test {
    path: PathBuf,
    expected_exit_code: i32,
    expected_output: Vec<ExpectedLine>,
    expected_runtime_error: Option<ExpectedLine>,
    expected_compile_error: HashSet<String>,
}

impl Test {
    fn parse<P>(path: P) -> Result<Option<Self>, Error>
    where
        P: AsRef<Path>,
    {
        let mut test = Self {
            path: path.as_ref().to_path_buf(),
            expected_exit_code: 0,
            expected_output: Vec::default(),
            expected_runtime_error: None,
            expected_compile_error: HashSet::default(),
        };
        let reader = BufReader::new(File::open(path)?);
        for (idx, line) in reader.lines().enumerate() {
            let line = line?;
            let line_number = idx + 1;
            if is_non_test(&line) {
                return Ok(None);
            }
            if let Some(captures) = parse_expected_output(&line) {
                if let Some(message) = captures.get(1) {
                    test.expected_output
                        .push(ExpectedLine::new(message.as_str(), line_number));
                }
            } else if let Some(captures) = parse_expected_runtime_error(&line) {
                if let Some(message) = captures.get(1) {
                    test.expected_exit_code = 70;
                    test.expected_runtime_error =
                        Some(ExpectedLine::new(message.as_str(), line_number));
                }
            } else if let Some(captures) = parse_expected_compile_error(&line) {
                let language = captures.get(3);
                if language.is_none() || language.is_some_and(|l| l.as_str() == "c") {
                    let line_number = captures.get(4).map_or(line_number, |m| {
                        m.as_str().parse().expect("Invalid line number")
                    });
                    if let Some(message) = captures.get(5) {
                        test.expected_exit_code = 65;
                        test.expected_compile_error
                            .insert(format!("[{line_number}] {}", message.as_str()));
                    }
                }
            }
        }
        if test.expected_runtime_error.is_some() && !test.expected_compile_error.is_empty() {
            return Err(Error::ParseTest(
                "Cannot expect both compile and runtime errors".to_string(),
            ));
        }
        Ok(Some(test))
    }

    fn run<P>(self, failures: &mut Vec<String>, executable: P) -> Result<(), Error>
    where
        P: AsRef<Path>,
    {
        let mut command = Command::new(executable.as_ref());
        let mut error_lines = Vec::default();
        let mut output_lines = Vec::default();
        let command_output = command.arg(self.path.clone()).output()?;
        for line in command_output.stderr.lines() {
            error_lines.push(line?);
        }
        for line in command_output.stdout.lines() {
            output_lines.push(line?);
        }
        self.validate_exit_code(
            failures,
            command_output.status.code().unwrap_or(0),
            &error_lines,
        );
        self.validate_output(failures, &output_lines);
        if self
            .validate_runtime_error(failures, &error_lines)
            .is_none()
        {
            self.validate_compile_error(failures, &error_lines);
        }
        Ok(())
    }

    fn validate_exit_code(&self, failures: &mut Vec<String>, exit_code: i32, lines: &[String]) {
        if !self.expected_exit_code == exit_code {
            failures.push(format!(
                "Expected return code {} and got {exit_code}. Stderr:",
                self.expected_exit_code
            ));
            lines.iter().cloned().for_each(|e| failures.push(e));
        }
    }

    fn validate_output(&self, failures: &mut Vec<String>, lines: &[String]) {
        for (idx, line) in lines.iter().enumerate() {
            let Some(expected_output) = self.expected_output.get(idx) else {
                failures.push(format!("Got output '{line}' when none was expected."));
                continue;
            };
            if *line != expected_output.data {
                failures.push(format!(
                    "Expected output '{}' on line {} and got '{line}'.",
                    expected_output.data, expected_output.number
                ));
            }
        }
        for expected_output in &self.expected_output[lines.len()..] {
            failures.push(format!(
                "Missing expected output '{}' on line {}.",
                expected_output.data, expected_output.number
            ));
        }
    }

    fn validate_runtime_error(&self, failures: &mut Vec<String>, lines: &[String]) -> Option<()> {
        self.expected_runtime_error.as_ref().map(|expected_output| {
            if lines.len() < 2 {
                failures.push(format!(
                    "Expected runtime error '{}' and got none.",
                    expected_output.data
                ));
                return;
            }
            if lines[0] != expected_output.data {
                failures.push(format!(
                    "Expected runtime error '{}' and got:",
                    expected_output.data,
                ));
                failures.push(lines[0].clone());
                return;
            }
            let mut stack_trace_captures = None;
            for line in &lines[1..] {
                stack_trace_captures = parse_stack_trace(line);
                if stack_trace_captures.is_some() {
                    break;
                }
            }
            let Some(stack_trace_captures) = stack_trace_captures else {
                failures.push("Expected stack trace and got:".to_string());
                lines.iter().skip(1).for_each(|e| failures.push(e.clone()));
                return;
            };
            let Some(line_number) = stack_trace_captures.get(1) else {
                failures.push(format!(
                    "Expected line number {} in stack trace and got none.",
                    expected_output.data
                ));
                return;
            };
            let line_number: usize = line_number.as_str().parse().expect("Invalid line number");
            if line_number != expected_output.number {
                failures.push(format!(
                    "Expected runtime error on line {} but was on line {}.",
                    expected_output.number, line_number
                ));
            }
        })
    }

    fn validate_compile_error(&self, failures: &mut Vec<String>, lines: &[String]) {
        let mut found_errors = HashSet::default();
        for line in lines {
            let Some(captures) = parse_syntax_error(line) else {
                failures.push("Unexpected output on stderr:".to_string());
                failures.push(line.clone());
                continue;
            };
            let (Some(line_number), Some(message)) = (captures.get(1), captures.get(2)) else {
                failures.push("Unexpected error:".to_string());
                failures.push(line.clone());
                continue;
            };
            let error = format!("[{}] {}", line_number.as_str(), message.as_str());
            if self.expected_compile_error.contains(&error) {
                found_errors.insert(error);
            } else {
                failures.push("Unexpected error:".to_string());
                failures.push(line.clone());
            }
        }
        for error in self.expected_compile_error.difference(&found_errors) {
            failures.push(format!("Missing expected error: {error}."));
        }
    }
}

#[derive(Debug, Default)]
struct Suite {
    expectations: usize,
    tests: Vec<Test>,
}

impl Suite {
    fn parse<P>(root: P) -> Result<Self, Error>
    where
        P: AsRef<Path>,
    {
        let mut suite = Self::default();
        let mut directories = VecDeque::default();
        directories.push_back(root.as_ref().to_path_buf());
        while let Some(directory) = directories.pop_front() {
            if !directory.components().any(|c| {
                let c = c.as_os_str();
                c == "benchmark" || c == "scanning" || c == "expressions"
            }) {
                for entry in fs::read_dir(&directory)? {
                    let entry = entry?;
                    let path = entry.path();
                    let file_type = entry.file_type()?;
                    if file_type.is_dir() {
                        directories.push_back(path);
                    } else if file_type.is_file() {
                        if let Some(ext) = path.extension() {
                            if ext == "lox" {
                                if let Some(test) = Test::parse(path)? {
                                    suite.expectations += test.expected_output.len();
                                    suite.expectations += test.expected_compile_error.len();
                                    if test.expected_runtime_error.is_some() {
                                        suite.expectations += 1;
                                    }
                                    suite.tests.push(test);
                                };
                            }
                        };
                    }
                }
            }
        }
        Ok(suite)
    }

    fn run<P>(self, executable: P) -> Result<(), Error>
    where
        P: AsRef<Path>,
    {
        let mut passed = 0;
        let mut failed = 0;
        for test in self.tests {
            let path = test.path.to_string_lossy().to_string();
            let mut failures = Vec::default();
            test.run(&mut failures, executable.as_ref())?;
            if failures.is_empty() {
                passed += 1;
            } else {
                failed += 1;
                for failure in &failures {
                    println!("{failure}");
                }
            }
            println!("Passed: {passed} Failed: {failed} ({path})",);
        }
        if failed == 0 {
            println!(
                "All {passed} tests passed ({} expectations).",
                self.expectations
            );
        } else {
            println!("{passed} tests passed. {failed} tests failed.");
        }
        Ok(())
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long)]
    directory: PathBuf,
    #[arg(short, long)]
    executable: PathBuf,
}

fn main() -> Result<(), Error> {
    let args = Args::parse();
    Suite::parse(args.directory)?.run(args.executable)
}
