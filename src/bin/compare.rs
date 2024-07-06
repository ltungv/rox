use std::{
    collections::HashMap,
    io::BufRead,
    path::{Path, PathBuf},
    process::Command,
};

use clap::Parser;

#[derive(Debug)]
enum Error {
    IO(std::io::Error),
    MissingOutput,
    ParseFloat(std::num::ParseFloatError),
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IO(err) => write!(f, "{err}"),
            Self::MissingOutput => write!(f, "Missing output."),
            Self::ParseFloat(err) => write!(f, "{err}"),
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self::IO(value)
    }
}

impl From<std::num::ParseFloatError> for Error {
    fn from(value: std::num::ParseFloatError) -> Self {
        Self::ParseFloat(value)
    }
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    directory: PathBuf,
    #[arg(short, long)]
    executables: Vec<PathBuf>,
}

fn run<P1, P2>(executable: P1, benchmark: P2) -> Result<f64, Error>
where
    P1: AsRef<Path>,
    P2: AsRef<Path>,
{
    let mut command = Command::new(executable.as_ref());
    let command_output = command.arg(benchmark.as_ref()).output()?;
    let line = command_output
        .stdout
        .lines()
        .last()
        .ok_or(Error::MissingOutput)??;
    Ok(line.parse()?)
}

fn compare<P>(executables: &[PathBuf], benchmark: P, iterations: usize) -> Result<(), Error>
where
    P: AsRef<Path>,
{
    let mut records: HashMap<PathBuf, f64> = HashMap::default();
    for executable in executables {
        records.insert(executable.clone(), f64::MAX);
    }
    for trail in 1..=iterations {
        let mut time_fast = f64::MAX;
        let mut time_slow = f64::MIN;
        for executable in executables {
            let elapsed = run(executable, benchmark.as_ref())?;
            if let Some(record) = records.get_mut(executable) {
                *record = record.min(elapsed);
            }
        }
        for executable in executables {
            let record = records[executable];
            time_fast = time_fast.min(record);
            time_slow = time_slow.max(record);
        }
        println!("trail #{trail} ({time_slow:.3}s - {time_fast:.3}s)");
        for executable in executables {
            let record = records[executable];
            let suffix = if record == time_fast {
                let percent_vs_slow = 100.0 * (time_slow / time_fast - 1.0);
                format!("{percent_vs_slow:.3}% faster")
            } else {
                let ratio_vs_fast = record / time_fast;
                format!("{ratio_vs_fast:.3}x of fastest")
            };
            println!("{:<48} {record:.3}s {suffix}", executable.to_string_lossy());
        }
        println!();
    }
    Ok(())
}

fn main() -> Result<(), Error> {
    let args = Args::parse();
    for entry in std::fs::read_dir(args.directory)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_file() {
            if let Some(ext) = path.extension() {
                if ext == "lox" {
                    println!("#");
                    println!("Comparing with '{}'.", path.to_string_lossy());
                    println!("#");
                    if let Err(err) = compare(&args.executables, path, 10) {
                        println!("Failed to compare: {err}");
                        println!();
                    }
                }
            };
        }
    }
    Ok(())
}
