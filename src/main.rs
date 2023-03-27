use std::{
    env,
    io::{self, BufRead, BufReader, Write},
    process,
};

use rox::{InterpretError, VirtualMachine};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() {
        run_repl()
    } else if args.len() == 1 {
        run_file(&args[0])
    } else {
        println!("Usage: rlox [path]\n");
        process::exit(64);
    }
}

fn run_repl() {
    let mut vm = VirtualMachine::new();
    let mut reader = BufReader::new(io::stdin());
    loop {
        print!("> ");
        if let Err(err) = std::io::stdout().flush() {
            eprintln!("{err}");
            process::exit(74);
        };
        let mut line = String::new();
        match reader.read_line(&mut line) {
            Err(err) => {
                eprintln!("{err}");
                process::exit(74);
            }
            Ok(n) => {
                if n == 0 {
                    break;
                }
                vm.interpret(&line).ok();
            }
        }
    }
}

fn run_file(path: &str) {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(err) => {
            eprintln!("{err}");
            process::exit(74);
        }
    };
    let mut vm = VirtualMachine::new();
    match vm.interpret(&src) {
        Ok(()) => {}
        Err(InterpretError::Compile) => process::exit(65),
        Err(InterpretError::Runtime) => process::exit(70),
    }
}
