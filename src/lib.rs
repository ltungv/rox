//! An interpreter for the Lox programming language.

#![deny(rust_2018_idioms, rust_2021_compatibility, clippy::all)]
#![warn(missing_docs)]

mod chunk;
mod compile;
mod heap;
mod object;
mod opcode;
mod scan;
mod stack;
mod table;
mod value;
mod vm;

use std::{error, fmt};

pub use vm::{RuntimeError, VirtualMachine};

/// A enumeration of all potential errors that might occur when working with the virtual machine.
#[derive(Debug)]
pub enum InterpretError {
    /// Error with compiling the source code.
    Compile,
    /// Error with running the bytecode.
    Runtime,
}

impl error::Error for InterpretError {}

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compile => f.write_str("Compile error."),
            Self::Runtime => f.write_str("Runtime error."),
        }
    }
}
