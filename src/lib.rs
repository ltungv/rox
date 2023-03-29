//! An interpreter for the Lox programming language.

#![deny(rust_2018_idioms, rust_2021_compatibility, clippy::all, unsafe_code)]
#![warn(missing_docs)]

mod chunk;
mod compile;
mod heap;
mod object;
mod opcode;
mod scan;
mod value;
mod vm;

pub use vm::{RuntimeError, VirtualMachine};

/// A enumeration of all potential errors that might occur when working with the virtual machine.
#[derive(Debug, thiserror::Error)]
pub enum InterpretError {
    /// Error with compiling the source code.
    #[error("Compile error.")]
    Compile,
    /// Error with running the bytecode.
    #[error("Runtime error.")]
    Runtime,
}
