//! Implementation of the bytecode virtual machine.

use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use crate::{
    chunk::{disassemble_chunk, disassemble_instruction, Chunk},
    compile::Parser,
    opcode::Opcode,
    stack::{Stack, StackError},
    value::{Value, ValueError},
    InterpretError,
};

/// The max number of values can be put onto the virtual machine's stack.
const VM_STACK_SIZE: usize = 256;

/// An enumeration of potential errors occur when running the bytecodes.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum RuntimeError {
    /// Can't parse a byte as an opcode.
    #[error(transparent)]
    InvalidOpcode(#[from] num_enum::TryFromPrimitiveError<Opcode>),

    /// Can't use the virtual machine's stack.
    #[error(transparent)]
    Stack(#[from] StackError),

    /// Can't perform some operations given the current operand(s).
    #[error(transparent)]
    Value(#[from] ValueError),
}

/// A bytecode virtual machine for the Lox programming language.
#[derive(Default)]
pub struct VirtualMachine {
    stack: Stack<Value, VM_STACK_SIZE>,
}

impl VirtualMachine {
    /// Create a new virtual machine that prints to the given output.
    pub fn new() -> Self {
        Self {
            stack: Stack::default(),
        }
    }

    #[cfg(debug_assertions)]
    fn stack_trace(&self) {
        print!("          ");
        for value in &self.stack {
            print!("[ {value} ]");
        }
        println!();
    }
}

impl VirtualMachine {
    /// Compile and execute the given source code.
    pub fn interpret(&mut self, src: &str) -> Result<(), InterpretError> {
        let mut parser = Parser::new(src);
        let chunk = parser.compile()?;

        #[cfg(debug_assertions)]
        disassemble_chunk(&chunk, "code");

        self.run(&chunk)?;
        Ok(())
    }

    fn run(&mut self, chunk: &Chunk) -> Result<(), RuntimeError> {
        let mut task = Task::new(self, chunk);
        task.run()?;
        Ok(())
    }

    fn print(&mut self, value: Value) {
        println!("{value}")
    }
}

struct Task<'vm, 'chunk> {
    vm: &'vm mut VirtualMachine,
    chunk: &'chunk Chunk,
    ip: usize,
}

impl<'vm, 'chunk> Task<'vm, 'chunk> {
    fn new(vm: &'vm mut VirtualMachine, chunk: &'chunk Chunk) -> Self {
        Self { vm, chunk, ip: 0 }
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.chunk.instructions[self.ip];
        self.ip += 1;
        byte
    }

    fn read_constant(&mut self) -> &Value {
        let constant_id = self.read_byte() as usize;
        &self.chunk.constants[constant_id]
    }
}

impl<'vm, 'chunk> Task<'vm, 'chunk> {
    fn run(&mut self) -> Result<(), RuntimeError> {
        loop {
            #[cfg(debug_assertions)]
            {
                self.vm.stack_trace();
                disassemble_instruction(self.chunk, self.ip);
            }
            match Opcode::try_from(self.read_byte())? {
                Opcode::Const => {
                    let constant = self.read_constant().clone();
                    self.vm.stack.push(constant)?;
                }
                Opcode::Nil => self.vm.stack.push(Value::Nil)?,
                Opcode::True => self.vm.stack.push(Value::Bool(true))?,
                Opcode::False => self.vm.stack.push(Value::Bool(false))?,
                Opcode::Print => {
                    let v = self.vm.stack.pop()?;
                    self.vm.print(v);
                }
                Opcode::NE => self.binary(|l, r| Ok(Value::Bool(l.ne(r))))?,
                Opcode::EQ => self.binary(|l, r| Ok(Value::Bool(l.eq(r))))?,
                Opcode::GT => self.binary(|l, r| Ok(Value::Bool(l.gt(r))))?,
                Opcode::GE => self.binary(|l, r| Ok(Value::Bool(l.ge(r))))?,
                Opcode::LT => self.binary(|l, r| Ok(Value::Bool(l.lt(r))))?,
                Opcode::LE => self.binary(|l, r| Ok(Value::Bool(l.le(r))))?,
                Opcode::Add => self.binary(|l, r| Ok(l.add(r)?))?,
                Opcode::Sub => self.binary(|l, r| Ok(l.sub(r)?))?,
                Opcode::Mul => self.binary(|l, r| Ok(l.mul(r)?))?,
                Opcode::Div => self.binary(|l, r| Ok(l.div(r)?))?,
                Opcode::Not => self.unary(|v| Ok(v.not()))?,
                Opcode::Neg => self.unary(|v| Ok(v.neg()?))?,
                Opcode::Ret => {
                    let v = self.vm.stack.pop()?;
                    self.vm.print(v);
                    break;
                }
                _ => unreachable!(),
            }
        }
        Ok(())
    }

    fn unary<F>(&mut self, func: F) -> Result<(), RuntimeError>
    where
        F: Fn(&Value) -> Result<Value, RuntimeError>,
    {
        let v = self.vm.stack.top_mut()?;
        *v = func(v)?;
        Ok(())
    }

    fn binary<F>(&mut self, func: F) -> Result<(), RuntimeError>
    where
        F: Fn(&Value, &Value) -> Result<Value, RuntimeError>,
    {
        let right = self.vm.stack.pop()?;
        let left = self.vm.stack.top_mut()?;
        *left = func(left, &right)?;
        Ok(())
    }
}
