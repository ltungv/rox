//! Implementation of the bytecode virtual machine.

use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use crate::{
    chunk::{disassemble_chunk, disassemble_instruction, Chunk},
    compile::Parser,
    object::Heap,
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
    heap: Heap,
    stack: Stack<Value, VM_STACK_SIZE>,
}

impl VirtualMachine {
    /// Create a new virtual machine that prints to the given output.
    pub fn new() -> Self {
        Self {
            heap: Heap::default(),
            stack: Stack::default(),
        }
    }
}

impl VirtualMachine {
    /// Compile and execute the given source code.
    pub fn interpret(&mut self, src: &str) -> Result<(), InterpretError> {
        let mut parser = Parser::new(src, &mut self.heap);
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
}

struct Task<'vm, 'chunk> {
    stack: &'vm mut Stack<Value, VM_STACK_SIZE>,
    heap: &'vm mut Heap,
    chunk: &'chunk Chunk,
    ip: usize,
}

impl<'vm, 'chunk> Task<'vm, 'chunk> {
    fn new(vm: &'vm mut VirtualMachine, chunk: &'chunk Chunk) -> Self {
        Self {
            stack: &mut vm.stack,
            heap: &mut vm.heap,
            chunk,
            ip: 0,
        }
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
                self.heap_trace();
                self.stack_trace();
                disassemble_instruction(self.chunk, self.ip);
            }
            match Opcode::try_from(self.read_byte())? {
                Opcode::Const => {
                    let constant = *self.read_constant();
                    self.stack.push(constant)?;
                }
                Opcode::Nil => self.stack.push(Value::Nil)?,
                Opcode::True => self.stack.push(Value::Bool(true))?,
                Opcode::False => self.stack.push(Value::Bool(false))?,
                Opcode::Print => {
                    let v = self.stack.pop()?;
                    self.print(v);
                }
                Opcode::NE => self.stack.binary(|l, r| Value::Bool(l.ne(&r)))?,
                Opcode::EQ => self.stack.binary(|l, r| Value::Bool(l.eq(&r)))?,
                Opcode::GT => self.stack.binary(|l, r| Value::Bool(l.gt(&r)))?,
                Opcode::GE => self.stack.binary(|l, r| Value::Bool(l.ge(&r)))?,
                Opcode::LT => self.stack.binary(|l, r| Value::Bool(l.lt(&r)))?,
                Opcode::LE => self.stack.binary(|l, r| Value::Bool(l.le(&r)))?,
                Opcode::Add => {
                    self.stack
                        .binary_result::<RuntimeError, _>(|l, r| match (l, r) {
                            (Value::Object(o1), Value::Object(o2)) => {
                                let object =
                                    self.heap.add_objects(&o1, &o2).map_err(ValueError::from)?;
                                Ok(Value::Object(object))
                            }
                            _ => Ok(l.add(&r)?),
                        })?
                }
                Opcode::Sub => self
                    .stack
                    .binary_result::<RuntimeError, _>(|l, r| Ok(l.sub(&r)?))?,
                Opcode::Mul => self
                    .stack
                    .binary_result::<RuntimeError, _>(|l, r| Ok(l.mul(&r)?))?,
                Opcode::Div => self
                    .stack
                    .binary_result::<RuntimeError, _>(|l, r| Ok(l.div(&r)?))?,
                Opcode::Not => self.stack.unary(|v| v.not())?,
                Opcode::Neg => self
                    .stack
                    .unary_result::<RuntimeError, _>(|v| Ok(v.neg()?))?,
                Opcode::Ret => {
                    let v = self.stack.pop()?;
                    self.print(v);
                    break;
                }
                _ => unreachable!(),
            }
        }
        Ok(())
    }

    fn print(&mut self, value: Value) {
        println!("{value}")
    }

    #[cfg(debug_assertions)]
    fn stack_trace(&self) {
        print!("          ");
        for value in self.stack.into_iter() {
            print!("[ {value} ]");
        }
        println!();
    }

    #[cfg(debug_assertions)]
    fn heap_trace(&self) {
        print!("          ");
        for object in self.heap.into_iter() {
            print!("[ {object} ]");
        }
        println!();
    }
}
