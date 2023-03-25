//! Implementation of the bytecode virtual machine.

use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use crate::{
    chunk::{disassemble_chunk, disassemble_instruction, Chunk},
    compile::Parser,
    object::{Heap, HeapError},
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

    /// Can't use the virtual machine's heap.
    #[error(transparent)]
    Heap(#[from] HeapError),

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
                Opcode::Print => self.print()?,
                Opcode::NE => self.ne()?,
                Opcode::EQ => self.eq()?,
                Opcode::GT => self.gt()?,
                Opcode::GE => self.ge()?,
                Opcode::LT => self.lt()?,
                Opcode::LE => self.le()?,
                Opcode::Add => self.add()?,
                Opcode::Sub => self.sub()?,
                Opcode::Mul => self.mul()?,
                Opcode::Div => self.div()?,
                Opcode::Not => self.not()?,
                Opcode::Neg => self.neg()?,
                Opcode::Ret => {
                    self.print()?;
                    break;
                }
                _ => unreachable!(),
            }
        }
        Ok(())
    }

    fn ne(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.ne(&r))))
    }

    fn eq(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.eq(&r))))
    }

    fn gt(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.gt(&r))))
    }

    fn ge(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.ge(&r))))
    }

    fn lt(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.lt(&r))))
    }

    fn le(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(Value::Bool(l.le(&r))))
    }

    fn add(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| match (l, r) {
            (Value::Object(o1), Value::Object(o2)) => {
                let object = self.heap.add_objects(&o1, &o2)?;
                Ok(Value::Object(object))
            }
            _ => Ok(l.add(&r)?),
        })
    }

    fn sub(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(l.sub(&r)?))
    }

    fn mul(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(l.mul(&r)?))
    }

    fn div(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_binary(|l, r| Ok(l.div(&r)?))
    }

    fn not(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_unary(|v| Ok(v.not()))
    }

    fn neg(&mut self) -> Result<(), RuntimeError> {
        self.stack.apply_unary(|v| Ok(v.neg()?))
    }

    fn print(&mut self) -> Result<(), RuntimeError> {
        let val = self.stack.pop()?;
        println!("{val}");
        Ok(())
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
