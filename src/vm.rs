//! Implementation of the bytecode virtual machine.

use std::{
    collections::HashMap,
    ops::{Add, Div, Mul, Neg, Not, Sub},
    rc::Rc,
};

use crate::{
    chunk::Chunk,
    compile::Parser,
    object::Heap,
    opcode::Opcode,
    stack::Stack,
    value::{Value, ValueError},
    InterpretError,
};

#[cfg(debug_assertions)]
use crate::chunk::{disassemble_chunk, disassemble_instruction};

/// The max number of values can be put onto the virtual machine's stack.
const VM_STACK_SIZE: usize = 256;

/// An enumeration of potential errors occur when running the bytecodes.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum RuntimeError {
    /// Can't parse a byte as an opcode.
    #[error(transparent)]
    InvalidOpcode(#[from] num_enum::TryFromPrimitiveError<Opcode>),

    /// Overflown the virtual machine's stack.
    #[error("Stack is overflown.")]
    StackOverflown,

    /// Exhausted the virtual machine's stack.
    #[error("Stack is exhausted.")]
    StackExhausted,

    /// Can't perform some operations given the current operand(s).
    #[error(transparent)]
    Value(#[from] ValueError),

    /// Can't find a variable in scope.
    #[error("Undefined variable '{0}'")]
    UndefinedVariable(String),
}

/// A bytecode virtual machine for the Lox programming language.
#[derive(Default)]
pub struct VirtualMachine {
    heap: Heap,
    stack: Stack<Value, VM_STACK_SIZE>,
    globals: HashMap<Rc<str>, Value>,
}

impl VirtualMachine {
    /// Create a new virtual machine that prints to the given output.
    pub fn new() -> Self {
        Self {
            heap: Heap::default(),
            stack: Stack::default(),
            globals: HashMap::default(),
        }
    }
}

impl VirtualMachine {
    /// Compile and execute the given source code.
    pub fn interpret(&mut self, src: &str) -> Result<(), InterpretError> {
        let mut parser = Parser::new(src, &mut self.heap);
        if let Some(chunk) = parser.compile() {
            #[cfg(debug_assertions)]
            disassemble_chunk(&chunk, "code");
            // Only run the chunk if we compiled it successfully.
            self.run(&chunk)?;
        }
        Ok(())
    }

    fn run(&mut self, chunk: &Chunk) -> Result<(), RuntimeError> {
        let mut task = Task::new(self, chunk);
        task.run()?;
        Ok(())
    }
}

/// A task is the structure responsible for executing a single chunk.
struct Task<'vm, 'chunk> {
    ip: usize,
    chunk: &'chunk Chunk,
    stack: &'vm mut Stack<Value, VM_STACK_SIZE>,
    heap: &'vm mut Heap,
    globals: &'vm mut HashMap<Rc<str>, Value>,
}

impl<'vm, 'chunk> Task<'vm, 'chunk> {
    fn new(vm: &'vm mut VirtualMachine, chunk: &'chunk Chunk) -> Self {
        Self {
            ip: 0,
            chunk,
            stack: &mut vm.stack,
            heap: &mut vm.heap,
            globals: &mut vm.globals,
        }
    }

    fn read_byte(&mut self) -> u8 {
        let byte = self.chunk.instructions[self.ip];
        self.ip += 1;
        byte
    }

    fn read_short(&mut self) -> u16 {
        let hi = self.chunk.instructions[self.ip] as u16;
        let lo = self.chunk.instructions[self.ip + 1] as u16;
        self.ip += 2;
        hi << 8 | lo
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
                Opcode::Const => self.constant()?,
                Opcode::Nil => {
                    self.stack_push(Value::Nil)?;
                }
                Opcode::True => {
                    self.stack_push(Value::Bool(true))?;
                }
                Opcode::False => {
                    self.stack_push(Value::Bool(false))?;
                }
                Opcode::Pop => {
                    self.stack_pop()?;
                }
                Opcode::GetLocal => self.get_local()?,
                Opcode::SetLocal => self.set_local()?,
                Opcode::GetGlobal => self.get_global()?,
                Opcode::SetGlobal => self.set_global()?,
                Opcode::DefineGlobal => self.defined_global()?,
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
                Opcode::Jump => self.jump(JumpDirection::Forward),
                Opcode::JumpIfTrue => self.jump_if_true()?,
                Opcode::JumpIfFalse => self.jump_if_false()?,
                Opcode::Loop => self.jump(JumpDirection::Backward),
                Opcode::Ret => break,
                _ => unreachable!(),
            }
        }
        Ok(())
    }

    fn jump(&mut self, direction: JumpDirection) {
        let offset = self.read_short() as usize;
        match direction {
            JumpDirection::Forward => self.ip += offset,
            JumpDirection::Backward => self.ip -= offset,
        }
    }

    fn jump_if_true(&mut self) -> Result<(), RuntimeError> {
        let offset = self.read_short();
        if self.stack_top()?.is_truthy() {
            self.ip += offset as usize;
        }
        Ok(())
    }

    fn jump_if_false(&mut self) -> Result<(), RuntimeError> {
        let offset = self.read_short();
        if self.stack_top()?.is_falsey() {
            self.ip += offset as usize;
        }
        Ok(())
    }

    /// Get a local variable.
    fn get_local(&mut self) -> Result<(), RuntimeError> {
        let slot = self.read_byte();
        self.stack_push(self.stack[slot.into()])?;
        Ok(())
    }

    /// Set a local variable.
    fn set_local(&mut self) -> Result<(), RuntimeError> {
        let slot = self.read_byte();
        self.stack[slot.into()] = *self.stack_top()?;
        Ok(())
    }

    /// Get a global variable or return a runtime error if it was not found.
    fn get_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_str()?;
        let value = self
            .globals
            .get(&name)
            .ok_or_else(|| RuntimeError::UndefinedVariable(name.to_string()))?;
        self.stack
            .push(*value)
            .ok_or(RuntimeError::StackOverflown)?;
        Ok(())
    }

    /// Set a global variable or return a runtime error if it was not found.
    fn set_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_str()?;
        let value = self.stack_top()?;
        if self.globals.insert(Rc::clone(&name), *value).is_none() {
            self.globals.remove(&name);
            return Err(RuntimeError::UndefinedVariable(name.to_string()));
        }
        Ok(())
    }

    /// Declare a variable with some initial value.
    fn defined_global(&mut self) -> Result<(), RuntimeError> {
        let constant = *self.read_constant();
        let global_name = constant.as_str()?;
        let global_value = self.stack_pop()?;
        self.globals.insert(global_name, global_value);
        Ok(())
    }

    /// Read the constant id from the next byte and load the constant with the found id.
    fn constant(&mut self) -> Result<(), RuntimeError> {
        let constant = *self.read_constant();
        self.stack
            .push(constant)
            .ok_or(RuntimeError::StackOverflown)?;
        Ok(())
    }

    fn ne(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.ne(&r)))?;
        Ok(())
    }

    fn eq(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.eq(&r)))?;
        Ok(())
    }

    fn gt(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.gt(&r)))?;
        Ok(())
    }

    fn ge(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.ge(&r)))?;
        Ok(())
    }

    fn lt(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.lt(&r)))?;
        Ok(())
    }

    fn le(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary(|l, r| Value::Bool(l.le(&r)))?;
        Ok(())
    }

    fn add(&mut self) -> Result<(), RuntimeError> {
        // NOTE: This function can't use the `apply_binary*` helper because rust borrow checker
        // disallow us from mutating the `self.heap` while calling the function. This happens
        // because the function also holds an exclusive reference to `self`.
        let rhs = self.stack_pop()?;
        let lhs = *self.stack_top()?;
        let res = match (lhs, rhs) {
            // Operations on objects might allocate a new one.
            (Value::Object(o1), Value::Object(o2)) => {
                Value::Object(self.heap.add_objects(&o1, &o2))
            }
            // Non-objects can used the `ops::Add` implementation for `Value`
            _ => lhs.add(&rhs)?,
        };
        let top = self.stack_top_mut()?;
        *top = res;
        Ok(())
    }

    fn sub(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary_err(|l, r| Ok(l.sub(&r)?))
    }

    fn mul(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary_err(|l, r| Ok(l.mul(&r)?))
    }

    fn div(&mut self) -> Result<(), RuntimeError> {
        self.apply_binary_err(|l, r| Ok(l.div(&r)?))
    }

    fn not(&mut self) -> Result<(), RuntimeError> {
        self.apply_unary(|v| v.not())?;
        Ok(())
    }

    fn neg(&mut self) -> Result<(), RuntimeError> {
        self.apply_unary_err(|v| Ok(v.neg()?))
    }

    fn print(&mut self) -> Result<(), RuntimeError> {
        let val = self.stack_pop()?;
        println!("{val}");
        Ok(())
    }

    /// Apply a unary function on the stack.
    fn apply_unary<F>(&mut self, mut func: F) -> Result<(), RuntimeError>
    where
        F: FnMut(Value) -> Value,
    {
        // Change the top of the stack in-place without doing a pop.
        let v = self.stack_top_mut()?;
        *v = func(*v);
        Ok(())
    }

    /// Apply a unary function that might return an error on the stack.
    fn apply_unary_err<F>(&mut self, mut func: F) -> Result<(), RuntimeError>
    where
        F: FnMut(Value) -> Result<Value, RuntimeError>,
    {
        // Change the top of the stack in-place without doing a pop.
        let v = self.stack_top_mut()?;
        *v = func(*v)?;
        Ok(())
    }

    /// Apply a binary function on the stack.
    fn apply_binary<F>(&mut self, mut func: F) -> Result<(), RuntimeError>
    where
        F: FnMut(Value, Value) -> Value,
    {
        // Pop once, then change the top of the stack in-place without doing a second pop.
        let rhs = self.stack_pop()?;
        let lhs = self.stack_top_mut()?;
        *lhs = func(*lhs, rhs);
        Ok(())
    }

    /// Apply a binary function that might return an error on the stack.
    fn apply_binary_err<F>(&mut self, mut func: F) -> Result<(), RuntimeError>
    where
        F: FnMut(Value, Value) -> Result<Value, RuntimeError>,
    {
        // Pop once, then change the top of the stack in-place without doing a second pop.
        let rhs = self.stack_pop()?;
        let lhs = self.stack_top_mut()?;
        *lhs = func(*lhs, rhs)?;
        Ok(())
    }

    fn stack_push(&mut self, value: Value) -> Result<usize, RuntimeError> {
        self.stack.push(value).ok_or(RuntimeError::StackOverflown)
    }

    fn stack_pop(&mut self) -> Result<Value, RuntimeError> {
        self.stack.pop().ok_or(RuntimeError::StackExhausted)
    }

    fn stack_top(&self) -> Result<&Value, RuntimeError> {
        self.stack.top().ok_or(RuntimeError::StackExhausted)
    }

    fn stack_top_mut(&mut self) -> Result<&mut Value, RuntimeError> {
        self.stack.top_mut().ok_or(RuntimeError::StackExhausted)
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

/// An enumeration that determine whether to jump forward or backward along the stream of
/// bytecode instructions.
pub(crate) enum JumpDirection {
    /// Jump forward.
    Forward,
    /// Jump backward.
    Backward,
}
