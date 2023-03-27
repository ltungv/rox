//! Implementation of the bytecode virtual machine.

use std::{
    cell::RefCell,
    collections::HashMap,
    ops::{Add, Deref, Div, Mul, Neg, Not, Sub},
    rc::Rc,
    str::FromStr,
};

use crate::{
    compile::Parser,
    heap::Heap,
    object::{ObjFun, ObjectContent, ObjectError, ObjectRef},
    opcode::Opcode,
    stack::Stack,
    value::{Value, ValueError},
    InterpretError,
};

#[cfg(debug_assertions)]
use crate::chunk::{disassemble_chunk, disassemble_instruction};

/// The max number of values can be put onto the virtual machine's stack.
const VM_STACK_SIZE: usize = 256;

/// The max number of call frames can be handled by the virtual machine.
const VM_FRAMES_MAX: usize = 64;

/// An enumeration of potential errors occur when running the bytecodes.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum RuntimeError {
    /// Can't parse a byte as an opcode.
    #[error(transparent)]
    InvalidOpcode(#[from] num_enum::TryFromPrimitiveError<Opcode>),

    /// Can't perform some operations given the current value(s).
    #[error(transparent)]
    Value(#[from] ValueError),

    /// Can't perform some operations given the current object(s).
    #[error(transparent)]
    Object(#[from] ObjectError),

    /// Overflown the virtual machine's stack.
    #[error("Stack is overflown.")]
    StackOverflown,

    /// Exhausted the virtual machine's stack.
    #[error("Stack is exhausted.")]
    StackExhausted,

    /// Can't find a variable in scope.
    #[error("Undefined variable '{0}'.")]
    UndefinedVariable(String),
}

/// A bytecode virtual machine for the Lox programming language.
#[derive(Default)]
pub struct VirtualMachine {
    stack: Stack<Value, VM_STACK_SIZE>,
    frames: Stack<CallFrame, VM_FRAMES_MAX>,
    globals: HashMap<Rc<str>, Value>,
    heap: Heap,
}

impl VirtualMachine {
    /// Create a new virtual machine that prints to the given output.
    pub fn new() -> Self {
        Self {
            stack: Stack::default(),
            frames: Stack::default(),
            globals: HashMap::default(),
            heap: Heap::default(),
        }
    }
}

impl VirtualMachine {
    /// Compile and execute the given source code.
    pub fn interpret(&mut self, src: &str) -> Result<(), InterpretError> {
        let mut parser = Parser::new(src, &mut self.heap);
        let object = parser.compile().ok_or(InterpretError::Compile)?;
        let fun = object.content.as_fun().expect("Expect function object.");

        self.stack_push(Value::Object(object))
            .expect("Expect stack empty.");
        self.frames.push(CallFrame {
            fun: object,
            ip: 0,
            slot: 0,
        });

        #[cfg(debug_assertions)]
        {
            let fun = fun.borrow();
            match &fun.name {
                None => disassemble_chunk(&fun.chunk, "code"),
                Some(s) => disassemble_chunk(&fun.chunk, s),
            };
        }

        let mut task = Task::new(self);
        task.run().map_err(|err| {
            eprintln!("{err}");
            let line = fun.borrow().chunk.get_line(self.frame().ip - 1);
            eprintln!("{line} in script");
            self.stack.reset();
            InterpretError::Runtime
        })
    }

    fn frame(&self) -> &CallFrame {
        self.frames.top().expect("Expect a call frame.")
    }

    fn frame_mut(&mut self) -> &mut CallFrame {
        self.frames.top_mut().expect("Expect a call frame.")
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

/// A task is the structure responsible for executing a single chunk.
struct Task<'vm> {
    vm: &'vm mut VirtualMachine,
}

impl<'vm> Task<'vm> {
    /// Create a new task given the chunk to be run.
    fn new(vm: &'vm mut VirtualMachine) -> Self {
        Self { vm }
    }

    /// Read the next byte in the stream of bytecode instructions.
    fn read_byte(&mut self) -> u8 {
        self.vm.frame_mut().read_byte()
    }

    /// Read the next 2 bytes in the stream of bytecode instructions.
    fn read_short(&mut self) -> u16 {
        self.vm.frame_mut().read_short()
    }

    /// Read the next byte in the stream of bytecode instructions and return the constant at the
    /// index given by the byte.
    fn read_constant(&mut self) -> Value {
        self.vm.frame_mut().read_constant()
    }
}

impl<'vm> Task<'vm> {
    fn run(&mut self) -> Result<(), RuntimeError> {
        loop {
            #[cfg(debug_assertions)]
            {
                self.vm.heap_trace();
                self.vm.stack_trace();
                let frame = self.vm.frame();
                disassemble_instruction(&frame.fun().borrow().chunk, frame.ip);
            }
            match Opcode::try_from(self.read_byte())? {
                Opcode::Const => self.constant()?,
                Opcode::Nil => {
                    self.vm.stack_push(Value::Nil)?;
                }
                Opcode::True => {
                    self.vm.stack_push(Value::Bool(true))?;
                }
                Opcode::False => {
                    self.vm.stack_push(Value::Bool(false))?;
                }
                Opcode::Pop => {
                    self.vm.stack_pop()?;
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
        let frame = self.vm.frame_mut();
        match direction {
            JumpDirection::Forward => frame.ip += offset,
            JumpDirection::Backward => frame.ip -= offset,
        }
    }

    fn jump_if_true(&mut self) -> Result<(), RuntimeError> {
        let offset = self.read_short();
        if self.vm.stack_top()?.is_truthy() {
            let frame = self.vm.frame_mut();
            frame.ip += offset as usize;
        }
        Ok(())
    }

    fn jump_if_false(&mut self) -> Result<(), RuntimeError> {
        let offset = self.read_short();
        if self.vm.stack_top()?.is_falsey() {
            let frame = self.vm.frame_mut();
            frame.ip += offset as usize;
        }
        Ok(())
    }

    /// Get a local variable.
    fn get_local(&mut self) -> Result<(), RuntimeError> {
        let slot = self.read_byte() as usize;
        let frame_slot = self.vm.frame().slot;
        self.vm.stack_push(self.vm.stack[frame_slot + slot])?;
        Ok(())
    }

    /// Set a local variable.
    fn set_local(&mut self) -> Result<(), RuntimeError> {
        let slot = self.read_byte() as usize;
        let frame_slot = self.vm.frame().slot;
        self.vm.stack[frame_slot + slot] = *self.vm.stack_top()?;
        Ok(())
    }

    /// Get a global variable or return a runtime error if it was not found.
    fn get_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_object()?.content.as_string()?;
        let value = self
            .vm
            .globals
            .get(&name)
            .ok_or_else(|| RuntimeError::UndefinedVariable(name.to_string()))?;
        self.vm
            .stack
            .push(*value)
            .ok_or(RuntimeError::StackOverflown)?;
        Ok(())
    }

    /// Set a global variable or return a runtime error if it was not found.
    fn set_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_object()?.content.as_string()?;
        let value = self.vm.stack_top()?;
        if !self.vm.globals.contains_key(&name) {
            return Err(RuntimeError::UndefinedVariable(name.to_string()));
        }
        self.vm.globals.insert(name, *value);
        Ok(())
    }

    /// Declare a variable with some initial value.
    fn defined_global(&mut self) -> Result<(), RuntimeError> {
        let constant = self.read_constant();
        let global_name = constant.as_object()?.content.as_string()?;
        let global_value = self.vm.stack_pop()?;
        self.vm.globals.insert(global_name, global_value);
        Ok(())
    }

    /// Read the constant id from the next byte and load the constant with the found id.
    fn constant(&mut self) -> Result<(), RuntimeError> {
        let constant = self.read_constant();
        self.vm
            .stack
            .push(constant)
            .ok_or(RuntimeError::StackOverflown)?;
        Ok(())
    }

    fn ne(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = Value::Bool(lhs.deref().ne(&rhs));
        Ok(())
    }

    fn eq(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = Value::Bool(lhs.deref().eq(&rhs));
        Ok(())
    }

    fn gt(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().gt(&rhs)?;
        Ok(())
    }

    fn ge(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().ge(&rhs)?;
        Ok(())
    }

    fn lt(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().lt(&rhs)?;
        Ok(())
    }

    fn le(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().le(&rhs)?;
        Ok(())
    }

    fn add(&mut self) -> Result<(), RuntimeError> {
        // NOTE: This function can't use the `apply_binary*` helper because rust borrow checker
        // disallow us from mutating the `self.heap` while calling the function. This happens
        // because the function also holds an exclusive reference to `self`.
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top()?;
        let res = match (*lhs, rhs) {
            // Operations on objects might allocate a new one.
            (Value::Object(o1), Value::Object(o2)) => match (&o1.content, &o2.content) {
                (ObjectContent::String(s1), ObjectContent::String(s2)) => {
                    let s1 = String::from_str(s1).expect("Infallible.");
                    let s2 = String::from_str(s2).expect("Infallible.");
                    let s = s1 + &s2;
                    Value::Object(self.vm.heap.alloc_string(s))
                }
                _ => {
                    return Err(RuntimeError::Value(ValueError::InvalidUse(
                        "Operands must be two numbers or two strings.",
                    )))
                }
            },
            // Non-objects can used the `ops::Add` implementation for `Value`
            _ => lhs.add(&rhs)?,
        };
        let top = self.vm.stack_top_mut()?;
        *top = res;
        Ok(())
    }

    fn sub(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().sub(&rhs)?;
        Ok(())
    }

    fn mul(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().mul(&rhs)?;
        Ok(())
    }

    fn div(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.vm.stack_pop()?;
        let lhs = self.vm.stack_top_mut()?;
        *lhs = lhs.deref().div(&rhs)?;
        Ok(())
    }

    fn not(&mut self) -> Result<(), RuntimeError> {
        let v = self.vm.stack_top_mut()?;
        *v = v.not();
        Ok(())
    }

    fn neg(&mut self) -> Result<(), RuntimeError> {
        let v = self.vm.stack_top_mut()?;
        *v = v.neg()?;
        Ok(())
    }

    fn print(&mut self) -> Result<(), RuntimeError> {
        let val = self.vm.stack_pop()?;
        println!("{val}");
        Ok(())
    }
}

struct CallFrame {
    fun: ObjectRef,
    ip: usize,
    slot: usize,
}

impl CallFrame {
    fn fun(&self) -> &RefCell<ObjFun> {
        self.fun.content.as_fun().expect("Expect function object.")
    }

    /// Read the next byte in the stream of bytecode instructions.
    fn read_byte(&mut self) -> u8 {
        let byte = self.fun().borrow_mut().chunk.instructions[self.ip];
        self.ip += 1;
        byte
    }

    /// Read the next 2 bytes in the stream of bytecode instructions.
    fn read_short(&mut self) -> u16 {
        let hi = self.fun().borrow_mut().chunk.instructions[self.ip] as u16;
        let lo = self.fun().borrow_mut().chunk.instructions[self.ip + 1] as u16;
        self.ip += 2;
        hi << 8 | lo
    }

    /// Read the next byte in the stream of bytecode instructions and return the constant at the
    /// index given by the byte.
    fn read_constant(&mut self) -> Value {
        let constant_id = self.read_byte() as usize;
        self.fun().borrow_mut().chunk.constants[constant_id]
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
