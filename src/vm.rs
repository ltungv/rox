//! Implementation of the bytecode virtual machine.

use std::{
    cell::Cell,
    error, fmt,
    ops::{Add, Div, Mul, Neg, Not, Sub},
    ptr::NonNull,
};

use crate::{
    compile::{Parser, MAX_FRAMES},
    heap::Heap,
    object::{
        self, ObjBoundMethod, ObjClass, ObjClosure, ObjFun, ObjInstance, ObjNativeFun, ObjUpvalue,
        Object, RefBoundMethod, RefClass, RefClosure, RefFun, RefInstance, RefNativeFun, RefString,
        RefUpvalue,
    },
    opcode::{self, Opcode},
    static_vec::StaticVec,
    table::Table,
    value::{self, Value},
    InterpretError,
};

#[cfg(feature = "dbg-execution")]
use crate::chunk::disassemble_instruction;

/// The max number of values can be put onto the virtual machine's stack.
const VM_STACK_SIZE: usize = 256;

/// An enumeration of potential errors occur when running the byte codes.
#[derive(Debug)]
pub enum RuntimeError {
    /// Can't perform some operations given the current value(s).
    Value(value::Error),
    /// Can't perform some operations given the current object(s).
    Object(object::Error),
    /// Can't parse an invalid byte code.
    OpCode(opcode::Error),
    /// Overflow the virtual machine's stack.
    StackOverflow,
    /// Can't access a property.
    ObjectHasNoProperty,
    /// Can't access a field.
    ObjectHasNoField,
    /// Can't find a variable in scope.
    UndefinedVariable(String),
    /// Can't find a property in the instance.
    UndefinedProperty(String),
    /// Can't inherit objects that are not supported.
    InvalidSuperclass,
    /// Can't call objects that are not supported.
    InvalidCallee,
    /// Can't invoke objects that are not supported.
    InvalidMethodInvocation,
    /// Called a function/method with incorrect number of arguments.
    InvalidArgumentsCount {
        /// The arity of the function.
        arity: u8,
        /// The number of arguments given.
        argc: u8,
    },
}

impl error::Error for RuntimeError {}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(err) => err.fmt(f),
            Self::Object(err) => err.fmt(f),
            Self::OpCode(err) => err.fmt(f),
            Self::StackOverflow => f.write_str("Stack overflow."),
            Self::ObjectHasNoProperty => f.write_str("Only instances have properties."),
            Self::ObjectHasNoField => f.write_str("Only instances have fields."),
            Self::UndefinedVariable(name) => write!(f, "Undefined variable '{name}'."),
            Self::UndefinedProperty(name) => write!(f, "Undefined property '{name}'."),
            Self::InvalidSuperclass => f.write_str("Superclass must be a class."),
            Self::InvalidCallee => f.write_str("Can only call functions and classes."),
            Self::InvalidMethodInvocation => f.write_str("Only instances have methods."),
            Self::InvalidArgumentsCount { arity, argc } => {
                write!(f, "Expected {arity} arguments but got {argc}.",)
            }
        }
    }
}

impl From<value::Error> for RuntimeError {
    fn from(err: value::Error) -> Self {
        Self::Value(err)
    }
}

impl From<object::Error> for RuntimeError {
    fn from(err: object::Error) -> Self {
        Self::Object(err)
    }
}

impl From<opcode::Error> for RuntimeError {
    fn from(err: opcode::Error) -> Self {
        Self::OpCode(err)
    }
}

/// A bytecode virtual machine for the Lox programming language.
#[derive(Debug)]
pub struct VirtualMachine {
    stack: StaticVec<Value, VM_STACK_SIZE>,
    frames: StaticVec<CallFrame, MAX_FRAMES>,
    current_frame: NonNull<CallFrame>,
    open_upvalues: Vec<RefUpvalue>,
    globals: Table<Value>,
    grey_objects: Vec<Object>,
    heap: Heap,
    str_init: RefString,
}

impl VirtualMachine {
    /// Create a new virtual machine that prints to the given output.
    #[must_use]
    pub fn new() -> Option<Self> {
        let mut heap = Heap::default();
        let str_init = heap.intern(String::from("init"));
        let mut vm = Self {
            stack: StaticVec::default(),
            frames: StaticVec::default(),
            current_frame: NonNull::dangling(),
            open_upvalues: Vec::default(),
            globals: Table::default(),
            grey_objects: Vec::default(),
            heap,
            str_init,
        };
        match vm.setup_natives() {
            Ok(()) => Some(vm),
            Err(err) => {
                eprintln!("{err}");
                vm.trace_calls();
                vm.stack.clear();
                None
            }
        }
    }
}

impl VirtualMachine {
    /// Compile and execute the given source code.
    ///
    /// # Errors
    ///
    /// Return an error if the source code can't be compiled or if there's a runtime error.
    pub fn interpret(&mut self, src: &str) -> Result<(), InterpretError> {
        let parser = Parser::new(src, &mut self.heap);
        let fun = parser.compile().ok_or(InterpretError::Compile)?;
        self.run(fun).map_err(|err| {
            eprintln!("{err}");
            self.trace_calls();
            self.stack.clear();
            InterpretError::Runtime
        })
    }

    fn setup_natives(&mut self) -> Result<(), RuntimeError> {
        self.define_native("clock", 0, clock_native)?;
        Ok(())
    }

    fn run(&mut self, fun: ObjFun) -> Result<(), RuntimeError> {
        // Push the constant onto the stack so GC won't remove it while allocating the function.
        for constant in &fun.chunk.constants {
            self.stack_push(*constant)?;
        }
        let constant_count = fun.chunk.constants.len();
        let (fun_object, fun_ref) = self.alloc_fun(fun);
        // Remove all added constants.
        self.stack_remove_top(constant_count);

        // Push the function onto the stack so GC won't remove it while we allocating the closure.
        self.stack_push(Value::Object(fun_object))?;
        // Create a closure for the script function. Note that script can't have upvalues.
        let (closure_object, closure_ref) = self.alloc_closure(ObjClosure {
            fun: fun_ref,
            upvalues: Vec::new(),
        });
        // Pop the fun object as we no longer need it.
        self.stack_pop();

        // Push the closure onto the stack so GC won't remove for the entire runtime.
        self.stack_push(Value::Object(closure_object))?;
        // Start running the closure.
        self.call_closure(closure_ref, 0).and_then(|()| self.exec())
    }

    fn exec(&mut self) -> Result<(), RuntimeError> {
        loop {
            #[cfg(feature = "dbg-execution")]
            {
                self.trace_stack();
                let frame = self.frame();
                let offset = unsafe {
                    frame.ip.offset_from(
                        frame
                            .closure
                            .as_ref()
                            .fun
                            .as_ref()
                            .chunk
                            .instructions
                            .as_ptr(),
                    )
                };
                disassemble_instruction(
                    &frame.closure.as_ref().fun.as_ref().chunk,
                    usize::try_from(offset).expect("invalid ip."),
                );
            }

            match Opcode::try_from(self.read_byte())? {
                Opcode::Const => self.constant()?,
                Opcode::Nil => self.stack_push(Value::Nil)?,
                Opcode::True => self.stack_push(Value::Bool(true))?,
                Opcode::False => self.stack_push(Value::Bool(false))?,
                Opcode::Pop => {
                    self.stack_pop();
                }
                Opcode::GetLocal => self.get_local()?,
                Opcode::SetLocal => self.set_local(),
                Opcode::GetGlobal => self.get_global()?,
                Opcode::SetGlobal => self.set_global()?,
                Opcode::DefineGlobal => self.define_global()?,
                Opcode::GetUpvalue => self.get_upvalue()?,
                Opcode::SetUpvalue => self.set_upvalue(),
                Opcode::GetProperty => self.get_property()?,
                Opcode::SetProperty => self.set_property()?,
                Opcode::GetSuper => self.get_super()?,
                Opcode::NE => self.ne(),
                Opcode::EQ => self.eq(),
                Opcode::GT => self.gt()?,
                Opcode::GE => self.ge()?,
                Opcode::LT => self.lt()?,
                Opcode::LE => self.le()?,
                Opcode::Add => self.add()?,
                Opcode::Sub => self.sub()?,
                Opcode::Mul => self.mul()?,
                Opcode::Div => self.div()?,
                Opcode::Not => self.not(),
                Opcode::Neg => self.neg()?,
                Opcode::Print => self.print(),
                Opcode::Jump => self.jump(JumpDirection::Forward),
                Opcode::JumpIfTrue => self.jump_if_true(),
                Opcode::JumpIfFalse => self.jump_if_false(),
                Opcode::Loop => self.jump(JumpDirection::Backward),
                Opcode::Call => self.call()?,
                Opcode::Invoke => self.invoke()?,
                Opcode::SuperInvoke => self.super_invoke()?,
                Opcode::Closure => self.closure()?,
                Opcode::CloseUpvalue => self.close_upvalue(),
                Opcode::Ret => {
                    if self.ret()? {
                        break;
                    }
                }
                Opcode::Class => self.class()?,
                Opcode::Inherit => self.inherit()?,
                Opcode::Method => self.method()?,
            }
        }
        Ok(())
    }

    fn super_invoke(&mut self) -> Result<(), RuntimeError> {
        let method = self.read_constant().as_string()?;
        let argc = self.read_byte();

        let superclass = self.stack_pop().as_class()?;
        self.invoke_from_class(superclass, method, argc)?;
        Ok(())
    }

    fn invoke(&mut self) -> Result<(), RuntimeError> {
        let method = self.read_constant().as_string()?;
        let argc = self.read_byte();

        let receiver = self.stack_top(argc as usize);
        let instance = receiver
            .as_instance()
            .map_err(|_| RuntimeError::InvalidMethodInvocation)?;

        if let Some(field) = instance.as_ref().fields.get(method) {
            *self.stack_top_mut(argc as usize) = field;
            self.call_value(field, argc)?;
        } else {
            self.invoke_from_class(instance.as_ref().class, method, argc)?;
        }

        Ok(())
    }

    fn invoke_from_class(
        &mut self,
        class: RefClass,
        name: RefString,
        argc: u8,
    ) -> Result<(), RuntimeError> {
        let class_ref = class;
        let method = class_ref
            .as_ref()
            .methods
            .get(name)
            .ok_or_else(|| RuntimeError::UndefinedProperty(name.as_ref().to_string()))?;
        self.call_closure(method, argc)?;
        Ok(())
    }

    // Bind a method to a class definition. At this moment, a closure object should be the top most
    // item in the stack, and a class definition object should be the second top most item.
    fn method(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let closure = self.stack_pop().as_closure()?;
        let class = self.stack_top(0).as_class()?;
        class.as_ref().methods.set(name, closure);
        Ok(())
    }

    fn bind_method(&mut self, class: RefClass, name: RefString) -> Result<bool, RuntimeError> {
        match class.as_ref().methods.get(name) {
            Some(method) => {
                let (bound, _) = self.alloc_bound_method(ObjBoundMethod {
                    receiver: *self.stack_top(0),
                    method,
                });
                self.stack_pop();
                self.stack_push(Value::Object(bound))?;
                Ok(true)
            }
            None => Ok(false),
        }
    }

    fn get_property(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let instance = self
            .stack_top(0)
            .as_instance()
            .map_err(|_| RuntimeError::ObjectHasNoProperty)?;

        if let Some(value) = instance.as_ref().fields.get(name) {
            self.stack_pop();
            self.stack_push(value)?;
            Ok(())
        } else if self.bind_method(instance.as_ref().class, name)? {
            Ok(())
        } else {
            Err(RuntimeError::UndefinedProperty(name.as_ref().to_string()))
        }
    }

    fn set_property(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let value = self.stack_pop();
        let instance = self
            .stack_top(0)
            .as_instance()
            .map_err(|_| RuntimeError::ObjectHasNoField)?;

        instance.as_ref().fields.set(name, value);
        self.stack_pop();
        self.stack_push(value)?;
        Ok(())
    }

    fn get_super(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let superclass = self.stack_pop().as_class()?;
        if !self.bind_method(superclass, name)? {
            return Err(RuntimeError::UndefinedProperty(name.as_ref().to_string()));
        }
        Ok(())
    }

    fn class(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let (class, _) = self.alloc_class(ObjClass::new(name));
        self.stack_push(Value::Object(class))?;
        Ok(())
    }

    fn inherit(&mut self) -> Result<(), RuntimeError> {
        let superclass = self
            .stack_top(1)
            .as_class()
            .map_err(|_| RuntimeError::InvalidSuperclass)?;
        let subclass = self.stack_top(0).as_class()?;
        for (method_name, method) in &superclass.as_ref().methods {
            subclass.as_ref().methods.set(method_name, method);
        }
        self.stack_pop();
        Ok(())
    }

    /// Get the value of the variable capture by an upvalue.
    fn get_upvalue(&mut self) -> Result<(), RuntimeError> {
        let upvalue_slot = self.read_byte();
        let upvalue = self.frame().closure.as_ref().upvalues[upvalue_slot as usize];
        match upvalue.as_ref().get() {
            // Value is on the stack.
            ObjUpvalue::Open(stack_slot) => {
                // SAFETY: The compiler should produce safe byte codes such that we never
                // access uninitialized data.
                let value = unsafe { self.stack.get_unchecked(stack_slot) };
                self.stack_push(*value)?;
            }
            // Value is on the heap.
            ObjUpvalue::Closed(value) => {
                self.stack_push(value)?;
            }
        }
        Ok(())
    }

    /// Set the value of the variable capture by an upvalue.
    fn set_upvalue(&mut self) {
        let upvalue_slot = self.read_byte();
        let value = *self.stack_top(0);
        let upvalue = self.frame().closure.as_ref().upvalues[upvalue_slot as usize];
        match upvalue.as_ref().get() {
            // Value is on the stack.
            ObjUpvalue::Open(stack_slot) => {
                // SAFETY: The compiler should produce safe code that access a safe part of the stack.
                let v = unsafe { self.stack.get_unchecked_mut(stack_slot) };
                *v = value;
            }
            // Value is on the heap.
            ObjUpvalue::Closed(_) => {
                upvalue.as_ref().set(ObjUpvalue::Closed(value));
            }
        }
    }

    fn closure(&mut self) -> Result<(), RuntimeError> {
        let fun = self.read_constant().as_fun()?;
        let mut upvalues = Vec::with_capacity(fun.as_ref().upvalue_count);
        for _ in 0..upvalues.capacity() {
            let is_local = self.read_byte() == 1;
            let index = self.read_byte() as usize;
            if is_local {
                upvalues.push(self.capture_upvalue(self.frame().slot + index));
            } else {
                upvalues.push(self.frame().closure.as_ref().upvalues[index]);
            }
        }

        let (closure, _) = self.alloc_closure(ObjClosure { fun, upvalues });
        self.stack_push(Value::Object(closure))?;

        Ok(())
    }

    fn close_upvalue(&mut self) {
        self.close_upvalues(self.stack.len() - 1);
        self.stack_pop();
    }

    /// Create an open upvalue capturing the variable at the stack index given by `location`.
    fn capture_upvalue(&mut self, location: usize) -> RefUpvalue {
        // Check if there's an existing open upvalues that references the same stack slot. We want
        // to close over a variable not a value. Thus, closures can shared data through the same
        // captured variable.
        for upvalue in &self.open_upvalues {
            if let ObjUpvalue::Open(loc) = upvalue.as_ref().get() {
                if loc == location {
                    return *upvalue;
                }
            }
        }
        // Make a new open upvalue.
        let (_, upvalue_ref) = self.alloc_upvalue(ObjUpvalue::Open(location));
        self.open_upvalues.push(upvalue_ref);
        upvalue_ref
    }

    // Close all upvalues whose referenced stack slot went out of scope. Here, `last` is the lowest
    // stack slot that went out of scope.
    fn close_upvalues(&mut self, last: usize) {
        for upvalue in &self.open_upvalues {
            // Check if we reference a slot that went out of scope.
            let stack_slot = match upvalue.as_ref().get() {
                ObjUpvalue::Open(slot) if slot >= last => Some(slot),
                _ => None,
            };
            // Hoist the variable up into the upvalue so it can live after the stack frame is pop.
            if let Some(slot) = stack_slot {
                // SAFETY: The compiler should produce safe code that access a safe part of the stack.
                let v = unsafe { self.stack.get_unchecked(slot) };
                upvalue.as_ref().set(ObjUpvalue::Closed(*v));
            }
        }
        // remove closed upvalues from list of open upvalues
        self.open_upvalues
            .retain(|v| matches!(v.as_ref().get(), ObjUpvalue::Open(_)));
    }

    /// Return from a function call
    fn ret(&mut self) -> Result<bool, RuntimeError> {
        // Get the result of the function.
        let result = self.stack_pop();
        // The compiler didn't emit Opcode::CloseUpvalue at the end of each of the outer most scope
        // that defines the body. That scope contains function parameters and also local variables
        // that need to be closed over.
        self.close_upvalues(self.frame().slot);
        let frame = self.frames_pop();
        if self.frames.len() == 0 {
            // Have reach the end of the script if there's no stack frame left.
            self.stack_pop();
            return Ok(true);
        }
        // Pop all data related to the stack frame.
        self.stack_remove_top(self.stack.len() - frame.slot);
        // Put the function result on the stack.
        self.stack_push(result)?;
        Ok(false)
    }

    fn call(&mut self) -> Result<(), RuntimeError> {
        let argc = self.read_byte();
        let v = self.stack_top(argc as usize);
        self.call_value(*v, argc)?;
        Ok(())
    }

    fn call_value(&mut self, callee: Value, argc: u8) -> Result<(), RuntimeError> {
        match callee {
            Value::Object(o) => self.call_object(o, argc),
            _ => Err(RuntimeError::InvalidCallee),
        }
    }

    fn call_object(&mut self, callee: Object, argc: u8) -> Result<(), RuntimeError> {
        match &callee {
            Object::Closure(c) => self.call_closure(*c, argc),
            Object::NativeFun(f) => self.call_native(*f, argc),
            Object::Class(c) => self.call_class(*c, argc),
            Object::BoundMethod(m) => self.call_bound_method(*m, argc),
            _ => Err(RuntimeError::InvalidCallee),
        }
    }

    fn call_closure(&mut self, callee: RefClosure, argc: u8) -> Result<(), RuntimeError> {
        if argc != callee.as_ref().fun.as_ref().arity {
            return Err(RuntimeError::InvalidArgumentsCount {
                arity: callee.as_ref().fun.as_ref().arity,
                argc,
            });
        }
        let frame = CallFrame {
            closure: callee,
            ip: callee.as_ref().fun.as_ref().chunk.instructions.as_ptr(),
            slot: self.stack.len() - argc as usize - 1,
        };
        self.frames_push(frame)?;
        Ok(())
    }

    fn call_native(&mut self, callee: RefNativeFun, argc: u8) -> Result<(), RuntimeError> {
        if argc != callee.as_ref().arity {
            return Err(RuntimeError::InvalidArgumentsCount {
                arity: callee.as_ref().arity,
                argc,
            });
        }
        let argc = argc as usize;
        let call = callee.as_ref().call;
        let res = call(self.stack.last_chunk(argc));
        self.stack_remove_top(argc + 1);
        self.stack_push(res)?;
        Ok(())
    }

    fn call_class(&mut self, callee: RefClass, argc: u8) -> Result<(), RuntimeError> {
        // Allocate a new instance and put it on top of the stack.
        let (instance, _) = self.alloc_instance(ObjInstance::new(callee));
        *self.stack_top_mut(argc.into()) = Value::Object(instance);
        // Call the 'init' method if there's one
        if let Some(init) = callee.as_ref().methods.get(self.str_init) {
            self.call_closure(init, argc)?;
        } else if argc != 0 {
            return Err(RuntimeError::InvalidArgumentsCount { arity: 0, argc });
        }
        Ok(())
    }

    fn call_bound_method(&mut self, callee: RefBoundMethod, argc: u8) -> Result<(), RuntimeError> {
        *self.stack_top_mut(argc as usize) = callee.as_ref().receiver;
        self.call_closure(callee.as_ref().method, argc)?;
        Ok(())
    }

    fn jump(&mut self, direction: JumpDirection) {
        let offset = self.read_short();
        let frame = self.frame_mut();
        unsafe {
            match direction {
                JumpDirection::Forward => frame.ip = frame.ip.add(offset as usize),
                JumpDirection::Backward => frame.ip = frame.ip.sub(offset as usize),
            }
        }
    }

    fn jump_if_true(&mut self) {
        let offset = self.read_short();
        let val = self.stack_top(0);
        if val.is_truthy() {
            let frame = self.frame_mut();
            frame.ip = unsafe { frame.ip.add(offset as usize) };
        }
    }

    fn jump_if_false(&mut self) {
        let offset = self.read_short();
        let val = self.stack_top(0);
        if val.is_falsey() {
            let frame = self.frame_mut();
            frame.ip = unsafe { frame.ip.add(offset as usize) };
        }
    }

    /// Get a local variable.
    fn get_local(&mut self) -> Result<(), RuntimeError> {
        let slot = self.read_byte() as usize;
        let frame_slot = self.frame().slot;
        // SAFETY: The compiler should produce safe code that access a safe part of the stack.
        let value = unsafe { self.stack.get_unchecked(frame_slot + slot) };
        self.stack_push(*value)?;
        Ok(())
    }

    /// Set a local variable.
    fn set_local(&mut self) {
        let slot = self.read_byte() as usize;
        let frame_slot = self.frame().slot;
        let value = *self.stack_top(0);
        // SAFETY: The compiler should produce safe code that access a safe part of the stack.
        let v = unsafe { self.stack.get_unchecked_mut(frame_slot + slot) };
        *v = value;
    }

    /// Get a global variable or return a runtime error if it was not found.
    fn get_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let value = self
            .globals
            .get(name)
            .ok_or_else(|| RuntimeError::UndefinedVariable(name.as_ref().to_string()))?;
        self.stack_push(value)?;
        Ok(())
    }

    /// Set a global variable or return a runtime error if it was not found.
    fn set_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let value = self.stack_top(0);
        if self.globals.get(name).is_none() {
            return Err(RuntimeError::UndefinedVariable(name.as_ref().to_string()));
        }
        self.globals.set(name, *value);
        Ok(())
    }

    /// Declare a variable with some initial value.
    fn define_global(&mut self) -> Result<(), RuntimeError> {
        let name = self.read_constant().as_string()?;
        let value = self.stack_pop();
        self.globals.set(name, value);
        Ok(())
    }

    /// Read the constant id from the next byte and load the constant with the found id.
    fn constant(&mut self) -> Result<(), RuntimeError> {
        let constant = self.read_constant();
        self.stack_push(constant)?;
        Ok(())
    }

    fn ne(&mut self) {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).ne(&rhs));
    }

    fn eq(&mut self) {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).eq(&rhs));
    }

    fn gt(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).gt(&rhs)?);
        Ok(())
    }

    fn ge(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).ge(&rhs)?);
        Ok(())
    }

    fn lt(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).lt(&rhs)?);
        Ok(())
    }

    fn le(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = Value::Bool((*lhs).le(&rhs)?);
        Ok(())
    }

    fn add(&mut self) -> Result<(), RuntimeError> {
        // The peek the first 2 items on the stack instead of pop so the GC can see them and won't
        // deallocate the objects when we allocate a new object for the result.
        let rhs = self.stack_top(0);
        let lhs = self.stack_top(1);
        let result = match (*lhs, rhs) {
            // Operations on objects might allocate a new one.
            (Value::Object(o1), Value::Object(o2)) => match (o1, o2) {
                (Object::String(s1), Object::String(s2)) => {
                    let mut s =
                        String::with_capacity(s1.as_ref().data.len() + s1.as_ref().data.len());
                    s.push_str(s1.as_ref().data.as_ref());
                    s.push_str(s2.as_ref().data.as_ref());
                    let (object, _) = self.alloc_string(s);
                    Value::Object(object)
                }
                _ => {
                    return Err(RuntimeError::Value(
                        value::Error::BinaryOperandsMustBeNumbersOrStrings,
                    ))
                }
            },
            // Non-objects can used the `ops::Add` implementation for `Value`
            _ => lhs.add(rhs)?,
        };
        // Remove the RHS.
        self.stack_pop();
        // Update the LHS.
        *self.stack_top_mut(0) = result;
        Ok(())
    }

    fn sub(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = lhs.sub(&rhs)?;
        Ok(())
    }

    fn mul(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = lhs.mul(&rhs)?;
        Ok(())
    }

    fn div(&mut self) -> Result<(), RuntimeError> {
        let rhs = self.stack_pop();
        let lhs = self.stack_top_mut(0);
        *lhs = lhs.div(&rhs)?;
        Ok(())
    }

    fn not(&mut self) {
        let v = self.stack_top_mut(0);
        *v = v.not();
    }

    fn neg(&mut self) -> Result<(), RuntimeError> {
        let v = self.stack_top_mut(0);
        *v = v.neg()?;
        Ok(())
    }

    fn print(&mut self) {
        let val = self.stack_pop();
        println!("{val}");
    }

    fn gc(&mut self) {
        if self.heap.size() <= self.heap.next_gc() {
            return;
        }

        #[cfg(feature = "dbg-heap")]
        let before = {
            println!("-- gc begin");
            self.heap.size()
        };

        self.mark_sweep();

        #[cfg(feature = "dbg-heap")]
        {
            let after = self.heap.size();
            let next = self.heap.next_gc();
            let delta = before.abs_diff(after);
            println!("-- gc end");
            println!("   collected {delta} bytes (from {before} to {after}) next at {next}");
        };
    }

    fn mark_sweep(&mut self) {
        self.mark_roots();
        while let Some(grey_object) = self.grey_objects.pop() {
            grey_object.mark_references(&mut self.grey_objects);
        }
        // SAFETY: We make sure that the sweep step has correctly mark all reachable objects, so
        // sweep can be run safely.
        unsafe { self.heap.sweep() };
    }

    fn mark_roots(&mut self) {
        self.grey_objects.clear();
        if self.str_init.mark() {
            self.grey_objects.push(Object::String(self.str_init));
        }
        for value in &self.stack {
            if let Value::Object(o) = value {
                o.mark(&mut self.grey_objects);
            }
        }
        for frame in &self.frames {
            if frame.closure.mark() {
                self.grey_objects.push(Object::Closure(frame.closure));
            }
        }
        for upvalue in &self.open_upvalues {
            if upvalue.mark() {
                self.grey_objects.push(Object::Upvalue(*upvalue));
            }
        }
        for (k, v) in &self.globals {
            if k.mark() {
                self.grey_objects.push(Object::String(k));
            }
            if let Value::Object(o) = v {
                o.mark(&mut self.grey_objects);
            }
        }
    }

    /// Read the next byte in the stream of bytecode instructions.
    fn read_byte(&mut self) -> u8 {
        // SAFETY: The compiler should produce correct byte codes
        // so we never read an out-of-bound index.
        unsafe { self.frame_mut().read_byte() }
    }

    /// Read the next 2 bytes in the stream of bytecode instructions.
    fn read_short(&mut self) -> u16 {
        // SAFETY: The compiler should produce correct byte codes
        // so we never read an out-of-bound index.
        unsafe { self.frame_mut().read_short() }
    }

    /// Read the next byte in the stream of bytecode instructions and return the constant at the
    /// index given by the byte.
    fn read_constant(&mut self) -> Value {
        // SAFETY: The compiler should produce correct byte codes
        // so we never read an out-of-bound index.
        unsafe { self.frame_mut().read_constant() }
    }

    const fn frame(&self) -> &CallFrame {
        unsafe { self.current_frame.as_ref() }
    }

    fn frame_mut(&mut self) -> &mut CallFrame {
        unsafe { self.current_frame.as_mut() }
    }

    fn frames_push(&mut self, frame: CallFrame) -> Result<usize, RuntimeError> {
        let frame_count = self.frames.len();
        if frame_count == MAX_FRAMES {
            return Err(RuntimeError::StackOverflow);
        }
        // SAFETY: We already checked if the stack frame is full.
        unsafe { self.frames.push_unchecked(frame) };
        self.current_frame = NonNull::from(self.frames.last_mut(0));
        Ok(frame_count)
    }

    fn frames_pop(&mut self) -> CallFrame {
        let ret = self.frames.pop();
        if self.frames.len() > 0 {
            self.current_frame = NonNull::from(self.frames.last_mut(0));
        }
        ret
    }

    fn stack_push(&mut self, value: Value) -> Result<(), RuntimeError> {
        if self.stack.len() == VM_STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }
        // SAFETY: We already checked if the stack is full.
        unsafe { self.stack.push_unchecked(value) };
        Ok(())
    }

    fn stack_pop(&mut self) -> Value {
        self.stack.pop()
    }

    fn stack_top(&self, n: usize) -> &Value {
        self.stack.last(n)
    }

    fn stack_top_mut(&mut self, n: usize) -> &mut Value {
        self.stack.last_mut(n)
    }

    fn stack_remove_top(&mut self, n: usize) {
        self.stack.remove(n);
    }

    fn trace_calls(&self) {
        for frame in self.frames.into_iter().rev() {
            let offset = unsafe {
                usize::try_from(
                    frame.ip.offset_from(
                        frame
                            .closure
                            .as_ref()
                            .fun
                            .as_ref()
                            .chunk
                            .instructions
                            .as_ptr(),
                    ),
                )
                .expect("invalid ip.")
            };
            let line = frame
                .closure
                .as_ref()
                .fun
                .as_ref()
                .chunk
                .get_line(offset - 1);
            frame
                .closure
                .as_ref()
                .fun
                .as_ref()
                .name
                .as_ref()
                .map_or_else(
                    || eprintln!("{line} in script."),
                    |s| eprintln!("{line} in {}().", s.as_ref().data),
                );
        }
    }

    fn define_native(
        &mut self,
        name: &str,
        arity: u8,
        call: fn(&[Value]) -> Value,
    ) -> Result<(), RuntimeError> {
        let (name, name_ref) = self.alloc_string(String::from(name));
        self.stack_push(Value::Object(name))?;
        let (fun, _) = self.alloc_native_fun(ObjNativeFun { arity, call });
        self.stack_push(Value::Object(fun))?;
        self.globals.set(name_ref, *self.stack_top(0));

        self.stack_pop();
        self.stack_pop();
        Ok(())
    }

    fn alloc_string(&mut self, s: String) -> (Object, RefString) {
        self.gc();
        let s = self.heap.intern(s);
        (Object::String(s), s)
    }

    fn alloc_upvalue(&mut self, upvalue: ObjUpvalue) -> (Object, RefUpvalue) {
        self.gc();
        self.heap.alloc(Cell::new(upvalue), Object::Upvalue)
    }

    fn alloc_closure(&mut self, closure: ObjClosure) -> (Object, RefClosure) {
        self.gc();
        self.heap.alloc(closure, Object::Closure)
    }

    fn alloc_fun(&mut self, fun: ObjFun) -> (Object, RefFun) {
        self.gc();
        self.heap.alloc(fun, Object::Fun)
    }

    fn alloc_native_fun(&mut self, native_fun: ObjNativeFun) -> (Object, RefNativeFun) {
        self.gc();
        self.heap.alloc(native_fun, Object::NativeFun)
    }

    fn alloc_class(&mut self, class: ObjClass) -> (Object, RefClass) {
        self.gc();
        self.heap.alloc(class, Object::Class)
    }

    fn alloc_instance(&mut self, instance: ObjInstance) -> (Object, RefInstance) {
        self.gc();
        self.heap.alloc(instance, Object::Instance)
    }

    fn alloc_bound_method(&mut self, method: ObjBoundMethod) -> (Object, RefBoundMethod) {
        self.gc();
        self.heap.alloc(method, Object::BoundMethod)
    }

    #[cfg(feature = "dbg-execution")]
    fn trace_stack(&self) {
        print!("          ");
        for value in &self.stack {
            print!("[ {value} ]");
        }
        println!();
    }
}

fn clock_native(_args: &[Value]) -> Value {
    let start = std::time::SystemTime::now();
    let since_epoch = start
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or(std::time::Duration::ZERO);
    Value::Number(since_epoch.as_secs_f64())
}

#[derive(Debug)]
struct CallFrame {
    closure: RefClosure,
    ip: *const u8,
    slot: usize,
}

impl CallFrame {
    /// Read the next byte in the stream of bytecode instructions.
    unsafe fn read_byte(&mut self) -> u8 {
        let byte = *self.ip;
        self.ip = self.ip.add(1);
        byte
    }

    /// Read the next 2 bytes in the stream of bytecode instructions.
    unsafe fn read_short(&mut self) -> u16 {
        let hi = u16::from(*self.ip);
        let lo = u16::from(*self.ip.add(1));
        self.ip = self.ip.add(2);
        hi << 8 | lo
    }

    /// Read the next byte in the stream of bytecode instructions and return the constant at the
    /// index given by the byte.
    unsafe fn read_constant(&mut self) -> Value {
        let constant_id = *self.ip;
        self.ip = self.ip.add(1);
        *self
            .closure
            .as_ref()
            .fun
            .as_ref()
            .chunk
            .constants
            .get_unchecked(constant_id as usize)
    }
}

/// An enumeration that determine whether to jump forward or backward along the stream of
/// bytecode instructions.
#[derive(Clone, Copy)]
pub enum JumpDirection {
    /// Jump forward.
    Forward,
    /// Jump backward.
    Backward,
}
