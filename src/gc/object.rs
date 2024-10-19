#![allow(missing_docs)]

use std::{cell::Cell, ptr::NonNull};

use crate::{list::List, opcode::Opcode, scan::Line};

use super::{Alloc, Gc, Ptr, Trace};

/// A enumeration of all supported primitive types in Lox and their underlying value.
#[derive(Debug, Clone, Copy)]
pub enum Value<'heap> {
    /// A nothing value in Lox
    Nil,
    /// A boolean value in Lox
    Bool(bool),
    /// A number value in Lox
    Number(f64),
    /// A heap-allocated object
    Object(Object<'heap>),
}

unsafe impl<'heap> Trace for Value<'heap> {
    fn trace(&self) {
        if let Self::Object(o) = self {
            o.trace();
        }
    }
}

/// A numeration of all object types.
#[derive(Clone, Copy, Debug)]
pub enum Object<'heap> {
    /// A string object
    String(Ptr<'heap, StringObject>),
    /// An upvalue object
    Upvalue(Ptr<'heap, UpvalueObject<'heap>>),
    /// A closure object
    Closure(Ptr<'heap, ClosureObject<'heap>>),
    /// A function object
    Function(Ptr<'heap, FunctionObject<'heap>>),
    /// A native function object
    NativeFunction(Ptr<'heap, NativeFunctionObject<'heap>>),
    /// A class object
    Class(Ptr<'heap, ClassObject<'heap>>),
    /// A class instance object
    Instance(Ptr<'heap, InstanceObject<'heap>>),
    /// A bound method object
    Method(Ptr<'heap, MethodObject<'heap>>),
}

unsafe impl<'heap> Trace for Object<'heap> {
    fn trace(&self) {
        match self {
            Object::String(s) => s.trace(),
            Object::Upvalue(u) => u.trace(),
            Object::Closure(c) => c.trace(),
            Object::Function(f) => f.trace(),
            Object::NativeFunction(n) => n.trace(),
            Object::Class(c) => c.trace(),
            Object::Instance(i) => i.trace(),
            Object::Method(m) => m.trace(),
        }
    }
}

#[derive(Debug)]
pub enum RootedObject<'root, 'heap> {
    /// A string object
    String(Gc<'root, Alloc<'heap, StringObject>>),
    /// An upvalue object
    Upvalue(Gc<'root, Alloc<'heap, UpvalueObject<'heap>>>),
    /// A closure object
    Closure(Gc<'root, Alloc<'heap, ClosureObject<'heap>>>),
    /// A function object
    Function(Gc<'root, Alloc<'heap, FunctionObject<'heap>>>),
    /// A native function object
    NativeFunction(Gc<'root, Alloc<'heap, NativeFunctionObject<'heap>>>),
    /// A class object
    Class(Gc<'root, Alloc<'heap, ClassObject<'heap>>>),
    /// A class instance object
    Instance(Gc<'root, Alloc<'heap, InstanceObject<'heap>>>),
    /// A bound method object
    Method(Gc<'root, Alloc<'heap, MethodObject<'heap>>>),
}

impl<'root, 'heap> From<Gc<'root, Object<'heap>>> for RootedObject<'root, 'heap> {
    fn from(value: Gc<'root, Object<'heap>>) -> Self {
        unsafe { std::mem::transmute(*value) }
    }
}

/// A type alias for a heap-allocated string.
pub type GcString<'heap> = Ptr<'heap, StringObject>;

/// The content of a heap-allocated string object.
#[derive(Debug)]
pub struct StringObject {
    pub data: String,
    pub hash: u32,
}

unsafe impl Trace for StringObject {
    fn trace(&self) {}
}

/// A type alias for a heap-allocated upvalue.
pub type GcUpvalue<'heap> = Ptr<'heap, Cell<UpvalueObject<'heap>>>;

#[derive(Clone, Copy, Debug)]
pub enum UpvalueObject<'heap> {
    Open(usize),
    Close(Object<'heap>),
}

unsafe impl<'heap> Trace for UpvalueObject<'heap> {
    fn trace(&self) {
        if let Self::Close(o) = self {
            o.trace();
        }
    }
}

/// A type alias for a heap-allocated closure.
pub type GcClosure<'heap> = Ptr<'heap, ClosureObject<'heap>>;

/// The content of a heap-allocated closure object.
#[derive(Debug)]
pub struct ClosureObject<'heap> {
    /// The function definition of this closure.
    pub fun: GcFunction<'heap>,
    /// The variables captured by this closure.
    pub upvalues: Vec<GcUpvalue<'heap>>,
}

unsafe impl<'heap> Trace for ClosureObject<'heap> {
    fn trace(&self) {
        self.fun.trace();
        self.upvalues.trace();
    }
}

impl<'root, 'heap> Gc<'root, Alloc<'heap, ClosureObject<'heap>>> {
    fn fun(self) -> Gc<'root, Alloc<'heap, FunctionObject<'heap>>> {
        unsafe { self.project(|alloc| alloc.get_ref().as_ref().fun.pin()) }
    }

    fn upvalues(self) -> Gc<'root, Vec<GcUpvalue<'heap>>> {
        unsafe { self.project(|alloc| alloc.map_unchecked(|alloc| &alloc.as_ref().upvalues)) }
    }
}

// A type alias for a heap-allocated fun.
pub type GcFunction<'heap> = Ptr<'heap, FunctionObject<'heap>>;

/// The content of a heap-allocated function object.
#[derive(Debug)]
pub struct FunctionObject<'heap> {
    /// The name of the function
    pub name: Option<GcString<'heap>>,
    /// Number of parameters the function has
    pub arity: u8,
    /// Number of upvalues captured by the function
    pub upvalue_count: usize,
    /// The bytecode chunk of this function
    pub chunk: Chunk<'heap>,
}

unsafe impl<'heap> Trace for FunctionObject<'heap> {
    fn trace(&self) {
        self.name.trace();
        self.chunk.trace();
    }
}

impl<'root, 'heap> Gc<'root, Alloc<'heap, FunctionObject<'heap>>> {
    fn name(self) -> Gc<'root, Option<GcString<'heap>>> {
        unsafe { self.project(|alloc| alloc.map_unchecked(|alloc| &alloc.as_ref().name)) }
    }

    fn chunk(self) -> Gc<'root, Chunk<'heap>> {
        unsafe { self.project(|alloc| alloc.map_unchecked(|alloc| &alloc.as_ref().chunk)) }
    }
}

// A type alias for a heap-allocated native fun.
pub type GcNativeFunction<'heap> = Ptr<'heap, NativeFunctionObject<'heap>>;

/// The content of a heap-allocated native function object.
#[derive(Debug)]
pub struct NativeFunctionObject<'heap> {
    /// Number of parameters
    pub arity: u8,
    /// Native function reference
    pub call: fn(&[Value<'heap>]) -> Value<'heap>,
}

unsafe impl<'heap> Trace for NativeFunctionObject<'heap> {
    fn trace(&self) {}
}

// A type alias for a heap-allocated class definition.
pub type GcClass<'heap> = Ptr<'heap, ClassObject<'heap>>;

/// The content of a heap-allocated class definition object.
#[derive(Debug)]
pub struct ClassObject<'heap> {
    /// The name of the class.
    pub name: GcString<'heap>,
    // /// All the methods defined in the class.
    // TODO: Add pub methods: Table<RefClosure>,
}

unsafe impl<'heap> Trace for ClassObject<'heap> {
    fn trace(&self) {
        self.name.trace();
    }
}

impl<'root, 'heap> Gc<'root, Alloc<'heap, ClassObject<'heap>>> {
    fn name(self) -> Gc<'root, Alloc<'heap, StringObject>> {
        unsafe { self.project(|alloc| alloc.get_ref().as_ref().name.pin()) }
    }
}
// A type alias for a heap-allocated class instance.
pub type GcInstance<'heap> = Ptr<'heap, InstanceObject<'heap>>;

/// The content of a heap-allocated class instance object.
#[derive(Debug)]
pub struct InstanceObject<'heap> {
    // The class of this instance.
    pub class: GcClass<'heap>,
    // /// All the fields defined in the instance.
    // TODO: Add pub fields: Table<Value<'heap>>,
}

unsafe impl<'heap> Trace for InstanceObject<'heap> {
    fn trace(&self) {
        self.class.trace();
    }
}

impl<'root, 'heap> Gc<'root, Alloc<'heap, InstanceObject<'heap>>> {
    fn class(self) -> Gc<'root, Alloc<'heap, ClassObject<'heap>>> {
        unsafe { self.project(|alloc| alloc.get_ref().as_ref().class.pin()) }
    }
}

// A type alias for a heap-allocated bound method.
pub type GcMethod<'heap> = Ptr<'heap, MethodObject<'heap>>;

/// The content of a heap-allocated bound method object.
#[derive(Debug)]
pub struct MethodObject<'heap> {
    pub receiver: Value<'heap>,
    pub method: GcClosure<'heap>,
}

unsafe impl<'heap> Trace for MethodObject<'heap> {
    fn trace(&self) {
        self.receiver.trace();
        self.method.trace();
    }
}

impl<'root, 'heap> Gc<'root, Alloc<'heap, MethodObject<'heap>>> {
    fn receiver(self) -> Gc<'root, Value<'heap>> {
        unsafe { self.project(|alloc| alloc.map_unchecked(|alloc| &alloc.as_ref().receiver)) }
    }

    fn method(self) -> Gc<'root, Alloc<'heap, ClosureObject<'heap>>> {
        unsafe { self.project(|alloc| alloc.get_ref().as_ref().method.pin()) }
    }
}

/// A chunk holds a sequence of instructions to be executes and their data.
#[derive(Debug, Default)]
pub struct Chunk<'heap> {
    pub instructions: Vec<u8>,
    pub constants: List<Value<'heap>, 256>,
    lines: Vec<RunLength<Line>>,
}

unsafe impl<'heap> Trace for Chunk<'heap> {
    fn trace(&self) {
        self.constants.trace();
    }
}

impl<'heap> Chunk<'heap> {
    /// Write an opcode into the chunk.
    pub fn write(&mut self, opcode: Opcode, line: Line) {
        self.write_byte(opcode.into(), line);
    }

    /// Write an arbitrarily byte into the chunk.
    pub fn write_byte(&mut self, byte: u8, line: Line) {
        self.instructions.push(byte);
        self.add_line(line);
    }

    /// Write a constant into the chunk and return its index. If the max number
    /// of constants is reached, we return None instead of Some(index).
    pub fn write_constant(&mut self, value: Value<'heap>) -> Option<u8> {
        u8::try_from(self.constants.len()).ok().inspect(|_| {
            // SAFETY: We already checked if the number of constants is valid by limiting the size
            // of our constant vector to `u8::MAX`.
            unsafe {
                self.constants.push_unchecked(value);
            }
        })
    }

    /// Get the line information of the bytecode at a specific offset.
    pub fn add_line(&mut self, line: Line) {
        match self.lines.last_mut() {
            Some(last_line) if last_line.data == line => last_line.length += 1,
            _ => self.lines.push(RunLength::new(line)),
        }
    }

    /// Get the line information of the bytecode at a specific offset.
    pub fn get_line(&self, offset: usize) -> Line {
        let mut length = 0;
        for line in &self.lines {
            length += line.length;
            if length > offset {
                return line.data;
            }
        }
        Line::default()
    }
}

#[derive(Debug)]
struct RunLength<T> {
    data: T,
    length: usize,
}

impl<T> RunLength<T> {
    const fn new(data: T) -> Self {
        Self { data, length: 1 }
    }
}
