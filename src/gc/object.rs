#![allow(missing_docs)]

use std::cell::Cell;

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
    // TODO: Replace chunk with the one that uses the new object type.
    pub chunk: Chunk<'heap>,
}

unsafe impl<'heap> Trace for FunctionObject<'heap> {
    fn trace(&self) {
        self.name.trace();
        self.chunk.trace();
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
    // TODO: Replace Object with Value.
    pub call: fn(&[Object<'heap>]) -> Object<'heap>,
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
    fn trace(&self) {}
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
    fn trace(&self) {}
}

// A type alias for a heap-allocated bound method.
pub type GcMethod<'heap> = Ptr<'heap, MethodObject<'heap>>;

/// The content of a heap-allocated bound method object.
#[derive(Debug)]
pub struct MethodObject<'heap> {
    // TODO: Replace Object with Value.
    pub receiver: Object<'heap>,
    pub method: GcClosure<'heap>,
}

unsafe impl<'heap> Trace for MethodObject<'heap> {
    fn trace(&self) {}
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

// /// Go through the instructions in the chunk and display them in human-readable format.
// #[cfg(feature = "dbg-execution")]
// pub fn disassemble<'heap>(chunk: &Chunk<'heap>, name: &str) {
//     println!("== {name} ==");
//     let mut offset = 0;
//     while offset < chunk.instructions.len() {
//         offset = disassemble_instruction(chunk, offset);
//     }
// }
//
// /// Display an instruction in human readable format.
// #[cfg(feature = "dbg-execution")]
// pub fn disassemble_instruction<'heap>(chunk: &Chunk<'heap>, offset: usize) -> usize {
//     use crate::vm::JumpDirection;
//
//     let line_current = chunk.get_line(offset);
//     let line_previous = chunk.get_line(offset.saturating_sub(1));
//     // Annotation for separating instructions from different lines.
//     print!("{offset:04} ");
//     if offset > 0 && line_current == line_previous {
//         print!("   | ");
//     } else {
//         print!("{:4} ", *line_current);
//     }
//     let instruction = match Opcode::try_from(chunk.instructions[offset]) {
//         Ok(inst) => inst,
//         Err(err) => panic!("{}", err),
//     };
//     // Print each individual instruction.
//     match instruction {
//         Opcode::Const => disassemble_constant(chunk, offset, "OP_CONST"),
//         Opcode::Nil => disassemble_simple(offset, "OP_NIL"),
//         Opcode::True => disassemble_simple(offset, "OP_TRUE"),
//         Opcode::False => disassemble_simple(offset, "OP_FALSE"),
//         Opcode::Pop => disassemble_simple(offset, "OP_POP"),
//         Opcode::GetLocal => disassemble_byte(chunk, offset, "OP_GET_LOCAL"),
//         Opcode::SetLocal => disassemble_byte(chunk, offset, "OP_SET_LOCAL"),
//         Opcode::GetGlobal => disassemble_constant(chunk, offset, "OP_GET_GLOBAL"),
//         Opcode::SetGlobal => disassemble_constant(chunk, offset, "OP_SET_GLOBAL"),
//         Opcode::DefineGlobal => disassemble_constant(chunk, offset, "OP_DEFINE_GLOBAL"),
//         Opcode::GetUpvalue => disassemble_byte(chunk, offset, "OP_GET_UPVALUE"),
//         Opcode::SetUpvalue => disassemble_byte(chunk, offset, "OP_SET_UPVALUE"),
//         Opcode::GetProperty => disassemble_constant(chunk, offset, "OP_GET_PROPERTY"),
//         Opcode::SetProperty => disassemble_constant(chunk, offset, "OP_SET_PROPERTY"),
//         Opcode::GetSuper => disassemble_constant(chunk, offset, "OP_GET_SUPER"),
//         Opcode::NE => disassemble_simple(offset, "OP_NE"),
//         Opcode::EQ => disassemble_simple(offset, "OP_EQ"),
//         Opcode::GT => disassemble_simple(offset, "OP_GT"),
//         Opcode::GE => disassemble_simple(offset, "OP_GE"),
//         Opcode::LT => disassemble_simple(offset, "OP_LT"),
//         Opcode::LE => disassemble_simple(offset, "OP_LE"),
//         Opcode::Add => disassemble_simple(offset, "OP_ADD"),
//         Opcode::Sub => disassemble_simple(offset, "OP_SUB"),
//         Opcode::Mul => disassemble_simple(offset, "OP_MUL"),
//         Opcode::Div => disassemble_simple(offset, "OP_DIV"),
//         Opcode::Not => disassemble_simple(offset, "OP_NOT"),
//         Opcode::Neg => disassemble_simple(offset, "OP_NEG"),
//         Opcode::Print => disassemble_simple(offset, "OP_PRINT"),
//         Opcode::Jump => disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP"),
//         Opcode::JumpIfTrue => {
//             disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP_IF_TRUE")
//         }
//         Opcode::JumpIfFalse => {
//             disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP_IF_FALSE")
//         }
//         Opcode::Loop => disassemble_jump(chunk, offset, JumpDirection::Backward, "OP_LOOP"),
//         Opcode::Call => disassemble_byte(chunk, offset, "OP_CALL"),
//         Opcode::Invoke => disassemble_invoke(chunk, offset, "OP_INVOKE"),
//         Opcode::SuperInvoke => disassemble_invoke(chunk, offset, "OP_SUPER_INVOKE"),
//         Opcode::Closure => {
//             let mut offset = offset + 1;
//             let constant_id = chunk.instructions[offset] as usize;
//             // SAFETY: The compiler must work correctly.
//             let constant = unsafe { chunk.constants.get_unchecked(constant_id) };
//             offset += 1;
//             println!("{:-16} {constant_id:4} {constant}", "OP_CLOSURE");
//             let fun = constant.as_fun().expect("expect function object.");
//             let upvalue_count = fun.as_ref().upvalue_count;
//             for _ in 0..upvalue_count {
//                 let is_local = chunk.instructions[offset + 1] == 1;
//                 let index = chunk.instructions[offset + 2];
//                 let upvalue_type = if is_local { "local" } else { "upvalue" };
//                 println!("{offset:04}    |                     {upvalue_type} {index}");
//                 offset += 2;
//             }
//             offset
//         }
//         Opcode::CloseUpvalue => disassemble_simple(offset, "OP_CLOSE_UPVALUE"),
//         Opcode::Ret => disassemble_simple(offset, "OP_RET"),
//         Opcode::Class => disassemble_constant(chunk, offset, "OP_CLASS"),
//         Opcode::Inherit => disassemble_simple(offset, "OP_INHERIT"),
//         Opcode::Method => disassemble_constant(chunk, offset, "OP_METHOD"),
//     }
// }
//
// /// Display a simple instruction in human-readable format.
// #[cfg(feature = "dbg-execution")]
// fn disassemble_simple(offset: usize, name: &'static str) -> usize {
//     println!("{name}");
//     offset + 1
// }
//
// /// Display a constant instruction in human-readable format.
// #[cfg(feature = "dbg-execution")]
// fn disassemble_constant(chunk: &Chunk, offset: usize, name: &'static str) -> usize {
//     let constant_id = chunk.instructions[offset + 1] as usize;
//     // SAFETY: The compiler must work correctly.
//     let constant = unsafe { chunk.constants.get_unchecked(constant_id) };
//     println!("{name:-16} {constant_id:4} {constant}");
//     offset + 2
// }
//
// /// Display a byte instruction in human-readable format.
// #[cfg(feature = "dbg-execution")]
// fn disassemble_byte(chunk: &Chunk, offset: usize, name: &'static str) -> usize {
//     let slot = chunk.instructions[offset + 1] as usize;
//     println!("{name:-16} {slot:4}");
//     offset + 2
// }
//
// /// Display a jump instruction in human-readable format.
// #[cfg(feature = "dbg-execution")]
// fn disassemble_jump(chunk: &Chunk, offset: usize, dir: JumpDirection, name: &'static str) -> usize {
//     let hi = u16::from(chunk.instructions[offset + 1]);
//     let lo = u16::from(chunk.instructions[offset + 2]);
//     let jump = hi << 8 | lo;
//     let target = match dir {
//         JumpDirection::Forward => offset + 3 + jump as usize,
//         JumpDirection::Backward => offset + 3 - jump as usize,
//     };
//     println!("{name:-16} {offset:4} -> {target}");
//     offset + 3
// }
//
// /// Display a invoke instruction in human-readable format.
// #[cfg(feature = "dbg-execution")]
// fn disassemble_invoke(chunk: &Chunk, offset: usize, name: &'static str) -> usize {
//     let slot = chunk.instructions[offset + 1];
//     let argc = chunk.instructions[offset + 2];
//     // SAFETY: The compiler must work correctly.
//     let file_name = unsafe { chunk.constants.get_unchecked(slot as usize) };
//     println!("{name:-16} {slot:4} ({argc} args) {file_name}",);
//     offset + 3
// }
