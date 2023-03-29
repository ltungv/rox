use crate::{opcode::Opcode, scan::Line, value::Value};

#[cfg(debug_assertions)]
use crate::vm::JumpDirection;

/// A chunk holds a sequence of instructions to be executes and their data.
#[derive(Debug, Default)]
pub(crate) struct Chunk {
    pub(crate) constants: Vec<Value>,
    pub(crate) instructions: Vec<u8>,
    lines: Vec<RunLength<Line>>,
}

impl Chunk {
    /// Write an opcode into the chunk.
    pub(crate) fn write(&mut self, opcode: Opcode, line: Line) {
        self.write_byte(opcode.into(), line)
    }

    /// Write an arbitrarily byte into the chunk.
    pub(crate) fn write_byte(&mut self, byte: u8, line: Line) {
        self.instructions.push(byte);
        self.add_line(line);
    }

    /// Write a constant into the chunk.
    pub(crate) fn write_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    /// Get the line information of the bytecode at a specific offset.
    pub(crate) fn add_line(&mut self, line: Line) {
        match self.lines.last_mut() {
            Some(last_line) if last_line.data == line => last_line.length += 1,
            _ => self.lines.push(RunLength::new(line)),
        }
    }

    /// Get the line information of the bytecode at a specific offset.
    pub(crate) fn get_line(&self, offset: usize) -> Line {
        let mut length = 0;
        for line in self.lines.iter() {
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
    fn new(data: T) -> Self {
        Self { data, length: 1 }
    }
}

/// Go through the instructions in the chunk and display them in human-readable format.
#[cfg(debug_assertions)]
pub(crate) fn disassemble_chunk(chunk: &Chunk, name: &str) {
    println!("== {name} ==");
    let mut offset = 0;
    while offset < chunk.instructions.len() {
        offset = disassemble_instruction(chunk, offset);
    }
}

/// Display an instruction in human readable format.
#[cfg(debug_assertions)]
pub(crate) fn disassemble_instruction(chunk: &Chunk, offset: usize) -> usize {
    let line_current = chunk.get_line(offset);
    let line_previous = chunk.get_line(offset.saturating_sub(1));
    // Annotation for seperating instructions from different lines.
    print!("{offset:04} ");
    if offset > 0 && line_current == line_previous {
        print!("   | ");
    } else {
        print!("{:4} ", *line_current);
    }
    let instruction = match Opcode::try_from(chunk.instructions[offset]) {
        Ok(inst) => inst,
        Err(err) => panic!("{}", err),
    };
    // Print each individual instruction.
    match instruction {
        Opcode::Const => disassemble_constant(chunk, offset, "OP_CONST"),
        Opcode::Nil => disassemble_simple(offset, "OP_NIL"),
        Opcode::True => disassemble_simple(offset, "OP_TRUE"),
        Opcode::False => disassemble_simple(offset, "OP_FALSE"),
        Opcode::Pop => disassemble_simple(offset, "OP_POP"),
        Opcode::GetLocal => disassemble_byte(chunk, offset, "OP_GET_LOCAL"),
        Opcode::SetLocal => disassemble_byte(chunk, offset, "OP_SET_LOCAL"),
        Opcode::GetGlobal => disassemble_constant(chunk, offset, "OP_GET_GLOBAL"),
        Opcode::SetGlobal => disassemble_constant(chunk, offset, "OP_SET_GLOBAL"),
        Opcode::DefineGlobal => disassemble_constant(chunk, offset, "OP_DEFINE_GLOBAL"),
        Opcode::GetUpvalue => disassemble_byte(chunk, offset, "OP_GET_UPVALUE"),
        Opcode::SetUpvalue => disassemble_byte(chunk, offset, "OP_SET_UPVALUE"),
        Opcode::Print => disassemble_simple(offset, "OP_PRINT"),
        Opcode::NE => disassemble_simple(offset, "OP_NE"),
        Opcode::EQ => disassemble_simple(offset, "OP_EQ"),
        Opcode::GT => disassemble_simple(offset, "OP_GT"),
        Opcode::GE => disassemble_simple(offset, "OP_GE"),
        Opcode::LT => disassemble_simple(offset, "OP_LT"),
        Opcode::LE => disassemble_simple(offset, "OP_LE"),
        Opcode::Add => disassemble_simple(offset, "OP_ADD"),
        Opcode::Sub => disassemble_simple(offset, "OP_SUB"),
        Opcode::Mul => disassemble_simple(offset, "OP_MUL"),
        Opcode::Div => disassemble_simple(offset, "OP_DIV"),
        Opcode::Not => disassemble_simple(offset, "OP_NOT"),
        Opcode::Neg => disassemble_simple(offset, "OP_NEG"),
        Opcode::Jump => disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP"),
        Opcode::JumpIfTrue => {
            disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP_IF_TRUE")
        }
        Opcode::JumpIfFalse => {
            disassemble_jump(chunk, offset, JumpDirection::Forward, "OP_JUMP_IF_FALSE")
        }
        Opcode::Loop => disassemble_jump(chunk, offset, JumpDirection::Backward, "OP_LOOP"),
        Opcode::Call => disassemble_byte(chunk, offset, "OP_CALL"),
        Opcode::Closure => {
            let mut offset = offset + 1;
            let constant_id = chunk.instructions[offset] as usize;
            let constant = &chunk.constants[constant_id];
            offset += 1;
            println!("{:-16} {constant_id:4} {constant}", "OP_CLOSURE");
            let object = constant.as_object().expect("Expect object.");
            let fun = object.as_fun().expect("Expect function object.");
            let upvalue_count = fun.borrow().upvalue_count;
            for _ in 0..upvalue_count {
                let is_local = chunk.instructions[offset + 1] == 1;
                let index = chunk.instructions[offset + 2];
                let upvalue_type = if is_local { "local" } else { "upvalue" };
                println!("{offset:04}    |                     {upvalue_type} {index}");
                offset += 2;
            }
            offset
        }
        Opcode::CloseUpvalue => disassemble_simple(offset, "OP_CLOSE_UPVALUE"),
        Opcode::Ret => disassemble_simple(offset, "OP_RET"),
        _ => unreachable!(),
    }
}

/// Display a simple instruction in human-readable format.
#[cfg(debug_assertions)]
fn disassemble_simple(offset: usize, name: &'static str) -> usize {
    println!("{name}");
    offset + 1
}

/// Display a constant instruction in human-readable format.
#[cfg(debug_assertions)]
fn disassemble_constant(chunk: &Chunk, offset: usize, name: &'static str) -> usize {
    let constant_id = chunk.instructions[offset + 1] as usize;
    let constant = &chunk.constants[constant_id];
    println!("{name:-16} {constant_id:4} {constant}");
    offset + 2
}

/// Display a byte instruction in human-readable format.
#[cfg(debug_assertions)]
fn disassemble_byte(chunk: &Chunk, offset: usize, name: &'static str) -> usize {
    let slot = chunk.instructions[offset + 1] as usize;
    println!("{name:-16} {slot:4}");
    offset + 2
}

/// Display a jump instruction in human-readable format.
#[cfg(debug_assertions)]
fn disassemble_jump(chunk: &Chunk, offset: usize, dir: JumpDirection, name: &'static str) -> usize {
    let hi = chunk.instructions[offset + 1] as u16;
    let lo = chunk.instructions[offset + 2] as u16;
    let jump = hi << 8 | lo;
    let target = match dir {
        JumpDirection::Forward => offset + 3 + jump as usize,
        JumpDirection::Backward => offset + 3 - jump as usize,
    };
    println!("{name:-16} {offset:4} -> {target}");
    offset + 3
}
