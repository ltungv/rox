use crate::{opcode::Opcode, scan::Line, value::Value};

/// An enumeration of potential errors occur when compiling Lox.
#[derive(Debug, thiserror::Error)]
pub enum ChunkError {
    /// Can't add more constant to the chunk.
    #[error("Too many constants in one chunk.")]
    ConstantLimitExceeded,
}

/// A chunk holds a sequence of instructions to be executes and their data.
#[derive(Debug, Default)]
pub(crate) struct Chunk {
    pub(crate) constants: Vec<Value>,
    pub(crate) instructions: Vec<u8>,
    pub(crate) lines: Vec<usize>,
}

impl Chunk {
    /// Write an opcode into the chunk.
    pub(crate) fn write(&mut self, opcode: Opcode, line: Line) {
        self.write_byte(opcode.into(), line)
    }

    /// Write an arbitrarily byte into the chunk.
    pub(crate) fn write_byte(&mut self, byte: u8, line: Line) {
        self.instructions.push(byte);
        self.lines.push(*line);
    }

    /// Write a constant along with an instruction to load it into the chunk.
    pub(crate) fn write_constant(&mut self, value: Value, line: Line) -> Result<(), ChunkError> {
        let constant_id = self.constants.len();
        if constant_id >= u8::MAX.into() {
            return Err(ChunkError::ConstantLimitExceeded);
        }
        self.constants.push(value);
        self.write_byte(constant_id as u8, line);
        Ok(())
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
    let line_current = chunk.lines[offset];
    let line_previous = chunk.lines[offset.saturating_sub(1)];
    // Annotation for seperating instructions from different lines.
    print!("{offset:04} ");
    if offset > 0 && line_current == line_previous {
        print!("   | ");
    } else {
        print!("{line_current:4} ");
    }
    let instruction = match Opcode::try_from(chunk.instructions[offset]) {
        Ok(inst) => inst,
        Err(err) => panic!("{}", err),
    };
    // Print each individual instruction.
    match instruction {
        Opcode::Constant => disassemble_constant(chunk, offset, "CONSTANT"),
        Opcode::Nil => disassemble_simple(offset, "OP_NIL"),
        Opcode::True => disassemble_simple(offset, "OP_TRUE"),
        Opcode::False => disassemble_simple(offset, "OP_FALSE"),
        Opcode::Print => disassemble_simple(offset, "PRINT"),
        Opcode::Equal => disassemble_simple(offset, "OP_EQUAL"),
        Opcode::Greater => disassemble_simple(offset, "OP_GREATER"),
        Opcode::Less => disassemble_simple(offset, "OP_LESS"),
        Opcode::Add => disassemble_simple(offset, "OP_ADD"),
        Opcode::Subtract => disassemble_simple(offset, "OP_SUBTRACT"),
        Opcode::Multiply => disassemble_simple(offset, "OP_MULTIPLY"),
        Opcode::Divide => disassemble_simple(offset, "OP_DIVIDE"),
        Opcode::Not => disassemble_simple(offset, "OP_NOT"),
        Opcode::Negate => disassemble_simple(offset, "OP_NEGATE"),
        Opcode::Return => disassemble_simple(offset, "RETURN"),
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
