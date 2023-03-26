use crate::{opcode::Opcode, scan::Line, stack::Stack, value::Value};

/// A chunk holds a sequence of instructions to be executes and their data.
#[derive(Debug, Default)]
pub(crate) struct Chunk {
    pub(crate) constants: Stack<Value, { u8::MAX as usize + 1 }>,
    pub(crate) instructions: Vec<u8>,
    pub(crate) lines: Vec<Line>,
    pub(crate) line_run_lengths: Vec<usize>,
}

impl Chunk {
    /// Write an opcode into the chunk.
    pub(crate) fn write(&mut self, opcode: Opcode, line: Line) {
        self.write_byte(opcode.into(), line)
    }

    /// Write an arbitrarily byte into the chunk.
    pub(crate) fn write_byte(&mut self, byte: u8, line: Line) {
        self.instructions.push(byte);
        match self.lines.last() {
            Some(n) if *n == line => {
                if let Some(run_length) = self.line_run_lengths.last_mut() {
                    *run_length += 1
                }
            }
            _ => {
                self.lines.push(line);
                self.line_run_lengths.push(1);
            }
        }
    }

    /// Write a constant into the chunk.
    pub(crate) fn write_constant(&mut self, value: Value) -> Option<usize> {
        self.constants.push(value)
    }

    /// Get the line information of the bytecode at a specific offset.
    pub(crate) fn get_line(&self, offset: usize) -> Line {
        let mut total_run_length = 0;
        for (i, run_length) in self.line_run_lengths.iter().enumerate() {
            total_run_length += run_length;
            if total_run_length > offset {
                return *self.lines.get(i).unwrap();
            }
        }
        Line::default()
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
