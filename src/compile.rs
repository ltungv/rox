//! Implementation of the bytecode compiler for the Lox lanaguage.

use std::{mem, num::ParseFloatError};

use crate::{
    chunk::{disassemble_chunk, Chunk, ChunkError},
    opcode::Opcode,
    scan::{Kind, Line, Scanner, Token},
    value::Value,
};

/// An enumeration of potential errors occur when compiling Lox.
#[derive(Debug, thiserror::Error)]
pub enum CompileError {
    /// Can't parse a lexeme as a 64-bit float.
    #[error(transparent)]
    InvalidNumber(#[from] ParseFloatError),

    /// Can't add more constant to the chunk.
    #[error(transparent)]
    Chunk(#[from] ChunkError),

    /// Errors with arbitrary message.
    #[error("{0}")]
    Generic(String),
}

/// Scan for tokens and emit corresponding bytecodes.
///
/// Lox uses lexical scoping so the compiler knows where it is within the stack while parsing the
/// source code. We are simulating the virtual machine's stack so at runtime we can pre-allocate
/// the needed space on to the stack, and access locals through array index for better preformance.
///
/// ## Locals Stack
///
/// ```text
/// {
///     var a = 1;             // STACK: [ 1 ]
///     {
///         var b = 2;         // STACK: [ 1 ] [ 2 ]
///         {
///             var c = 3;     // STACK: [ 1 ] [ 2 ] [ 3 ]
///             {
///                 var d = 4; // STACK: [ 1 ] [ 2 ] [ 3 ] [ 4 ]
///             }              // STACK: [ 1 ] [ 2 ] [ 3 ] [ x ]
///
///             var e = 5;     // STACK: [ 1 ] [ 2 ] [ 3 ] [ 5 ]
///         }                  // STACK: [ 1 ] [ 2 ] [ x ] [ x ]
///     }                      // STACK: [ 1 ] [ x ]
///
///     var f = 6;             // STACK: [ 1 ] [ 6 ]
///     {
///         var g = 7;         // STACK: [ 1 ] [ 6 ] [ 7 ]
///     }                      // STACK: [ 1 ] [ 6 ] [ x ]
/// }                          // STACK: [ x ] [ x ]
/// ```
///
/// ## Grammars
///
/// ```text
/// program    --> decl* EOF ;
/// decl       --> classDecl
///              | funDecl
///              | varDecl
///              | stmt ;
/// classDecl  --> "class" IDENT ( "<" IDENT )? "{" function* "}" ;
/// funDecl    --> "fun" function ;
/// function   --> IDENT "(" params? ")" block ;
/// params     --> IDENT ( "," IDENT )* ;
/// varDecl    --> "var" IDENT ( "=" expr )? ";" ;
/// stmt       --> block
///              | exprStmt
///              | forStmt
///              | ifStmt
///              | printStmt
///              | returnStmt
///              | whileStmt ;
/// block      --> "{" decl* "}" ;
/// exprStmt   --> expr ";" ;
/// forStmt    --> "for" "(" ( varDecl | exprStmt | ";" ) expr? ";" expr? ")" stmt ;
/// ifStmt     --> "if" "(" expr ")" stmt ( "else" stmt )? ;
/// printStmt  --> "print" expr ";" ;
/// returnStmt --> "return" expr? ";" ;
/// whileStmt  --> "while" "(" expr ")" stmt ;
/// expr       --> assign ;
/// assign     --> ( call "." )? IDENT "=" expr ";"
///              | or ;
/// or         --> and ( "or" and )* ;
/// and        --> equality ( "and" equality )* ;
/// equality   --> comparison ( ( "!=" | "==" ) comparison )* ;
/// comparison --> term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
/// term       --> factor ( ( "-" | "+" ) factor )* ;
/// factor     --> unary ( ( "/" | "*" ) unary )* ;
/// unary      --> ( "!" | "-" ) unary
///              | call ;
/// call       --> primary ( "(" args? ")" | "." IDENT )* ;
/// args       --> expr ( "," expr )* ;
/// primary    --> IDENT | NUMBER | STRING
///              | "this" | "super" "." IDENT
///              | "true" | "false" | "nil"
///              | "(" expr ")" ;
/// ```
pub(crate) struct Parser<'src> {
    /// The token previously consumed token.
    token_prev: Token<'src>,
    /// The token currently consumed token.
    token_curr: Token<'src>,
    /// The scanner for turning source bytes into tokens.
    scanner: Scanner<'src>,
    /// The chunk that is being written to.
    chunk: Chunk,
}

impl<'src> Parser<'src> {
    pub(crate) fn new(src: &'src str) -> Self {
        Self {
            token_prev: Token::placeholder(),
            token_curr: Token::placeholder(),
            scanner: Scanner::new(src),
            chunk: Chunk::default(),
        }
    }

    pub(crate) fn compile(&mut self) -> Result<Chunk, CompileError> {
        let result = self.build_chunk();
        if let Err(err) = &result {
            #[cfg(debug_assertions)]
            disassemble_chunk(self.chunk_mut(), "code");

            match err {
                CompileError::Generic(msg) => eprintln!("{msg}"),
                _ => eprintln!(
                    "{}",
                    self.error_at(
                        self.token_prev.line,
                        self.token_prev.lexeme,
                        &err.to_string()
                    )
                ),
            }
        }
        result
    }

    fn build_chunk(&mut self) -> Result<Chunk, CompileError> {
        self.advance();
        self.expression()?;
        self.consume(Kind::Eof, "Expect end of expression.")?;
        self.emit(Opcode::Return);
        Ok(mem::take(self.chunk_mut()))
    }

    fn expression(&mut self) -> Result<(), CompileError> {
        self.parse_precedence(Precedence::Assignment)
    }

    fn parse_precedence(&mut self, precedence: Precedence) -> Result<(), CompileError> {
        self.advance();
        let can_assign = precedence <= Precedence::Assignment;
        self.prefix_rule(can_assign)?;

        while precedence <= Precedence::of(self.token_curr.kind) {
            self.advance();
            self.infix_rule(can_assign)?;
        }
        Ok(())
    }

    fn prefix_rule(&mut self, _can_assign: bool) -> Result<(), CompileError> {
        match self.token_prev.kind {
            Kind::LParen => self.grouping()?,
            Kind::Minus | Kind::Bang => self.unary()?,
            Kind::Number => self.number()?,
            Kind::True | Kind::False | Kind::Nil => self.literal(),
            _ => return Err(self.error_prev("Expect expression")),
        }
        Ok(())
    }

    fn infix_rule(&mut self, _can_assign: bool) -> Result<(), CompileError> {
        match self.token_prev.kind {
            Kind::Minus
            | Kind::Plus
            | Kind::Slash
            | Kind::Star
            | Kind::BangEqual
            | Kind::EqualEqual
            | Kind::Greater
            | Kind::GreaterEqual
            | Kind::Less
            | Kind::LessEqual => self.binary(),
            _ => Err(self.error_prev("Expect expression")),
        }
    }

    fn grouping(&mut self) -> Result<(), CompileError> {
        self.expression()?;
        self.consume(Kind::RParen, "Expect ')' after expression")
    }

    fn unary(&mut self) -> Result<(), CompileError> {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::Unary)?;
        match token_kind {
            Kind::Minus => self.emit(Opcode::Negate),
            _ => unreachable!(),
        }
        Ok(())
    }

    fn binary(&mut self) -> Result<(), CompileError> {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::of(token_kind).next())?;
        match token_kind {
            Kind::BangEqual => {
                self.emit(Opcode::Equal);
                self.emit(Opcode::Not);
            }
            Kind::EqualEqual => self.emit(Opcode::Equal),
            Kind::Greater => self.emit(Opcode::Greater),
            Kind::GreaterEqual => {
                self.emit(Opcode::Less);
                self.emit(Opcode::Not);
            }
            Kind::Less => self.emit(Opcode::Less),
            Kind::LessEqual => {
                self.emit(Opcode::Greater);
                self.emit(Opcode::Not);
            }
            Kind::Plus => self.emit(Opcode::Add),
            Kind::Minus => self.emit(Opcode::Subtract),
            Kind::Star => self.emit(Opcode::Multiply),
            Kind::Slash => self.emit(Opcode::Divide),
            _ => unreachable!(),
        }
        Ok(())
    }

    fn number(&mut self) -> Result<(), CompileError> {
        let value = Value::Number(self.token_prev.lexeme.parse()?);
        self.emit_constant(value)
    }

    fn literal(&mut self) {
        match self.token_prev.kind {
            Kind::False => self.emit(Opcode::False),
            Kind::Nil => self.emit(Opcode::Nil),
            Kind::True => self.emit(Opcode::True),
            _ => unreachable!(),
        }
    }

    fn emit(&mut self, opcode: Opcode) {
        let line = self.token_prev.line;
        let chunk = self.chunk_mut();
        chunk.write(opcode, line);
    }

    fn emit_constant(&mut self, value: Value) -> Result<(), CompileError> {
        let line = self.token_prev.line;
        let chunk = self.chunk_mut();
        chunk.write(Opcode::Constant, line);
        chunk.write_constant(value, line)?;
        Ok(())
    }

    fn chunk_mut(&mut self) -> &mut Chunk {
        &mut self.chunk
    }

    fn advance(&mut self) {
        loop {
            match self.scanner.scan() {
                Err(err) => {
                    eprintln!("{err}");
                }
                Ok(token) => {
                    self.token_prev = std::mem::replace(&mut self.token_curr, token);
                    break;
                }
            }
        }
    }

    fn consume(&mut self, token_kind: Kind, message: &'static str) -> Result<(), CompileError> {
        if self.token_curr.kind != token_kind {
            return Err(self.error_curr(message));
        }
        self.advance();
        Ok(())
    }

    fn error_prev(&mut self, message: &str) -> CompileError {
        CompileError::Generic(self.error_at(self.token_prev.line, self.token_prev.lexeme, message))
    }

    fn error_curr(&mut self, message: &str) -> CompileError {
        CompileError::Generic(self.error_at(self.token_curr.line, self.token_curr.lexeme, message))
    }

    fn error_at(&mut self, line: Line, lexeme: &str, message: &str) -> String {
        if lexeme.is_empty() {
            format!("{line} Error at end: {message}.")
        } else {
            format!("{line} Error at '{lexeme}': {message}.")
        }
    }
}

/// All precedence levels in Lox
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    /// No precedence
    None,
    /// Operator `=`
    Assignment,
    /// Operator `or`
    Or,
    /// Operator `and`
    And,
    /// Operator `==` `!=`
    Equality,
    /// Operator `<` `>` `<=` `>=`
    Comparison,
    /// Operator `+` `-`
    Term,
    /// Operator `*` `/`
    Factor,
    /// Operator `!` `-`
    Unary,
    /// Operator `.` `()`
    Call,
    /// Literal and keywords
    Primary,
}

impl Precedence {
    /// Get the immediately higher precedence level
    fn next(&self) -> Self {
        match self {
            Self::None => Self::Assignment,
            Self::Assignment => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Equality,
            Self::Equality => Self::Comparison,
            Self::Comparison => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::Primary,
            Self::Primary => Self::Primary,
        }
    }

    fn of(kind: Kind) -> Self {
        match kind {
            Kind::Or => Precedence::Or,
            Kind::And => Precedence::And,
            Kind::BangEqual | Kind::EqualEqual => Precedence::Equality,
            Kind::Greater | Kind::GreaterEqual | Kind::Less | Kind::LessEqual => {
                Precedence::Comparison
            }
            Kind::Minus | Kind::Plus => Precedence::Term,
            Kind::Slash | Kind::Star => Precedence::Factor,
            Kind::LParen | Kind::Dot => Precedence::Call,
            _ => Self::None,
        }
    }
}
