//! Implementation of the bytecode compiler for the Lox lanaguage.

use std::{mem, num::ParseFloatError};

use crate::{
    chunk::{disassemble_chunk, Chunk},
    object::Heap,
    opcode::Opcode,
    scan::{Kind, Line, ScanErrors, Scanner, Token},
    stack::Stack,
    value::Value,
};

/// An enumeration of potential errors occur when compiling Lox.
#[derive(Debug, thiserror::Error)]
pub enum CompileError {
    /// Can't parse a lexeme as a 64-bit float. If we see this error, then there must be an error
    /// in the scanner.
    #[error(transparent)]
    InvalidNumber(#[from] ParseFloatError),

    /// Errors with arbitrary message.
    #[error("{0}")]
    Generic(String),
}

/// Scan for tokens and emit corresponding bytecodes.
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
pub(crate) struct Parser<'src, 'vm> {
    /// The flag to indicate that the compilation process had error(s).
    had_error: bool,
    /// The token previously consumed token.
    token_prev: Token<'src>,
    /// The token currently consumed token.
    token_curr: Token<'src>,
    /// The scanner for turning source bytes into tokens.
    scanner: Scanner<'src>,
    /// The compiler's state for tracking scopes.
    compiler: Compiler<'src>,
    /// The heap of the currently running virtual machine.
    heap: &'vm mut Heap,
    /// The chunk that is being written to.
    chunk: Chunk,
}

impl<'src, 'vm> Parser<'src, 'vm> {
    /// Create a new parser that reads the given source string.
    pub(crate) fn new(src: &'src str, heap: &'vm mut Heap) -> Self {
        Self {
            had_error: false,
            token_prev: Token::placeholder(),
            token_curr: Token::placeholder(),
            scanner: Scanner::new(src),
            compiler: Compiler::default(),
            heap,
            chunk: Chunk::default(),
        }
    }

    /// Compile the source and returns its chunk.
    pub(crate) fn compile(&mut self) -> Option<Chunk> {
        let chunk = self.build_chunk();
        if self.had_error {
            #[cfg(debug_assertions)]
            disassemble_chunk(&chunk, "code");
            return None;
        }
        Some(chunk)
    }

    fn build_chunk(&mut self) -> Chunk {
        self.advance();
        while !self.advance_if(Kind::Eof) {
            self.declaration();
        }
        self.emit(Opcode::Ret);
        mem::take(self.chunk_mut())
    }

    /// Parse declaration assuming that we're at the start of a statement. If no declaration is
    /// found, fall back to parsing a statement.
    ///
    /// ## Grammar
    ///
    /// decl       --> classDecl
    ///              | funDecl
    ///              | varDecl
    ///              | stmt ;
    fn declaration(&mut self) {
        // Report and recover from errors. We try to compile until EOF to detect all potential
        // issue instead of eagerly stop as soon as there's an error.
        if let Err(err) = self.declaration_unsync() {
            eprintln!("{err}");
            self.synchronize();
        }
    }

    fn declaration_unsync(&mut self) -> Result<(), CompileError> {
        if self.advance_if(Kind::Var) {
            self.var_declaration()?;
        } else {
            self.statement()?;
        }
        Ok(())
    }

    /// Parse a statement assuming that we're at the start of it. All lines of code must be
    /// statements in order to be executed.
    ///
    /// ## Grammar
    ///
    /// stmt       --> block
    ///              | exprStmt
    ///              | forStmt
    ///              | ifStmt
    ///              | printStmt
    ///              | returnStmt
    ///              | whileStmt ;
    fn statement(&mut self) -> Result<(), CompileError> {
        if self.advance_if(Kind::LBrace) {
            self.begin_scope();
            self.block()?;
            self.end_scope();
        } else if self.advance_if(Kind::Print) {
            self.print_statement()?;
        } else {
            self.expression_statement()?;
        }
        Ok(())
    }

    fn block(&mut self) -> Result<(), CompileError> {
        while !self.check_curr(Kind::RBrace) && !self.check_curr(Kind::Eof) {
            self.declaration();
        }
        self.consume(Kind::RBrace, "Expect '}' after block")
    }

    /// Parse a print statement assuming that we've already consumed the 'print' keyword.
    ///
    /// ## Grammar
    ///
    /// printStmt  --> "print" expr ";" ;
    fn print_statement(&mut self) -> Result<(), CompileError> {
        self.expression()?;
        self.consume(Kind::Semicolon, "Expect ';' after value")?;
        self.emit(Opcode::Print);
        Ok(())
    }

    /// Parse an expression statement assuming that we're at the start of it.
    ///
    /// ## Grammar
    ///
    /// exprStmt   --> expr ";" ;
    fn expression_statement(&mut self) -> Result<(), CompileError> {
        self.expression()?;
        self.consume(Kind::Semicolon, "Expect ';' after expression")?;
        self.emit(Opcode::Pop);
        Ok(())
    }

    /// Parse a variable declaration assuming that we've already consumed the 'var' keyword.
    ///
    /// ## Grammar
    ///
    /// varDecl    --> "var" IDENT ( "=" expr )? ";" ;
    ///
    /// ## Local variables
    ///
    /// Lox uses lexical scoping so the compiler knows where it is within the stack while parsing the
    /// source code. We are simulating the virtual machine's stack so at runtime we can pre-allocate
    /// the needed space on to the stack, and access locals through array index for better performance.
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
    fn var_declaration(&mut self) -> Result<(), CompileError> {
        let global_id = self.parse_variable("Expect variable name")?;
        if self.advance_if(Kind::Equal) {
            // Parse the initial value assigned to the variable.
            self.expression()?;
        } else {
            // Emit bytecodes for setting the value to 'nil' if no initial expression was found.
            self.emit(Opcode::Nil);
        }
        self.consume(Kind::Semicolon, "Expect ';' after variable declaration")?;
        self.define_variable(global_id);
        Ok(())
    }

    /// Parse the identifier declared as the variable name.
    fn parse_variable(&mut self, message: &str) -> Result<u8, CompileError> {
        self.consume(Kind::Ident, message)?;
        self.declare_variable()?;
        if self.compiler().scope_depth > 0 {
            // Return a dummy constant id if we're in a local scope. Local variable don't
            // need to store their names as constants because we access them at runtime
            // through the stack index.
            return Ok(0);
        }
        self.identifier_constant(self.token_prev)
    }

    fn declare_variable(&mut self) -> Result<(), CompileError> {
        let name = self.token_prev;
        let compiler = self.compiler_mut();
        if compiler.scope_depth == 0 {
            return Ok(());
        }
        for local in &compiler.locals {
            if local.depth != -1 && local.depth < compiler.scope_depth {
                break;
            }
            if local.name.lexeme == name.lexeme {
                return Err(self.error_prev("Already a variable with this name in this scope"));
            }
        }
        self.add_local(name)
    }

    fn add_local(&mut self, name: Token<'src>) -> Result<(), CompileError> {
        let compiler = self.compiler_mut();
        // When a local variable is first declared, it is marked as "uninitialized" by setting
        // depth=-1. Once we finish parsing the variable initializer, we set depth back to its
        // correct scope depth.
        let local = Local { name, depth: -1 };
        compiler
            .locals
            .push(local)
            .ok_or_else(|| self.error_prev("Too many local variables in function"))?;
        Ok(())
    }

    /// Put the name of the identifier as a string object in the list of constant.
    fn identifier_constant(&mut self, name: Token<'_>) -> Result<u8, CompileError> {
        let s = String::from(name.lexeme.trim_matches('"'));
        let value = Value::Object(self.heap.alloc_string(s));
        self.make_constant(value)
    }

    /// Emit bytecodes for defining a global variable.
    fn define_variable(&mut self, global_id: u8) {
        if self.compiler().scope_depth > 0 {
            // If we are in a local scope, we don't need to emit bytecodes for loading a variable's
            // value. We have already executed the code for the variable’s initializer (or the
            // implicit nil), and that value is sitting right on top of the stack as the only
            // remaining temporary. We also know that new locals are allocated at the top of
            // the stack.
            self.mark_initialized();
            return;
        }
        self.emit(Opcode::DefineGlobal);
        self.emit_byte(global_id);
    }

    fn mark_initialized(&mut self) {
        let compiler = self.compiler_mut();
        let local = compiler
            .locals
            .top_mut()
            .expect("A local varialbe should have been declared.");
        local.depth = compiler.scope_depth;
    }

    /// Parse an expression assuming that we're at the start of it.
    ///
    /// ## Grammar
    ///
    /// expr       --> assign ;
    fn expression(&mut self) -> Result<(), CompileError> {
        self.parse_precedence(Precedence::Assignment)
    }

    /// Starts at the current token and parses any expression at the given precedence level
    /// or higher
    ///
    /// ## Grammar
    ///
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
    fn parse_precedence(&mut self, precedence: Precedence) -> Result<(), CompileError> {
        // An expression can be a target for assignment iff it's not part of any expression that
        // has a higher precedence than assignment.
        let can_assign = precedence <= Precedence::Assignment;
        self.advance();
        self.prefix_rule(can_assign)?;
        while precedence <= Precedence::of(self.token_curr.kind) {
            self.advance();
            self.infix_rule()?;
        }
        // The assignment target is wrong, if the current expression can be assigned to but we
        // haven't consumed the '=' after all the steps.
        if can_assign && self.advance_if(Kind::Equal) {
            return Err(self.error_prev("Invalid assignment target"));
        }
        Ok(())
    }

    /// Parse a prefix expression if the consumed token can be used in a prefix operation.
    fn prefix_rule(&mut self, can_assign: bool) -> Result<(), CompileError> {
        match self.token_prev.kind {
            Kind::LParen => self.grouping()?,
            Kind::Minus | Kind::Bang => self.unary()?,
            Kind::Ident => self.variable(can_assign)?,
            Kind::String => self.string()?,
            Kind::Number => self.number()?,
            Kind::True | Kind::False | Kind::Nil => self.literal(),
            _ => return Err(self.error_prev("Expect expression")),
        }
        Ok(())
    }

    /// Parse an infix expression if the consumed token can be used in a infix operation.
    fn infix_rule(&mut self) -> Result<(), CompileError> {
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

    /// Parse a grouping of expressions assuming that the '(' token has been consumed.
    ///
    /// ## Grammar
    ///
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    fn grouping(&mut self) -> Result<(), CompileError> {
        self.expression()?;
        self.consume(Kind::RParen, "Expect ')' after expression")
    }

    /// Parse a unary operation assuming that the operator token has been consumed.
    ///
    /// ## Grammar
    ///
    /// unary      --> ( "!" | "-" ) unary
    ///              | call ;
    fn unary(&mut self) -> Result<(), CompileError> {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::Unary)?;
        match token_kind {
            Kind::Bang => self.emit(Opcode::Not),
            Kind::Minus => self.emit(Opcode::Neg),
            _ => unreachable!(),
        }
        Ok(())
    }

    /// Parse a binary operation assuming that the LHS token and the operator token
    /// have been consumed.
    ///
    /// ## Grammar
    ///
    /// or         --> and ( "or" and )* ;
    /// and        --> equality ( "and" equality )* ;
    /// equality   --> comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison --> term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term       --> factor ( ( "-" | "+" ) factor )* ;
    /// factor     --> unary ( ( "/" | "*" ) unary )* ;
    fn binary(&mut self) -> Result<(), CompileError> {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::of(token_kind).next())?;
        match token_kind {
            Kind::BangEqual => self.emit(Opcode::NE),
            Kind::EqualEqual => self.emit(Opcode::EQ),
            Kind::Greater => self.emit(Opcode::GT),
            Kind::GreaterEqual => self.emit(Opcode::GE),
            Kind::Less => self.emit(Opcode::LT),
            Kind::LessEqual => self.emit(Opcode::LE),
            Kind::Plus => self.emit(Opcode::Add),
            Kind::Minus => self.emit(Opcode::Sub),
            Kind::Star => self.emit(Opcode::Mul),
            Kind::Slash => self.emit(Opcode::Div),
            _ => unreachable!(),
        }
        Ok(())
    }

    /// Parse a variable identifier within an expression.
    ///
    /// ## Grammar
    ///
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    fn variable(&mut self, can_assign: bool) -> Result<(), CompileError> {
        self.named_variable(self.token_prev, can_assign)?;
        Ok(())
    }

    /// Emit the bytecodes for loading a variable with a particular name.
    fn named_variable(&mut self, name: Token<'_>, can_assign: bool) -> Result<(), CompileError> {
        // Get the constant that holds our identifier.
        let (arg, op_get, op_set) = match self.resolve_local(name)? {
            None => {
                let id = self.identifier_constant(name)?;
                (id, Opcode::GetGlobal, Opcode::SetGlobal)
            }
            Some(id) => (id, Opcode::GetLocal, Opcode::SetLocal),
        };

        if can_assign && self.advance_if(Kind::Equal) {
            // The LHS can be used as an assignment target.
            self.expression()?;
            self.emit(op_set);
            self.emit_byte(arg);
        } else {
            // The LHS can't be used as an assignment target.
            self.emit(op_get);
            self.emit_byte(arg);
        }
        Ok(())
    }

    fn resolve_local(&mut self, name: Token<'_>) -> Result<Option<u8>, CompileError> {
        let compiler = self.compiler();
        for (id, local) in compiler.locals.into_iter().enumerate() {
            if local.name.lexeme == name.lexeme {
                if local.depth == -1 {
                    return Err(self.error_prev("Can't read local variable in its own initializer"));
                }
                return Ok(Some(id as u8));
            }
        }
        Ok(None)
    }

    /// Create a string literal and emit bytecodes to load it value.
    ///
    /// ## Grammar
    ///
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    fn string(&mut self) -> Result<(), CompileError> {
        let s = String::from(self.token_prev.lexeme.trim_matches('"'));
        let value = Value::Object(self.heap.alloc_string(s));
        self.emit_constant(value)?;
        Ok(())
    }

    /// Create a number literal and emit bytecodes to load it value.
    ///
    /// ## Grammar
    ///
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    fn number(&mut self) -> Result<(), CompileError> {
        let value = Value::Number(self.token_prev.lexeme.parse()?);
        self.emit_constant(value)
    }

    /// Create a literal and emit bytecodes to load it value.
    ///
    /// ## Grammar
    ///
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    fn literal(&mut self) {
        match self.token_prev.kind {
            Kind::False => self.emit(Opcode::False),
            Kind::Nil => self.emit(Opcode::Nil),
            Kind::True => self.emit(Opcode::True),
            _ => unreachable!(),
        }
    }

    /// Write the byte representing the given opcode into the current compiling chunk.
    fn emit(&mut self, opcode: Opcode) {
        let line = self.token_prev.line;
        let chunk = self.chunk_mut();
        chunk.write(opcode, line);
    }

    /// Write the byte into the current compiling chunk.
    fn emit_byte(&mut self, byte: u8) {
        let line = self.token_prev.line;
        let chunk = self.chunk_mut();
        chunk.write_byte(byte, line);
    }

    /// Write a constant and the necessary bytecodes for loading it to
    /// the currently compiling chunk.
    fn emit_constant(&mut self, value: Value) -> Result<(), CompileError> {
        let constant_id = self.make_constant(value)?;
        let line = self.token_prev.line;
        let chunk = self.chunk_mut();
        chunk.write(Opcode::Const, line);
        chunk.write_byte(constant_id, line);
        Ok(())
    }

    /// Write a constant to the currently compiling chunk.
    fn make_constant(&mut self, value: Value) -> Result<u8, CompileError> {
        let chunk = self.chunk_mut();
        let constant_id = match chunk.write_constant(value) {
            None => return Err(self.error_prev("Too many constants in one chunk")),
            Some(id) => id,
        };
        Ok(constant_id as u8)
    }

    /// Get a mutable reference to the currently compiling chunk.
    fn chunk_mut(&mut self) -> &mut Chunk {
        &mut self.chunk
    }

    fn begin_scope(&mut self) {
        self.compiler_mut().scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.compiler_mut().scope_depth -= 1;

        while let Some(local) = self.compiler().locals.top() {
            if local.depth <= self.compiler().scope_depth {
                break;
            }
            self.emit(Opcode::Pop);
            self.compiler_mut().locals.pop();
        }
    }

    fn compiler(&self) -> &Compiler<'src> {
        &self.compiler
    }

    fn compiler_mut(&mut self) -> &mut Compiler<'src> {
        &mut self.compiler
    }

    /// Synchronize the parser to a normal state where we can continue parsing
    /// after an error occured.
    fn synchronize(&mut self) {
        // When synchronize is called, there must be an error that happened. Thus we mark the flag
        // so our parse won't return the errorneous chunk back to the caller.
        self.had_error = true;
        while !self.check_curr(Kind::Eof) {
            // Skip tokens until we reach a statement boundary. Once we found something that look like
            // a state, we can be confident that compilation can go back to normal.
            if self.check_prev(Kind::Semicolon)
                || self.check_curr(Kind::Class)
                || self.check_curr(Kind::Fun)
                || self.check_curr(Kind::Var)
                || self.check_curr(Kind::For)
                || self.check_curr(Kind::If)
                || self.check_curr(Kind::While)
                || self.check_curr(Kind::Print)
                || self.check_curr(Kind::Return)
            {
                return;
            }
            self.advance();
        }
    }

    /// Go through the tokens return by the scanner a set up 2 fields `token_prev` and
    /// `token_curr`.
    fn advance(&mut self) {
        let mut scan_errors = ScanErrors::default();
        loop {
            match self.scanner.scan() {
                Err(err) => scan_errors.push(err),
                Ok(token) => {
                    self.token_prev = std::mem::replace(&mut self.token_curr, token);
                    break;
                }
            }
        }
        if !scan_errors.is_empty() {
            self.had_error = true;
            eprintln!("{scan_errors}");
        }
    }

    /// Move to the next token iff the current token kind matches the given token kind.
    fn advance_if(&mut self, kind: Kind) -> bool {
        if !self.check_curr(kind) {
            return false;
        }
        self.advance();
        true
    }

    /// Check if the current token has the given `token_kind`. Return an error with a custom
    /// message if the condition does not hold.
    fn consume(&mut self, token_kind: Kind, message: &str) -> Result<(), CompileError> {
        if !self.check_curr(token_kind) {
            return Err(self.error_curr(message));
        }
        self.advance();
        Ok(())
    }

    /// Check the current token kind matches the given token kind.
    fn check_curr(&self, kind: Kind) -> bool {
        self.token_curr.kind == kind
    }

    /// Check the previous token kind matches the given token kind.
    fn check_prev(&self, kind: Kind) -> bool {
        self.token_prev.kind == kind
    }

    /// Create an compilation error pointing at the line of the previous token.
    fn error_prev(&mut self, message: &str) -> CompileError {
        CompileError::Generic(self.error_at(self.token_prev.line, self.token_prev.lexeme, message))
    }

    /// Create an compilation error pointing at the line of the current token.
    fn error_curr(&mut self, message: &str) -> CompileError {
        CompileError::Generic(self.error_at(self.token_curr.line, self.token_curr.lexeme, message))
    }

    /// Create an compilation error pointing at a particular line and lexeme.
    fn error_at(&mut self, line: Line, lexeme: &str, message: &str) -> String {
        if lexeme.is_empty() {
            format!("{line} Error at end: {message}.")
        } else {
            format!("{line} Error at '{lexeme}': {message}.")
        }
    }
}

/// A structure for tracking the compiler current scoped states.
#[derive(Debug, Default)]
struct Compiler<'src> {
    /// A stack of local variables sorted by the order in which they are declared.
    locals: Stack<Local<'src>, { u8::MAX as usize + 1 }>,
    /// The number of "blocks" surrounding the current piece of code that we're compiling.
    scope_depth: isize,
}

/// A structure the representing local variables during compilation time.
#[derive(Debug)]
struct Local<'src> {
    /// The token that stores the name of the local identifier.
    name: Token<'src>,
    /// The scope depth in which the local variable was declared.
    depth: isize,
}

/// All precedence levels in Lox.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    /// No precedence.
    None,
    /// Operator `=`.
    Assignment,
    /// Operator `or`.
    Or,
    /// Operator `and`.
    And,
    /// Operator `==` `!=`.
    Equality,
    /// Operator `<` `>` `<=` `>=`.
    Comparison,
    /// Operator `+` `-`.
    Term,
    /// Operator `*` `/`.
    Factor,
    /// Operator `!` `-`.
    Unary,
    /// Operator `.` `()`.
    Call,
    /// Literal and keywords.
    Primary,
}

impl Precedence {
    /// Get the immediately higher precedence level.
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

    /// Get the precedence of a specific token kind.
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
