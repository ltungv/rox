//! Implementation of the bytecode compiler for the Lox language.

use crate::{
    heap::Heap,
    list::List,
    object::{ObjFun, Object},
    opcode::Opcode,
    scan::{Kind, Line, Scanner, Token},
    value::Value,
};

#[cfg(feature = "dbg-execution")]
use crate::chunk::disassemble;

/// The max number of call frames can be handled by the virtual machine.
pub const MAX_FRAMES: usize = 64;

/// Max number of parameters a function can accept.
const MAX_PARAMS: usize = u8::MAX as usize;

/// Max number of local variables a function can contain.
const MAX_LOCALS: usize = 1 << 8;

/// Max number of upvalues a function can contain.
const MAX_UPVALUES: usize = 1 << 8;

/// Scan for tokens and emit corresponding byte codes.
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
pub struct Parser<'src, 'vm> {
    /// The flag to indicate that the compilation process had error(s).
    had_error: bool,
    /// The flag to indicate that the compilation process is in a bad state.
    panicking: bool,
    /// The token previously consumed token.
    token_prev: Token<'src>,
    /// The token currently consumed token.
    token_curr: Token<'src>,
    /// The scanner for turning source bytes into tokens.
    scanner: Scanner<'src>,
    /// The compiler's state for tracking classes.
    classes: List<ClassCompiler, MAX_FRAMES>,
    /// The compiler's state for tracking scopes.
    compilers: List<Compiler<'src>, MAX_FRAMES>,
    /// The heap of the currently running virtual machine.
    heap: &'vm mut Heap,
}

impl<'src, 'vm> Parser<'src, 'vm> {
    /// Create a new parser that reads the given source string.
    pub fn new(src: &'src str, heap: &'vm mut Heap) -> Self {
        let fun = ObjFun::new(None);
        let mut compilers = List::default();
        // SAFETY: We just created `compilers` and are sure that it's not full.
        unsafe {
            compilers.push_unchecked(Compiler::new(fun, FunctionType::Script));
        }
        Self {
            had_error: false,
            panicking: false,
            token_prev: Token::placeholder(),
            token_curr: Token::placeholder(),
            scanner: Scanner::new(src),
            classes: List::default(),
            compilers,
            heap,
        }
    }

    /// Compile the source and returns its chunk.
    pub fn compile(mut self) -> Option<ObjFun> {
        self.build();
        let compiler = self.take();
        if self.had_error {
            None
        } else {
            Some(compiler.fun)
        }
    }

    fn take(&mut self) -> Compiler<'src> {
        self.emit_return();
        let mut compiler = self.compilers.pop();
        compiler.fun.upvalue_count = compiler.upvalues.len();

        #[cfg(feature = "dbg-execution")]
        match &compiler.fun.name {
            None => disassemble(&compiler.fun.chunk, "code"),
            Some(s) => disassemble(&compiler.fun.chunk, &s.as_ref().data),
        };

        compiler
    }

    fn build(&mut self) {
        self.advance();
        while !self.advance_if(Kind::Eof) {
            self.declaration();
        }
    }

    /// Parse declaration assuming that we're at the start of a statement. If no declaration is
    /// found, fall back to parsing a statement.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// decl       --> classDecl
    ///              | funDecl
    ///              | varDecl
    ///              | stmt ;
    /// ```
    fn declaration(&mut self) {
        if self.advance_if(Kind::Var) {
            self.var_declaration();
        } else if self.advance_if(Kind::Fun) {
            self.fun_declaration();
        } else if self.advance_if(Kind::Class) {
            self.class_declaration();
        } else {
            self.statement();
        }

        if self.panicking {
            self.synchronize();
        }
    }

    /// Parse a variable declaration assuming that we've already consumed the 'var' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// varDecl    --> "var" IDENT ( "=" expr )? ";" ;
    /// ```
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
    fn var_declaration(&mut self) {
        let global_id = self.parse_variable("Expect variable name.");
        if self.advance_if(Kind::Equal) {
            // Parse the initial value assigned to the variable.
            self.expression();
        } else {
            // Emit byte codes for setting the value to 'nil' if no initial expression was found.
            self.emit(Opcode::Nil);
        }
        self.consume(Kind::Semicolon, "Expect ';' after variable declaration.");
        self.define_variable(global_id);
    }

    /// Parse a variable declaration assuming that we've already consumed the 'fun' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// funDecl    --> "fun" function ;
    /// ```
    fn fun_declaration(&mut self) {
        let fun_name_const = self.parse_variable("Expect function name.");
        // Unlike variable, function can refer to its own name when its definition. Thus, we mark
        // the function as initialized right after when it's created.
        self.mark_initialized();
        self.function(FunctionType::Function);
        // Define the function after we have finished parsing.
        self.define_variable(fun_name_const);
    }

    /// Parse a variable declaration assuming that we've already consumed the 'class' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// classDecl  --> "class" IDENT ( "<" IDENT )? "{" function* "}" ;
    /// ```
    fn class_declaration(&mut self) {
        self.consume(Kind::Ident, "Expect class name.");
        // Track the identifier token, so we can load it after finish parsing all methods.
        let class_name = self.token_prev;
        let name_const = self.identifier_constant(class_name);
        // Emit instructions for declaring a class definition with the given name.
        self.declare_variable();
        self.emit(Opcode::Class);
        self.emit_byte(name_const);
        self.define_variable(name_const);

        if self.classes.len() == MAX_FRAMES {
            self.error_prev("Too many nested classes.");
        } else {
            // SAFETY: We already checked if `classes` is full.
            unsafe {
                // Keep track of the number of nesting class declarations.
                self.classes.push_unchecked(ClassCompiler::new());
            };
        }

        // Inherit from parent.
        if self.advance_if(Kind::Less) {
            // Parse superclass name and load it onto the stack
            self.consume(Kind::Ident, "Expect superclass name.");
            self.variable(false);
            if class_name.lexeme == self.token_prev.lexeme {
                self.error_prev("A class can't inherit from itself.");
            }

            // Add a synthetic token to represent the super class and define a variable
            // using that token.
            self.begin_scope();
            self.add_local(Token {
                kind: Kind::Ident,
                line: self.token_curr.line,
                lexeme: "super",
            });
            self.define_variable(0);

            // Load subclass onto the stack.
            self.named_variable(class_name, false);
            self.emit(Opcode::Inherit);
            self.class_compiler_mut(0).has_super = true;
        }

        // Put the class object back onto the stack.
        self.named_variable(class_name, false);
        // Parse class' methods.
        self.consume(Kind::LBrace, "Expect '{' before class body.");
        while !self.check_curr(Kind::RBrace) && !self.check_curr(Kind::Eof) {
            self.method();
        }
        self.consume(Kind::RBrace, "Expect '}' after class body.");
        // Remove the class object from the stack.
        self.emit(Opcode::Pop);

        // End the scope that we began when inheriting.
        if self.class_compiler(0).has_super {
            self.end_scope();
        }

        // Remove one class nesting level.
        self.classes.pop();
    }

    /// Parse all the methods presented in a class body. Classes don't have field declarations.
    fn method(&mut self) {
        self.consume(Kind::Ident, "Expect method name.");
        let name_const = self.identifier_constant(self.token_prev);

        // Select the type of function based on its name
        if self.token_prev.lexeme == "init" {
            self.function(FunctionType::Initializer);
        } else {
            self.function(FunctionType::Method);
        }

        self.emit(Opcode::Method);
        self.emit_byte(name_const);
    }

    /// Parse a function block assuming that we've already consumed its name.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// function   --> IDENT "(" params? ")" block ;
    /// ```
    fn function(&mut self, fun_type: FunctionType) {
        // Interned the function name and allocate a new function.
        let fun_name = self.heap.intern(String::from(self.token_prev.lexeme));
        if self.compilers.len() == MAX_FRAMES {
            self.error_prev("Too many nested calls.");
        } else {
            // SAFETY: We already checked if `compilers` is full.
            unsafe {
                // Keep track of the number of nesting class declarations.
                self.compilers
                    .push_unchecked(Compiler::new(ObjFun::new(Some(fun_name)), fun_type));
            };
        }

        self.begin_scope();
        self.consume(Kind::LParen, "Expect '(' after function name.");
        if !self.check_curr(Kind::RParen) {
            loop {
                let compiler = self.compiler_mut(0);
                if compiler.fun.arity as usize == MAX_PARAMS {
                    self.error_curr("Can't have more than 255 parameters.");
                    return;
                }

                // Treat params like variables.
                compiler.fun.arity += 1;
                let ident_id = self.parse_variable("Expect parameter name.");
                self.define_variable(ident_id);

                if !self.advance_if(Kind::Comma) {
                    break;
                }
            }
        }
        self.consume(Kind::RParen, "Expect ')' after parameters.");
        self.consume(Kind::LBrace, "Expect '{' before function body.");
        self.block();

        // Create a constant for the compiled function.
        let compiler = self.take();
        let (fun_object, _) = self.heap.alloc(compiler.fun, Object::Fun);
        let constant_id = self.make_constant(Value::Object(fun_object));
        self.emit(Opcode::Closure);
        self.emit_byte(constant_id);

        for upvalue in &*compiler.upvalues {
            if upvalue.is_local {
                self.emit_byte(1);
            } else {
                self.emit_byte(0);
            }
            self.emit_byte(upvalue.index);
        }
    }

    /// Parse the identifier and declare it as the variable name.
    fn parse_variable(&mut self, message: &str) -> u8 {
        self.consume(Kind::Ident, message);
        self.declare_variable();
        if self.compiler(0).scope_depth > 0 {
            // Return a dummy constant id if we're in a local scope. Local variable don't
            // need to store their names as constants because we access them at runtime
            // through the stack index.
            0
        } else {
            self.identifier_constant(self.token_prev)
        }
    }

    /// Try to declare a local variable.
    fn declare_variable(&mut self) {
        let name = self.token_prev;
        let compiler = self.compiler_mut(0);
        // Skip this step for global scope.
        if compiler.scope_depth > 0 {
            for local in compiler.locals.iter().rev() {
                if local.depth != -1 && local.depth < compiler.scope_depth {
                    // Stop if we've gone through all initialized variable in the current scope.
                    break;
                }
                if local.name == name.lexeme {
                    // Return an error if any variable in the current scope has the same name.
                    self.error_prev("Already a variable with this name in this scope.");
                    return;
                }
            }
            self.add_local(name);
        }
    }

    fn add_local(&mut self, name: Token<'src>) {
        let compiler = self.compiler_mut(0);
        let local_count = compiler.locals.len();
        if local_count == MAX_LOCALS {
            self.error_prev("Too many local variables in function.");
            return;
        }
        // When a local variable is first declared, it is marked as "uninitialized" by setting
        // depth=-1. Once we finish parsing the variable initializer, we set depth back to its
        // correct scope depth.
        let local = Local {
            name: name.lexeme,
            depth: -1,
            is_captured: false,
        };
        // SAFETY: We already checked if `locals` is full.
        unsafe {
            compiler.locals.push_unchecked(local);
        }
    }

    /// Put an identifier as a string object in the list of constant.
    fn identifier_constant(&mut self, name: Token<'_>) -> u8 {
        let s = String::from(name.lexeme.trim_matches('"'));
        let s = self.heap.intern(s);
        let value = Value::Object(Object::String(s));
        self.make_constant(value)
    }

    /// Emit byte codes for defining a global variable.
    fn define_variable(&mut self, global_id: u8) {
        // If we are in a local scope, we don't need to emit byte codes for loading a variable's
        // value. We have already executed the code for the variable’s initializer (or the
        // implicit nil), and that value is sitting right on top of the stack as the only
        // remaining temporary.
        if self.compiler(0).scope_depth > 0 {
            // Mark declared variable as initialized
            self.mark_initialized();
        } else {
            self.emit(Opcode::DefineGlobal);
            self.emit_byte(global_id);
        }
    }

    /// A local variable is initialized if its depth is not -1.
    ///
    /// ## Why?
    ///
    /// Consider the following code
    ///
    /// ```lox
    /// {
    ///     var a = 1;
    ///     {
    ///         var a = a;
    ///     }
    /// }
    /// ```
    ///
    /// By the time we parse the initializer part of `var a = a`, a local variable named `a` has
    /// already been added to the list of local variable. Thus, the RHS in the assignment `var a =
    /// a` references the variable `a` on the LHS itself. This behavior is undesirable and Lox
    /// disallow a variable to reference itself when initializing
    ///
    /// This is solved by first adding an uninitialized local with `depth = -1`. While parsing the
    /// initializer, if we encounter a uninitialized variable, we return an error. Once the full
    /// variable declaration has been parsed, we went back to the local to set its depth to the
    /// correct value.
    fn mark_initialized(&mut self) {
        let compiler = self.compiler_mut(0);
        // Do nothing if we are in the global scope.
        if compiler.scope_depth > 0 {
            compiler.locals.last_mut(0).depth = compiler.scope_depth;
        }
    }

    /// Parse a statement assuming that we're at the start of it. All lines of code must be
    /// statements in order to be executed.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// stmt       --> block
    ///              | exprStmt
    ///              | forStmt
    ///              | ifStmt
    ///              | printStmt
    ///              | returnStmt
    ///              | whileStmt ;
    /// ```
    fn statement(&mut self) {
        if self.advance_if(Kind::LBrace) {
            self.begin_scope();
            self.block();
            self.end_scope();
        } else if self.advance_if(Kind::Print) {
            self.print_statement();
        } else if self.advance_if(Kind::If) {
            self.if_statement();
        } else if self.advance_if(Kind::While) {
            self.while_statement();
        } else if self.advance_if(Kind::For) {
            self.for_statement();
        } else if self.advance_if(Kind::Return) {
            self.return_statement();
        } else {
            self.expression_statement();
        }
    }

    /// Parse a block assuming that we've already consumed the '{' token.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// block      --> "{" decl* "}" ;
    /// ```
    fn block(&mut self) {
        while !self.check_curr(Kind::RBrace) && !self.check_curr(Kind::Eof) {
            self.declaration();
        }
        self.consume(Kind::RBrace, "Expect '}' after block.");
    }

    /// Parse a print statement assuming that we've already consumed the 'print' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// printStmt  --> "print" expr ";" ;
    /// ```
    fn print_statement(&mut self) {
        self.expression();
        self.consume(Kind::Semicolon, "Expect ';' after value.");
        self.emit(Opcode::Print);
    }

    /// Parse an if statement assuming that we've already consumed the 'print' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// ifStmt     --> "if" "(" expr ")" stmt ( "else" stmt )? ;
    /// ```
    fn if_statement(&mut self) {
        // Conditional part.
        self.consume(Kind::LParen, "Expect '(' after 'if'.");
        self.expression();
        self.consume(Kind::RParen, "Expect ')' after condition.");
        // Jump over the then statement if condition is false.
        let jump_skip_then = self.emit_jump(Opcode::JumpIfFalse);
        // Pop the temporary value on stack created by the conditional expression.
        self.emit(Opcode::Pop);
        // Then statement.
        self.statement();
        // Jump over the else statement after finish executing the then statement.
        let jump_skip_else = self.emit_jump(Opcode::Jump);
        // Patch jump to skip to right before the else statement.
        self.patch_jump(jump_skip_then);
        // Pop the temporary value on stack created by the conditional expression.
        self.emit(Opcode::Pop);
        // Else statement.
        if self.advance_if(Kind::Else) {
            self.statement();
        }
        // Patch jump to skip to right after the else statement.
        self.patch_jump(jump_skip_else);
    }

    /// Parse an if statement assuming that we've already consumed the 'while' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// whileStmt  --> "while" "(" expr ")" stmt ;
    /// ```
    fn while_statement(&mut self) {
        // Track the start of the loop where we can jump back to.
        let loop_start = self.compiler(0).fun.chunk.instructions.len();
        // Conditional part.
        self.consume(Kind::LParen, "Expect '(' after 'while'.");
        self.expression();
        self.consume(Kind::RParen, "Expect ')' after condition.");
        // Jump over the loop body if condition is false.
        let jump_exit = self.emit_jump(Opcode::JumpIfFalse);
        // Pop the temporary value on stack created by the conditional expression.
        self.emit(Opcode::Pop);
        // Loop body.
        self.statement();
        // Emit instructions for jumping back to the start of the loop.
        self.emit_loop(loop_start);
        // Patch jump to skip to right after the loop body.
        self.patch_jump(jump_exit);
        // Pop the temporary value on stack created by the conditional expression.
        self.emit(Opcode::Pop);
    }

    /// Parse an if statement assuming that we've already consumed the 'for' keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// forStmt    --> "for" "(" ( varDecl | exprStmt | ";" ) expr? ";" expr? ")" stmt ;
    /// ```
    fn for_statement(&mut self) {
        // A for statement create its own scope.
        self.begin_scope();
        // Loop's initializer.
        self.consume(Kind::LParen, "Expect '(' after 'for'.");
        if self.advance_if(Kind::Semicolon) {
            // Empty initializer. Ignored.
        } else if self.advance_if(Kind::Var) {
            self.var_declaration();
        } else {
            self.expression_statement();
        }
        // Loop's condition.
        let loop_start = self.compiler(0).fun.chunk.instructions.len();
        let jump_exit = if self.advance_if(Kind::Semicolon) {
            // The conditional part is empty, so we don't have to emit a jump instruction.
            None
        } else {
            // Conditional expression.
            self.expression();
            self.consume(Kind::Semicolon, "Expect ';' after loop condition.");
            // Jump out of the loop.
            let jump_exit = self.emit_jump(Opcode::JumpIfFalse);
            // Clear out the result of the expression.
            self.emit(Opcode::Pop);
            Some(jump_exit)
        };
        // Loop's incrementor.
        let increment_start = if self.advance_if(Kind::RParen) {
            // The increment part is empty, so we don't have to emit a jump instruction.
            None
        } else {
            // If there's an incrementor, we immediately jump to the loop's body so it can be
            // executed first.
            let jump_to_body = self.emit_jump(Opcode::Jump);
            // Keep track of the incrementor's starting position.
            let increment_start = self.compiler(0).fun.chunk.instructions.len();
            // Parse expression and ignore its result at runtime.
            self.expression();
            self.emit(Opcode::Pop);
            self.consume(Kind::RParen, "Expect ')' after for clauses.");
            // Jump back the the start of the loop so we can start a new iteration.
            self.emit_loop(loop_start);
            // Patch jump to right before loop's body.
            self.patch_jump(jump_to_body);
            Some(increment_start)
        };
        // Loop's body.
        self.statement();
        match increment_start {
            // Jump back to the first instruction in the loop if there's no incrementor.
            None => self.emit_loop(loop_start),
            // Jump back to the incrementor so its expression can be run after the body.
            Some(offset) => self.emit_loop(offset),
        }
        // Patch loop exit jump if we have an exit condition.
        if let Some(jump_exit) = jump_exit {
            self.patch_jump(jump_exit);
            // Clear out the result of the expression.
            self.emit(Opcode::Pop);
        }
        // End the scope one we finish with the for loop
        self.end_scope();
    }

    /// Parse a return statement assuming that we've consumed the `return` keyword.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// returnStmt --> "return" expr? ";" ;
    /// ```
    fn return_statement(&mut self) {
        if self.compiler(0).fun_type == FunctionType::Script {
            self.error_prev("Can't return from top-level code.");
            return;
        }
        // Empty return put nil as the value of the function.
        if self.advance_if(Kind::Semicolon) {
            self.emit_return();
        } else {
            if self.compiler(0).fun_type == FunctionType::Initializer {
                self.error_prev("Can't return a value from an initializer.");
            }
            // Returned the value of an expression.
            self.expression();
            self.consume(Kind::Semicolon, "Expect ';' after return value.");
            self.emit(Opcode::Ret);
        }
    }

    /// Parse an expression statement assuming that we're at the start of it.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// exprStmt   --> expr ";" ;
    /// ```
    fn expression_statement(&mut self) {
        self.expression();
        self.consume(Kind::Semicolon, "Expect ';' after expression.");
        self.emit(Opcode::Pop);
    }

    /// Parse an expression assuming that we're at the start of it.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// expr       --> assign ;
    /// ```
    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }

    /// Starts at the current token and parses any expression at the given precedence level
    /// or higher
    ///
    /// ## Grammar
    ///
    /// ```text
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
    fn parse_precedence(&mut self, precedence: Precedence) {
        // An expression can be a target for assignment iff it's not part of any expression that
        // has a higher precedence than assignment.
        let can_assign = precedence <= Precedence::Assignment;
        self.advance();
        self.prefix_rule(can_assign);
        while precedence <= Precedence::of(self.token_curr.kind) {
            self.advance();
            self.infix_rule(can_assign);
        }
        // The assignment target is wrong, if the current expression can be assigned to but we
        // haven't consumed the '=' after all the steps.
        if can_assign && self.advance_if(Kind::Equal) {
            self.error_prev("Invalid assignment target.");
        }
    }

    /// Parse a prefix expression if the consumed token can be used in a prefix operation.
    fn prefix_rule(&mut self, can_assign: bool) {
        match self.token_prev.kind {
            Kind::LParen => self.grouping(),
            Kind::Minus | Kind::Bang => self.unary(),
            Kind::This => self.this(),
            Kind::Super => self.super_(),
            Kind::Ident => self.variable(can_assign),
            Kind::String => self.string(),
            Kind::Number => self.number(),
            Kind::True | Kind::False | Kind::Nil => self.literal(),
            _ => self.error_prev("Expect expression."),
        }
    }

    /// Parse an infix expression if the consumed token can be used in a infix operation.
    fn infix_rule(&mut self, can_assign: bool) {
        match self.token_prev.kind {
            Kind::LParen => self.call(),
            Kind::Dot => self.dot(can_assign),
            Kind::Or => self.or(),
            Kind::And => self.and(),
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
            _ => self.error_prev("Expect expression."),
        }
    }

    /// Parse a grouping of expressions assuming that the '(' token has been consumed.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    /// ```
    fn grouping(&mut self) {
        self.expression();
        self.consume(Kind::RParen, "Expect ')' after expression.");
    }

    /// Parse a unary operation assuming that the operator token has been consumed.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// unary      --> ( "!" | "-" ) unary
    ///              | call ;
    /// ```
    fn unary(&mut self) {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::Unary);
        match token_kind {
            Kind::Bang => self.emit(Opcode::Not),
            Kind::Minus => self.emit(Opcode::Neg),
            _ => unreachable!(),
        }
    }

    /// Parse a binary operation assuming that the LHS token and the operator token
    /// have been consumed.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// equality   --> comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison --> term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term       --> factor ( ( "-" | "+" ) factor )* ;
    /// factor     --> unary ( ( "/" | "*" ) unary )* ;
    /// ```
    fn binary(&mut self) {
        let token_kind = self.token_prev.kind;
        self.parse_precedence(Precedence::of(token_kind).next());
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
    }

    /// Parse the 'or' operator with short-circuiting.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// or         --> and ( "or" and )* ;
    /// ```
    fn or(&mut self) {
        // Jump pass all right operand once the condition is true.
        let jump_short_circuit = self.emit_jump(Opcode::JumpIfTrue);
        // Clean up the result of the previous expression.
        self.emit(Opcode::Pop);
        // Parse right operand.
        self.parse_precedence(Precedence::Or);
        // Patch jump to skip to the end of the expression.
        self.patch_jump(jump_short_circuit);
    }

    /// Parse the 'and' operator with short-circuiting.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// and        --> equality ( "and" equality )* ;
    /// ```
    fn and(&mut self) {
        // Jump pass all right operand once the condition is false.
        let jump_short_circuit = self.emit_jump(Opcode::JumpIfFalse);
        // Clean up the result of the previous expression.
        self.emit(Opcode::Pop);
        // Parse right operand.
        self.parse_precedence(Precedence::And);
        // Patch jump to skip to the end of the expression.
        self.patch_jump(jump_short_circuit);
    }

    /// Parse a function call when the function name and '(' have been consumed.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// call       --> primary ( "(" args? ")" | "." IDENT )* ;
    /// ```
    fn call(&mut self) {
        let argc = self.argument_list();
        self.emit(Opcode::Call);
        self.emit_byte(argc);
    }

    fn dot(&mut self, can_assign: bool) {
        self.consume(Kind::Ident, "Expect property name after '.'.");
        let name = self.identifier_constant(self.token_prev);

        if can_assign && self.advance_if(Kind::Equal) {
            self.expression();
            self.emit(Opcode::SetProperty);
            self.emit_byte(name);
        } else if self.advance_if(Kind::LParen) {
            // If we found an open parenthesis after a dotted identifier,
            // it's must be a method call.
            let argc = self.argument_list();
            self.emit(Opcode::Invoke);
            self.emit_byte(name);
            self.emit_byte(argc);
        } else {
            self.emit(Opcode::GetProperty);
            self.emit_byte(name);
        }
    }

    /// Parse the parameters of function call where the '(' token after the function
    /// name has been consumed.
    fn argument_list(&mut self) -> u8 {
        let mut argc = 0;
        if !self.check_curr(Kind::RParen) {
            loop {
                self.expression();
                if argc as usize == MAX_PARAMS {
                    self.error_prev("Can't have more than 255 arguments.");
                    break;
                }
                argc += 1;
                if !self.advance_if(Kind::Comma) {
                    break;
                }
            }
        }
        self.consume(Kind::RParen, "Expect ')' after arguments.");
        argc
    }

    /// Parse the 'this' keyword as a local variable.
    fn this(&mut self) {
        if self.classes.len() == 0 {
            self.error_prev("Can't use 'this' outside of a class.");
            return;
        }
        self.variable(false);
    }

    /// Parse the 'this' keyword as a local variable.
    fn super_(&mut self) {
        if self.classes.len() == 0 {
            self.error_prev("Can't use 'super' outside of a class.");
        } else if !self.class_compiler(0).has_super {
            self.error_prev("Can't use 'super' in a class with no superclass.");
        }

        self.consume(Kind::Dot, "Expect '.' after 'super'.");
        self.consume(Kind::Ident, "Expect superclass method name.");
        let name = self.identifier_constant(self.token_prev);

        // Load 'this' value onto the stack.
        self.named_variable(
            Token {
                kind: Kind::Ident,
                line: self.token_curr.line,
                lexeme: "this",
            },
            false,
        );
        let superclass_token = Token {
            kind: Kind::Ident,
            line: self.token_curr.line,
            lexeme: "super",
        };
        if self.advance_if(Kind::LParen) {
            // Optimization so that we don't have to create ObjBoundMethod if the super access is
            // called immediately.
            let argc = self.argument_list();
            self.named_variable(superclass_token, false);
            self.emit(Opcode::SuperInvoke);
            self.emit_byte(name);
            self.emit_byte(argc);
        } else {
            // Create ObjBoundMethod that can be assigned to some identifier.
            self.named_variable(superclass_token, false);
            self.emit(Opcode::GetSuper);
            self.emit_byte(name);
        }
    }

    /// Parse a variable identifier within an expression.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    /// ```
    fn variable(&mut self, can_assign: bool) {
        self.named_variable(self.token_prev, can_assign);
    }

    /// Emit the byte codes for loading a variable with a particular name.
    fn named_variable(&mut self, name: Token<'_>, can_assign: bool) {
        let (arg, op_get, op_set) = self
            // Find value in local frame.
            .resolve_local(name, 0)
            .map(|local| (local, Opcode::GetLocal, Opcode::SetLocal))
            .or_else(|| {
                // Find value in one frame above.
                self.resolve_upvalue(name, 0)
                    .map(|upval| (upval, Opcode::GetUpvalue, Opcode::SetUpvalue))
            })
            .unwrap_or_else(|| {
                // Find value in globals table.
                let id = self.identifier_constant(name);
                (id, Opcode::GetGlobal, Opcode::SetGlobal)
            });

        if can_assign && self.advance_if(Kind::Equal) {
            // The LHS can be used as an assignment target.
            self.expression();
            self.emit(op_set);
        } else {
            // The LHS can't be used as an assignment target.
            self.emit(op_get);
        }
        self.emit_byte(arg);
    }

    /// Find the stack index the hold the local variable with the given name.
    fn resolve_local(&mut self, name: Token<'_>, height: usize) -> Option<u8> {
        if height >= self.compilers.len() {
            // There's no compiler at this height.
            return None;
        }
        // Walk up from low scope to high scope to find a local with the given name.
        let compiler = self.compiler(height);
        for (id, local) in (0..=u8::MAX).zip(compiler.locals.iter()).rev() {
            if local.name == name.lexeme {
                if local.depth == -1 {
                    self.error_prev("Can't read local variable in its own initializer.");
                }
                // Found a valid value for the variable.
                return Some(id);
            }
        }
        None
    }

    /// Get the index of an upvalue within the current chunk.
    ///
    /// An upvalue refers to a local variable in an enclosing function. Every closure maintains
    /// an array of upvalues, one for each surrounding local variable that the closure uses.
    fn resolve_upvalue(&mut self, name: Token<'_>, height: usize) -> Option<u8> {
        if height >= self.compilers.len() {
            // There's no compiler at this height
            return None;
        }
        // Find a matching local variable in the enclosing function.
        if let Some(local) = self.resolve_local(name, height + 1) {
            // Mark the variable in the enclosing function as captured so we know to emit the
            // correct opcode for hoisting up the upvalue.
            unsafe {
                self.compiler_mut(height + 1)
                    .locals
                    .get_unchecked_mut(local as usize)
                    .is_captured = true;
            }
            return Some(self.add_upvalue(height, local, true));
        }
        // Find a matching upvalue in the enclosing function. An upvalue is like a node in a linked
        // list where its can references:
        // 1. Local variable of the immediately enclosing function.
        // 2. Upvalues of enclosing functions that are not the immediately enclosing one..
        if let Some(upvalue) = self.resolve_upvalue(name, height + 1) {
            return Some(self.add_upvalue(height, upvalue, false));
        }
        None
    }

    /// An an upvalue to the chunk. If we reference a value that has been captured, the index of
    /// corresponding upvalue is returned instead of adding a new upvalue.
    fn add_upvalue(&mut self, height: usize, index: u8, is_local: bool) -> u8 {
        // Find an upvalue that references the same index.
        for (upvalue_id, upvalue) in (0..=u8::MAX).zip(&*self.compiler(height).upvalues) {
            if upvalue.index == index && upvalue.is_local == is_local {
                return upvalue_id;
            }
        }
        let compiler = self.compiler_mut(height);
        let Ok(upvalue_count) = u8::try_from(compiler.upvalues.len()) else {
            self.error_prev("Too many closure variables in function.");
            return 0;
        };
        // Add the upvalue.
        let upvalue = Upvalue { is_local, index };
        // SAFETY: We already checked if `upvalues` is full.
        unsafe {
            compiler.upvalues.push_unchecked(upvalue);
        }
        upvalue_count
    }

    /// Create a string literal and emit byte codes to load it value.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    /// ```
    fn string(&mut self) {
        let s = String::from(self.token_prev.lexeme.trim_matches('"'));
        let s = self.heap.intern(s);
        let value = Value::Object(Object::String(s));
        self.emit_constant(value);
    }

    /// Create a number literal and emit byte codes to load it value.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    /// ```
    fn number(&mut self) {
        if let Ok(number) = self.token_prev.lexeme.parse() {
            let value = Value::Number(number);
            self.emit_constant(value);
        } else {
            self.error_prev("Expecting digits.");
        }
    }

    /// Create a literal and emit byte codes to load it value.
    ///
    /// ## Grammar
    ///
    /// ```text
    /// primary    --> IDENT | NUMBER | STRING
    ///              | "this" | "super" "." IDENT
    ///              | "true" | "false" | "nil"
    ///              | "(" expr ")" ;
    /// ```
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
        self.compiler_mut(0).fun.chunk.write(opcode, line);
    }

    /// Write the byte into the current compiling chunk.
    fn emit_byte(&mut self, byte: u8) {
        let line = self.token_prev.line;
        self.compiler_mut(0).fun.chunk.write_byte(byte, line);
    }

    /// Emit a jump instruction along with a 16-byte placeholder for the offset.
    fn emit_jump(&mut self, opcode: Opcode) -> usize {
        self.emit(opcode);
        self.emit_byte(0xff);
        self.emit_byte(0xff);
        self.compiler(0).fun.chunk.instructions.len() - 2
    }

    /// Emit a loop instruction along with a 16-byte placeholder for the offset.
    fn emit_loop(&mut self, start: usize) {
        self.emit(Opcode::Loop);
        // We do +2 to adjust for the 2 offset bytes.
        if let Ok(jump) = u16::try_from(self.compiler(0).fun.chunk.instructions.len() - start + 2) {
            let [hi, lo] = jump.to_be_bytes();
            self.emit_byte(hi);
            self.emit_byte(lo);
        } else {
            self.error_prev("Loop body too large.");
        }
    }

    /// Emit an implicit nil return.
    fn emit_return(&mut self) {
        if self.compiler(0).fun_type == FunctionType::Initializer {
            // A class initializer should put the instance on top of the stack when finish.
            self.emit(Opcode::GetLocal);
            self.emit_byte(0);
        } else {
            // Any other function emit NIL instead.
            self.emit(Opcode::Nil);
        }
        self.emit(Opcode::Ret);
    }

    /// Write a constant and the necessary byte codes for loading it to
    /// the currently compiling chunk.
    fn emit_constant(&mut self, value: Value) {
        let constant_id = self.make_constant(value);
        self.emit(Opcode::Const);
        self.emit_byte(constant_id);
    }

    fn patch_jump(&mut self, offset: usize) {
        // We do -2 to adjust for the 2 offset bytes.
        if let Ok(jump) = u16::try_from(self.compiler(0).fun.chunk.instructions.len() - offset - 2)
        {
            let [hi, lo] = jump.to_be_bytes();
            self.compiler_mut(0).fun.chunk.instructions[offset] = hi;
            self.compiler_mut(0).fun.chunk.instructions[offset + 1] = lo;
        } else {
            self.error_prev("Too much code to jump over.");
        }
    }

    /// Write a constant to the currently compiling chunk.
    fn make_constant(&mut self, value: Value) -> u8 {
        self.compiler_mut(0)
            .fun
            .chunk
            .write_constant(value)
            .map_or_else(
                || {
                    self.error_prev("Too many constants in one chunk.");
                    0
                },
                |idx| idx,
            )
    }

    /// Start a new scope.
    fn begin_scope(&mut self) {
        // Update the current scope.
        self.compiler_mut(0).scope_depth += 1;
    }

    /// End the current scope
    fn end_scope(&mut self) {
        // Update the current scope.
        self.compiler_mut(0).scope_depth -= 1;
        while self.compiler(0).locals.len() > 0 {
            let local = self.compiler(0).locals.last(0);
            // End once we reach the current scope.
            if local.depth <= self.compiler(0).scope_depth {
                break;
            }
            // Variables at the scope bellow get popped out of the stack. If the variable is
            // captured by some closure, we hoist it up into the heap.
            if local.is_captured {
                self.emit(Opcode::CloseUpvalue);
            } else {
                self.emit(Opcode::Pop);
            }
            self.compiler_mut(0).locals.pop();
        }
    }

    fn class_compiler(&self, height: usize) -> &ClassCompiler {
        let index = self.classes.len() - height - 1;
        unsafe { self.classes.get_unchecked(index) }
    }

    fn class_compiler_mut(&mut self, height: usize) -> &mut ClassCompiler {
        let index = self.classes.len() - height - 1;
        unsafe { self.classes.get_unchecked_mut(index) }
    }

    fn compiler(&self, height: usize) -> &Compiler<'src> {
        let index = self.compilers.len() - height - 1;
        unsafe { self.compilers.get_unchecked(index) }
    }

    fn compiler_mut(&mut self, height: usize) -> &mut Compiler<'src> {
        let index = self.compilers.len() - height - 1;
        unsafe { self.compilers.get_unchecked_mut(index) }
    }

    /// Synchronize the parser to a normal state where we can continue parsing
    /// after an error occurred.
    fn synchronize(&mut self) {
        self.panicking = false;
        while !self.check_curr(Kind::Eof) {
            // Skip tokens until we reach a statement boundary. Once we found something that look like
            // a statement, we can be confident that compilation can go back to normal.
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

    /// Go through the tokens return by the scanner a set up 2 fields
    /// `token_prev` and `token_curr`.
    fn advance(&mut self) {
        loop {
            match self.scanner.scan() {
                Err(err) => {
                    self.had_error = true;
                    if !self.panicking {
                        self.panicking = true;
                        eprintln!("{err}");
                    }
                }
                Ok(token) => {
                    self.token_prev = std::mem::replace(&mut self.token_curr, token);
                    break;
                }
            }
        }
    }

    /// Move to the next token iff the current token kind matches the given token kind.
    fn advance_if(&mut self, kind: Kind) -> bool {
        let matched = self.check_curr(kind);
        if matched {
            self.advance();
        }
        matched
    }

    /// Check if the current token has the given `token_kind`. Return an error with a custom
    /// message if the condition does not hold.
    fn consume(&mut self, token_kind: Kind, message: &str) {
        if self.check_curr(token_kind) {
            self.advance();
        } else {
            self.error_curr(message);
        }
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
    fn error_prev(&mut self, message: &str) {
        self.error_at(self.token_prev.line, self.token_prev.lexeme, message);
    }

    /// Create an compilation error pointing at the line of the current token.
    fn error_curr(&mut self, message: &str) {
        self.error_at(self.token_curr.line, self.token_curr.lexeme, message);
    }

    /// Create an compilation error pointing at a particular line and lexeme.
    fn error_at(&mut self, line: Line, lexeme: &str, message: &str) {
        if self.panicking {
            return;
        }
        self.had_error = true;
        self.panicking = true;
        if lexeme.is_empty() {
            eprintln!("{line} Error at end: {message}");
        } else {
            eprintln!("{line} Error at '{lexeme}': {message}");
        }
    }
}

/// A structure for tracking the compiler current nested classes.
#[derive(Debug)]
struct ClassCompiler {
    has_super: bool,
}

impl ClassCompiler {
    const fn new() -> Self {
        Self { has_super: false }
    }
}

/// A structure for tracking the compiler current scoped states.
#[derive(Debug)]
struct Compiler<'src> {
    fun: ObjFun,
    fun_type: FunctionType,
    /// The number of "blocks" surrounding the current piece of code that we're compiling.
    scope_depth: isize,
    /// A stack of local variables sorted by the order in which they are declared.
    locals: List<Local<'src>, MAX_LOCALS>,
    /// A stack of local variables sorted by the order in which they are declared.
    upvalues: List<Upvalue, MAX_UPVALUES>,
}

impl<'src> Compiler<'src> {
    fn new(fun: ObjFun, fun_type: FunctionType) -> Self {
        // If we're in a method/initializer then slot 0 is used for the class instance.
        // Otherwise, it's used for holding the executing function.
        let first_slot_name = match fun_type {
            FunctionType::Method | FunctionType::Initializer => "this",
            _ => "",
        };
        let mut locals = List::default();
        // SAFETY: We just created `locals` and are sure that it's not full.
        unsafe {
            locals.push_unchecked(Local {
                name: first_slot_name,
                depth: 0,
                is_captured: false,
            });
        };
        Self {
            fun,
            fun_type,
            scope_depth: 0,
            locals,
            upvalues: List::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum FunctionType {
    Script,
    Function,
    Method,
    Initializer,
}

#[derive(Debug)]
struct Upvalue {
    is_local: bool,
    index: u8,
}

/// A structure the representing local variables during compilation time.
#[derive(Debug)]
struct Local<'src> {
    /// The token that stores the name of the local identifier.
    name: &'src str,
    /// The scope depth in which the local variable was declared.
    depth: isize,
    /// The flag to check where this local variable is captured by some closure.
    is_captured: bool,
}

/// All precedence levels in Lox.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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
    const fn next(self) -> Self {
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
            Self::Call | Self::Primary => Self::Primary,
        }
    }

    /// Get the precedence of a specific token kind.
    const fn of(kind: Kind) -> Self {
        match kind {
            Kind::Or => Self::Or,
            Kind::And => Self::And,
            Kind::BangEqual | Kind::EqualEqual => Self::Equality,
            Kind::Greater | Kind::GreaterEqual | Kind::Less | Kind::LessEqual => Self::Comparison,
            Kind::Minus | Kind::Plus => Self::Term,
            Kind::Slash | Kind::Star => Self::Factor,
            Kind::LParen | Kind::Dot => Self::Call,
            _ => Self::None,
        }
    }
}
