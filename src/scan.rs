use std::{error, fmt, ops};

/// An enumeration of all the potential errors occur while scanning.
#[derive(Debug)]
pub enum Error {
    /// A string literal is unterminated.
    UnterminatedString(Line),
    /// Encounter an unexpected character while scanning.
    UnexpectedCharacter(Line),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnterminatedString(line) => write!(f, "{line} Error: Unterminated string."),
            Self::UnexpectedCharacter(line) => write!(f, "{line} Error: Unexpected character."),
        }
    }
}

/// Scanner reads characters from the source code and groups them in to a sequence of tokens.
pub struct Scanner<'src> {
    /// The original source string used when we need to make references for the tokens' lexeme.
    src: &'src str,
    /// The number of the current line through which the scanner is going.
    line: Line,
    /// The first byte postition of a lexeme.
    lexeme_head: usize,
    /// The last byte postition of a lexeme.
    lexeme_tail: usize,
}

impl<'src> Scanner<'src> {
    /// Create a new scanner for the given string.
    pub fn new(src: &'src str) -> Self {
        Self {
            src,
            line: Line::default(),
            lexeme_head: 0,
            lexeme_tail: 0,
        }
    }

    /// Consume and return the next token from source. When there's no token left, subsequent calls
    /// will always return the EOF token.
    pub fn scan(&mut self) -> Result<Token<'src>, Error> {
        self.skip_whitespace();
        let c = match self.advance() {
            None => {
                return Ok(Token {
                    kind: Kind::Eof,
                    line: self.line,
                    lexeme: "",
                });
            }
            Some(c) => c,
        };

        let token = match c {
            b'(' => self.make_token(Kind::LParen),
            b')' => self.make_token(Kind::RParen),
            b'{' => self.make_token(Kind::LBrace),
            b'}' => self.make_token(Kind::RBrace),
            b';' => self.make_token(Kind::Semicolon),
            b',' => self.make_token(Kind::Comma),
            b'.' => self.make_token(Kind::Dot),
            b'-' => self.make_token(Kind::Minus),
            b'+' => self.make_token(Kind::Plus),
            b'/' => self.make_token(Kind::Slash),
            b'*' => self.make_token(Kind::Star),
            b'!' => {
                if self.consume(b'=') {
                    self.make_token(Kind::BangEqual)
                } else {
                    self.make_token(Kind::Bang)
                }
            }
            b'=' => {
                if self.consume(b'=') {
                    self.make_token(Kind::EqualEqual)
                } else {
                    self.make_token(Kind::Equal)
                }
            }
            b'<' => {
                if self.consume(b'=') {
                    self.make_token(Kind::LessEqual)
                } else {
                    self.make_token(Kind::Less)
                }
            }
            b'>' => {
                if self.consume(b'=') {
                    self.make_token(Kind::GreaterEqual)
                } else {
                    self.make_token(Kind::Greater)
                }
            }
            b'"' => self.string()?,
            n if Self::is_digit(n) => self.number(),
            c if Self::is_valid_ident(c) => self.identity(),
            _ => {
                return Err(Error::UnexpectedCharacter(self.line));
            }
        };

        Ok(token)
    }

    fn identity(&mut self) -> Token<'src> {
        // Consume all alphanumeric characters.
        while self.peek_check(|c| Self::is_valid_ident(c) || Self::is_digit(c)) {
            self.advance();
        }
        // Make token based on the characters that we've consumed.
        let kind = match &self.src[self.lexeme_head..self.lexeme_tail] {
            "and" => Kind::And,
            "class" => Kind::Class,
            "else" => Kind::Else,
            "false" => Kind::False,
            "for" => Kind::For,
            "fun" => Kind::Fun,
            "if" => Kind::If,
            "nil" => Kind::Nil,
            "or" => Kind::Or,
            "print" => Kind::Print,
            "return" => Kind::Return,
            "super" => Kind::Super,
            "this" => Kind::This,
            "true" => Kind::True,
            "var" => Kind::Var,
            "while" => Kind::While,
            _ => Kind::Ident,
        };
        self.make_token(kind)
    }

    fn number(&mut self) -> Token<'src> {
        // Go through all numeric characters.
        while self.peek_check(Self::is_digit) {
            self.advance();
        }
        // Parse the decimal part if there's any.
        if self.peek_check(|c| c == b'.') && self.peek_next_check(Self::is_digit) {
            self.advance();
            while self.peek_check(Self::is_digit) {
                self.advance();
            }
        }
        self.make_token(Kind::Number)
    }

    fn string(&mut self) -> Result<Token<'src>, Error> {
        // Go through all characters that are not a double-quote.
        while self.peek_check(|c| c != b'"') {
            self.advance();
        }
        // Check if we reach EOF or an actual double-quote.
        if self.peek().is_none() {
            return Err(Error::UnterminatedString(self.line));
        }
        // Consume the terminating double-quote.
        self.advance();
        Ok(self.make_token(Kind::String))
    }

    fn skip_whitespace(&mut self) {
        // We treat comments, lines starting with 2 forward slashes, the same as whitespaces.
        while let Some(c) = self.peek() {
            match c {
                b' ' | b'\r' | b'\t' | b'\n' => {
                    self.advance();
                }
                b'/' => {
                    // Check if there're 2 consecutive forward slashes.
                    if !self.peek_next_check(|c| c == b'/') {
                        break;
                    }
                    // Discard characters until the end of line.
                    while self.peek_check(|c| c != b'\n') {
                        self.advance();
                    }
                }
                _ => break,
            }
        }
        self.lexeme_head = self.lexeme_tail;
    }

    /// Return the result of applying the given function to the next character in the iterator
    /// without consuming it. Return false if there's no more item.
    fn peek_check<F: Fn(u8) -> bool>(&self, check: F) -> bool {
        self.peek().is_some_and(check)
    }

    /// Return the result of applying the given function to the character after the next one in
    /// the iterator without consuming them. Return false if there's no more item.
    fn peek_next_check<F: Fn(u8) -> bool>(&self, check: F) -> bool {
        self.peek_next().is_some_and(check)
    }

    /// Return the next character in the iterator without consuming it.
    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.lexeme_tail).copied()
    }

    /// Return the character after the next one in the iterator without consuming them.
    fn peek_next(&self) -> Option<u8> {
        self.src.as_bytes().get(self.lexeme_tail + 1).copied()
    }

    /// Move the iterator forward by one character.
    fn advance(&mut self) -> Option<u8> {
        self.src.as_bytes().get(self.lexeme_tail).map(|&c| {
            self.lexeme_tail += 1;
            if c == b'\n' {
                self.line += 1;
            }
            c
        })
    }

    /// Consume the next chracter if it equals some expected character.
    fn consume(&mut self, expected: u8) -> bool {
        match self.peek() {
            None => false,
            Some(c) if c != expected => false,
            _ => {
                self.advance();
                true
            }
        }
    }

    /// Create a token of the given kind based on the current scanner's context.
    fn make_token(&self, kind: Kind) -> Token<'src> {
        Token {
            kind,
            lexeme: &self.src[self.lexeme_head..self.lexeme_tail],
            line: self.line,
        }
    }

    /// Return if the chracter is a valid ascii digit.
    const fn is_digit(c: u8) -> bool {
        c.is_ascii_digit()
    }

    /// Return if the chracter is alphabetic.
    const fn is_valid_ident(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_'
    }
}

/// Implementation of tokens that are allowed in Lox.
#[derive(Debug, Clone, Copy)]
pub struct Token<'src> {
    /// The kind of token.
    pub kind: Kind,
    /// The line in which this token was found.
    pub line: Line,
    /// The string segment in source that corresponds to this token.
    pub lexeme: &'src str,
}

impl<'src> Token<'src> {
    /// Create a token of type Eof with position set to the default value
    pub fn placeholder() -> Self {
        Self {
            kind: Kind::Eof,
            line: Line::default(),
            lexeme: "",
        }
    }
}

/// Lox token types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Single character '('
    LParen,
    /// Single character ')'
    RParen,
    /// Single character '{'
    LBrace,
    /// Single character '}'
    RBrace,
    /// Single character ';'
    Semicolon,
    /// Single character ','
    Comma,
    /// Single character '.'
    Dot,
    /// Single character '-'
    Minus,
    /// Single character '+'
    Plus,
    /// Single character '/'
    Slash,
    /// Single character '*'
    Star,
    /// Single character '!'
    Bang,
    /// Double character '!='
    BangEqual,
    /// Single character '='
    Equal,
    /// Double character '=='
    EqualEqual,
    /// Single character '>'
    Greater,
    /// Double character '>='
    GreaterEqual,
    /// Single character '<'
    Less,
    /// Double character '<='
    LessEqual,
    /// Named entity
    Ident,
    /// String literal
    String,
    /// Number literal
    Number,
    /// Keyword 'and'
    And,
    /// Keyword 'class'
    Class,
    /// Keyword 'else'
    Else,
    /// Boolean literal 'false'
    False,
    /// Keyword 'for'
    For,
    /// Keyword 'fun'
    Fun,
    /// Keyword 'if'
    If,
    /// Nothing literal 'nil'
    Nil,
    /// Keyword 'or'
    Or,
    /// Keyword 'print'
    Print,
    /// Keyword 'return'
    Return,
    /// Keyword 'super'
    Super,
    /// Keyword 'this'
    This,
    /// Boolean literal 'true'
    True,
    /// Keyword 'var'
    Var,
    /// Keyword 'while'
    While,
    /// Special token for indicating end-of-file
    Eof,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Line(usize);

impl Default for Line {
    fn default() -> Self {
        Self(1)
    }
}

impl ops::Deref for Line {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ops::AddAssign<usize> for Line {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "[line {}]", self.0)
    }
}
