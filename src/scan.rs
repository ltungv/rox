use std::{fmt, ops, str::Chars};

use itertools::MultiPeek;

/// An enumeration of all the potential errors occur while scanning.
#[derive(thiserror::Error, Debug, Clone, Copy)]
pub enum ScanError {
    /// A string literal is unterminated.
    #[error("{0} Error: Unterminated string.")]
    UnterminatedString(Line),
    /// Encounter an unexpected character while scanning.
    #[error("{0} Error: Unexpected character.")]
    UnexpectedCharacter(Line),
}

/// Scanner reads characters from the source code and groups them in to a sequence of tokens.
pub(crate) struct Scanner<'src> {
    /// The original source string used when we need to make references for the tokens' lexeme.
    src: &'src str,
    /// A multi-peekable iterator through all characters in the source string.
    src_iter: MultiPeek<Chars<'src>>,
    /// The number of the current line through which the scanner is going.
    line: Line,
    /// The first byte postition of a lexeme.
    lexeme_head: usize,
    /// The last byte postition of a lexeme.
    lexeme_tail: usize,
}

impl<'src> Scanner<'src> {
    /// Create a new scanner for the given string.
    pub(crate) fn new(src: &'src str) -> Self {
        let src_iter = itertools::multipeek(src.chars());
        Self {
            src,
            src_iter,
            line: Line::default(),
            lexeme_head: 0,
            lexeme_tail: 0,
        }
    }

    /// Consume and return the next token from source. When there's no token left, subsequent calls
    /// will always return the EOF token.
    pub(crate) fn scan(&mut self) -> Result<Token<'src>, ScanError> {
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
            '(' => self.make_token(Kind::LParen),
            ')' => self.make_token(Kind::RParen),
            '{' => self.make_token(Kind::LBrace),
            '}' => self.make_token(Kind::RBrace),
            ';' => self.make_token(Kind::Semicolon),
            ',' => self.make_token(Kind::Comma),
            '.' => self.make_token(Kind::Dot),
            '-' => self.make_token(Kind::Minus),
            '+' => self.make_token(Kind::Plus),
            '/' => self.make_token(Kind::Slash),
            '*' => self.make_token(Kind::Star),
            '!' => {
                if self.consume('=') {
                    self.make_token(Kind::BangEqual)
                } else {
                    self.make_token(Kind::Bang)
                }
            }
            '=' => {
                if self.consume('=') {
                    self.make_token(Kind::EqualEqual)
                } else {
                    self.make_token(Kind::Equal)
                }
            }
            '<' => {
                if self.consume('=') {
                    self.make_token(Kind::LessEqual)
                } else {
                    self.make_token(Kind::Less)
                }
            }
            '>' => {
                if self.consume('=') {
                    self.make_token(Kind::GreaterEqual)
                } else {
                    self.make_token(Kind::Greater)
                }
            }
            '"' => self.string()?,
            n if Self::is_digit(n) => self.number(),
            c if Self::is_alpha(c) => self.identity(),
            _ => {
                return Err(ScanError::UnexpectedCharacter(self.line));
            }
        };

        Ok(token)
    }

    fn identity(&mut self) -> Token<'src> {
        // Consume all alphanumeric characters.
        while self.peek_check(|c| Self::is_alpha(c) || Self::is_digit(c)) {
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
        if self.peek_check(|c| c == '.') && self.peek_next_check(Self::is_digit) {
            self.advance();
            while self.peek_check(Self::is_digit) {
                self.advance();
            }
        }
        self.make_token(Kind::Number)
    }

    fn string(&mut self) -> Result<Token<'src>, ScanError> {
        // Go through all characters that are not a double-quote.
        while self.peek_check(|c| c != '"') {
            self.advance();
        }
        // Check if we reach EOF or an actual double-quote.
        if self.peek().is_none() {
            return Err(ScanError::UnterminatedString(self.line));
        }
        // Consume the terminating double-quote.
        self.advance();
        Ok(self.make_token(Kind::String))
    }

    fn skip_whitespace(&mut self) {
        // We treat comments, lines starting with 2 forward slashes, the same as whitespaces.
        while let Some(c) = self.peek() {
            match c {
                ' ' | '\r' | '\t' | '\n' => {
                    self.advance();
                }
                '/' => {
                    // Check if there're 2 consecutive forward slashes.
                    if !self.peek_next_check(|c| c == '/') {
                        break;
                    }
                    // Discard characters until the end of line.
                    while self.peek_check(|c| c != '\n') {
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
    fn peek_check<F: Fn(char) -> bool>(&mut self, check: F) -> bool {
        self.peek().map(check).unwrap_or(false)
    }

    /// Return the result of applying the given function to the character after the next one in
    /// the iterator without consuming them. Return false if there's no more item.
    fn peek_next_check<F: Fn(char) -> bool>(&mut self, check: F) -> bool {
        self.peek_next().map(check).unwrap_or(false)
    }

    /// Return the next character in the iterator without consuming it.
    fn peek(&mut self) -> Option<char> {
        self.src_iter.reset_peek();
        self.src_iter.peek().copied()
    }

    /// Return the character after the next one in the iterator without consuming them.
    fn peek_next(&mut self) -> Option<char> {
        self.src_iter.reset_peek();
        match self.src_iter.peek() {
            None => None,
            Some(_) => self.src_iter.peek().copied(),
        }
    }

    /// Move the iterator forward by one character.
    fn advance(&mut self) -> Option<char> {
        self.src_iter.next().map(|c| {
            self.lexeme_tail += c.len_utf8();
            if c == '\n' {
                self.line += 1;
            }
            c
        })
    }

    /// Consume the next chracter if it equals some expected character.
    fn consume(&mut self, expected: char) -> bool {
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
    fn make_token(&mut self, kind: Kind) -> Token<'src> {
        Token {
            kind,
            lexeme: &self.src[self.lexeme_head..self.lexeme_tail],
            line: self.line,
        }
    }

    /// Return if the chracter is a valid ascii digit.
    fn is_digit(c: char) -> bool {
        c.is_ascii_digit()
    }

    /// Return if the chracter is alphabetic.
    fn is_alpha(c: char) -> bool {
        c.is_alphabetic() || c == '_'
    }
}

/// Implementation of tokens that are allowed in Lox.
#[derive(Debug)]
pub(crate) struct Token<'src> {
    /// The kind of token.
    pub(crate) kind: Kind,
    /// The line in which this token was found.
    pub(crate) line: Line,
    /// The string segment in source that corresponds to this token.
    pub(crate) lexeme: &'src str,
}

impl<'src> Token<'src> {
    /// Create a token of type Eof with position set to the default value
    pub(crate) fn placeholder() -> Self {
        Self {
            kind: Kind::Eof,
            line: Line::default(),
            lexeme: "",
        }
    }
}

/// Lox token types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
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

#[derive(Debug, Clone, Copy)]
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
