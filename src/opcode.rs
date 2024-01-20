/// Opcode is a byte specifying the action that the VM must take.
///
/// # Notes
///
/// If it was for performances purposes, the following options could be considered:
/// + Having the opcode designed to be as close as possbible to existing lower-level instructions
/// + Having specialized opcode for constant
///
/// We don't have a `Opcode::NotEqual` because we will transform `a != b` to `!(a == b)` to demonstrated
/// that bytecode can deviate from the actual user's code as long as they behave similarly. This is also
/// applied for operator `<=` and operator `>=`.
///
/// `a <= b` does not equals equivalent to `!(a > b)`, similarly with greater and greater or equal.
/// According to [IEEE 754] all comparison operators return `false` when an operand is `NaN`. These
/// are implementation details that we should keep in mind when making a real language.
///
/// [IEEE 754]: https://en.wikipedia.org/wiki/IEEE_754
#[derive(Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum Opcode {
    /// Load a constant
    Const = 0,
    /// Load a `nil` value
    Nil = 1,
    /// Load a `true` value
    True = 2,
    /// Load a `false` value
    False = 3,
    /// Pop the top of the stack
    Pop = 4,
    /// Set the value of a global variable
    GetLocal = 5,
    /// Set the value of a local variable
    SetLocal = 6,
    /// Get the value of a global variable
    GetGlobal = 7,
    /// Set the value of a global variable
    SetGlobal = 8,
    /// Pop the top of the stack and define a variable initialized with that value.
    DefineGlobal = 9,
    /// Get a variable through its upvalue
    GetUpvalue = 10,
    /// Set a variable through its upvalue
    SetUpvalue = 11,
    /// Get the value of a property on the class instance
    GetProperty = 12,
    /// Set the value of a property on the class instance
    SetProperty = 13,
    /// Get the super class instance of the current class
    GetSuper = 14,
    /// Check for inequality between 2 operands.
    NE = 15,
    /// Check for equality between 2 operands.
    EQ = 16,
    /// Compare if the first operand is greater than the second
    GT = 17,
    /// Compare if the first operand is greater than or equal the second
    GE = 18,
    /// Compare if the first operand is less than the second
    LT = 19,
    /// Compare if the first operand is less than or equal the second
    LE = 20,
    /// Add two number operands or two string operands
    Add = 21,
    /// Subtract two number operands
    Sub = 22,
    /// Multiply two number operands
    Mul = 23,
    /// Divide two number operands
    Div = 24,
    /// Apply logical `not` to a single boolean operand
    Not = 25,
    /// Negate a single number operand
    Neg = 26,
    /// Print an expression in human readable format
    Print = 27,
    /// Jump forward for n instructions
    Jump = 28,
    /// Jump forward for n instructions if current stack top is truthy
    JumpIfTrue = 29,
    /// Jump forward for n instructions if current stack top is falsey
    JumpIfFalse = 30,
    /// Jump backward for n instructions
    Loop = 31,
    /// Make a function call
    Call = 32,
    /// Invoke method call directly without going though an access operation
    Invoke = 33,
    /// Invoke super call directly without going though an access operation
    SuperInvoke = 34,
    /// Add a new closure
    Closure = 35,
    /// Move captured value to the heap
    CloseUpvalue = 36,
    /// Return from the current function
    Ret = 37,
    /// Create a class and bind it to a name
    Class = 38,
    /// Create a inheritance relation between two classes
    Inherit = 39,
    /// Define a method
    Method = 40,
}

impl From<Opcode> for u8 {
    fn from(op: Opcode) -> Self {
        op as Self
    }
}

impl TryFrom<u8> for Opcode {
    type Error = String;
    fn try_from(byte: u8) -> Result<Self, Self::Error> {
        let op = match byte {
            0 => Self::Const,
            1 => Self::Nil,
            2 => Self::True,
            3 => Self::False,
            4 => Self::Pop,
            5 => Self::GetLocal,
            6 => Self::SetLocal,
            7 => Self::GetGlobal,
            8 => Self::SetGlobal,
            9 => Self::DefineGlobal,
            10 => Self::GetUpvalue,
            11 => Self::SetUpvalue,
            12 => Self::GetProperty,
            13 => Self::SetProperty,
            14 => Self::GetSuper,
            15 => Self::NE,
            16 => Self::EQ,
            17 => Self::GT,
            18 => Self::GE,
            19 => Self::LT,
            20 => Self::LE,
            21 => Self::Add,
            22 => Self::Sub,
            23 => Self::Mul,
            24 => Self::Div,
            25 => Self::Not,
            26 => Self::Neg,
            27 => Self::Print,
            28 => Self::Jump,
            29 => Self::JumpIfTrue,
            30 => Self::JumpIfFalse,
            31 => Self::Loop,
            32 => Self::Call,
            33 => Self::Invoke,
            34 => Self::SuperInvoke,
            35 => Self::Closure,
            36 => Self::CloseUpvalue,
            37 => Self::Ret,
            38 => Self::Class,
            39 => Self::Inherit,
            40 => Self::Method,
            b => return Err(format!("Unknown byte-code '{b}'")),
        };
        Ok(op)
    }
}
