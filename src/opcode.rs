use num_enum::{IntoPrimitive, TryFromPrimitive};

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
#[derive(Debug, Eq, PartialEq, IntoPrimitive, TryFromPrimitive)]
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
    /// Pop the top of the stack and define a variable initialized with that value.
    DefineGlobal = 8,
    /// Set the value of a global variable
    SetGlobal = 9,
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
    /// Jump forward for n instructions if current stack top is falsey
    JumpIfFalse = 29,
    /// Jump backward for n instructions
    Loop = 30,
    /// Make a function call
    Call = 31,
    /// Invoke method call directly without going though an access operation
    Invoke = 32,
    /// Invoke super call directly without going though an access operation
    SuperInvoke = 33,
    /// Add a new closure
    Closure = 34,
    /// Move captured value to the heap
    CloseUpvalue = 35,
    /// Return from the current function
    Ret = 36,
    /// Create a class and bind it to a name
    Class = 37,
    /// Create a inheritance relation between two classes
    Inherit = 38,
    /// Define a method
    Method = 39,
}
