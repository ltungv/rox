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
    Constant = 0,
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
    /// Check for equality between 2 operands.
    Equal = 15,
    /// Compare if the first operand is greater than the second
    Greater = 16,
    /// Compare if the first operand is less than the second
    Less = 17,
    /// Add two number operands or two string operands
    Add = 18,
    /// Subtract two number operands
    Subtract = 19,
    /// Multiply two number operands
    Multiply = 20,
    /// Divide two number operands
    Divide = 21,
    /// Apply logical `not` to a single boolean operand
    Not = 22,
    /// Negate a single number operand
    Negate = 23,
    /// Print an expression in human readable format
    Print = 24,
    /// Jump forward for n instructions
    Jump = 25,
    /// Jump forward for n instructions if current stack top is falsey
    JumpIfFalse = 26,
    /// Jump backward for n instructions
    Loop = 27,
    /// Make a function call
    Call = 28,
    /// Invoke method call directly without going though an access operation
    Invoke = 29,
    /// Invoke super call directly without going though an access operation
    SuperInvoke = 30,
    /// Add a new closure
    Closure = 31,
    /// Move captured value to the heap
    CloseUpvalue = 32,
    /// Return from the current function
    Return = 33,
    /// Create a class and bind it to a name
    Class = 34,
    /// Create a inheritance relation between two classes
    Inherit = 35,
    /// Define a method
    Method = 36,
}
