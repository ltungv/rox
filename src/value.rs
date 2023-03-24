use std::{cmp::Ordering, fmt, ops};

use crate::object::Object;

#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ValueError {
    #[error("{0}")]
    InvalidUse(&'static str),
}

/// A enumeration of all supported primitive types in Lox and their underlying value.
#[derive(Debug, Clone)]
pub(crate) enum Value {
    /// A nothing value in Lox
    Nil,
    /// A boolean value in Lox
    Bool(bool),
    /// A number value in Lox
    Number(f64),
    /// A heap-allocated object
    Object(Object),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(v1), Self::Bool(v2)) => v1 == v2,
            (Self::Number(v1), Self::Number(v2)) => v1.eq(v2),
            _ => false,
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Number(v1), Self::Number(v2)) => v1.partial_cmp(v2),
            _ => None,
        }
    }
}

impl ops::Add for &Value {
    type Output = Result<Value, ValueError>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 + n2)),
            _ => Err(ValueError::InvalidUse(
                "Operands must be two numbers or two strings",
            )),
        }
    }
}

impl ops::Sub for &Value {
    type Output = Result<Value, ValueError>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 - n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers")),
        }
    }
}

impl ops::Mul for &Value {
    type Output = Result<Value, ValueError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 * n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers")),
        }
    }
}

impl ops::Div for &Value {
    type Output = Result<Value, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 / n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers")),
        }
    }
}

impl ops::Neg for &Value {
    type Output = Result<Value, ValueError>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),
            _ => Err(ValueError::InvalidUse("Operand must be a number")),
        }
    }
}

impl ops::Not for &Value {
    type Output = Value;

    fn not(self) -> Self::Output {
        Value::Bool(match self {
            Value::Bool(b) => !b,
            Value::Nil => true,
            _ => false,
        })
    }
}

impl Default for Value {
    fn default() -> Self {
        Self::Nil
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Number(n) => {
                if n.trunc().eq(n) {
                    // Try to truncate the decimals if `n` is a whole number.
                    write!(f, "{n:.0?}")
                } else {
                    // Print the number as normal.
                    write!(f, "{n:?}")
                }
            }
            Self::Object(o) => write!(f, "{o}"),
        }
    }
}
