use std::{cmp::Ordering, fmt, ops, rc::Rc};

use crate::object::{ObjectContent, ObjectRef};

#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ValueError {
    #[error("{0}")]
    InvalidUse(&'static str),
    #[error("Invalid cast.")]
    InvalidCast,
}

/// A enumeration of all supported primitive types in Lox and their underlying value.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Value {
    /// A nothing value in Lox
    Nil,
    /// A boolean value in Lox
    Bool(bool),
    /// A number value in Lox
    Number(f64),
    /// A heap-allocated object
    Object(ObjectRef),
}

impl Value {
    /// Cast the value as a constant string
    pub(crate) fn as_str(&self) -> Result<Rc<str>, ValueError> {
        if let Value::Object(o) = self {
            if let ObjectContent::String(s) = &o.content {
                return Ok(Rc::clone(s));
            }
        }
        Err(ValueError::InvalidCast)
    }

    pub(crate) fn is_truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    pub(crate) fn is_falsey(&self) -> bool {
        match self {
            Value::Bool(b) => !b,
            Value::Nil => true,
            _ => false,
        }
    }

    pub(crate) fn lt(&self, other: &Self) -> Result<Value, ValueError> {
        match self.partial_cmp(other) {
            Some(Ordering::Less) => Ok(Value::Bool(true)),
            Some(_) => Ok(Value::Bool(false)),
            None => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }

    pub(crate) fn le(&self, other: &Self) -> Result<Value, ValueError> {
        match self.partial_cmp(other) {
            Some(Ordering::Less | Ordering::Equal) => Ok(Value::Bool(true)),
            Some(_) => Ok(Value::Bool(false)),
            None => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }

    pub(crate) fn gt(&self, other: &Self) -> Result<Value, ValueError> {
        match self.partial_cmp(other) {
            Some(Ordering::Greater) => Ok(Value::Bool(true)),
            Some(_) => Ok(Value::Bool(false)),
            None => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }

    pub(crate) fn ge(&self, other: &Self) -> Result<Value, ValueError> {
        match self.partial_cmp(other) {
            Some(Ordering::Greater | Ordering::Equal) => Ok(Value::Bool(true)),
            Some(_) => Ok(Value::Bool(false)),
            None => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(v1), Self::Bool(v2)) => v1 == v2,
            (Self::Number(v1), Self::Number(v2)) => v1.eq(v2),
            (Self::Object(o1), Self::Object(o2)) => o1.eq(o2),
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
                "Operands must be two numbers or two strings.",
            )),
        }
    }
}

impl ops::Sub for &Value {
    type Output = Result<Value, ValueError>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 - n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }
}

impl ops::Mul for &Value {
    type Output = Result<Value, ValueError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 * n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }
}

impl ops::Div for &Value {
    type Output = Result<Value, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 / n2)),
            _ => Err(ValueError::InvalidUse("Operands must be numbers.")),
        }
    }
}

impl ops::Neg for &Value {
    type Output = Result<Value, ValueError>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),
            _ => Err(ValueError::InvalidUse("Operand must be a number.")),
        }
    }
}

impl ops::Not for &Value {
    type Output = Value;

    fn not(self) -> Self::Output {
        Value::Bool(self.is_falsey())
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
