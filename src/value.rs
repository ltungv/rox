use std::{cmp::Ordering, fmt, ops};

use crate::object::{Gc, Object, RefClass, RefClosure, RefFun, RefInstance, RefString};

#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ValueError {
    #[error("Operand must be a number.")]
    UnaryOperandsMustBeNumber,
    #[error("Operands must be numbers.")]
    BinaryOperandsMustBeNumbers,
    #[error("Operands must be two numbers or two strings.")]
    BinaryOperandsMustBeNumbersOrStrings,
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
    Object(Object),
}

impl Value {
    /// Cast the object as a string.
    pub(crate) fn as_string(&self) -> Result<RefString, ValueError> {
        if let Self::Object(Object::String(s)) = self {
            Ok(*s)
        } else {
            Err(ValueError::InvalidCast)
        }
    }

    /// Cast the object as a closure.
    pub(crate) fn as_closure(&self) -> Result<RefClosure, ValueError> {
        if let Self::Object(Object::Closure(c)) = self {
            Ok(*c)
        } else {
            Err(ValueError::InvalidCast)
        }
    }

    /// Cast the object as a fun.
    pub(crate) fn as_fun(&self) -> Result<RefFun, ValueError> {
        if let Self::Object(Object::Fun(f)) = self {
            Ok(*f)
        } else {
            Err(ValueError::InvalidCast)
        }
    }

    /// Cast the object as a class.
    pub(crate) fn as_class(&self) -> Result<RefClass, ValueError> {
        if let Self::Object(Object::Class(c)) = self {
            Ok(*c)
        } else {
            Err(ValueError::InvalidCast)
        }
    }

    /// Cast the object as an instance.
    pub(crate) fn as_instance(&self) -> Result<RefInstance, ValueError> {
        if let Self::Object(Object::Instance(i)) = self {
            Ok(*i)
        } else {
            Err(ValueError::InvalidCast)
        }
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

    pub(crate) fn lt(&self, other: &Self) -> Result<bool, ValueError> {
        match self.partial_cmp(other) {
            Some(order) => Ok(matches!(order, Ordering::Less)),
            None => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }

    pub(crate) fn le(&self, other: &Self) -> Result<bool, ValueError> {
        match self.partial_cmp(other) {
            Some(order) => Ok(matches!(order, Ordering::Less | Ordering::Equal)),
            None => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }

    pub(crate) fn gt(&self, other: &Self) -> Result<bool, ValueError> {
        match self.partial_cmp(other) {
            Some(order) => Ok(matches!(order, Ordering::Greater)),
            None => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }

    pub(crate) fn ge(&self, other: &Self) -> Result<bool, ValueError> {
        match self.partial_cmp(other) {
            Some(order) => Ok(matches!(order, Ordering::Greater | Ordering::Equal)),
            None => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(v1), Self::Bool(v2)) => v1 == v2,
            (Self::Number(v1), Self::Number(v2)) => v1.eq(v2),
            (Self::Object(Object::String(s1)), Self::Object(Object::String(s2))) => {
                Gc::ptr_eq(s1, s2)
            }
            (Self::Object(Object::Upvalue(v1)), Self::Object(Object::Upvalue(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
            (Self::Object(Object::Closure(v1)), Self::Object(Object::Closure(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
            (Self::Object(Object::Fun(v1)), Self::Object(Object::Fun(v2))) => Gc::ptr_eq(v1, v2),
            (Self::Object(Object::NativeFun(v1)), Self::Object(Object::NativeFun(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
            (Self::Object(Object::Class(v1)), Self::Object(Object::Class(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
            (Self::Object(Object::Instance(v1)), Self::Object(Object::Instance(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
            (Self::Object(Object::BoundMethod(v1)), Self::Object(Object::BoundMethod(v2))) => {
                Gc::ptr_eq(v1, v2)
            }
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
            _ => Err(ValueError::BinaryOperandsMustBeNumbersOrStrings),
        }
    }
}

impl ops::Sub for &Value {
    type Output = Result<Value, ValueError>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 - n2)),
            _ => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }
}

impl ops::Mul for &Value {
    type Output = Result<Value, ValueError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 * n2)),
            _ => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }
}

impl ops::Div for &Value {
    type Output = Result<Value, ValueError>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Number(n1), Value::Number(n2)) => Ok(Value::Number(n1 / n2)),
            _ => Err(ValueError::BinaryOperandsMustBeNumbers),
        }
    }
}

impl ops::Neg for &Value {
    type Output = Result<Value, ValueError>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Number(n) => Ok(Value::Number(-n)),
            _ => Err(ValueError::UnaryOperandsMustBeNumber),
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
