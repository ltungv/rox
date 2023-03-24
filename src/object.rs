use std::fmt;

/// The structure of a heap-allocated object.
#[derive(Debug, Clone)]
pub(crate) struct Object {
    /// A header shared by all object types.
    header: ObjectHeader,
    /// The object's data.
    content: ObjectContent,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// The structure for the object header shared by all object types.
#[derive(Debug, Clone)]
pub(crate) struct ObjectHeader;

/// A enumeration of all supported object types in Lox and their underlying value.
#[derive(Debug, Clone)]
pub(crate) enum ObjectContent {}

impl fmt::Display for ObjectContent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        // match self {
        //     // Self::String(s) => write!(f, "{s}"),
        //     // Self::Closure(c) => write!(f, "{c}"),
        //     // Self::Fun(fun) => write!(f, "{fun}"),
        //     // Self::Class(c) => write!(f, "{}", c.borrow()),
        //     // Self::Instance(i) => write!(f, "{}", i.borrow()),
        //     // Self::BoundMethod(m) => write!(f, "{m}"),
        // }
        write!(f, "object")
    }
}
