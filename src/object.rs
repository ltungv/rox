use std::{fmt, ops, ptr::NonNull, rc::Rc};

/// A reference to the heap-allocated object.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ObjectRef(pub(crate) NonNull<Object>);

impl ops::Deref for ObjectRef {
    type Target = Object;

    #[allow(unsafe_code)]
    fn deref(&self) -> &Self::Target {
        // SAFETY: If we still own a handle then the underlying must not be deallocated. Thus, it's
        // safe to get a reference from the raw pointer.
        unsafe { self.0.as_ref() }
    }
}

impl PartialEq for ObjectRef {
    fn eq(&self, other: &Self) -> bool {
        self.content.eq(&other.content)
    }
}
impl fmt::Display for ObjectRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// The structure of a heap-allocated object.
#[derive(Debug, Clone)]
pub struct Object {
    /// A pointer to the next object in the linked list of allocated objects.
    pub(crate) next: Option<NonNull<Object>>,
    /// The object's data.
    pub(crate) content: ObjectContent,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// A enumeration of all supported object types in Lox and their underlying value.
#[derive(Debug, Clone)]
pub(crate) enum ObjectContent {
    /// A heap allocated string
    String(Rc<str>),
    // /// A closure that can captured surrounding variables
    // Closure(Gc<ObjClosure>),
    // /// A function object
    // Fun(Gc<ObjFun>),
    // /// A class object
    // Class(Gc<RefCell<ObjClass>>),
    // /// A class instance
    // Instance(Gc<RefCell<ObjInstance>>),
    // /// A class instance
    // BoundMethod(Gc<ObjBoundMethod>),
}

impl PartialEq for ObjectContent {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ObjectContent::String(s1), ObjectContent::String(s2)) => Rc::ptr_eq(s1, s2),
        }
    }
}

impl fmt::Display for ObjectContent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Self::String(s) => write!(f, "{s}"),
            // Self::Closure(c) => write!(f, "{c}"),
            // Self::Fun(fun) => write!(f, "{fun}"),
            // Self::Class(c) => write!(f, "{}", c.borrow()),
            // Self::Instance(i) => write!(f, "{}", i.borrow()),
            // Self::BoundMethod(m) => write!(f, "{m}"),
        }
    }
}
