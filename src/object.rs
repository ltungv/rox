use std::{cell::RefCell, fmt, rc::Rc};

use rustc_hash::FxHashMap;

use crate::{chunk::Chunk, heap::Gc, value::Value};

/// A type alias for a heap-allocated string.
pub(crate) type RefString = Gc<Rc<str>>;

/// A type alias for a heap-allocated upvalue.
pub(crate) type RefUpvalue = Gc<RefCell<ObjUpvalue>>;

/// A type alias for a heap-allocated closure.
pub(crate) type RefClosure = Gc<ObjClosure>;

/// A type alias for a heap-allocated fun.
pub(crate) type RefFun = Gc<ObjFun>;

/// A type alias for a heap-allocated native fun.
pub(crate) type RefNativeFun = Gc<ObjNativeFun>;

/// A type alias for a heap-allocated class definition.
pub(crate) type RefClass = Gc<RefCell<ObjClass>>;

/// A type alias for a heap-allocated class instance.
pub(crate) type RefInstance = Gc<RefCell<ObjInstance>>;

/// A type alias for a heap-allocated bound method.
pub(crate) type RefBoundMethod = Gc<ObjBoundMethod>;

/// An enumeration of all potential errors that occur when working with objects.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ObjectError {
    #[error("Invalid cast.")]
    InvalidCast,
}

/// A numeration of all object types.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Object {
    /// A string object
    String(RefString),
    /// An upvalue object
    Upvalue(RefUpvalue),
    /// A closure object
    Closure(RefClosure),
    /// A function object
    Fun(RefFun),
    /// A native function object
    NativeFun(RefNativeFun),
    /// A class object
    Class(RefClass),
    /// A class instance object
    Instance(RefInstance),
    /// A bound method object
    BoundMethod(RefBoundMethod),
}

impl Object {
    /// Case the object as a string.
    pub(crate) fn as_string(&self) -> Result<&RefString, ObjectError> {
        if let Self::String(s) = self {
            Ok(s)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Case the object as an upvalue.
    pub(crate) fn as_upvalue(&self) -> Result<&RefUpvalue, ObjectError> {
        if let Self::Upvalue(u) = self {
            Ok(u)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Case the object as a closure.
    pub(crate) fn as_closure(&self) -> Result<&RefClosure, ObjectError> {
        if let Self::Closure(c) = self {
            Ok(c)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Case the object as a fun.
    pub(crate) fn as_fun(&self) -> Result<&RefFun, ObjectError> {
        if let Self::Fun(f) = self {
            Ok(f)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Case the object as a class.
    pub(crate) fn as_class(&self) -> Result<&RefClass, ObjectError> {
        if let Self::Class(c) = self {
            Ok(c)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Case the object as an instance.
    pub(crate) fn as_instance(&self) -> Result<&RefInstance, ObjectError> {
        if let Self::Instance(i) = self {
            Ok(i)
        } else {
            Err(ObjectError::InvalidCast)
        }
    }

    /// Mark the current object reference and put it in `grey_objects` if its has not been marked.
    pub(crate) fn mark(&self, grey_objects: &mut Vec<Object>) {
        match self {
            Self::String(s) if s.mark() => grey_objects.push(*self),
            Self::Upvalue(v) if v.mark() => grey_objects.push(*self),
            Self::Closure(c) if c.mark() => grey_objects.push(*self),
            Self::Fun(f) if f.mark() => grey_objects.push(*self),
            Self::NativeFun(f) if f.mark() => grey_objects.push(*self),
            Self::Class(c) if c.mark() => grey_objects.push(*self),
            Self::Instance(i) if i.mark() => grey_objects.push(*self),
            Self::BoundMethod(m) if m.mark() => grey_objects.push(*self),
            _ => {}
        }
    }

    /// Unmark the object.
    pub(crate) fn unmark(&self) {
        match self {
            Self::String(s) => s.unmark(),
            Self::Upvalue(v) => v.unmark(),
            Self::Closure(c) => c.unmark(),
            Self::Fun(f) => f.unmark(),
            Self::NativeFun(f) => f.unmark(),
            Self::Class(c) => c.unmark(),
            Self::Instance(i) => i.unmark(),
            Self::BoundMethod(m) => m.unmark(),
        }
    }

    /// Return whether the object is marked.
    pub(crate) fn is_marked(&self) -> bool {
        match self {
            Self::String(s) => s.is_marked(),
            Self::Upvalue(v) => v.is_marked(),
            Self::Closure(c) => c.is_marked(),
            Self::Fun(f) => f.is_marked(),
            Self::NativeFun(f) => f.is_marked(),
            Self::Class(c) => c.is_marked(),
            Self::Instance(i) => i.is_marked(),
            Self::BoundMethod(m) => m.is_marked(),
        }
    }

    /// Mark all object references that can be directly access by the current object and put them
    /// in `grey_objects` if they have not been marked.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        match &self {
            Object::Upvalue(upvalue) => upvalue.borrow().mark_references(grey_objects),
            Object::Closure(closure) => closure.mark_references(grey_objects),
            Object::Fun(fun) => fun.mark_references(grey_objects),
            Object::Class(class) => class.borrow().mark_references(grey_objects),
            Object::Instance(instance) => instance.borrow().mark_references(grey_objects),
            Object::BoundMethod(method) => method.mark_references(grey_objects),
            Object::String(_) | Object::NativeFun(_) => {}
        }
    }

    /// Get the next object reference in the linked list.
    pub(crate) fn get_next(&self) -> Option<Self> {
        match self {
            Self::String(s) => s.get_next(),
            Self::Upvalue(v) => v.get_next(),
            Self::Closure(c) => c.get_next(),
            Self::Fun(f) => f.get_next(),
            Self::NativeFun(f) => f.get_next(),
            Self::Class(c) => c.get_next(),
            Self::Instance(i) => i.get_next(),
            Self::BoundMethod(m) => m.get_next(),
        }
    }

    /// Set the next object reference in the linked list.
    pub(crate) fn set_next(&self, next: Option<Object>) {
        match self {
            Self::String(s) => s.set_next(next),
            Self::Upvalue(v) => v.set_next(next),
            Self::Closure(c) => c.set_next(next),
            Self::Fun(f) => f.set_next(next),
            Self::NativeFun(f) => f.set_next(next),
            Self::Class(c) => c.set_next(next),
            Self::Instance(i) => i.set_next(next),
            Self::BoundMethod(m) => m.set_next(next),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::String(s) => write!(f, "{}", ***s),
            Object::Upvalue(v) => write!(f, "{}", (***v).borrow()),
            Object::Closure(c) => write!(f, "{}", ***c),
            Object::Fun(fun) => write!(f, "{}", ***fun),
            Object::NativeFun(fun) => write!(f, "{}", ***fun),
            Object::Class(c) => write!(f, "{}", (***c).borrow()),
            Object::Instance(i) => write!(f, "{}", (***i).borrow()),
            Object::BoundMethod(m) => write!(f, "{}", ***m),
        }
    }
}

/// The content of an heap-allocated closure object.
#[derive(Debug)]
pub(crate) struct ObjClosure {
    // The function definition of this closure.
    pub(crate) fun: RefFun,
    // The variables captured by this closure.
    pub(crate) upvalues: Vec<RefUpvalue>,
}

impl ObjClosure {
    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if self.fun.mark() {
            grey_objects.push(Object::Fun(self.fun));
        }
        for upvalue in &self.upvalues {
            if upvalue.mark() {
                grey_objects.push(Object::Upvalue(*upvalue));
            }
        }
    }
}

impl fmt::Display for ObjClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", **self.fun)
    }
}

/// The content of an heap-allocated upvalue object.
#[derive(Debug)]
pub(crate) enum ObjUpvalue {
    /// An open upvalue references a stack slot and represents a variable that has not been
    /// closed over.
    Open(usize),
    /// A closed upvalue owns a heap-allocated value and represents a variable that has been
    /// closed over.
    Closed(Value),
}

impl ObjUpvalue {
    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let ObjUpvalue::Closed(Value::Object(obj)) = self {
            obj.mark(grey_objects);
        }
    }
}

impl fmt::Display for ObjUpvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "upvalue")
    }
}

/// The content of an heap-allocated function object.
#[derive(Debug)]
pub(crate) struct ObjFun {
    /// The name of the function
    pub(crate) name: Option<Rc<str>>,
    /// Number of parameters the function has
    pub(crate) arity: u8,
    /// Number of upvalues captured by the function
    pub(crate) upvalue_count: u8,
    /// The bytecode chunk of this function
    pub(crate) chunk: Chunk,
}

impl ObjFun {
    /// Create a new function object given its name.
    pub(crate) fn new(name: Option<Rc<str>>) -> Self {
        Self {
            name,
            arity: 0,
            upvalue_count: 0,
            chunk: Chunk::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        for constant in &self.chunk.constants {
            if let Value::Object(obj) = constant {
                obj.mark(grey_objects);
            }
        }
    }
}

impl fmt::Display for ObjFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match &self.name {
            None => write!(f, "<script>"),
            Some(s) => write!(f, "<fn {s}>"),
        }
    }
}

/// The content of an heap-allocated native function object.
pub(crate) struct ObjNativeFun {
    /// Number of parameters
    pub(crate) arity: u8,
    /// Native function reference
    pub(crate) call: fn(&[Value]) -> Value,
}

impl fmt::Display for ObjNativeFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "<native fn>")
    }
}

impl fmt::Debug for ObjNativeFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "<native fn>")
    }
}

/// The content of an heap-allocated class definition object.
#[derive(Debug)]
pub(crate) struct ObjClass {
    /// The name of the class.
    pub(crate) name: Rc<str>,
    /// A the methods defined in the class.
    pub(crate) methods: FxHashMap<Rc<str>, RefClosure>,
}

impl ObjClass {
    pub(crate) fn new(name: Rc<str>) -> Self {
        Self {
            name,
            methods: FxHashMap::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        for method in self.methods.values() {
            if method.mark() {
                grey_objects.push(Object::Closure(*method));
            }
        }
    }
}

impl fmt::Display for ObjClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// The content of an heap-allocated class instance object.
#[derive(Debug)]
pub(crate) struct ObjInstance {
    pub(crate) class: RefClass,
    pub(crate) fields: FxHashMap<Rc<str>, Value>,
}

impl ObjInstance {
    /// Create a new class object given its name.
    pub(crate) fn new(class: RefClass) -> Self {
        Self {
            class,
            fields: FxHashMap::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if self.class.mark() {
            grey_objects.push(Object::Class(self.class))
        }
        for value in self.fields.values() {
            if let Value::Object(obj) = value {
                obj.mark(grey_objects);
            }
        }
    }
}

impl fmt::Display for ObjInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} instance", (**self.class).borrow())
    }
}

/// The content of an heap-allocated bound method object.
#[derive(Debug)]
pub(crate) struct ObjBoundMethod {
    pub(crate) receiver: Value,
    pub(crate) method: RefClosure,
}

impl ObjBoundMethod {
    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let Value::Object(o) = self.receiver {
            o.mark(grey_objects);
        }
        if self.method.mark() {
            grey_objects.push(Object::Closure(self.method))
        }
    }
}

impl fmt::Display for ObjBoundMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", **self.method)
    }
}
