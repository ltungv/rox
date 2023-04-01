use std::{
    cell::{Cell, Ref, RefCell, RefMut},
    fmt,
    marker::PhantomData,
    ops,
    ptr::NonNull,
    rc::Rc,
};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{chunk::Chunk, value::Value};

/// An enumeration of all potential errors that occur when working with objects.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ObjectError {
    #[error("Invalid cast.")]
    InvalidCast,
}

/// A reference to the heap-allocated object providing shared ownership. The underlying pointer is
/// ensured by the VM to always be valid, and data is cleaned using a mark and sweep GC.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ObjectRef {
    ptr: NonNull<Object>,
    obj: PhantomData<Object>,
}

impl ObjectRef {
    /// Create a new object reference by leaking the given box.
    pub(crate) fn new(boxed: Box<Object>) -> Self {
        Self {
            ptr: NonNull::from(Box::leak(boxed)),
            obj: PhantomData,
        }
    }

    /// Return the raw pointer to the object.
    pub(crate) fn as_ptr(&self) -> *mut Object {
        self.ptr.as_ptr()
    }

    /// Put the current object reference in `grey_objects` if its not in `black_objects`.
    pub(crate) fn mark(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        if black_objects.contains(&self.ptr.as_ptr()) {
            return;
        }

        #[cfg(feature = "dbg-heap")]
        println!("{:p} mark {self}", self.ptr);

        grey_objects.push(*self);
    }
}

impl ops::Deref for ObjectRef {
    type Target = Object;

    #[allow(unsafe_code)]
    fn deref(&self) -> &Self::Target {
        // SAFETY: If we still own a handle then the underlying must not be deallocated. Thus, it's
        // safe to get a reference from the raw pointer.
        unsafe { self.ptr.as_ref() }
    }
}

impl PartialEq for ObjectRef {
    fn eq(&self, other: &Self) -> bool {
        match (&self.content, &other.content) {
            (ObjectContent::String(s1), ObjectContent::String(s2)) => Rc::ptr_eq(s1, s2),
            (ObjectContent::Closure(_), ObjectContent::Closure(_)) => self.ptr.eq(&other.ptr),
            (ObjectContent::Fun(_), ObjectContent::Fun(_)) => self.ptr.eq(&other.ptr),
            (ObjectContent::NativeFun(_), ObjectContent::NativeFun(_)) => self.ptr.eq(&other.ptr),
            (ObjectContent::Class(_), ObjectContent::Class(_)) => self.ptr.eq(&other.ptr),
            (ObjectContent::Instance(_), ObjectContent::Instance(_)) => self.ptr.eq(&other.ptr),
            (ObjectContent::BoundMethod(_), ObjectContent::BoundMethod(_)) => {
                self.ptr.eq(&other.ptr)
            }
            _ => false,
        }
    }
}

impl fmt::Display for ObjectRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// The structure of a heap-allocated object.
#[derive(Debug)]
pub(crate) struct Object {
    /// A pointer to the next object in the linked list of allocated objects.
    pub(crate) next: Cell<Option<ObjectRef>>,
    /// The object's data.
    pub(crate) content: ObjectContent,
}

impl Object {
    /// Create a new object given its content and the pointer to the next object in the linked list
    /// of allocated objects.
    pub(crate) fn new(next: Option<ObjectRef>, content: ObjectContent) -> Self {
        Self {
            next: Cell::new(next),
            content,
        }
    }

    /// Cast the object to a string reference.
    pub(crate) fn as_string(&self) -> Result<Rc<str>, ObjectError> {
        match &self.content {
            ObjectContent::String(s) => Ok(Rc::clone(s)),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a upvalue reference.
    pub(crate) fn as_upvalue(&self) -> Result<Ref<'_, ObjUpvalue>, ObjectError> {
        match &self.content {
            ObjectContent::Upvalue(u) => Ok(u.borrow()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a mutable upvalue reference.
    pub(crate) fn as_upvalue_mut(&self) -> Result<RefMut<'_, ObjUpvalue>, ObjectError> {
        match &self.content {
            ObjectContent::Upvalue(u) => Ok(u.borrow_mut()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a closure reference.
    pub(crate) fn as_closure(&self) -> Result<&ObjClosure, ObjectError> {
        match &self.content {
            ObjectContent::Closure(c) => Ok(c),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a function reference.
    pub(crate) fn as_fun(&self) -> Result<&ObjFun, ObjectError> {
        match &self.content {
            ObjectContent::Fun(f) => Ok(f),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a class definition reference.
    pub(crate) fn as_class(&self) -> Result<Ref<'_, ObjClass>, ObjectError> {
        match &self.content {
            ObjectContent::Class(c) => Ok(c.borrow()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a mutable class definition reference.
    pub(crate) fn as_class_mut(&self) -> Result<RefMut<'_, ObjClass>, ObjectError> {
        match &self.content {
            ObjectContent::Class(c) => Ok(c.borrow_mut()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a class instance reference.
    pub(crate) fn as_instance(&self) -> Result<Ref<'_, ObjInstance>, ObjectError> {
        match &self.content {
            ObjectContent::Instance(i) => Ok(i.borrow()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a mutable class instance reference.
    pub(crate) fn as_instance_mut(&self) -> Result<RefMut<'_, ObjInstance>, ObjectError> {
        match &self.content {
            ObjectContent::Instance(i) => Ok(i.borrow_mut()),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Cast the object to a class instance reference.
    pub(crate) fn as_bound_method(&self) -> Result<&ObjBoundMethod, ObjectError> {
        match &self.content {
            ObjectContent::BoundMethod(m) => Ok(m),
            _ => Err(ObjectError::InvalidCast),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        match &self.content {
            ObjectContent::Upvalue(upvalue) => upvalue
                .borrow()
                .mark_references(grey_objects, black_objects),
            ObjectContent::Closure(closure) => closure.mark_references(grey_objects, black_objects),
            ObjectContent::Fun(fun) => fun.mark_references(grey_objects, black_objects),
            ObjectContent::Class(class) => {
                class.borrow().mark_references(grey_objects, black_objects)
            }
            ObjectContent::Instance(instance) => instance
                .borrow()
                .mark_references(grey_objects, black_objects),
            ObjectContent::BoundMethod(method) => {
                method.mark_references(grey_objects, black_objects)
            }
            ObjectContent::String(_) | ObjectContent::NativeFun(_) => {}
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// A enumeration of all supported object types in Lox and their underlying value.
#[derive(Debug)]
pub(crate) enum ObjectContent {
    /// A string object
    String(Rc<str>),
    /// An upvalue object
    Upvalue(RefCell<ObjUpvalue>),
    /// A closure object
    Closure(ObjClosure),
    /// A function object
    Fun(ObjFun),
    /// A native function object
    NativeFun(NativeFun),
    /// A class object
    Class(RefCell<ObjClass>),
    /// A class instance object
    Instance(RefCell<ObjInstance>),
    /// A bound method object
    BoundMethod(ObjBoundMethod),
}

impl fmt::Display for ObjectContent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Self::String(s) => write!(f, "{s}"),
            Self::Upvalue(u) => write!(f, "{}", u.borrow()),
            Self::Closure(c) => write!(f, "{c}"),
            Self::Fun(fun) => write!(f, "{fun}"),
            Self::NativeFun(fun) => write!(f, "{fun}"),
            Self::Class(c) => write!(f, "{}", c.borrow()),
            Self::Instance(i) => write!(f, "{}", i.borrow()),
            Self::BoundMethod(m) => write!(f, "{m}"),
        }
    }
}

/// The content of an heap-allocated closure object.
#[derive(Debug)]
pub(crate) struct ObjClosure {
    // The function definition of this closure.
    pub(crate) fun: ObjectRef,
    // The variables captured by this closure.
    pub(crate) upvalues: Vec<ObjectRef>,
}

impl ObjClosure {
    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        self.fun.mark(grey_objects, black_objects);
        for upvalue in &self.upvalues {
            upvalue.mark(grey_objects, black_objects);
        }
    }
}

impl fmt::Display for ObjClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fun)
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
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        if let ObjUpvalue::Closed(Value::Object(obj)) = self {
            obj.mark(grey_objects, black_objects);
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
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        for constant in &self.chunk.constants {
            if let Value::Object(obj) = constant {
                obj.mark(grey_objects, black_objects);
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
pub(crate) struct NativeFun {
    /// Number of parameters
    pub(crate) arity: u8,
    /// Native function reference
    pub(crate) call: fn(&[Value]) -> Value,
}

impl fmt::Display for NativeFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "<native fn>")
    }
}

impl fmt::Debug for NativeFun {
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
    pub(crate) methods: FxHashMap<Rc<str>, ObjectRef>,
}

impl ObjClass {
    pub(crate) fn new(name: Rc<str>) -> Self {
        Self {
            name,
            methods: FxHashMap::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        for method in self.methods.values() {
            method.mark(grey_objects, black_objects);
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
    pub(crate) class: ObjectRef,
    pub(crate) fields: FxHashMap<Rc<str>, Value>,
}

impl ObjInstance {
    /// Create a new class object given its name.
    pub(crate) fn new(class: ObjectRef) -> Self {
        Self {
            class,
            fields: FxHashMap::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        self.class.mark(grey_objects, black_objects);
        for value in self.fields.values() {
            if let Value::Object(obj) = value {
                obj.mark(grey_objects, black_objects);
            }
        }
    }
}

impl fmt::Display for ObjInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} instance", self.class)
    }
}

/// The content of an heap-allocated bound method object.
#[derive(Debug)]
pub(crate) struct ObjBoundMethod {
    pub(crate) receiver: Value,
    pub(crate) method: ObjectRef,
}

impl ObjBoundMethod {
    /// Mark all object references that can be directly access by the current object.
    pub(crate) fn mark_references(
        &self,
        grey_objects: &mut Vec<ObjectRef>,
        black_objects: &FxHashSet<*mut Object>,
    ) {
        if let Value::Object(o) = self.receiver {
            o.mark(grey_objects, black_objects);
        }
        self.method.mark(grey_objects, black_objects)
    }
}

impl fmt::Display for ObjBoundMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.method)
    }
}
