use std::{
    cell::Cell,
    error, fmt, mem,
    ops::{self, BitXor, Deref},
    ptr::NonNull,
};

use crate::{chunk::Chunk, table::Table, value::Value};

/// A type alias for a heap-allocated string.
pub type RefString = Gc<ObjString>;

/// A type alias for a heap-allocated upvalue.
pub type RefUpvalue = Gc<Cell<ObjUpvalue>>;

/// A type alias for a heap-allocated closure.
pub type RefClosure = Gc<ObjClosure>;

/// A type alias for a heap-allocated fun.
pub type RefFun = Gc<ObjFun>;

/// A type alias for a heap-allocated native fun.
pub type RefNativeFun = Gc<ObjNativeFun>;

/// A type alias for a heap-allocated class definition.
pub type RefClass = Gc<ObjClass>;

/// A type alias for a heap-allocated class instance.
pub type RefInstance = Gc<ObjInstance>;

/// A type alias for a heap-allocated bound method.
pub type RefBoundMethod = Gc<ObjBoundMethod>;

/// An enumeration of all potential errors that occur when working with objects.
#[derive(Debug)]
pub enum Error {
    InvalidCast,
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCast => write!(f, "Invalid cast."),
        }
    }
}

/// A numeration of all object types.
#[derive(Debug, Clone, Copy)]
pub enum Object {
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
    /// Mark the current object reference and put it in `grey_objects` if its has not been marked.
    pub fn mark(&self, grey_objects: &mut Vec<Self>) {
        let marked = match self {
            Self::String(s) => s.mark(),
            Self::Upvalue(v) => v.mark(),
            Self::Closure(c) => c.mark(),
            Self::Fun(f) => f.mark(),
            Self::NativeFun(f) => f.mark(),
            Self::Class(c) => c.mark(),
            Self::Instance(i) => i.mark(),
            Self::BoundMethod(m) => m.mark(),
        };
        if marked {
            grey_objects.push(*self);
        }
    }

    /// Unmark the object.
    pub fn unmark(&self) -> bool {
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
    pub fn marked(&self) -> bool {
        match self {
            Self::String(s) => s.marked(),
            Self::Upvalue(v) => v.marked(),
            Self::Closure(c) => c.marked(),
            Self::Fun(f) => f.marked(),
            Self::NativeFun(f) => f.marked(),
            Self::Class(c) => c.marked(),
            Self::Instance(i) => i.marked(),
            Self::BoundMethod(m) => m.marked(),
        }
    }

    /// Mark all object references that can be directly access by the current object and put them
    /// in `grey_objects` if they have not been marked.
    pub fn mark_references(&self, grey_objects: &mut Vec<Self>) {
        match self {
            Self::Upvalue(upvalue) => upvalue.as_ref().get().mark_references(grey_objects),
            Self::Closure(closure) => closure.as_ref().mark_references(grey_objects),
            Self::Fun(fun) => fun.as_ref().mark_references(grey_objects),
            Self::Class(class) => class.as_ref().mark_references(grey_objects),
            Self::Instance(instance) => instance.as_ref().mark_references(grey_objects),
            Self::BoundMethod(method) => method.as_ref().mark_references(grey_objects),
            Self::String(_) | Self::NativeFun(_) => {}
        }
    }

    /// Get the next object reference in the linked list.
    pub fn get_next(&self) -> Option<Self> {
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
    pub fn set_next(&self, next: Option<Self>) {
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

    #[cfg(feature = "dbg-heap")]
    pub fn addr(&self) -> usize {
        match self {
            Self::String(s) => s.as_ptr() as usize,
            Self::Upvalue(v) => v.as_ptr() as usize,
            Self::Closure(c) => c.as_ptr() as usize,
            Self::Fun(f) => f.as_ptr() as usize,
            Self::NativeFun(f) => f.as_ptr() as usize,
            Self::Class(c) => c.as_ptr() as usize,
            Self::Instance(i) => i.as_ptr() as usize,
            Self::BoundMethod(m) => m.as_ptr() as usize,
        }
    }
}

impl GcSized for Object {
    fn size(&self) -> usize {
        match self {
            Self::String(s) => s.size(),
            Self::Upvalue(v) => v.size(),
            Self::Closure(c) => c.size(),
            Self::Fun(fun) => fun.size(),
            Self::NativeFun(fun) => fun.size(),
            Self::Class(c) => c.size(),
            Self::Instance(i) => i.size(),
            Self::BoundMethod(m) => m.size(),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::String(s) => write!(f, "{}", s.as_ref()),
            Self::Upvalue(v) => write!(f, "{}", v.as_ref().get()),
            Self::Closure(c) => write!(f, "{}", c.as_ref()),
            Self::Fun(fun) => write!(f, "{}", fun.as_ref()),
            Self::NativeFun(fun) => write!(f, "{}", fun.as_ref()),
            Self::Class(c) => write!(f, "{}", c.as_ref()),
            Self::Instance(i) => write!(f, "{}", i.as_ref()),
            Self::BoundMethod(m) => write!(f, "{}", m.as_ref()),
        }
    }
}

/// The content of a heap-allocated string object.
#[derive(Debug)]
pub struct ObjString {
    pub data: String,
    pub hash: u32,
}

impl ObjString {
    pub fn hash(s: &str) -> u32 {
        let mut hash = 2_166_136_261;
        for b in s.bytes() {
            hash = hash.bitxor(u32::from(b));
            hash = hash.wrapping_mul(16_777_619);
        }
        hash
    }
}

impl GcSized for ObjString {
    fn size(&self) -> usize {
        mem::size_of::<Self>() + mem::size_of_val(&*self.data)
    }
}

impl From<&str> for ObjString {
    fn from(value: &str) -> Self {
        let data = String::from(value);
        let hash = Self::hash(value);
        Self { data, hash }
    }
}

impl fmt::Display for ObjString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.data)
    }
}

/// The content of a heap-allocated closure object.
#[derive(Debug)]
pub struct ObjClosure {
    /// The function definition of this closure.
    pub fun: RefFun,
    /// The variables captured by this closure.
    pub upvalues: Vec<RefUpvalue>,
}

impl ObjClosure {
    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
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

impl GcSized for ObjClosure {
    fn size(&self) -> usize {
        mem::size_of::<Self>() + mem::size_of_val(&*self.upvalues)
    }
}

impl fmt::Display for ObjClosure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fun.as_ref())
    }
}

/// The content of a heap-allocated upvalue object.
#[derive(Debug, Clone, Copy)]
pub enum ObjUpvalue {
    /// An open upvalue references a stack slot and represents a variable that has not been
    /// closed over.
    Open(usize),
    /// A closed upvalue owns a heap-allocated value and represents a variable that has been
    /// closed over.
    Closed(Value),
}

impl ObjUpvalue {
    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let Self::Closed(Value::Object(obj)) = self {
            obj.mark(grey_objects);
        }
    }
}

impl GcSized for ObjUpvalue {
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl fmt::Display for ObjUpvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "upvalue")
    }
}

/// The content of a heap-allocated function object.
#[derive(Debug)]
pub struct ObjFun {
    /// The name of the function
    pub name: Option<RefString>,
    /// Number of parameters the function has
    pub arity: u8,
    /// Number of upvalues captured by the function
    pub upvalue_count: usize,
    /// The bytecode chunk of this function
    pub chunk: Chunk,
}

impl ObjFun {
    /// Create a new function object given its name.
    pub fn new(name: Option<RefString>) -> Self {
        Self {
            name,
            arity: 0,
            upvalue_count: 0,
            chunk: Chunk::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let Some(name) = &self.name {
            if name.mark() {
                grey_objects.push(Object::String(*name));
            }
        }
        for constant in &*self.chunk.constants {
            if let Value::Object(obj) = constant {
                obj.mark(grey_objects);
            }
        }
    }
}

impl GcSized for ObjFun {
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl fmt::Display for ObjFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match &self.name {
            None => write!(f, "<script>"),
            Some(s) => write!(f, "<fn {}>", s.data),
        }
    }
}

/// The content of a heap-allocated native function object.
pub struct ObjNativeFun {
    /// Number of parameters
    pub arity: u8,
    /// Native function reference
    pub call: fn(&[Value]) -> Value,
}

impl GcSized for ObjNativeFun {
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }
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

/// The content of a heap-allocated class definition object.
#[derive(Debug)]
pub struct ObjClass {
    /// The name of the class.
    pub name: RefString,
    /// A the methods defined in the class.
    pub methods: Table<RefClosure>,
}

impl ObjClass {
    pub fn new(name: RefString) -> Self {
        Self {
            name,
            methods: Table::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if self.name.mark() {
            grey_objects.push(Object::String(self.name));
        }
        for (&k, &v) in &self.methods {
            if k.mark() {
                grey_objects.push(Object::String(k));
            }
            if v.mark() {
                grey_objects.push(Object::Closure(v));
            }
        }
    }
}

impl GcSized for ObjClass {
    fn size(&self) -> usize {
        mem::size_of_val(&self.name) + mem::size_of_val(&self.methods)
    }
}

impl fmt::Display for ObjClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name.data)
    }
}

/// The content of a heap-allocated class instance object.
#[derive(Debug)]
pub struct ObjInstance {
    pub class: RefClass,
    pub fields: Table<Value>,
}

impl ObjInstance {
    /// Create a new class object given its name.
    pub fn new(class: RefClass) -> Self {
        Self {
            class,
            fields: Table::default(),
        }
    }

    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if self.class.mark() {
            grey_objects.push(Object::Class(self.class));
        }
        for (&k, &v) in &self.fields {
            if k.mark() {
                grey_objects.push(Object::String(k));
            }
            if let Value::Object(obj) = v {
                obj.mark(grey_objects);
            }
        }
    }
}

impl GcSized for ObjInstance {
    fn size(&self) -> usize {
        mem::size_of_val(&self.class) + mem::size_of_val(&self.fields)
    }
}

impl fmt::Display for ObjInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} instance", self.class.as_ref())
    }
}

/// The content of a heap-allocated bound method object.
#[derive(Debug)]
pub struct ObjBoundMethod {
    pub receiver: Value,
    pub method: RefClosure,
}

impl ObjBoundMethod {
    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let Value::Object(o) = &self.receiver {
            o.mark(grey_objects);
        }
        if self.method.mark() {
            grey_objects.push(Object::Closure(self.method));
        }
    }
}

impl GcSized for ObjBoundMethod {
    fn size(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl fmt::Display for ObjBoundMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.method.as_ref())
    }
}

pub trait GcSized {
    fn size(&self) -> usize;
}

#[derive(Debug)]
pub struct GcData<T> {
    next: Cell<Option<Object>>,
    mark: Cell<bool>,
    data: T,
}

impl<T> GcData<T> {
    pub const fn new(next: Option<Object>, data: T) -> Self {
        Self {
            next: Cell::new(next),
            mark: Cell::new(false),
            data,
        }
    }

    pub fn get_next(&self) -> Option<Object> {
        self.next.get()
    }

    pub fn set_next(&self, next: Option<Object>) {
        self.next.set(next);
    }

    pub fn mark(&self) -> bool {
        self.mark.replace(true)
    }

    pub fn unmark(&self) -> bool {
        self.mark.replace(false)
    }

    pub fn marked(&self) -> bool {
        self.mark.get()
    }
}

impl<T> AsRef<T> for GcData<T> {
    fn as_ref(&self) -> &T {
        &self.data
    }
}

impl<T: GcSized> GcSized for GcData<T> {
    fn size(&self) -> usize {
        mem::size_of_val(&self.next) + mem::size_of_val(&self.mark) + self.data.size()
    }
}

impl<T: GcSized + Copy> GcSized for Cell<T> {
    fn size(&self) -> usize {
        self.get().size()
    }
}

#[derive(Debug)]
pub struct Gc<T> {
    ptr: NonNull<GcData<T>>,
}

impl<T> Gc<T> {
    pub fn new(boxed: Box<GcData<T>>) -> Self {
        Self {
            ptr: NonNull::from(Box::leak(boxed)),
        }
    }

    pub unsafe fn release(self) {
        _ = Box::from_raw(self.ptr.as_ptr());
    }

    pub fn ptr_eq(lhs: Self, rhs: Self) -> bool {
        lhs.ptr.eq(&rhs.ptr)
    }

    #[cfg(feature = "dbg-heap")]
    pub const fn as_ptr(&self) -> *const GcData<T> {
        self.ptr.as_ptr()
    }
}

impl<T: GcSized> GcSized for Gc<T> {
    fn size(&self) -> usize {
        self.deref().size()
    }
}

impl<T> ops::Deref for Gc<T> {
    type Target = GcData<T>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> Copy for Gc<T> {}
impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        *self
    }
}
