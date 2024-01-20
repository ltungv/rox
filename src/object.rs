use std::{
    cell::{Cell, RefCell},
    error, fmt, mem,
    ops::{self, BitXor, Deref},
    ptr::NonNull,
};

use crate::{chunk::Chunk, table::Table, value::Value};

/// A type alias for a heap-allocated string.
pub type RefString = Gc<ObjString>;

/// A type alias for a heap-allocated upvalue.
pub type RefUpvalue = Gc<RefCell<ObjUpvalue>>;

/// A type alias for a heap-allocated closure.
pub type RefClosure = Gc<ObjClosure>;

/// A type alias for a heap-allocated fun.
pub type RefFun = Gc<ObjFun>;

/// A type alias for a heap-allocated native fun.
pub type RefNativeFun = Gc<ObjNativeFun>;

/// A type alias for a heap-allocated class definition.
pub type RefClass = Gc<RefCell<ObjClass>>;

/// A type alias for a heap-allocated class instance.
pub type RefInstance = Gc<RefCell<ObjInstance>>;

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
    pub fn unmark(&self) {
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
    pub fn is_marked(&self) -> bool {
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
    pub fn mark_references(&self, grey_objects: &mut Vec<Self>) {
        match &self {
            Self::Upvalue(upvalue) => upvalue.borrow().mark_references(grey_objects),
            Self::Closure(closure) => closure.mark_references(grey_objects),
            Self::Fun(fun) => fun.mark_references(grey_objects),
            Self::Class(class) => class.borrow().mark_references(grey_objects),
            Self::Instance(instance) => instance.borrow().mark_references(grey_objects),
            Self::BoundMethod(method) => method.mark_references(grey_objects),
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
            Self::String(s) => write!(f, "{}", ***s),
            Self::Upvalue(v) => write!(f, "{}", (***v).borrow()),
            Self::Closure(c) => write!(f, "{}", ***c),
            Self::Fun(fun) => write!(f, "{}", ***fun),
            Self::NativeFun(fun) => write!(f, "{}", ***fun),
            Self::Class(c) => write!(f, "{}", (***c).borrow()),
            Self::Instance(i) => write!(f, "{}", (***i).borrow()),
            Self::BoundMethod(m) => write!(f, "{}", ***m),
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
    // The function definition of this closure.
    pub fun: RefFun,
    // The variables captured by this closure.
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
        write!(f, "{}", **self.fun)
    }
}

/// The content of an heap-allocated upvalue object.
#[derive(Debug)]
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

/// The content of an heap-allocated function object.
#[derive(Debug)]
pub struct ObjFun {
    /// The name of the function
    pub name: Option<RefString>,
    /// Number of parameters the function has
    pub arity: u8,
    /// Number of upvalues captured by the function
    pub upvalue_count: u16,
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
        if let Some(name) = self.name {
            if name.mark() {
                grey_objects.push(Object::String(name));
            }
        }
        for constant in &self.chunk.constants {
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

/// The content of an heap-allocated native function object.
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

/// The content of an heap-allocated class definition object.
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
        for (k, v) in &self.methods {
            if k.mark() {
                grey_objects.push(Object::String(*k));
            }
            if v.mark() {
                grey_objects.push(Object::Closure(*v));
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

/// The content of an heap-allocated class instance object.
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
        for (k, v) in &self.fields {
            if k.mark() {
                grey_objects.push(Object::String(*k));
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
        write!(f, "{} instance", (**self.class).borrow())
    }
}

/// The content of an heap-allocated bound method object.
#[derive(Debug)]
pub struct ObjBoundMethod {
    pub receiver: Value,
    pub method: RefClosure,
}

impl ObjBoundMethod {
    /// Mark all object references that can be directly access by the current object.
    pub fn mark_references(&self, grey_objects: &mut Vec<Object>) {
        if let Value::Object(o) = self.receiver {
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
        write!(f, "{}", **self.method)
    }
}

pub trait GcSized {
    fn size(&self) -> usize;
}

impl<T: GcSized> GcSized for RefCell<T> {
    fn size(&self) -> usize {
        self.borrow().size()
    }
}

#[derive(Debug)]
pub struct GcData<T> {
    next: Cell<Option<Object>>,
    marked: Cell<bool>,
    data: T,
}

impl<T> GcData<T> {
    pub fn new(next: Option<Object>, data: T) -> Self {
        Self {
            next: Cell::new(next),
            marked: Cell::new(false),
            data,
        }
    }

    pub fn get_next(&self) -> Option<Object> {
        self.next.get()
    }

    pub fn set_next(&self, next: Option<Object>) {
        self.next.set(next);
    }

    pub fn is_marked(&self) -> bool {
        self.marked.get()
    }

    pub fn mark(&self) -> bool {
        if self.marked.get() {
            return false;
        }
        self.marked.set(true);
        true
    }

    pub fn unmark(&self) {
        self.marked.set(false);
    }
}

impl<T> ops::Deref for GcData<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T: GcSized> GcSized for GcData<T> {
    fn size(&self) -> usize {
        mem::size_of_val(&self.next) + mem::size_of_val(&self.marked) + self.data.size()
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
        let _ = Box::from_raw(self.ptr.as_ptr());
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
