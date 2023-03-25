use std::{
    collections::HashMap, convert::Infallible, fmt, ops, ptr::NonNull, rc::Rc, str::FromStr,
};

/// A managed heap that cleanups memory using a tracing garbage collector.
#[derive(Debug, Default)]
pub(crate) struct Heap {
    intern_str: Vec<Rc<str>>,
    intern_ids: HashMap<Rc<str>, usize>,
    head: Option<NonNull<Object>>,
}

impl Heap {
    pub(crate) fn alloc_string(&mut self, s: String) -> ObjectHandle {
        let content = self.take_string(s);
        self.alloc(content)
    }

    pub(crate) fn add_objects(
        &mut self,
        lhs: &ObjectHandle,
        rhs: &ObjectHandle,
    ) -> Result<ObjectHandle, ObjectError> {
        match (&lhs.content, &rhs.content) {
            (ObjectContent::String(s1), ObjectContent::String(s2)) => {
                let s1 = String::from_str(s1)?;
                let s2 = String::from_str(s2)?;
                let s = s1 + &s2;
                Ok(self.alloc_string(s))
            }
        }
    }

    fn take_string(&mut self, s: String) -> ObjectContent {
        match self.intern_ids.get(s.as_str()) {
            Some(id) => ObjectContent::String(Rc::clone(&self.intern_str[*id])),
            None => {
                let s = Rc::from(s);
                let intern_id = self.intern_str.len();
                self.intern_str.push(Rc::clone(&s));
                self.intern_ids.insert(Rc::clone(&s), intern_id);
                ObjectContent::String(s)
            }
        }
    }

    /// Allocates a new object and returns a handle to it. The object is pushed to the head of
    /// the list of allocated data.
    fn alloc(&mut self, content: ObjectContent) -> ObjectHandle {
        let object = Box::new(Object {
            next: self.head,
            content,
        });
        let object_ptr = NonNull::from(Box::leak(object));
        self.head = Some(object_ptr);
        ObjectHandle(object_ptr)
    }

    /// Remove the object at the head of the linked list.
    #[allow(unsafe_code)]
    fn pop(&mut self) -> Option<ObjectContent> {
        // SAFETY: If the object was deallocated, it must be removed from the linked list. If
        // we still can access the object from the linked list then it must have not been
        // deallocated.
        self.head.map(|head| {
            let object = unsafe { Box::from_raw(head.as_ptr()) };
            self.head = object.next;
            object.content
        })
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

impl IntoIterator for &Heap {
    type Item = ObjectHandle;

    type IntoIter = HeapIter;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { next: self.head }
    }
}

pub(crate) struct HeapIter {
    next: Option<NonNull<Object>>,
}

impl Iterator for HeapIter {
    type Item = ObjectHandle;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            // SAFETY: If the object was deallocated, it must be removed from the linked list. If
            // we still can access the object from the linked list then it must have not been
            // deallocated.
            self.next = unsafe { node.as_ref().next };
            return Some(ObjectHandle(node));
        }
        None
    }
}

#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ObjectError {
    #[error("{0}")]
    InvalidUse(&'static str),

    #[error(transparent)]
    Infallable(#[from] Infallible),
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ObjectHandle(NonNull<Object>);

impl ops::Deref for ObjectHandle {
    type Target = Object;

    #[allow(unsafe_code)]
    fn deref(&self) -> &Self::Target {
        // SAFETY: If we still own a handle then the underlying must not be deallocated. Thus, it's
        // safe to get a reference from the raw pointer.
        unsafe { self.0.as_ref() }
    }
}

impl PartialEq for ObjectHandle {
    fn eq(&self, other: &Self) -> bool {
        self.content.eq(&other.content)
    }
}
impl fmt::Display for ObjectHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.content)
    }
}

/// The structure of a heap-allocated object.
#[derive(Debug, Clone)]
pub struct Object {
    /// A pointer to the next object in the linked list of allocated objects.
    next: Option<NonNull<Object>>,
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

// /// A structure for class instance information
// #[derive(Debug)]
// pub struct ObjInstance {
//     /// The class type of this instance
//     pub class: Gc<RefCell<ObjClass>>,
//     /// The fields that this instance stores
//     pub fields: FxHashMap<StrId, Value>,
// }
//
// impl ObjInstance {
//     /// Create a new instance of the given class.
//     pub fn new(class: Gc<RefCell<ObjClass>>) -> Self {
//         Self {
//             class,
//             fields: FxHashMap::default(),
//         }
//     }
// }
//
// impl fmt::Display for ObjInstance {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
//         write!(f, "{} instance", intern::str(self.class.borrow().name))
//     }
// }
//
// /// A structure for holding class information
// #[derive(Debug)]
// pub struct ObjClass {
//     /// Class name
//     pub name: StrId,
//     /// Mapping of all methods defined on the class
//     pub methods: FxHashMap<StrId, Value>,
// }
//
// impl ObjClass {
//     /// Create a new class with the given name
//     pub fn new(name: StrId) -> Self {
//         Self {
//             name,
//             methods: FxHashMap::default(),
//         }
//     }
// }
//
// impl fmt::Display for ObjClass {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
//         write!(f, "{}", intern::str(self.name))
//     }
// }
//
// /// A class method that is bound to the instance that it was called on
// #[derive(Debug)]
// pub struct ObjBoundMethod {
//     /// Bound instance
//     pub receiver: Value,
//     /// The closure object of the method
//     pub method: Gc<ObjClosure>,
// }
//
// impl ObjBoundMethod {
//     /// Create a new method bound to the given receiver
//     pub fn new(receiver: Value, method: Gc<ObjClosure>) -> Self {
//         Self { receiver, method }
//     }
// }
//
// impl fmt::Display for ObjBoundMethod {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
//         write!(f, "{}", self.method)
//     }
// }
//
// /// A structure for managing closed-over value
// #[derive(Debug)]
// pub enum ObjUpvalue {
//     /// This field stores a slot offset which points to a value that was captured
//     Open(usize),
//     /// This stores the closed over value
//     Closed(Value),
// }
//
// /// A function that capture its surrounding environemnt,
// #[derive(Debug)]
// pub struct ObjClosure {
//     /// The base function of this closure
//     pub fun: Gc<ObjFun>,
//     /// Upvalues for indirect access to closed-over variables
//     pub upvalues: Vec<Gc<RefCell<ObjUpvalue>>>,
// }
//
// impl fmt::Display for ObjClosure {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
//         write!(f, "{}", self.fun)
//     }
// }
//
// impl ObjClosure {
//     /// Create a new closure of the function that captures the variables specified in the list of upvalues
//     pub fn new(fun: Gc<ObjFun>, upvalues: Vec<Gc<RefCell<ObjUpvalue>>>) -> Self {
//         Self { fun, upvalues }
//     }
// }
//
// /// A function object that holds the bytecode of the function along with other metadata
// #[derive(Debug)]
// pub struct ObjFun {
//     /// The name of the function
//     pub name: StrId,
//     /// Number of parameters the function has
//     pub arity: u8,
//     /// The bytecode chunk of this function
//     pub chunk: Chunk,
// }
//
// impl ObjFun {
//     /// Create a new function of the given name, with its arity set to 0 and its chunk set to the
//     /// default value
//     pub fn new(name: StrId) -> Self {
//         Self {
//             name,
//             arity: 0,
//             chunk: Chunk::default(),
//         }
//     }
// }
//
// impl fmt::Display for ObjFun {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
//         let name_str = intern::str(self.name);
//         if name_str.is_empty() {
//             write!(f, "<script>")
//         } else {
//             write!(f, "<fn {name_str}>")
//         }
//     }
// }
