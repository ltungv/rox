use std::{collections::HashMap, fmt, ops, ptr::NonNull, rc::Rc, str::FromStr};

/// A managed heap that cleanups memory using a tracing garbage collector.
#[derive(Debug, Default)]
pub(crate) struct Heap {
    intern_str: Vec<Rc<str>>,
    intern_ids: HashMap<Rc<str>, usize>,
    head: Option<NonNull<Object>>,
}

impl Heap {
    /// Allocates a new string object using the content of the input string.
    pub(crate) fn alloc_string(&mut self, s: String) -> ObjectRef {
        let content = self.take_string(s);
        self.alloc(content)
    }

    /// Performs arithmetic addition on two object and returns a new object representing the result
    /// of the operation.
    pub(crate) fn add_objects(&mut self, lhs: &ObjectRef, rhs: &ObjectRef) -> ObjectRef {
        match (&lhs.content, &rhs.content) {
            (ObjectContent::String(s1), ObjectContent::String(s2)) => {
                let s1 = String::from_str(s1).expect("Infallible.");
                let s2 = String::from_str(s2).expect("Infallible.");
                let s = s1 + &s2;
                self.alloc_string(s)
            }
        }
    }

    /// Interned a string and return the object's content holding the reference.
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
    fn alloc(&mut self, content: ObjectContent) -> ObjectRef {
        let object = Box::new(Object {
            next: self.head,
            content,
        });
        let object_ptr = NonNull::from(Box::leak(object));
        self.head = Some(object_ptr);
        ObjectRef(object_ptr)
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
    #[cfg(not(debug_assertions))]
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }

    #[cfg(debug_assertions)]
    fn drop(&mut self) {
        let mut objects_count = 0;
        while self.pop().is_some() {
            objects_count += 1;
        }
        println!("Heap: Dropped {objects_count} objects");
        println!("Heap: Iterned string reference strong counts");
        for s in &self.intern_str {
            println!("  - '{}': {}", s, Rc::strong_count(s));
        }
    }
}

impl IntoIterator for &Heap {
    type Item = ObjectRef;

    type IntoIter = HeapIter;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { next: self.head }
    }
}

/// An iterator through all currently allocated objects.
pub(crate) struct HeapIter {
    next: Option<NonNull<Object>>,
}

impl Iterator for HeapIter {
    type Item = ObjectRef;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            // SAFETY: If the object was deallocated, it must be removed from the linked list. If
            // we still can access the object from the linked list then it must have not been
            // deallocated.
            self.next = unsafe { node.as_ref().next };
            return Some(ObjectRef(node));
        }
        None
    }
}

/// A reference to the heap-allocated object.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ObjectRef(NonNull<Object>);

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
