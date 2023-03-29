use std::{cell::RefCell, collections::HashMap, ptr::NonNull, rc::Rc};

use crate::object::{NativeFun, ObjClosure, ObjFun, ObjUpvalue, Object, ObjectContent, ObjectRef};

/// A managed heap that cleanups memory using a tracing garbage collector.
#[derive(Debug, Default)]
pub(crate) struct Heap {
    intern_str: Vec<Rc<str>>,
    intern_ids: HashMap<Rc<str>, usize>,
    head: Option<ObjectRef>,
}

impl Heap {
    /// Allocates a new string object using the content of the input string.
    pub(crate) fn alloc_string(&mut self, s: String) -> ObjectRef {
        let content = self.take_string(s);
        self.alloc(ObjectContent::String(content))
    }

    /// Allocates a new upvalue object using the content of the input string.
    pub(crate) fn alloc_upvalue(&mut self, upvalue: ObjUpvalue) -> ObjectRef {
        self.alloc(ObjectContent::Upvalue(RefCell::new(upvalue)))
    }

    /// Allocates a new closure object.
    pub(crate) fn alloc_closure(&mut self, closure: ObjClosure) -> ObjectRef {
        self.alloc(ObjectContent::Closure(RefCell::new(closure)))
    }

    /// Allocates a new function object.
    pub(crate) fn alloc_fun(&mut self, fun: ObjFun) -> ObjectRef {
        self.alloc(ObjectContent::Fun(RefCell::new(fun)))
    }

    /// Allocates a new native function object.
    pub(crate) fn alloc_native_fun(&mut self, native_fun: NativeFun) -> ObjectRef {
        self.alloc(ObjectContent::NativeFun(native_fun))
    }

    /// Interned a string and return the object's content holding the reference.
    pub(crate) fn take_string(&mut self, s: String) -> Rc<str> {
        match self.intern_ids.get(s.as_str()) {
            Some(id) => Rc::clone(&self.intern_str[*id]),
            None => {
                let s = Rc::from(s);
                let intern_id = self.intern_str.len();
                self.intern_str.push(Rc::clone(&s));
                self.intern_ids.insert(Rc::clone(&s), intern_id);
                s
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
        let object = ObjectRef::from(object_ptr);
        self.head = Some(object);
        object
    }

    /// Remove the object at the head of the linked list.
    #[allow(unsafe_code)]
    fn pop(&mut self) -> Option<ObjectContent> {
        // SAFETY: If the object was deallocated, it must be removed from the linked list. If
        // we still can access the object from the linked list then it must have not been
        // deallocated.
        self.head.map(|head| {
            let object: Box<Object> = head.into();
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
    next: Option<ObjectRef>,
}

impl Iterator for HeapIter {
    type Item = ObjectRef;

    #[allow(unsafe_code)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            // SAFETY: If the object was deallocated, it must be removed from the linked list. If
            // we still can access the object from the linked list then it must have not been
            // deallocated.
            self.next = node.next;
            return Some(node);
        }
        None
    }
}
