use std::{collections::HashMap, ptr::NonNull, rc::Rc};

use crate::object::{ObjFun, Object, ObjectContent, ObjectRef};

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

    /// Allocates a new string object using the content of the input string.
    pub(crate) fn alloc_fun(&mut self, fun: ObjFun) -> ObjectRef {
        self.alloc(ObjectContent::Fun(fun))
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
