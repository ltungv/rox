use std::{collections::HashMap, mem, ptr::NonNull, rc::Rc};

use crate::object::{NativeFun, ObjClosure, ObjFun, ObjUpvalue, Object, ObjectContent, ObjectRef};

/// A managed heap that cleanups memory using a tracing garbage collector.
#[derive(Debug)]
pub(crate) struct Heap {
    alloc_bytes: usize,
    next_gc: usize,
    gc_growth_factor: usize,
    intern_str: Vec<Rc<str>>,
    intern_ids: HashMap<Rc<str>, usize>,
    head: Option<ObjectRef>,
}

impl Default for Heap {
    fn default() -> Self {
        Self {
            alloc_bytes: 0,
            next_gc: 1024 * 1024,
            gc_growth_factor: 2,
            intern_str: Vec::default(),
            intern_ids: HashMap::default(),
            head: None,
        }
    }
}

impl Heap {
    /// Allocates a new string object using the content of the input string.
    pub(crate) fn alloc_string(&mut self, s: String) -> ObjectRef {
        let content = self.intern(s);
        self.alloc(ObjectContent::String(content))
    }

    /// Allocates a new upvalue object using the content of the input string.
    pub(crate) fn alloc_upvalue(&mut self, upvalue: ObjUpvalue) -> ObjectRef {
        self.alloc(ObjectContent::Upvalue(upvalue))
    }

    /// Allocates a new closure object.
    pub(crate) fn alloc_closure(&mut self, closure: ObjClosure) -> ObjectRef {
        self.alloc(ObjectContent::Closure(closure))
    }

    /// Allocates a new function object.
    pub(crate) fn alloc_fun(&mut self, fun: ObjFun) -> ObjectRef {
        self.alloc(ObjectContent::Fun(fun))
    }

    /// Allocates a new native function object.
    pub(crate) fn alloc_native_fun(&mut self, native_fun: NativeFun) -> ObjectRef {
        self.alloc(ObjectContent::NativeFun(native_fun))
    }

    /// Interned a string and return the object's content holding the reference.
    pub(crate) fn intern(&mut self, s: String) -> Rc<str> {
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

    pub(crate) fn size(&self) -> usize {
        self.alloc_bytes
    }

    pub(crate) fn next_gc(&self) -> usize {
        #[cfg(not(feature = "dbg-stress-gc"))]
        let next = self.next_gc;

        #[cfg(feature = "dbg-stress-gc")]
        let next = 0;

        next
    }

    pub(crate) fn sweep(&mut self) {
        let mut prev_obj: Option<ObjectRef> = None;
        let mut curr_obj = self.head;

        while let Some(mut curr_ref) = curr_obj {
            if curr_ref.is_marked() {
                curr_ref.unmark();
                prev_obj = curr_obj;
                curr_obj = curr_ref.next;
            } else {
                curr_obj = curr_ref.next;
                if let Some(ref mut prev_ref) = prev_obj {
                    prev_ref.next = curr_ref.next;
                } else {
                    self.head = curr_obj;
                }
                self.release(curr_ref);
            }
        }

        #[cfg(feature = "dbg-heap")]
        self.trace_dangling_strings();

        self.intern_str.retain(|s| Rc::strong_count(s) > 2);
        self.intern_ids.retain(|k, _| Rc::strong_count(k) > 2);
        self.next_gc = self.alloc_bytes * self.gc_growth_factor;
    }

    /// Allocates a new object and returns a handle to it. The object is pushed to the head of
    /// the list of allocated data.
    fn alloc(&mut self, content: ObjectContent) -> ObjectRef {
        let object = Box::new(Object::new(self.head, content));
        let object_sz = mem::size_of_val(&object);
        self.alloc_bytes += object_sz;

        #[cfg(feature = "dbg-heap")]
        println!("{object:p} alloc {object} ({object_sz} bytes)");

        let object_ptr = NonNull::from(Box::leak(object));
        let object = ObjectRef::from(object_ptr);
        self.head = Some(object);
        object
    }

    #[allow(unsafe_code)]
    fn release(&mut self, obj: ObjectRef) -> Box<Object> {
        // SAFETY: If we still own a handle then the underlying data must not be deallocated.
        // Thus, it's consume and box it.
        let boxed = unsafe { Box::from_raw(obj.0.as_ptr()) };
        let boxed_sz = mem::size_of_val(&boxed);
        self.alloc_bytes -= boxed_sz;

        #[cfg(feature = "dbg-heap")]
        println!("{:p} free {obj} ({boxed_sz} bytes)", obj.0);

        boxed
    }

    /// Remove the object at the head of the linked list.
    fn pop(&mut self) -> Option<ObjectContent> {
        self.head.map(|head| {
            self.head = head.next;
            let object = self.release(head);
            object.content
        })
    }

    #[cfg(feature = "dbg-heap")]
    fn trace_dangling_strings(&self) {
        for s in &self.intern_str {
            if Rc::strong_count(s) <= 2 {
                println!("{:p} free {s}", s.as_ptr())
            }
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        while self.pop().is_some() {}
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

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            self.next = node.next;
            return Some(node);
        }
        None
    }
}
