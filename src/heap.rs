use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    mem,
    rc::Rc,
};

use crate::object::{
    NativeFun, ObjBoundMethod, ObjClass, ObjClosure, ObjFun, ObjInstance, ObjUpvalue, Object,
    ObjectContent, ObjectRef,
};

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
            intern_str: Vec::new(),
            intern_ids: HashMap::new(),
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
        self.alloc(ObjectContent::Upvalue(RefCell::new(upvalue)))
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

    /// Allocates a new class object.
    pub(crate) fn alloc_class(&mut self, class: ObjClass) -> ObjectRef {
        self.alloc(ObjectContent::Class(RefCell::new(class)))
    }

    /// Allocates a new instance object.
    pub(crate) fn alloc_instance(&mut self, instance: ObjInstance) -> ObjectRef {
        self.alloc(ObjectContent::Instance(RefCell::new(instance)))
    }

    /// Allocates a new bound method object.
    pub(crate) fn alloc_bound_method(&mut self, method: ObjBoundMethod) -> ObjectRef {
        self.alloc(ObjectContent::BoundMethod(method))
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

    /// Release all objects whose address is not included in the hash set. This method also remove
    /// the intern strings when objects no long reference them.
    ///
    /// ## Safety
    ///
    /// We must ensure that no other piece of our code will ever use the references that are not in
    /// the hash set, otherwise we'll invalidate references that are in used.
    #[allow(unsafe_code)]
    pub(crate) unsafe fn sweep(&mut self, black_objects: &HashSet<*mut Object>) {
        let mut prev_obj: Option<ObjectRef> = None;
        let mut curr_obj = self.head;

        while let Some(curr_ref) = curr_obj {
            if black_objects.contains(&curr_ref.as_ptr()) {
                prev_obj = curr_obj;
                curr_obj = curr_ref.next.get();
            } else {
                curr_obj = curr_ref.next.get();
                if let Some(prev_ref) = prev_obj {
                    prev_ref.next.swap(&curr_ref.next);
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
        let boxed = Box::new(Object::new(self.head, content));
        let boxed_sz = mem::size_of_val(&boxed);
        self.alloc_bytes += boxed_sz;

        #[cfg(feature = "dbg-heap")]
        println!("{boxed:p} alloc {boxed} ({boxed_sz} bytes)",);

        let obj = ObjectRef::new(boxed);
        self.head = Some(obj);
        obj
    }

    /// Release an object reference from the managed heap.
    ///
    /// ## Safety
    ///
    /// We must ensure that no other piece of our code will ever use this reference, otherwise we'll
    /// invalidate a reference that is in used.
    #[allow(unsafe_code)]
    unsafe fn release(&mut self, obj: ObjectRef) -> Box<Object> {
        let boxed = Box::from_raw(obj.as_ptr());
        let boxed_sz = mem::size_of_val(&boxed);
        self.alloc_bytes -= boxed_sz;

        #[cfg(feature = "dbg-heap")]
        println!("{boxed:p} free {boxed} ({boxed_sz} bytes)");

        boxed
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
    #[allow(unsafe_code)]
    fn drop(&mut self) {
        // Safety: If the heap is drop then both the compiler and vm will no longer be in use so
        // deallocating all objects is safe.
        for object in self.into_iter() {
            unsafe { self.release(object) };
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

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            self.next = node.next.get();
            return Some(node);
        }
        None
    }
}
