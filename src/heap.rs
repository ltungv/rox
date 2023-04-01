use std::{cell::RefCell, mem, rc::Rc};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::object::{
    NativeFun, ObjBoundMethod, ObjClass, ObjClosure, ObjFun, ObjInstance, ObjUpvalue, Object,
    ObjectContent, ObjectRef,
};

/// The default GC threshold when initialize.
const GC_NEXT_THRESHOLD: usize = 1024 * 1024;

/// The default GC threshold growth factor. Each time a GC is performed, we set the next GC
/// threshold to `GC_GROWTH_FACTOR * <current_allocated_bytes>`.
const GC_GROWTH_FACTOR: usize = 2;

/// A managed heap that use `ObjectRef` to give out references to allocated objects. Objects are
/// linked together using an intrusive linked-list, so the heap can traverse all allocated objects.
///
/// Our current Heap design does not own the objects that it allocates. Instead, the references that
/// we hand out provide shared ownership to the object. Because we control how the VM is run, we
/// know exactly when an object can be deallocated. Thus, in the context of the VM,  `ObjectRef` is
/// similar to a smart pointer that can deallocate itself when its no longer in use.
#[derive(Debug)]
pub(crate) struct Heap {
    // States for the GC.
    alloc_bytes: usize,
    gc_next_threshold: usize,
    gc_growth_factor: usize,

    // We save space and speed up string comparison by interning them. We intern string by storing
    // all unique strings in a vector, and use a hash map to store mappings between a string and
    // its index.
    intern_str: Vec<Rc<str>>,
    intern_ids: FxHashMap<Rc<str>, usize>,

    // The head of the singly linked list of heap-allocated objects.
    head: Option<ObjectRef>,
}

impl Default for Heap {
    fn default() -> Self {
        Self {
            alloc_bytes: 0,
            gc_next_threshold: GC_NEXT_THRESHOLD,
            gc_growth_factor: GC_GROWTH_FACTOR,
            intern_str: Vec::new(),
            intern_ids: FxHashMap::default(),
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

    /// Interned a string and returned a reference counted pointer to it. If the given string has
    /// been interned, an existing `Rc<str>` is cloned and returned. Otherwise, we turn the given
    /// string into a new `Rc<str>` and add it to our collection of unique strings.
    pub(crate) fn intern(&mut self, s: String) -> Rc<str> {
        match self.intern_ids.get(s.as_str()) {
            // Clone the reference counted pointer, increasing its strong count.
            Some(id) => Rc::clone(&self.intern_str[*id]),
            None => {
                let s = Rc::from(s);
                let intern_id = self.intern_str.len();
                // Use a `Vec` so we can have an index for each string.
                self.intern_str.push(Rc::clone(&s));
                // Use a hash map so we can quickly check for uniqueness and find the index of
                // some interned string.
                self.intern_ids.insert(Rc::clone(&s), intern_id);
                s
            }
        }
    }

    /// Returned the number of bytes that are being allocated.
    pub(crate) fn size(&self) -> usize {
        self.alloc_bytes
    }

    /// Returned the next GC threshold in bytes. If `Self::size() > Self::next_gc()`, the user should start
    /// tracing all reachable objects and hand it to `Self::sweep`.
    pub(crate) fn next_gc(&self) -> usize {
        #[cfg(not(feature = "dbg-stress-gc"))]
        let next = self.gc_next_threshold;

        #[cfg(feature = "dbg-stress-gc")]
        let next = 0;

        next
    }

    /// Release all objects whose address is not included in the hash set. This method also remove
    /// the intern strings when objects no long reference them.
    ///
    /// ## Safety
    ///
    /// We must ensure that all reachable pointers are included in `black_objects`.
    #[allow(unsafe_code)]
    pub(crate) unsafe fn sweep(&mut self, black_objects: &FxHashSet<*mut Object>) {
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

        // The minimum number strong count should be 2 (1 for the vec and 1 for the hash map).
        // Thus, any string that has `Rc::strong_count == 2` is no longer referenced and we can
        // remove it.
        self.intern_str.retain(|s| Rc::strong_count(s) > 2);
        self.intern_ids.retain(|k, _| Rc::strong_count(k) > 2);

        self.gc_next_threshold = self.alloc_bytes * self.gc_growth_factor;
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
    /// + We must ensure that no other piece of our code will ever use this reference, otherwise we'll
    /// invalidate a reference that is in used.
    /// + Before calling this method, we must ensure that the object is removed from the linked list of
    /// heap-allocated objects.
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
