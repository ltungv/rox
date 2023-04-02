use std::{cell::Cell, marker::PhantomData, mem, ops::Deref, ptr::NonNull, rc::Rc};

use rustc_hash::FxHashMap;

use crate::object::Object;

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
    head: Option<Object>,
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
    /// Allocates a new object and returns a handle to it. The object is pushed to the head of
    /// the list of allocated data.
    pub(crate) fn alloc<T, F>(&mut self, data: T, map: F) -> Object
    where
        F: Fn(Gc<T>) -> Object,
    {
        let boxed = Box::new(GcData::new(self.head, data));
        let size = mem::size_of_val(&boxed);
        self.alloc_bytes += size;

        #[cfg(feature = "dbg-heap")]
        println!("{boxed:p} alloc {size} bytes",);

        let object = map(Gc::new(boxed));
        self.head = Some(object);
        object
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

    /// Release all objects whose address is not included in the hash set. This method also remove
    /// the intern strings when objects no long reference them.
    ///
    /// ## Safety
    ///
    /// We must ensure that all reachable pointers have been marked. Otherwise, we'll deallocate
    /// objects that are in-used and leave dangling pointers.
    #[allow(unsafe_code)]
    pub(crate) unsafe fn sweep(&mut self) {
        let mut prev_obj: Option<Object> = None;
        let mut curr_obj = self.head;

        while let Some(curr_ref) = curr_obj {
            let next = curr_ref.get_next();
            if curr_ref.is_marked() {
                curr_ref.unmark();
                prev_obj = curr_obj;
                curr_obj = next;
            } else {
                curr_obj = next;
                if let Some(prev_ref) = prev_obj {
                    prev_ref.set_next(next);
                } else {
                    self.head = curr_obj;
                }
                self.dealloc(curr_ref);
            }
        }

        #[cfg(feature = "dbg-heap")]
        self.trace_dangling_strings();

        // The minimum number strong count should be 2 (1 for the vec and 1 for the hash map).
        // Thus, any string that has `Rc::strong_count == 2` is no longer referenced and we can
        // remove it.
        self.intern_str.retain(|s| Rc::strong_count(s) > 2);
        self.intern_ids.retain(|k, _| Rc::strong_count(k) > 2);
        // Update the interned index.
        for (i, s) in self.intern_str.iter().enumerate() {
            self.intern_ids.insert(Rc::clone(s), i);
        }

        self.gc_next_threshold = self.alloc_bytes * self.gc_growth_factor;
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

    /// Deallocate an object from the managed heap.
    ///
    /// ## Safety
    ///
    /// + We must ensure that no other piece of our code will ever use this reference, otherwise we'll
    /// invalidate a reference that is in used.
    /// + Before calling this method, we must ensure that the object is removed from the linked list of
    /// heap-allocated objects.
    #[allow(unsafe_code)]
    unsafe fn dealloc(&mut self, object: Object) {
        match object {
            Object::String(s) => {
                self.release(s);
            }
            Object::Upvalue(v) => {
                self.release(v);
            }
            Object::Closure(c) => {
                self.release(c);
            }
            Object::Fun(f) => {
                self.release(f);
            }
            Object::NativeFun(f) => {
                self.release(f);
            }
            Object::Class(c) => {
                self.release(c);
            }
            Object::Instance(i) => {
                self.release(i);
            }
            Object::BoundMethod(m) => {
                self.release(m);
            }
        };
    }

    /// Deallocate an object's data from the managed heap.
    ///
    /// ## Safety
    ///
    /// + We must ensure that no other piece of our code will ever use this reference, otherwise we'll
    /// invalidate a reference that is in used.
    /// + Before calling this method, we must ensure that the object is removed from the linked list of
    /// heap-allocated objects.
    #[allow(unsafe_code)]
    unsafe fn release<T>(&mut self, data: Gc<T>) -> Box<GcData<T>> {
        let boxed = Box::from_raw(data.as_ptr());
        let size = mem::size_of_val(&boxed);
        self.alloc_bytes -= size;

        #[cfg(feature = "dbg-heap")]
        println!("{boxed:p} free {size} bytes");

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
            unsafe { self.dealloc(object) };
        }
    }
}

impl IntoIterator for &Heap {
    type Item = Object;

    type IntoIter = HeapIter;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { next: self.head }
    }
}

/// An iterator through all currently allocated objects.
pub(crate) struct HeapIter {
    next: Option<Object>,
}

impl Iterator for HeapIter {
    type Item = Object;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            self.next = node.get_next();
            return Some(node);
        }
        None
    }
}

pub(crate) struct GcData<T> {
    next: Cell<Option<Object>>,
    marked: Cell<bool>,
    data: T,
}

impl<T> GcData<T> {
    pub(crate) fn new(next: Option<Object>, data: T) -> Self {
        Self {
            next: Cell::new(next),
            marked: Cell::new(false),
            data,
        }
    }

    pub(crate) fn get_next(&self) -> Option<Object> {
        self.next.get()
    }

    pub(crate) fn set_next(&self, next: Option<Object>) {
        self.next.set(next);
    }

    pub(crate) fn is_marked(&self) -> bool {
        self.marked.get()
    }

    pub(crate) fn mark(&self) -> bool {
        if self.marked.get() {
            return false;
        }
        self.marked.set(true);
        true
    }

    pub(crate) fn unmark(&self) {
        self.marked.set(false)
    }
}

impl<T> Deref for GcData<T> {
    type Target = T;

    #[allow(unsafe_code)]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

#[derive(Debug)]
pub(crate) struct Gc<T> {
    ptr: NonNull<GcData<T>>,
    ptr_: PhantomData<GcData<T>>,
}

impl<T> Gc<T> {
    pub(crate) fn new(boxed: Box<GcData<T>>) -> Self {
        Self {
            ptr: NonNull::from(Box::leak(boxed)),
            ptr_: PhantomData,
        }
    }

    pub(crate) fn as_ptr(&self) -> *mut GcData<T> {
        self.ptr.as_ptr()
    }
}

impl<T> Deref for Gc<T> {
    type Target = GcData<T>;

    #[allow(unsafe_code)]
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> Copy for Gc<T> {}
impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            ptr_: self.ptr_,
        }
    }
}
