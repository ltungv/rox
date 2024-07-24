use crate::{
    object::{Gc, GcData, GcSized, ObjString, Object, RefString},
    table::Table,
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
pub struct Heap {
    // States for the GC.
    alloc_bytes: usize,
    gc_next_threshold: usize,
    gc_growth_factor: usize,
    strings: Table<()>,
    // The head of the singly linked list of heap-allocated objects.
    head: Option<Object>,
}

impl Default for Heap {
    fn default() -> Self {
        Self {
            alloc_bytes: 0,
            gc_next_threshold: GC_NEXT_THRESHOLD,
            gc_growth_factor: GC_GROWTH_FACTOR,
            strings: Table::default(),
            head: None,
        }
    }
}

impl Heap {
    /// Allocates a new object and returns a handle to it. The object is pushed to the head of
    /// the list of allocated data.
    pub fn alloc<T: GcSized, F>(&mut self, data: T, map: F) -> (Object, Gc<T>)
    where
        F: Fn(Gc<T>) -> Object,
    {
        let boxed = Box::new(GcData::new(self.head, data));
        let content = Gc::new(boxed);
        let object = map(content);
        let size = object.size();
        self.head = Some(object);
        self.alloc_bytes += size;

        #[cfg(feature = "dbg-heap")]
        println!(
            "0x{:x} alloc {object} ({size} bytes) [{}]",
            object.addr(),
            self.alloc_bytes
        );

        (object, content)
    }

    /// Interned a string and returned a reference to it. The same reference is returned for 2
    /// equal strings.
    pub fn intern(&mut self, data: String) -> RefString {
        let hash = ObjString::hash(&data);
        if let Some(s) = self.strings.find(&data, hash) {
            return s;
        }
        let obj_string = ObjString { data, hash };
        let (_, s) = self.alloc(obj_string, Object::String);
        self.strings.set(s, ());
        s
    }

    /// Release all objects whose address is not included in the hash set. This method also remove
    /// the intern strings when objects no long reference them.
    ///
    /// ## Safety
    ///
    /// We must ensure that all reachable pointers have been marked. Otherwise, we'll deallocate
    /// objects that are in-used and leave dangling pointers.
    pub unsafe fn sweep(&mut self) {
        let mut prev_obj: Option<Object> = None;
        let mut curr_obj = self.head;

        let mut dangling_strings = Vec::with_capacity(self.strings.len());
        for (k, ()) in &self.strings {
            if !k.is_marked() {
                dangling_strings.push(*k);
            }
        }
        for s in dangling_strings {
            self.strings.del(s);
        }

        while let Some(curr_ref) = &mut curr_obj {
            let next = curr_ref.get_next();
            if curr_ref.is_marked() {
                curr_ref.unmark();
                prev_obj = curr_obj;
                curr_obj = next;
            } else {
                self.dealloc(*curr_ref);
                curr_obj = next;
                if let Some(prev_ref) = &mut prev_obj {
                    prev_ref.set_next(next);
                } else {
                    self.head = curr_obj;
                }
            }
        }

        self.gc_next_threshold = self.alloc_bytes * self.gc_growth_factor;
    }

    /// Returned the number of bytes that are being allocated.
    pub const fn size(&self) -> usize {
        self.alloc_bytes
    }

    /// Returned the next GC threshold in bytes. If `Self::size() > Self::next_gc()`, the user should start
    /// tracing all reachable objects and hand it to `Self::sweep`.
    pub const fn next_gc(&self) -> usize {
        #[cfg(not(feature = "dbg-stress-gc"))]
        {
            self.gc_next_threshold
        }

        #[cfg(feature = "dbg-stress-gc")]
        {
            let _ = self;
            0
        }
    }

    /// Deallocate an object from the managed heap.
    ///
    /// ## Safety
    ///
    /// + We must ensure that no other piece of our code will ever use this reference, otherwise we'll
    /// invalidate a reference that is in used.
    /// + Before calling this method, we must ensure that the object is removed from the linked list of
    /// heap-allocated objects.
    unsafe fn dealloc(&mut self, object: Object) {
        let size = object.size();
        self.alloc_bytes -= size;

        #[cfg(feature = "dbg-heap")]
        println!(
            "0x{:x} free {object} ({size} bytes) [{}]",
            object.addr(),
            self.alloc_bytes
        );

        match object {
            Object::String(s) => {
                s.release();
            }
            Object::Upvalue(v) => {
                v.release();
            }
            Object::Closure(c) => {
                c.release();
            }
            Object::Fun(f) => {
                f.release();
            }
            Object::NativeFun(f) => {
                f.release();
            }
            Object::Class(c) => {
                c.release();
            }
            Object::Instance(i) => {
                i.release();
            }
            Object::BoundMethod(m) => {
                m.release();
            }
        };
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // Safety: If the heap is drop then both the compiler and vm will no longer be in use so
        // deallocating all objects is safe.
        for object in &*self {
            unsafe { self.dealloc(object) };
        }

        debug_assert_eq!(0, self.alloc_bytes);
    }
}

impl IntoIterator for &Heap {
    type Item = Object;

    type IntoIter = Iter;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { next: self.head }
    }
}

/// An iterator through all currently allocated objects.
#[derive(Debug)]
pub struct Iter {
    next: Option<Object>,
}

impl Iterator for Iter {
    type Item = Object;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.next {
            self.next = node.get_next();
            return Some(node);
        }
        None
    }
}
