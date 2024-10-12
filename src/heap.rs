use crate::{
    object::{Gc, GcData, GcSized, ObjString, Object, RefString},
    table::Table,
};

/// The default GC threshold when initialize.
const GC_NEXT_THRESHOLD: usize = 1024 * 1024;

/// The default GC threshold growth factor. Each time a GC is performed, we set
/// the next GC threshold to `GC_GROWTH_FACTOR * <current_allocated_bytes>`.
const GC_GROWTH_FACTOR: usize = 2;

/// A managed heap.
///
/// Objects are linked together using an intrusive linked-list, so the heap can
/// traverse all allocated objects.
///
/// In our current design, the heap does not own the objects that it allocated.
/// Instead, the references that we hand out provide shared read/write access to
/// the object. Because we control how the VM is run, we know exactly when an
/// object can be deallocated. Thus, in the context of the VM,  `Gc<T>` is
/// similar to a smart pointer that deallocates itself when it's no longer used.
#[derive(Debug)]
pub struct Heap {
    // The total number of bytes used by allocated objects.
    alloc_bytes: usize,
    // The byte threshold where a GC should be done.
    gc_next_threshold: usize,
    // The factor by which the byte threshold should grow.
    gc_growth_factor: usize,
    // The table of interned strings.
    strings: Table<()>,
    // The head of the linked list of heap-allocated objects.
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
    /// Allocates an object and returns its handle. The object is pushed to the
    /// front of the list of allocated objects.
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

    /// Interns a string and returns its handle. The same reference is returned
    /// for two equal strings.
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

    /// Releases all objects that aren't marked. This method also removes
    /// interned strings when no object is referencing them.
    ///
    /// ## Safety
    ///
    /// The caller must ensure that all reachable pointers have been marked.
    /// Otherwise, we'll deallocate objects that are in use and leave dangling
    /// pointers.
    pub unsafe fn sweep(&mut self) {
        let mut prev_obj: Option<Object> = None;
        let mut curr_obj = self.head;

        let mut dangling_strings = Vec::with_capacity(self.strings.len());
        for (&k, ()) in &self.strings {
            if !k.marked() {
                dangling_strings.push(k);
            }
        }
        for s in dangling_strings {
            self.strings.del(s);
        }

        while let Some(curr_ref) = curr_obj {
            let next = curr_ref.get_next();
            if curr_ref.unmark() {
                prev_obj = curr_obj;
                curr_obj = next;
            } else {
                self.dealloc(curr_ref);
                curr_obj = next;
                if let Some(prev_ref) = prev_obj {
                    prev_ref.set_next(next);
                } else {
                    self.head = curr_obj;
                }
            }
        }

        self.gc_next_threshold = self.alloc_bytes * self.gc_growth_factor;
    }

    /// Returns the number of bytes that are being allocated.
    pub const fn size(&self) -> usize {
        self.alloc_bytes
    }

    /// Returns the next GC threshold in bytes. If `Self::size() > Self::next_gc()`,
    /// we should start tracing all reachable objects and call `Self::sweep`.
    pub const fn next_gc(&self) -> usize {
        #[cfg(not(feature = "dbg-stress-gc"))]
        {
            self.gc_next_threshold
        }
        #[cfg(feature = "dbg-stress-gc")]
        {
            _ = self;
            0
        }
    }

    /// Deallocates an object.
    ///
    /// ## Safety
    ///
    /// + The caller must ensure that no other piece of code will ever use this
    ///   reference. Otherwise, we'll risk dereferencing a dangling pointer.
    /// + Before calling this method, the caller must ensure that the object was
    ///   removed from the linked list of heap-allocated objects.
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
        // Safety: If the heap is drop, both the compiler and VM are no longer
        // in use so.
        for object in &*self {
            unsafe {
                self.dealloc(object);
            }
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
