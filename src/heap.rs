use crate::{
    object::{Gc, GcData, ObjString, Object, RefString},
    table::Table,
    value::Value,
};

#[cfg(feature = "dbg-heap")]
use std::mem;

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
    strings: Table<Value>,
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
    pub(crate) fn alloc<T, F>(&mut self, data: T, map: F) -> (Object, Gc<T>)
    where
        F: Fn(Gc<T>) -> Object,
    {
        let boxed = Box::new(GcData::new(self.head, data));
        let content = Gc::new(boxed);
        let size = content.mem_size();
        let object = map(content);

        #[cfg(feature = "dbg-heap")]
        println!("0x{:x} alloc {object} ({size} bytes)", object.addr());

        self.alloc_bytes += size;
        self.head = Some(object);
        (object, content)
    }

    /// Interned a string and returned a reference counted pointer to it. If the given string has
    /// been interned, an existing `Rc<str>` is cloned and returned. Otherwise, we turn the given
    /// string into a new `Rc<str>` and add it to our collection of unique strings.
    pub(crate) fn intern(&mut self, data: String) -> RefString {
        let hash = ObjString::hash(&data);
        match self.strings.find(&data, hash) {
            // Clone the reference counted pointer, increasing its strong count.
            Some(s) => s,
            None => {
                let obj_string = ObjString { data, hash };
                let (_, s) = self.alloc(obj_string, Object::String);
                self.strings.set(s, Value::Nil);
                #[cfg(feature = "dbg-heap")]
                println!(
                    "{:p} alloc '{}' ({} bytes)",
                    s.as_ptr(),
                    s.data,
                    mem::size_of_val(&*s)
                );
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
    pub(crate) unsafe fn sweep(&mut self) {
        let mut prev_obj: Option<Object> = None;
        let mut curr_obj = self.head;

        for (k, _) in self.strings.iter() {
            if !k.is_marked() {
                self.strings.del(k);
            }
        }

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
    unsafe fn dealloc(&mut self, object: Object) {
        let size = object.mem_size();

        #[cfg(feature = "dbg-heap")]
        println!("0x{:x} free {object} ({size} bytes)", object.addr());

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
        self.alloc_bytes -= size;
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // Safety: If the heap is drop then both the compiler and vm will no longer be in use so
        // deallocating all objects is safe.
        for object in self.into_iter() {
            unsafe { self.dealloc(object) };
        }

        debug_assert_eq!(0, self.alloc_bytes);
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
