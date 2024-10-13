use std::{cell::RefCell, pin::Pin, ptr::NonNull};

use super::{alloc::Alloc, link::Link, GcRaw, Trace};

/// [`Heap`] holds pointers to all values that can be garbage collected.
#[derive(Default)]
pub struct Heap<'heap> {
    link: Link<Alloc<'heap, dyn Trace + 'heap>>,
    roots: RefCell<Vec<Option<NonNull<dyn Trace + 'heap>>>>,
}

impl<'heap> std::fmt::Debug for Heap<'heap> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Heap").finish()
    }
}

impl<'heap> Heap<'heap> {
    /// Deallocates every values that are no longer reachable.
    pub fn collect(self: Pin<&Self>) {
        println!("Collect");
        for root in self.roots.borrow().iter().flatten() {
            let root = unsafe { root.as_ref() };
            root.trace();
        }
        for alloc in self.link().iter_mut() {
            if alloc.marked() {
                alloc.unmark();
            } else {
                println!("Free {alloc:p}");
                let alloc = unsafe { alloc.get_unchecked_mut() };
                let alloc = unsafe { Box::from_raw(std::ptr::from_mut(alloc)) };
                drop(alloc);
            }
        }
    }

    pub(super) fn alloc<T: Trace + 'heap>(self: Pin<&Self>, data: T) -> GcRaw<'heap, T> {
        let raw = GcRaw::new(data);
        println!("Alloc {:p}", raw.ptr);
        self.link().insert(raw.unsize().pin_mut());
        raw
    }

    pub(super) fn add_root(self: Pin<&Self>) -> usize {
        let mut roots = self.roots.borrow_mut();
        let id = roots.len();
        roots.push(None);
        id
    }

    pub(super) fn pop_root(self: Pin<&Self>) {
        self.roots.borrow_mut().pop();
    }

    pub(super) fn set_root<T: Trace + 'heap>(self: Pin<&Self>, id: usize, pin: Pin<&T>) {
        let trace = pin.get_ref() as &(dyn Trace + 'heap);
        self.roots.borrow_mut()[id] = Some(NonNull::from(trace));
    }

    fn link(self: Pin<&Self>) -> Pin<&Link<Alloc<'heap, dyn Trace + 'heap>>> {
        unsafe { self.map_unchecked(|heap| &heap.link) }
    }
}
