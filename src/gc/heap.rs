use core::{cell::Cell, cell::RefCell, pin::Pin, ptr::NonNull};

use super::{
    object::{Gc, Object},
    Trace,
};

#[derive(Default)]
pub struct Heap<'heap> {
    head: Cell<Option<Object>>,
    roots: RefCell<Vec<NonNull<dyn Trace + 'heap>>>,
}

impl<'heap> Heap<'heap> {
    pub fn alloc<T, F: Fn(Gc<T>) -> Object>(&self, data: T, map: F) -> (Gc<T>, Object) {
        let gc = Gc::new(data);
        let object = map(gc);

        unsafe { object.set_next(self.head.get()) };
        self.head.set(Some(object));
        (gc, object)
    }

    pub fn collect(&self) {
        println!("Collect");
        let roots = self.roots.borrow();
        for root in roots.iter() {
            let alloc = unsafe { root.as_ref() };
            alloc.trace();
        }

        let mut prev: Option<Object> = None;
        let mut curr = self.head.get();
        while let Some(curr_obj) = curr {
            println!("Checking {curr_obj:?}");
            let next = unsafe { curr_obj.get_next() };
            if unsafe { curr_obj.unmark() } {
                prev = curr;
                curr = next;
            } else {
                curr = next;
                unsafe { curr_obj.free() }
                if let Some(prev) = prev {
                    unsafe { prev.set_next(next) };
                } else {
                    self.head.set(curr);
                }
            }
        }
    }

    pub(super) fn enroot<'root>(&self, trace: Pin<&'root dyn Trace>) {
        let trace: Pin<&'heap dyn Trace> = unsafe { core::mem::transmute(trace) };
        let ptr = core::ptr::from_ref(trace.get_ref()).cast_mut();
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        self.roots.borrow_mut().push(ptr);
    }

    pub(super) fn uproot(&self) {
        self.roots.borrow_mut().pop();
    }
}
