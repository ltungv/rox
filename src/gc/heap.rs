use core::{cell::Cell, cell::RefCell, cell::RefMut, marker::PhantomData, ptr::NonNull};

use super::{alloc::Alloc, Object, Trace};

#[derive(Debug)]
pub struct Gc<T> {
    _own: PhantomData<T>,
    pub(super) ptr: NonNull<Alloc<T>>,
}

impl<T: Trace> Trace for Gc<T> {
    fn trace(&self) {
        let alloc = unsafe { self.ptr.as_ref() };
        alloc.trace();
    }
}

#[derive(Default)]
pub struct Heap {
    head: Cell<Option<NonNull<Alloc<Object>>>>,
    roots: RefCell<Vec<NonNull<dyn Trace>>>,
}

impl Heap {
    pub fn alloc(&self, object: Object) -> Gc<Object> {
        let alloc = Box::new(Alloc::new(object));
        alloc.set_next(self.head.get());

        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(alloc)) };
        self.head.set(Some(ptr));

        println!("Alloc {ptr:?}");

        Gc {
            _own: PhantomData,
            ptr,
        }
    }

    pub fn collect(&self) {
        println!("Collect");
        let roots = self.roots.borrow();
        for root in roots.iter() {
            let alloc = unsafe { root.as_ref() };
            alloc.trace();
        }

        let mut prev: Option<NonNull<Alloc<Object>>> = None;
        let mut curr = self.head.get();
        while let Some(mut curr_ptr) = curr {
            println!("Checking {curr_ptr:?}");
            let curr_ref = unsafe { curr_ptr.as_mut() };
            let next = curr_ref.get_next();
            if curr_ref.is_marked() {
                prev = curr;
                curr = next;
            } else {
                curr = next;
                unsafe { Alloc::free(core::ptr::from_mut(curr_ref)) }
                if let Some(prev_ptr) = prev {
                    let prev_ref = unsafe { prev_ptr.as_ref() };
                    prev_ref.set_next(next);
                } else {
                    self.head.set(curr);
                }
            }
        }
    }

    pub fn roots_mut(&self) -> RefMut<'_, Vec<NonNull<dyn Trace>>> {
        self.roots.borrow_mut()
    }
}
