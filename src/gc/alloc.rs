use core::{cell::Cell, marker::PhantomPinned, ptr::NonNull};

use super::Trace;

pub struct Alloc<T> {
    _pin: PhantomPinned,
    next: Cell<Option<NonNull<Self>>>,
    mark: Cell<bool>,
    data: T,
}

impl<T> AsRef<T> for Alloc<T> {
    fn as_ref(&self) -> &T {
        &self.data
    }
}

impl<T: Trace> Trace for Alloc<T> {
    fn trace(&self) {
        if !self.mark.replace(true) {
            println!("Mark {:?}", core::ptr::from_ref(self));
            self.data.trace();
        }
    }
}

impl<T> Alloc<T> {
    pub const fn new(data: T) -> Self {
        Self {
            _pin: PhantomPinned,
            next: Cell::new(None),
            mark: Cell::new(false),
            data,
        }
    }

    pub unsafe fn free(ptr: *mut Self) {
        println!("Freeing {ptr:?}");
        drop(Box::from_raw(ptr));
    }

    pub fn is_marked(&self) -> bool {
        self.mark.replace(false)
    }

    pub fn get_next(&self) -> Option<NonNull<Self>> {
        self.next.get()
    }

    pub fn set_next(&self, next: Option<NonNull<Self>>) {
        self.next.set(next);
    }
}
