use core::{pin::Pin, ptr::NonNull};

use super::{
    alloc::Alloc,
    heap::{Gc, Heap},
    Trace,
};

pub struct Root<'root, T> {
    pin: Pin<&'root mut T>,
    heap: &'root Heap,
}

impl<'root, T> Drop for Root<'root, T> {
    fn drop(&mut self) {
        self.heap.roots_mut().pop();
    }
}

impl<'root, T> core::ops::Deref for Root<'root, Gc<T>> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        let alloc = unsafe { self.pin.ptr.as_ref() };
        alloc.as_ref()
    }
}

impl<'root, T: Trace> Root<'root, T> {
    pub unsafe fn new_unchecked(data: &'root mut T, heap: &'root Heap) -> Self {
        let mut roots = heap.roots_mut();
        let ptr = core::ptr::from_mut(data) as *mut dyn Trace;
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        roots.push(ptr);
        let pin = Pin::new_unchecked(data);
        Self { pin, heap }
    }
}
