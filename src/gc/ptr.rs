use core::{marker::PhantomData, pin::Pin, ptr::NonNull};

use super::{alloc::Alloc, Heap, Traceable};

pub struct Gc<'root, T> {
    _ref: PhantomData<&'root Alloc<T>>,
    ptr: GcPointer<T>,
}

impl<'root, T> Gc<'root, T> {
    pub const fn new(ptr: GcPointer<T>) -> Self {
        Self {
            _ref: PhantomData,
            ptr,
        }
    }

    pub const fn raw(&self) -> GcPointer<T> {
        self.ptr
    }
}

pub struct GcEmbed<T> {
    _ref: PhantomData<Alloc<T>>,
    ptr: GcPointer<T>,
}

impl<T> Drop for GcEmbed<T> {
    fn drop(&mut self) {
        let alloc = unsafe { self.ptr.pin_mut() };
        if alloc.is_unmanaged() {
            unsafe { Alloc::free(core::ptr::from_mut(alloc.get_unchecked_mut())) };
        }
    }
}

impl<T> GcEmbed<T> {
    pub fn new(data: T) -> Self {
        println!("Alloc GcEmbed");
        Self {
            _ref: PhantomData,
            ptr: GcPointer::new(data),
        }
    }

    pub const fn raw(&self) -> GcPointer<T> {
        self.ptr
    }
}

pub struct GcPointer<T> {
    inner: NonNull<Alloc<T>>,
}

impl<T> Copy for GcPointer<T> {}

impl<T> Clone for GcPointer<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'heap, T: Traceable<'heap>> Traceable<'heap> for GcPointer<T> {
    fn mark(&self) {
        let alloc = unsafe { self.pin() };
        alloc.mark();
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        let alloc = unsafe { self.pin() };
        alloc.manage(heap);
    }
}

impl<T> GcPointer<T> {
    pub fn new(data: T) -> Self {
        let alloc = Box::new(Alloc::new(data));
        Self {
            inner: unsafe { NonNull::new_unchecked(Box::into_raw(alloc)) },
        }
    }

    pub unsafe fn pin(&self) -> Pin<&Alloc<T>> {
        Pin::new_unchecked(self.inner.as_ref())
    }

    pub unsafe fn pin_mut<'a>(&mut self) -> Pin<&'a mut Alloc<T>> {
        Pin::new_unchecked(self.inner.as_mut())
    }
}
