use core::{marker::PhantomData, pin::Pin, ptr::NonNull};

use super::{alloc::Alloc, Heap, Traceable};

pub struct Gc<'root, 'heap, T: Traceable<'heap>> {
    _ref: PhantomData<&'root Alloc<'heap, T>>,
    ptr: GcPointer<'heap, Alloc<'heap, T>>,
}

impl<'root, 'heap, T: Traceable<'heap>> Gc<'root, 'heap, T> {
    pub const fn enroot(ptr: GcPointer<'heap, Alloc<'heap, T>>) -> Self {
        Self {
            _ref: PhantomData,
            ptr,
        }
    }

    pub const fn reroot<'r>(gc: &Gc<'r, 'heap, T>) -> Self {
        Self {
            _ref: PhantomData,
            ptr: gc.ptr,
        }
    }

    pub const fn raw(&self) -> GcPointer<'heap, Alloc<'heap, T>> {
        self.ptr
    }
}

pub struct GcEmbed<'heap, T: Traceable<'heap>> {
    _ref: PhantomData<Alloc<'heap, T>>,
    ptr: GcPointer<'heap, Alloc<'heap, T>>,
}

impl<'heap, T: Traceable<'heap>> Drop for GcEmbed<'heap, T> {
    fn drop(&mut self) {
        let alloc = unsafe { self.ptr.pin_mut() };
        if alloc.is_unmanaged() {
            unsafe { Alloc::free(core::ptr::from_mut(alloc.get_unchecked_mut())) };
        }
    }
}

impl<'heap, T: Traceable<'heap>> GcEmbed<'heap, T> {
    pub fn new(data: T) -> Self {
        println!("Alloc GcEmbed");
        Self {
            _ref: PhantomData,
            ptr: GcPointer::new(Alloc::new(data)),
        }
    }

    pub const fn raw(&self) -> GcPointer<'heap, Alloc<'heap, T>> {
        self.ptr
    }
}

pub struct GcPointer<'heap, T: Traceable<'heap>> {
    _ref: PhantomData<&'heap T>,
    inner: NonNull<T>,
}

impl<'heap, T: Traceable<'heap>> Copy for GcPointer<'heap, T> {}

impl<'heap, T: Traceable<'heap>> Clone for GcPointer<'heap, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'heap, T: Traceable<'heap>> Traceable<'heap> for GcPointer<'heap, T> {
    fn mark(&self) {
        let alloc = unsafe { self.pin() };
        alloc.mark();
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        let alloc = unsafe { self.pin() };
        alloc.manage(heap);
    }
}

impl<'heap, T: Traceable<'heap>> GcPointer<'heap, T> {
    pub fn new(data: T) -> Self {
        let inner = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(data))) };
        Self {
            _ref: PhantomData,
            inner,
        }
    }

    pub unsafe fn pin(&self) -> Pin<&T> {
        Pin::new_unchecked(self.inner.as_ref())
    }

    pub unsafe fn pin_mut<'a>(&mut self) -> Pin<&'a mut T> {
        Pin::new_unchecked(self.inner.as_mut())
    }
}
