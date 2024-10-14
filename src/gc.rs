//! A safe garbage collector.

pub mod object;

mod alloc;
mod heap;
mod link;
mod root;

pub use heap::Heap;
pub use root::{Root, StackRoot};

use std::{cell::Cell, marker::PhantomData, pin::Pin, ptr::NonNull};

use alloc::Alloc;

/// [`enroot`] creates a stack-pinned root.
#[macro_export]
macro_rules! enroot {
    ($heap:ident, $($root:ident),*) => {$(
        let mut $root = $crate::gc::Root::new($heap.as_ref());
        let $root = unsafe { $crate::gc::StackRoot::new_unchecked(&mut $root) };
    )*};
}

/// [`Trace`] is implemented by types referencing values allocated on the managed heap. Types that
/// implement this trait are not necessarily allocated on the managed heap. The value itself or
/// values contained within it remain valid after garbage collections once they are traced.
///
/// # Safety
///
/// The implementor must make sure that every reachable managed values are properly traced.
/// Otherwise, incorrect implementation can result in dangling pointers.
pub unsafe trait Trace {
    /// Collects the set of reachable values starting from `&self` either by marking them or by
    /// other strategies.
    fn trace(&self);
}

unsafe impl<T: Copy + Trace> Trace for Cell<T> {
    fn trace(&self) {
        self.get().trace();
    }
}

/// [`Gc`] holds a pointer to a rooted value that is pinned on the stack or allocated on the
/// managed heap. The held pointer and every managed pointers reachable from it are proven to be
/// valid pass garbage collections. As a result, they can be safely dereferenced. The pointers'
/// validity is ensured by the `'root` lifetime which proves that the pointee is (transitively)
/// reachable from some value on the stack.
#[derive(Debug)]
pub struct Gc<'root, T: ?Sized> {
    _ref: PhantomData<&'root T>,
    ptr: NonNull<T>,
}

impl<'root, T: ?Sized> From<Pin<&T>> for Gc<'root, T> {
    fn from(pin: Pin<&T>) -> Self {
        Self {
            _ref: PhantomData,
            ptr: NonNull::from(pin.get_ref()),
        }
    }
}
impl<'root, T: ?Sized> std::ops::Deref for Gc<'root, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

unsafe impl<'root, T: ?Sized + Trace> Trace for Gc<'root, T> {
    fn trace(&self) {
        self.pin().trace();
    }
}

impl<'heap, T: ?Sized> Gc<'heap, T> {
    /// Returns a shared pinned reference to the managed value.
    #[must_use]
    pub fn pin(&self) -> Pin<&T> {
        unsafe { Pin::new_unchecked(self.ptr.as_ref()) }
    }

    /// Returns a mutable pinned reference to the managed value.
    #[must_use]
    pub fn pin_mut(&mut self) -> Pin<&mut T> {
        unsafe { Pin::new_unchecked(self.ptr.as_mut()) }
    }
}

/// [`GcBox`] holds a pointer to a value allocated on the stack. There is no guarantee that the
/// pointee remains valid pass garbage collections. This is used, instead of [`Gc`], for managed
/// value nested nested inside another managed value to prevent pointers from being incorrectly
/// proven valid. In order to safely dereference the pointer, we must create a [`Gc`] from
/// [`GcBox`] by going through a [`Gc`] of the value in which the [`GcBox`] is nested.
#[derive(Debug)]
pub struct Ptr<'heap, T: ?Sized> {
    _own: PhantomData<Alloc<'heap, T>>,
    inner: NonNull<Alloc<'heap, T>>,
}

impl<'heap, T: ?Sized> Copy for Ptr<'heap, T> {}
impl<'heap, T: ?Sized> Clone for Ptr<'heap, T> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<'heap, T: ?Sized + Trace> Trace for Ptr<'heap, T> {
    fn trace(&self) {
        self.pin().trace();
    }
}

impl<'heap, T: Trace + 'heap> Ptr<'heap, T> {
    fn unsize(self) -> Ptr<'heap, dyn Trace + 'heap> {
        let ptr = self.inner.as_ptr() as *mut Alloc<'heap, dyn Trace + 'heap>;
        Ptr {
            _own: PhantomData,
            inner: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}

impl<'heap, T: ?Sized> Ptr<'heap, T> {
    /// Returns a shared pinned reference to the managed value.
    #[must_use]
    fn pin<'pin>(self) -> Pin<&'pin Alloc<'heap, T>> {
        unsafe { Pin::new_unchecked(self.inner.as_ref()) }
    }

    /// Returns a mutable pinned reference to the managed value.
    #[must_use]
    fn pin_mut<'pin>(mut self) -> Pin<&'pin mut Alloc<'heap, T>> {
        unsafe { Pin::new_unchecked(self.inner.as_mut()) }
    }
}

impl<'heap, T> Ptr<'heap, T> {
    fn new(data: T) -> Self {
        let ptr = Box::into_raw(Box::new(Alloc::new(data)));
        Self {
            _own: PhantomData,
            inner: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}
