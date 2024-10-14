//! A safe garbage collector.

pub mod object;

mod alloc;
mod heap;
mod link;
mod root;

pub use heap::Heap;
pub use root::{Root, StackRoot};

use std::{marker::PhantomData, pin::Pin, ptr::NonNull};

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

/// [`Gc`] holds a pointer to a rooted value that is pinned on the stack or allocated on the
/// managed heap. The held pointer and every managed pointers reachable from it are proven to be
/// valid pass garbage collections. As a result, they can be safely dereferenced. The pointers'
/// validity is ensured by the `'root` lifetime which proves that the pointee is (transitively)
/// reachable from some value on the stack.
#[allow(clippy::module_name_repetitions)]
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
        let data = unsafe { self.ptr.as_ref() };
        data.trace();
    }
}

/// [`GcBox`] holds a pointer to a value allocated on the stack. There is no guarantee that the
/// pointee remains valid pass garbage collections. This is used, instead of [`Gc`], for managed
/// value nested nested inside another managed value to prevent pointers from being incorrectly
/// proven valid. In order to safely dereference the pointer, we must create a [`Gc`] from
/// [`GcBox`] by going through a [`Gc`] of the value in which the [`GcBox`] is nested.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct GcBox<'root, 'heap, T: ?Sized> {
    _ref: PhantomData<&'root T>,
    raw: GcRaw<'heap, T>,
}

impl<'root, 'heap, T: ?Sized> From<Pin<&Alloc<'heap, T>>> for GcBox<'root, 'heap, T> {
    fn from(pin: Pin<&Alloc<'heap, T>>) -> Self {
        Self {
            _ref: PhantomData,
            raw: GcRaw::from(pin),
        }
    }
}

unsafe impl<'root, 'heap, T: ?Sized + Trace> Trace for GcBox<'root, 'heap, T> {
    fn trace(&self) {
        self.raw.trace();
    }
}

impl<'root, 'heap, T: Trace + 'heap> GcBox<'root, 'heap, T> {
    /// Allocates a new value managed by the garbage collector that is not yet rooted.
    pub fn new(data: T, heap: Pin<&Heap<'heap>>) -> Self {
        let raw = heap.alloc(data);
        GcBox::from(raw)
    }
}

#[derive(Debug)]
struct GcRaw<'heap, T: ?Sized> {
    _own: PhantomData<Alloc<'heap, T>>,
    ptr: NonNull<Alloc<'heap, T>>,
}

impl<'heap, T: ?Sized> Copy for GcRaw<'heap, T> {}
impl<'heap, T: ?Sized> Clone for GcRaw<'heap, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'heap, T: ?Sized> From<Pin<&Alloc<'heap, T>>> for GcRaw<'heap, T> {
    fn from(pin: Pin<&Alloc<'heap, T>>) -> Self {
        Self {
            _own: PhantomData,
            ptr: NonNull::from(pin.get_ref()),
        }
    }
}

unsafe impl<'heap, T: ?Sized + Trace> Trace for GcRaw<'heap, T> {
    fn trace(&self) {
        let alloc = unsafe { self.ptr.as_ref() };
        alloc.trace();
    }
}

impl<'heap, T: Trace + 'heap> GcRaw<'heap, T> {
    fn unsize(self) -> GcRaw<'heap, dyn Trace + 'heap> {
        let ptr = self.ptr.as_ptr() as *mut Alloc<'heap, dyn Trace + 'heap>;
        GcRaw {
            _own: PhantomData,
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}

impl<'heap, T: ?Sized> GcRaw<'heap, T> {
    fn pin<'pin>(self) -> Pin<&'pin Alloc<'heap, T>> {
        unsafe { Pin::new_unchecked(self.ptr.as_ref()) }
    }

    fn pin_mut<'pin>(mut self) -> Pin<&'pin mut Alloc<'heap, T>> {
        unsafe { Pin::new_unchecked(self.ptr.as_mut()) }
    }
}

impl<'heap, T> GcRaw<'heap, T> {
    fn new(data: T) -> Self {
        let ptr = Box::into_raw(Box::new(Alloc::new(data)));
        Self {
            _own: PhantomData,
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}
