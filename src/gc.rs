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

/// [`Trace`] is implemented by types containing pointers to values managed by the garbage
/// collector. Pointers remain valid after a garbage collection if they are reachable through
/// tracing.
///
/// # Safety
///
/// The implementor must make sure that every garbage collected pointers are properly traced.
/// Otherwise, incorrect trace can result in dangling pointers when the values are used after
/// garbage collections.
pub unsafe trait Trace {
    /// Collects the set of reachable garbage collected pointers starting from `&self` either by
    /// marking the pointers or other strategies.
    fn trace(&self);
}

/// [`GcBox`] holds a pointer to a value managed by the garbage collector that is proven to not be
/// collected after garbage collections. As a result, the pointer behind [`GcBox`] can be safely
/// dereferenced. The pointer's validity is ensured by `'root` lifetime which proves that the value
/// is (transitively) rooted on the stack.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct GcBox<'root, 'heap, T: ?Sized> {
    _ref: PhantomData<&'root Alloc<'heap, T>>,
    raw: GcRaw<'heap, T>,
}

impl<'root, 'heap, T: ?Sized> From<GcRaw<'heap, T>> for GcBox<'root, 'heap, T> {
    fn from(raw: GcRaw<'heap, T>) -> Self {
        Self {
            _ref: PhantomData,
            raw,
        }
    }
}

unsafe impl<'root, 'heap, T: ?Sized + Trace> Trace for GcBox<'root, 'heap, T> {
    fn trace(&self) {
        self.raw.trace();
    }
}

/// [`GcRef`] holds a pointer to a value managed by the garbage collector that can be proven to not
/// be collected after garbage collection. This is used for managed value nested inside another
/// managed value. [`GcRef`] is proven to not be collected by creating a [`GcBox`] to the nested
/// value through a [`GcBox`] of its container.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct GcRef<'root, 'heap, T: ?Sized> {
    _ref: PhantomData<&'root Alloc<'heap, T>>,
    raw: GcRaw<'heap, T>,
}

impl<'root, 'heap, T: ?Sized> From<GcRaw<'heap, T>> for GcRef<'root, 'heap, T> {
    fn from(raw: GcRaw<'heap, T>) -> Self {
        Self {
            _ref: PhantomData,
            raw,
        }
    }
}

unsafe impl<'root, 'heap, T: ?Sized + Trace> Trace for GcRef<'root, 'heap, T> {
    fn trace(&self) {
        self.raw.trace();
    }
}

impl<'root, 'heap, T: Trace + 'heap> GcRef<'root, 'heap, T> {
    /// Allocates a new value managed by the garbage collector that is not yet rooted.
    pub fn new(data: T, heap: Pin<&Heap<'heap>>) -> Self {
        let raw = heap.alloc(data);
        GcRef::from(raw)
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

impl<'heap, T: ?Sized> From<NonNull<Alloc<'heap, T>>> for GcRaw<'heap, T> {
    fn from(ptr: NonNull<Alloc<'heap, T>>) -> Self {
        Self {
            _own: PhantomData,
            ptr,
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
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        Self::from(ptr)
    }
}
