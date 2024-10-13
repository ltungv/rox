use std::pin::Pin;

use super::{heap::Heap, GcBox, Trace};

/// [`StackRoot`] represents a value rooted on the stack from which the garbage collector can start
/// tracing. Pointers transitively reachable from rooted values are not collected and will live
/// pass a garbage collection.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct StackRoot<'pin, 'root, 'heap> {
    root: Pin<&'pin mut Root<'root, 'heap>>,
}

impl<'pin, 'root, 'heap> StackRoot<'pin, 'root, 'heap> {
    /// Creates stack-pinned root. This method should never be called directly instead of using the
    /// [`crate::gc::enroot`] macro.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the value beind `root` won't ever move once it's given to this
    /// method. Moving the pointee of `root` causes its lifetime to be not stack-like and leads to
    /// incorrect traces.
    pub unsafe fn new_unchecked(root: &'pin mut Root<'root, 'heap>) -> Self {
        Self {
            root: unsafe { Pin::new_unchecked(root) },
        }
    }

    /// Allocates a value managed by the garbage collector and enroots it.
    pub fn alloc<T: Trace + 'heap>(self, data: T) -> GcBox<'root, 'heap, T> {
        self.root.as_ref().alloc(data)
    }

    /// Enroots a stack value.
    pub fn enroot<T: Trace + 'heap>(self, data: Pin<&T>) {
        self.root.as_ref().enroot(data);
    }
}

/// [`Root`] manages the lifetime of rooted values.
pub struct Root<'root, 'heap> {
    id: usize,
    heap: Pin<&'root Heap<'heap>>,
}

impl<'root, 'heap> std::fmt::Debug for Root<'root, 'heap> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Root").field("id", &self.id).finish()
    }
}

impl<'root, 'heap> Drop for Root<'root, 'heap> {
    fn drop(&mut self) {
        self.heap.pop_root();
    }
}

impl<'root, 'heap> Root<'root, 'heap> {
    /// Creates a root from which a value managed by the garbage collector can be created.
    #[must_use]
    pub fn new(heap: Pin<&'root Heap<'heap>>) -> Self {
        let id = heap.add_root();
        Self { id, heap }
    }

    fn alloc<'pin, T: Trace + 'heap>(self: Pin<&'pin Self>, data: T) -> GcBox<'root, 'heap, T> {
        let raw = self.heap.alloc(data);
        self.heap.set_root(self.id, raw.pin());
        GcBox::from(raw)
    }

    fn enroot<'pin, T: Trace + 'heap>(self: Pin<&'pin Self>, pin: Pin<&T>) {
        self.heap.set_root(self.id, pin);
    }
}
