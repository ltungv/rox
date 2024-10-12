use core::pin::Pin;

use super::{heap::Heap, object::Gc, Trace};

/// Constructs a stack-pinned root.
macro_rules! root {
    ($heap:ident, $($root:ident),+) => {$(
        let $root = $root;
        let $root = unsafe { $crate::gc::root::Root::new_unchecked(&$root, &$heap) };
    )*}
}

/// Root holds a reference to a value pinned to the stack. Managed pointers that are transitively
/// reachable from the roots are not collected.
pub struct Root<'root, 'heap, T> {
    pin: Pin<&'root T>,
    heap: &'root Heap<'heap>,
}

impl<'root, 'heap, T> Drop for Root<'root, 'heap, T> {
    fn drop(&mut self) {
        self.heap.uproot();
    }
}

impl<'root, 'heap, T> core::ops::Deref for Root<'root, 'heap, Gc<T>> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        let ptr = self.pin.get_ptr();
        // SAFETY:
        // + We always allocated an object with `Box`, thus it is always aligned and initialized.
        // + We know that an object won't be garbage collected during `'root`.
        // + We never hand out unique references to objects.
        let raw = unsafe { ptr.as_ref() };
        raw.as_ref()
    }
}

impl<'root, 'heap, T: Trace> Root<'root, 'heap, T> {
    /// Enroots a value and ensures all reachable managed pointers live pass a garbage collection.
    /// To safely ensure that the referenced value is pinned, use the [`root!`] macro.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `data` won't ever be moved once it's given to this method.
    pub unsafe fn new_unchecked(data: &'root T, heap: &'root Heap<'heap>) -> Self {
        // SAFETY: We require the caller to ensure that `data` won't ever be moved.
        let pin = unsafe { Pin::new_unchecked(data) };
        heap.enroot(pin);
        Self { pin, heap }
    }
}
