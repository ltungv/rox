use std::{cell::Cell, marker::PhantomData, pin::Pin, ptr::NonNull};

pub(super) struct Link<T: ?Sized + AsRef<Self>> {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<T>>>,
}

impl<T: ?Sized + AsRef<Self>> std::fmt::Debug for Link<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Link")
            .field("prev", &self.prev.get().map(NonNull::as_ptr))
            .field("next", &self.next.get().map(NonNull::as_ptr))
            .finish()
    }
}

impl<T: ?Sized + AsRef<Self>> Default for Link<T> {
    fn default() -> Self {
        Self {
            prev: Cell::new(None),
            next: Cell::new(None),
        }
    }
}

impl<T: ?Sized + AsRef<Self>> Drop for Link<T> {
    fn drop(&mut self) {
        if let Some(prev) = self.prev.get() {
            let prev = unsafe { prev.as_ref() };
            prev.next.set(self.next.get());
        }
        if let Some(next) = self.next.get() {
            let next = unsafe { next.as_ref() };
            next.as_ref().prev.set(self.prev.get());
        }
    }
}

impl<T: ?Sized + AsRef<Self>> Link<T> {
    pub(super) fn insert(self: Pin<&Self>, next: Pin<&mut T>) {
        let next = unsafe { next.get_unchecked_mut() };
        let link = next.as_ref();
        link.prev.set(Some(NonNull::from(self.get_ref())));
        link.next.set(self.next.get());

        if let Some(next) = self.next.get() {
            let next = unsafe { next.as_ref() };
            next.as_ref().prev.set(Some(NonNull::from(link)));
        }
        self.next.set(Some(NonNull::from(next)));
    }

    pub(super) fn iter_mut(&self) -> IterMut<'_, T> {
        IterMut {
            _ref: PhantomData,
            next: self.next.get(),
        }
    }
}

pub(super) struct IterMut<'iter, T: ?Sized + AsRef<Link<T>>> {
    _ref: PhantomData<&'iter mut T>,
    next: Option<NonNull<T>>,
}

impl<'iter, T: ?Sized + AsRef<Link<T>>> Iterator for IterMut<'iter, T> {
    type Item = Pin<&'iter mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = unsafe { self.next?.as_mut() };
        self.next = next.as_ref().next.get();
        let pin = unsafe { Pin::new_unchecked(next) };
        Some(pin)
    }
}
