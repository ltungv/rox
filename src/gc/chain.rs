use core::{
    cell::Cell,
    marker::{PhantomData, PhantomPinned},
    ops::Deref,
    pin::Pin,
    ptr::NonNull,
};

pub struct Chain<T: AsRef<Chain<T>> + ?Sized> {
    _pin: PhantomPinned,
    prev: Cell<Option<NonNull<Chain<T>>>>,
    next: Cell<Option<NonNull<T>>>,
}

impl<T: AsRef<Self> + ?Sized> Default for Chain<T> {
    fn default() -> Self {
        Self {
            _pin: PhantomPinned,
            prev: Cell::new(None),
            next: Cell::new(None),
        }
    }
}

impl<T: AsRef<Self> + ?Sized> Drop for Chain<T> {
    fn drop(&mut self) {
        if let Some(prev) = self.prev.get() {
            let prev = unsafe { prev.as_ref() };
            prev.next.set(self.next.get());
        }
        if let Some(next) = self.next.get() {
            let next = unsafe { next.as_ref().as_ref() };
            next.prev.set(self.prev.get());
        }
    }
}

impl<T: AsRef<Self> + ?Sized> Chain<T> {
    pub fn link(self: Pin<&Self>, next: Pin<&mut T>) {
        let list = next.deref().as_ref();
        list.prev.set(Some(NonNull::from(self.get_ref())));
        list.next.set(self.next.get());

        if let Some(next) = self.next.get() {
            let next = unsafe { next.as_ref().as_ref() };
            next.prev.set(Some(NonNull::from(list)));
        }

        self.next
            .set(Some(NonNull::from(unsafe { next.get_unchecked_mut() })));
    }

    pub fn is_head(&self) -> bool {
        self.prev.get().is_none()
    }
}

impl<'iter, T: AsRef<Chain<T>> + ?Sized> IntoIterator for Pin<&'iter Chain<T>> {
    type Item = Pin<&'iter mut T>;

    type IntoIter = IterMut<'iter, T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            _ref: PhantomData,
            next: self.next.get(),
        }
    }
}

pub struct IterMut<'iter, T: AsRef<Chain<T>> + ?Sized> {
    _ref: PhantomData<&'iter mut T>,
    next: Option<NonNull<T>>,
}

impl<'iter, T: AsRef<Chain<T>> + ?Sized> Iterator for IterMut<'iter, T> {
    type Item = Pin<&'iter mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next = self.next?;
        let next = unsafe { next.as_mut() };
        self.next = next.as_ref().next.get();
        Some(unsafe { Pin::new_unchecked(next) })
    }
}
