use std::{cell::Cell, marker::PhantomPinned};

use super::{link::Link, Trace};

/// [`Alloc`] is a node in the link list of allocated managed data.
#[derive(Debug)]
pub struct Alloc<'heap, T: ?Sized> {
    _pin: PhantomPinned,
    link: Link<Alloc<'heap, dyn Trace + 'heap>>,
    mark: Cell<bool>,
    data: T,
}

impl<'heap> AsRef<Link<Self>> for Alloc<'heap, dyn Trace + 'heap> {
    fn as_ref(&self) -> &Link<Self> {
        &self.link
    }
}

impl<'heap, T: ?Sized> AsRef<T> for Alloc<'heap, T> {
    fn as_ref(&self) -> &T {
        &self.data
    }
}

unsafe impl<'heap, T: ?Sized + Trace> Trace for Alloc<'heap, T> {
    fn trace(&self) {
        if !self.mark.replace(true) {
            println!("Mark {self:p}");
            self.data.trace();
        }
    }
}

impl<'heap, T: ?Sized> Alloc<'heap, T> {
    pub(super) fn marked(&self) -> bool {
        self.mark.get()
    }

    pub(super) fn unmark(&self) {
        self.mark.set(false);
    }
}

impl<'heap, T> Alloc<'heap, T> {
    pub(super) fn new(data: T) -> Self {
        Self {
            _pin: PhantomPinned,
            link: Link::default(),
            mark: Cell::new(false),
            data,
        }
    }
}
