use core::{cell::Cell, marker::PhantomPinned};
use std::pin::Pin;

use super::{chain::Chain, Heap, Traceable};

pub struct Alloc<'heap, T: Traceable<'heap>> {
    _pin: PhantomPinned,
    list: Chain<Alloc<'heap, T>>,
    mark: Cell<bool>,
    data: T,
}

impl<'heap, T: Traceable<'heap>> AsRef<Chain<Self>> for Alloc<'heap, T> {
    fn as_ref(&self) -> &Chain<Self> {
        &self.list
    }
}

impl<'heap, T: Traceable<'heap>> Traceable<'heap> for Alloc<'heap, T> {
    fn mark(&self) {
        self.mark();
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        self.data.manage(heap);
    }
}

impl<'heap, T: Traceable<'heap>> Alloc<'heap, T> {
    pub fn new(data: T) -> Self {
        Self {
            _pin: PhantomPinned,
            list: Chain::default(),
            mark: Cell::new(false),
            data,
        }
    }

    pub unsafe fn free(ptr: *mut Self) {
        println!("Freeing {ptr:?}");
        drop(Box::from_raw(ptr));
    }

    pub fn mark(&self) {
        if !self.mark.replace(true) {
            self.data.mark();
        }
    }

    pub fn is_marked(&self) -> bool {
        self.mark.replace(false)
    }

    pub fn is_unmanaged(&self) -> bool {
        self.list.is_head()
    }
}
