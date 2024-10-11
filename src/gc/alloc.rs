use core::{cell::Cell, marker::PhantomPinned, pin::Pin};

use super::{chain::Chain, Heap, Traceable};

pub struct Alloc<T: ?Sized> {
    _pin: PhantomPinned,
    list: Chain<Alloc<T>>,
    mark: Cell<bool>,
    data: T,
}

impl<T: ?Sized> AsRef<Chain<Self>> for Alloc<T> {
    fn as_ref(&self) -> &Chain<Self> {
        &self.list
    }
}

impl<'heap, T: Traceable<'heap> + ?Sized> Traceable<'heap> for Alloc<T> {
    fn mark(&self) {
        if !self.mark.replace(true) {
            self.data.mark();
        }
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        self.data.manage(heap);
    }
}

impl<T> Alloc<T> {
    pub fn new(data: T) -> Self {
        Self {
            _pin: PhantomPinned,
            list: Chain::default(),
            mark: Cell::new(false),
            data,
        }
    }
}

impl<T: ?Sized> Alloc<T> {
    pub unsafe fn free(ptr: *mut Self) {
        println!("Freeing {ptr:?}");
        drop(Box::from_raw(ptr));
    }

    pub fn is_marked(&self) -> bool {
        self.mark.replace(false)
    }

    pub fn is_unmanaged(&self) -> bool {
        self.list.is_head()
    }
}
