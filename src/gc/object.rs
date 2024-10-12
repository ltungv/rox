use core::{
    cell::Cell,
    marker::{PhantomData, PhantomPinned},
    ptr::NonNull,
};

use super::Trace;

#[derive(Clone, Copy, Debug)]
pub enum Object {
    Upvalue(Gc<Upvalue>),
}

impl Trace for Object {
    fn trace(&self) {
        match self {
            Self::Upvalue(upvalue) => upvalue.trace(),
        }
    }
}

impl Object {
    pub(super) unsafe fn free(self) {
        match self {
            Self::Upvalue(gc) => gc.free(),
        }
    }

    pub(super) unsafe fn unmark(self) -> bool {
        match self {
            Self::Upvalue(gc) => gc.ptr.as_ref().unmark(),
        }
    }

    pub(super) unsafe fn get_next(self) -> Option<Self> {
        match self {
            Self::Upvalue(gc) => gc.ptr.as_ref().get_next(),
        }
    }

    pub(super) unsafe fn set_next(self, object: Option<Self>) {
        match self {
            Self::Upvalue(gc) => gc.ptr.as_ref().set_next(object),
        }
    }
}

#[derive(Debug)]
pub enum Upvalue {
    Open(usize),
    Closed(Object),
}

impl Trace for Upvalue {
    fn trace(&self) {
        if let Self::Closed(object) = self {
            object.trace();
        }
    }
}

#[derive(Debug)]
pub struct Gc<T> {
    _own: PhantomData<T>,
    ptr: NonNull<GcBox<T>>,
}

impl<T> Copy for Gc<T> {}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Trace> Trace for Gc<T> {
    fn trace(&self) {
        let raw = unsafe { self.ptr.as_ref() };
        if !raw.mark() {
            println!("Mark {:?}", core::ptr::from_ref(self));
            raw.data.trace();
        }
    }
}

impl<T> Gc<T> {
    pub(super) fn new(data: T) -> Self {
        let raw = Box::new(GcBox::new(data));
        let ptr = Box::into_raw(raw);
        let ptr = unsafe { NonNull::new_unchecked(ptr) };
        println!("Alloc {ptr:?}");
        Self {
            _own: PhantomData,
            ptr,
        }
    }

    pub(super) const fn get_ptr(self) -> NonNull<GcBox<T>> {
        self.ptr
    }

    unsafe fn free(self) {
        println!("Freeing {:?}", self.ptr);
        drop(Box::from_raw(self.ptr.as_ptr()));
    }
}

#[derive(Debug)]
pub(super) struct GcBox<T> {
    _pin: PhantomPinned,
    next: Cell<Option<Object>>,
    mark: Cell<bool>,
    data: T,
}

impl<T> AsRef<T> for GcBox<T> {
    fn as_ref(&self) -> &T {
        &self.data
    }
}

impl<T> GcBox<T> {
    const fn new(data: T) -> Self {
        Self {
            _pin: PhantomPinned,
            next: Cell::new(None),
            mark: Cell::new(false),
            data,
        }
    }

    fn mark(&self) -> bool {
        self.mark.replace(true)
    }

    fn unmark(&self) -> bool {
        self.mark.replace(false)
    }

    fn get_next(&self) -> Option<Object> {
        self.next.get()
    }

    fn set_next(&self, next: Option<Object>) {
        self.next.set(next);
    }
}
