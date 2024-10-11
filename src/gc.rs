//! A safe garbage collector.

mod alloc;
mod chain;
mod ptr;

use core::{cell::RefCell, marker::PhantomPinned, pin::Pin};

use alloc::Alloc;
use chain::Chain;
use ptr::{Gc, GcEmbed, GcPointer};

/// Constructs a stack-pinned root and returns its reference.
macro_rules! root {
    ($heap:ident, $($root:ident),+) => {$(
        let $root = $crate::gc::RawRoot::new($heap);
        let $root = unsafe { $crate::gc::Root::new_unchecked(&$root) };
    )*}
}

/// Constructs a stack-pinned heap and returns its reference.
macro_rules! heap {
    ($heap:ident) => {
        let $heap = $crate::gc::Heap::default();
        let $heap = unsafe { core::pin::Pin::new_unchecked(&$heap) };
    };
}

trait Traceable<'heap> {
    fn mark(&self);
    fn manage(&self, heap: Pin<&Heap<'heap>>);
}

struct Root<'root, 'heap> {
    raw: Pin<&'root RawRoot<'root, 'heap>>,
}

impl<'root, 'heap> Root<'root, 'heap> {
    unsafe fn new_unchecked(raw: &'root RawRoot<'root, 'heap>) -> Self {
        Self {
            raw: Pin::new_unchecked(raw),
        }
    }

    fn enroot(self, object: Object<'heap>) -> Gc<'root, Object<'heap>> {
        println!("Alloc Gc");
        let ptr = GcPointer::new(object);
        self.raw.heap.manage(ptr);
        self.raw.heap.roots.borrow_mut()[self.raw.id] = Some(ptr);
        Gc::new(ptr)
    }

    fn reroot<'current_root>(
        self,
        gc: &Gc<'current_root, Object<'heap>>,
    ) -> Gc<'root, Object<'heap>> {
        let ptr = gc.raw();
        self.raw.heap.roots.borrow_mut()[self.raw.id] = Some(ptr);
        Gc::new(ptr)
    }
}

struct RawRoot<'root, 'heap> {
    id: usize,
    heap: Pin<&'root Heap<'heap>>,
}

impl<'root, 'heap> Drop for RawRoot<'root, 'heap> {
    fn drop(&mut self) {
        let mut roots = self.heap.roots.borrow_mut();
        let root = roots.pop();
        debug_assert!(root.is_some());
        debug_assert_eq!(roots.len(), self.id);
    }
}

impl<'root, 'heap> RawRoot<'root, 'heap> {
    fn new(heap: Pin<&'root Heap<'heap>>) -> Self {
        let mut roots = heap.roots.borrow_mut();
        let id = roots.len();
        roots.push(None);
        Self { id, heap }
    }
}

#[derive(Default)]
struct Heap<'heap> {
    _pin: PhantomPinned,
    list: Chain<Alloc<Object<'heap>>>,
    roots: RefCell<Vec<Option<GcPointer<Object<'heap>>>>>,
}

impl<'heap> Heap<'heap> {
    fn collect(self: Pin<&Self>) {
        for root in self.roots.borrow().iter().flatten() {
            root.mark();
        }
        for alloc in self.list() {
            if !alloc.is_marked() {
                let ptr = unsafe { core::ptr::from_mut(alloc.get_unchecked_mut()) };
                println!("Collecting {ptr:?}");
                unsafe { Alloc::free(ptr) };
            }
        }
    }

    fn manage(self: Pin<&Self>, mut ptr: GcPointer<Object<'heap>>) {
        ptr.manage(self);
        self.list().link(unsafe { ptr.pin_mut() });
    }

    fn list(self: Pin<&Self>) -> Pin<&Chain<Alloc<Object<'heap>>>> {
        unsafe { self.map_unchecked(|heap| &heap.list) }
    }
}

enum Object<'heap> {
    Upvalue(Upvalue<'heap>),
}

impl<'heap> Traceable<'heap> for Object<'heap> {
    fn mark(&self) {
        match self {
            Self::Upvalue(upvalue) => upvalue.mark(),
        }
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        match self {
            Self::Upvalue(upvalue) => upvalue.manage(heap),
        }
    }
}

enum Upvalue<'heap> {
    Open(usize),
    Closed(GcEmbed<Object<'heap>>),
}

impl<'heap> Traceable<'heap> for Upvalue<'heap> {
    fn mark(&self) {
        if let Self::Closed(object) = self {
            object.raw().mark();
        }
    }

    fn manage(&self, heap: Pin<&Heap<'heap>>) {
        if let Self::Closed(object) = self {
            heap.manage(object.raw());
        }
    }
}

/// An example for using the GC.
pub fn example() {
    heap!(heap);
    {
        root!(heap, root2);
        {
            root!(heap, root1);
            _ = GcEmbed::new(Object::Upvalue(Upvalue::Open(0)));
            let upvalue = GcEmbed::new(Object::Upvalue(Upvalue::Open(1)));
            let upvalue = root1.enroot(Object::Upvalue(Upvalue::Closed(upvalue)));
            heap.collect();
            root2.reroot(&upvalue);
        }
        heap.collect();
    }
    heap.collect();
}
