//! A safe garbage collector.

mod alloc;
mod heap;
mod root;

use heap::{Gc, Heap};

/// Constructs a stack-pinned root and returns its reference.
macro_rules! root {
    ($heap:ident, $($root:ident),+) => {$(
        let mut $root = $root;
        let $root = unsafe { $crate::gc::root::Root::new_unchecked(&mut $root, &$heap) };
    )*}
}

trait Trace {
    fn trace(&self);
}

impl<T: Trace> Trace for Vec<T> {
    fn trace(&self) {
        self.iter().for_each(Trace::trace);
    }
}

#[derive(Debug)]
enum Object {
    Upvalue(Upvalue),
}

impl Trace for Object {
    fn trace(&self) {
        match self {
            Self::Upvalue(upvalue) => upvalue.trace(),
        }
    }
}

#[derive(Debug)]
enum Upvalue {
    Open(usize),
    Closed(Gc<Object>),
}

impl Trace for Upvalue {
    fn trace(&self) {
        if let Self::Closed(object) = self {
            object.trace();
        }
    }
}

/// An example for using the GC.
pub fn example() {
    let heap = Heap::default();
    {
        let o = heap.alloc(Object::Upvalue(Upvalue::Open(0)));
        let o = heap.alloc(Object::Upvalue(Upvalue::Closed(o)));
        println!("{:?}", &o);
        root!(heap, o);
        heap.collect();
        println!("{:?}", *o);
    }
    heap.collect();
}
