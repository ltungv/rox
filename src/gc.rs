//! A safe garbage collector.

mod heap;
mod object;
#[macro_use]
mod root;

use heap::Heap;
use object::{Object, Upvalue};

trait Trace {
    fn trace(&self);
}

impl<T: Trace> Trace for Vec<T> {
    fn trace(&self) {
        self.iter().for_each(Trace::trace);
    }
}

/// An example for using the GC.
pub fn example() {
    let heap = Heap::default();
    {
        let (_, o) = heap.alloc(Upvalue::Open(0), Object::Upvalue);
        let (_, o) = heap.alloc(Upvalue::Closed(o), Object::Upvalue);
        println!("{o:?}");
        root!(heap, o);
        heap.collect();
    }
    heap.collect();
}
