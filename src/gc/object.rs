#![allow(missing_docs)]

use super::{GcBox, Trace};

#[derive(Debug)]
pub enum Object<'root, 'heap> {
    Upvalue(GcBox<'root, 'heap, Upvalue<'root, 'heap>>),
}

unsafe impl<'root, 'heap> Trace for Object<'root, 'heap> {
    fn trace(&self) {
        match self {
            Self::Upvalue(v) => v.trace(),
        }
    }
}

#[derive(Debug)]
pub enum Upvalue<'root, 'heap> {
    Open(usize),
    Close(Object<'root, 'heap>),
}

unsafe impl<'root, 'heap> Trace for Upvalue<'root, 'heap> {
    fn trace(&self) {
        if let Self::Close(o) = self {
            o.trace();
        }
    }
}
