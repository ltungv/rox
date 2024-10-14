#![allow(missing_docs)]

use super::{GcBox, Trace};

#[derive(Debug)]
pub enum Object<'heap> {
    Upvalue(GcBox<'heap, Upvalue<'heap>>),
}

unsafe impl<'heap> Trace for Object<'heap> {
    fn trace(&self) {
        match self {
            Self::Upvalue(v) => v.trace(),
        }
    }
}

#[derive(Debug)]
pub enum Upvalue<'heap> {
    Open(usize),
    Close(Object<'heap>),
}

unsafe impl<'heap> Trace for Upvalue<'heap> {
    fn trace(&self) {
        if let Self::Close(o) = self {
            o.trace();
        }
    }
}
