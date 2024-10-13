use rox::{
    enroot,
    gc::{object::Object, GcRef, Heap},
};

fn main() {
    let heap = std::pin::pin!(Heap::default());
    {
        enroot!(heap, root);
        let _upvalue = root.alloc(Object::Upvalue(GcRef::new(
            rox::gc::object::Upvalue::Open(0),
            heap.as_ref(),
        )));

        enroot!(heap, root);
        let upvalue = std::pin::pin!(Object::Upvalue(GcRef::new(
            rox::gc::object::Upvalue::Open(0),
            heap.as_ref(),
        )));
        root.enroot(upvalue.as_ref());

        heap.as_ref().collect();
    }
    heap.as_ref().collect();
}
