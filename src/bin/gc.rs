use rox::{
    enroot,
    gc::{object::Object, GcRef, Heap},
};

fn main() {
    let heap = std::pin::pin!(Heap::default());
    {
        enroot!(heap, root);
        let upvalue1 = root.alloc(Object::Upvalue(GcRef::new(
            rox::gc::object::Upvalue::Open(0),
            heap.as_ref(),
        )));

        enroot!(heap, root);
        let upvalue = std::pin::pin!(Object::Upvalue(GcRef::new(
            rox::gc::object::Upvalue::Open(0),
            heap.as_ref(),
        )));
        let upvalue2 = root.enroot(upvalue.as_ref());

        println!("{:?}", *upvalue1);
        println!("{:?}", *upvalue2);

        heap.as_ref().collect();

        println!("{:?}", *upvalue1);
        println!("{:?}", *upvalue2);
    }
    heap.as_ref().collect();
}
