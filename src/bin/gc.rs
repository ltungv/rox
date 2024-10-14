use rox::{
    enroot,
    gc::{
        object::{Object, Upvalue},
        Heap,
    },
};

fn main() {
    let heap = std::pin::pin!(Heap::default());
    {
        enroot!(heap, root);
        let upvalue1 = root.alloc(Object::Upvalue(heap.as_ref().alloc(Upvalue::Open(0))));

        enroot!(heap, root);
        let upvalue = std::pin::pin!(Object::Upvalue(heap.as_ref().alloc(Upvalue::Open(0))));
        let upvalue2 = root.enroot(upvalue.as_ref());

        println!("{:?}", *upvalue1);
        println!("{:?}", *upvalue2);

        heap.as_ref().collect();

        println!("{:?}", *upvalue1);
        println!("{:?}", *upvalue2);
    }
    heap.as_ref().collect();
}
