use rox::{
    enroot,
    gc::{
        object::{Object, RootedObject, UpvalueObject},
        Heap,
    },
};

fn main() {
    let heap = std::pin::pin!(Heap::default());
    {
        enroot!(heap, root);
        let upvalue = std::pin::pin!(Object::Upvalue(heap.as_ref().alloc(UpvalueObject::Open(0))));
        let rooted = RootedObject::from(root.enroot(upvalue.as_ref()));
        let RootedObject::Upvalue(ref upvalue) = rooted else {
            unreachable!()
        };

        println!("{:?}", rooted);
        println!("{:?}", **upvalue);

        heap.as_ref().collect();

        println!("{:?}", rooted);
        println!("{:?}", **upvalue);
    }
    heap.as_ref().collect();
}
