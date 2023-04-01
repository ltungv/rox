use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pprof::criterion::{Output, PProfProfiler};
use rox::VirtualMachine;

pub fn interpret(c: &mut Criterion) {
    let mut g = c.benchmark_group("e2e");

    g.bench_function("binary_tree.lox", |b| {
        let src = include_str!("e2e/binary_tree.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("equality.lox", |b| {
        let src = include_str!("e2e/equality.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("fib20.lox", |b| {
        let src = include_str!("e2e/fib20.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("instantiation.lox", |b| {
        let src = include_str!("e2e/instantiation.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("invocation.lox", |b| {
        let src = include_str!("e2e/invocation.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("method_call.lox", |b| {
        let src = include_str!("e2e/method_call.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("properties.lox", |b| {
        let src = include_str!("e2e/properties.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("trees.lox", |b| {
        let src = include_str!("e2e/trees.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.bench_function("zoo.lox", |b| {
        let src = include_str!("e2e/zoo.lox");
        let mut vm = VirtualMachine::default();
        b.iter(|| vm.interpret(black_box(src)));
    });

    g.finish();
}

criterion_group!(
    name = e2e;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = interpret);
criterion_main!(e2e);
