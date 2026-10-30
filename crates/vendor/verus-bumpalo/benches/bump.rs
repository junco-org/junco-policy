use core::alloc::Layout;
use criterion::{Criterion, Throughput};
use std::hint::black_box;
use std::path::PathBuf;
use std::time::Duration;
use verus_bumpalo::Bump;
use vstd::prelude::Tracked;

const N: usize = 10_000;
const GROUPS: [&str; 4] = [
    "try-alloc/small/const",
    "try-alloc/small/opaque",
    "try-alloc/big/const",
    "try-alloc/big/opaque",
];

/// `OPAQUE` hides the layout from the optimizer on every call. The const variant
/// lets both allocators fold `layout.align()`, as real call sites do.
fn run<T, const OPAQUE: bool>(c: &mut Criterion, name: &str) {
    let layout = Layout::new::<T>();
    let l = move || if OPAQUE { black_box(layout) } else { layout };
    let cap = N * layout.size().max(1) * 2;
    let mut group = c.benchmark_group(name);
    group.throughput(Throughput::Elements(N as u64));
    group.sample_size(200);
    group.measurement_time(Duration::from_secs(10));

    group.bench_function("verus-bumpalo", |b| {
        let (mut arena, _st) = Bump::try_with_capacity(cap).unwrap();
        b.iter(|| {
            for _ in 0..N {
                let (p, _, _) = arena.try_alloc_layout(l(), Tracked::assume_new()).unwrap();
                black_box(p);
            }
            arena.reset(Tracked::assume_new(), Tracked::assume_new());
        });
        arena.free(Tracked::assume_new(), Tracked::assume_new());
    });

    group.bench_function("bumpalo", |b| {
        let mut arena = bumpalo::Bump::with_capacity(cap);
        b.iter(|| {
            for _ in 0..N {
                let p = arena.try_alloc_layout(l()).unwrap();
                black_box(p.as_ptr());
            }
            arena.reset();
        });
    });

    group.finish();
}

/// Prints verus-bumpalo / bumpalo time ratios from Criterion's saved estimates.
fn report() {
    let home = std::env::var_os("CRITERION_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("target"))
                .join("criterion")
        });
    let estimate = |group: &str, function: &str, key: &str| -> Option<f64> {
        let path = home
            .join(group.replace('/', "_"))
            .join(function)
            .join("new/estimates.json");
        let v: serde_json::Value = serde_json::from_slice(&std::fs::read(path).ok()?).ok()?;
        v[key]["point_estimate"].as_f64()
    };
    println!(
        "\n{:<24} {:>8} {:>8}   verus-bumpalo / bumpalo time",
        "group", "slope", "median"
    );
    for group in GROUPS {
        let ratio = |key: &str| match (
            estimate(group, "verus-bumpalo", key),
            estimate(group, "bumpalo", key),
        ) {
            (Some(v), Some(b)) => format!("{:.2}x", v / b),
            _ => "n/a".to_string(),
        };
        println!("{group:<24} {:>8} {:>8}", ratio("slope"), ratio("median"));
    }
}

fn main() {
    let mut c = Criterion::default().configure_from_args();
    run::<u8, false>(&mut c, GROUPS[0]);
    run::<u8, true>(&mut c, GROUPS[1]);
    run::<[usize; 32], false>(&mut c, GROUPS[2]);
    run::<[usize; 32], true>(&mut c, GROUPS[3]);
    c.final_summary();
    report();
}
