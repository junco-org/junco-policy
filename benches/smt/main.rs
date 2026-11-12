//! Criterion benchmark of `PolicyAnalyzer::tail_included` on RegExLib Subset inclusion instances of
//! Stanford, Veanes, and Bjørner (PLDI'21); see `README.md` for the dataset and its translation.
//!
//! Run with `cargo bench --bench smt`; pass a Criterion filter such as `-- unsat` for one kind.

use std::hint::black_box;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, SamplingMode, criterion_group, criterion_main};
use history_analysis::{Domains, Inclusion, PolicyAnalyzer};
use history_syntax::{Component, Component3, ComponentPattern, Head};

mod regexlib_subset;

use regexlib_subset::{ALPHABET, Char, INSTANCES};

/// Times `tail_included`; the head, analyzer and regexes are built outside the timed call.
fn benchmark_regexlib_subset(criterion: &mut Criterion) {
    // These tails have no variables, so any inhabited candidate head gives the same inclusion.
    let head = Head::<Char>::new([
        ComponentPattern::constant(Component3::C0(())),
        ComponentPattern::constant(Component3::C1(ALPHABET[0])),
        ComponentPattern::constant(Component3::C2(())),
    ]);
    let mut group = criterion.benchmark_group("regexlib_subset");
    group
        .sampling_mode(SamplingMode::Flat)
        .sample_size(50)
        .warm_up_time(Duration::from_millis(500))
        .measurement_time(Duration::from_secs(2));
    for instance in &INSTANCES {
        let (left, right) = ((instance.left)(), (instance.right)());
        let mut analyzer = PolicyAnalyzer::new(
            Domains::<Char>::infinite().with_domain(Component(1), ALPHABET.map(Component3::C1)),
        );
        let verdict = analyzer
            .tail_included(&head, &left, &right)
            .expect("benchmark regexes are valid");
        assert_eq!(
            matches!(verdict, Inclusion::Holds),
            instance.included,
            "{}",
            instance.file
        );
        let (kind, name) = instance.file.split_once('/').unwrap();
        group.bench_function(
            BenchmarkId::new(kind, name.trim_end_matches(".smt2")),
            |bencher| {
                bencher.iter(|| {
                    analyzer
                        .tail_included(black_box(&head), black_box(&left), black_box(&right))
                        .unwrap()
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, benchmark_regexlib_subset);
criterion_main!(benches);
