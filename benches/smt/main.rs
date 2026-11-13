//! Criterion benchmark of `PolicyAnalyzer::tail_included` on RegExLib Subset inclusion instances of
//! Stanford, Veanes, and Bjørner (PLDI'21); see `README.md` for the dataset and its translation.
//!
//! Run with `cargo bench --bench smt`; pass a Criterion filter such as `-- unsat` for one kind.

use std::hint::black_box;
use std::sync::Arc;
use std::time::{Duration, Instant};

use criterion::{BenchmarkId, Criterion, SamplingMode, criterion_group, criterion_main};
use history_analysis::{Components, Domains, Inclusion, PolicyAnalyzer, Value};
use history_semantics::CompiledRule;
use history_store::{History, Store};
use history_syntax::{Component, Component3, ComponentPattern, Head, Rule, RuleMode};

mod regexlib_subset;

use regexlib_subset::{ALPHABET, Char, INSTANCES};

fn concrete(components: &Components<Char>) -> Char {
    let [
        Value::Constant(Component3::C0(())),
        Value::Constant(Component3::C1(byte)),
        Value::Constant(Component3::C2(())),
    ] = components.values.as_slice()
    else {
        panic!("counterexample contains a fresh, mistagged or malformed declared coordinate");
    };
    assert!(
        ALPHABET.binary_search(byte).is_ok(),
        "character outside declared alphabet"
    );
    Char(*byte)
}

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
    let mut checked_counterexamples = 0usize;
    for instance in &INSTANCES {
        let (left, right) = ((instance.left)(), (instance.right)());
        let mut analyzer = PolicyAnalyzer::new(
            Domains::<Char>::infinite()
                .with_domain(Component(0), &[Component3::C0(())])
                .expect("principal domain")
                .with_domain(Component(1), &ALPHABET.map(Component3::C1))
                .expect("action domain")
                .with_domain(Component(2), &[Component3::C2(())])
                .expect("resource domain"),
        );
        let verdict = analyzer
            .tail_included(&head, &left, &right)
            .expect("benchmark regexes are valid");
        // Reuse concrete matchers and history outside the measured query. Initialize them only
        // when this instance returns its first counterexample.
        let mut concrete_matchers = None;
        let mut check = |verdict: &Inclusion<Char>| {
            assert_eq!(
                matches!(verdict, Inclusion::Holds),
                instance.included,
                "{}",
                instance.file
            );
            match verdict {
                Inclusion::Holds => {}
                Inclusion::Exhausted => panic!("benchmark search exhausted: {}", instance.file),
                Inclusion::Counterexample(witness) => {
                    let candidate = concrete(&witness.candidate);
                    assert_eq!(
                        candidate.0, ALPHABET[0],
                        "counterexample must match the head"
                    );
                    let (history, left_matcher, right_matcher) = concrete_matchers
                        .get_or_insert_with(|| {
                            let store =
                                Arc::new(Store::<Char>::new().expect("concrete validation store"));
                            let history =
                                History::new(store.clone()).expect("concrete validation history");
                            let left_matcher = CompiledRule::new(
                                store.clone(),
                                Rule::new(RuleMode::Forbid, head.clone(), left.clone()),
                            )
                            .expect("left concrete matcher");
                            let right_matcher = CompiledRule::new(
                                store,
                                Rule::new(RuleMode::Forbid, head.clone(), right.clone()),
                            )
                            .expect("right concrete matcher");
                            (history, left_matcher, right_matcher)
                        });
                    history.truncate(0).expect("reset concrete history");
                    for event in &witness.history {
                        history
                            .push(concrete(event))
                            .expect("append concrete character");
                    }
                    assert_eq!(
                        left_matcher.accepts_history(history, &candidate).unwrap(),
                        Some(true),
                        "left regex rejects concrete counterexample: {}",
                        instance.file
                    );
                    assert_eq!(
                        right_matcher.accepts_history(history, &candidate).unwrap(),
                        Some(false),
                        "right regex accepts concrete counterexample: {}",
                        instance.file
                    );
                    checked_counterexamples += 1;
                }
            }
        };
        check(&verdict);
        drop(verdict);
        let (kind, name) = instance.file.split_once('/').unwrap();
        group.bench_function(
            BenchmarkId::new(kind, name.trim_end_matches(".smt2")),
            |bencher| {
                bencher.iter_custom(|iterations| {
                    let mut elapsed = Duration::ZERO;
                    for _ in 0..iterations {
                        let started = Instant::now();
                        let verdict = analyzer
                            .tail_included(black_box(&head), black_box(&left), black_box(&right))
                            .unwrap();
                        elapsed += started.elapsed();
                        check(&verdict);
                        // Include result destruction, as the original aggregate timer did,
                        // while excluding the concrete validation above.
                        let started = Instant::now();
                        drop(verdict);
                        elapsed += started.elapsed();
                    }
                    elapsed
                });
            },
        );
    }
    group.finish();
    eprintln!(
        "validated {checked_counterexamples} concrete counterexamples; no fresh values at declared coordinates"
    );
}

criterion_group!(benches, benchmark_regexlib_subset);
criterion_main!(benches);
