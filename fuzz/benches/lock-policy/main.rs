//! Warm lock-policy decision latency over committed fuzzed histories of 2^4 ..= 2^16 events.
//!
//! Same generator and probes as `../lock_policy.rs`; this target extends the length sweep to
//! 65,536 events. Each length is its own tracked [`History`] built from one immutable prefix,
//! decided repeatedly by one retained policy: after the first call every rule resumes its cached
//! residual, so points are warm-progress decisions, not full-history replays.

use std::hint::black_box;
use std::sync::Arc;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, PlottingBackend, criterion_group, criterion_main};
use history_store::History;
use junco_policy::LockPolicy;
use lock_policy_harness::{BYTES_PER_EVENT, check, entropy, granted_history, probe_candidates};

/// Committed history lengths 2^4 ..= 2^16.
const LENGTHS: [usize; 13] = [
    16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
];
/// Fixed seed — criterion compares each run against the previous one, so the trace must not move.
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;

fn lock_scaling(criterion: &mut Criterion) {
    let longest = LENGTHS[LENGTHS.len() - 1];
    let history = granted_history(&entropy(SEED, longest * BYTES_PER_EVENT), longest)
        .expect("benchmark history generation failed");
    let store = history.store();
    let prefixes = LENGTHS.map(|length| {
        History::from_events(
            Arc::clone(store),
            history.as_slice()[..length].iter().copied(),
        )
        .expect("benchmark prefix construction failed")
    });
    let probes = probe_candidates();
    let mut verdict_policy =
        LockPolicy::new(Arc::clone(store)).expect("benchmark policy compilation failed");

    // A denial returns from the compiled policy early, so print each verdict once per point.
    for (name, candidate) in &probes {
        for (length, prefix) in LENGTHS.iter().zip(&prefixes) {
            let verdict = if check(&mut verdict_policy, prefix, candidate)
                .expect("benchmark preflight decision failed")
            {
                "grant"
            } else {
                "deny"
            };
            eprintln!("verdict {name}/{length}: {verdict}");
        }
    }

    let mut group = criterion.benchmark_group("lock_scaling");
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(2));
    group.sample_size(50);
    for (name, candidate) in &probes {
        for (length, prefix) in LENGTHS.iter().zip(&prefixes) {
            let mut policy =
                LockPolicy::new(Arc::clone(store)).expect("benchmark policy compilation failed");
            group.bench_with_input(BenchmarkId::new(*name, length), prefix, |bencher, trace| {
                bencher.iter(|| {
                    check(&mut policy, black_box(trace), black_box(candidate))
                        .expect("benchmark decision failed")
                })
            });
        }
    }
    group.finish();
}

// Pinned backend, as in `../lock_policy.rs`: `default_plotting_backend` would pick gnuplot
// whenever it is on `PATH`, changing who renders the report between machines.
criterion_group! {
    name = benches;
    config = Criterion::default().plotting_backend(PlottingBackend::Plotters);
    targets = lock_scaling
}
criterion_main!(benches);
