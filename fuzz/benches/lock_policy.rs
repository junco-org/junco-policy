//! How long one lock policy check takes, as a function of committed trace length.
//!
//! The traces come from the same generator the cargo-fuzz target drives
//! (`lock_policy_harness`), so the benchmark and the fuzzer never diverge. Each measured length is
//! its own tracked [`History`] owner built from the immutable prefix, decided repeatedly by one
//! retained policy: after the first call every rule resumes its cached residual, so these numbers
//! are warm-progress decisions rather than full-history replays.

use std::hint::black_box;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, PlottingBackend, criterion_group, criterion_main};
use junco_policy::{Bump, History, LockPolicy};
use lock_policy_harness::{BYTES_PER_EVENT, check, entropy, granted_history, probe_candidates};

/// Committed history lengths measured; geometric, so the growth rate reads off directly.
const LENGTHS: [usize; 6] = [0, 4, 16, 64, 256, 1024];
/// Fixed seed — criterion compares each run against the previous one, so the trace must not move.
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;

fn lock_decision_scaling(criterion: &mut Criterion) {
    let longest = LENGTHS[LENGTHS.len() - 1];
    let history = granted_history(&entropy(SEED, longest * BYTES_PER_EVENT), longest);
    let prefixes =
        LENGTHS.map(|length| History::from_events(history.as_slice()[..length].iter().copied()));
    let probes = probe_candidates();
    let verdict_arena = Bump::new();
    let mut verdict_policy = LockPolicy::new(&verdict_arena);

    // The verdict decides how much work a check does — a denial returns from the compiled policy
    // early — so print it once per measured point; timings are uninterpretable without it.
    for (name, candidate) in &probes {
        for (length, prefix) in LENGTHS.iter().zip(&prefixes) {
            let verdict = if check(&mut verdict_policy, prefix, candidate) {
                "grant"
            } else {
                "deny"
            };
            eprintln!("verdict {name}/{length}: {verdict}");
        }
    }

    let mut group = criterion.benchmark_group("lock_decision");
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(2));
    group.sample_size(50);
    for (name, candidate) in &probes {
        for (length, prefix) in LENGTHS.iter().zip(&prefixes) {
            let arena = Bump::new();
            let mut policy = LockPolicy::new(&arena);
            group.bench_with_input(BenchmarkId::new(*name, length), prefix, |bencher, trace| {
                bencher.iter(|| check(&mut policy, black_box(trace), black_box(candidate)))
            });
        }
    }
    group.finish();
}

// The backend is pinned rather than left to `default_plotting_backend`, which prefers gnuplot
// whenever the command happens to be on `PATH` — that would silently change who renders the report
// from one machine to the next.
criterion_group! {
    name = benches;
    config = Criterion::default().plotting_backend(PlottingBackend::Plotters);
    targets = lock_decision_scaling
}
criterion_main!(benches);
