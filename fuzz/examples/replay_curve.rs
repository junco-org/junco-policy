//! Throwaway grants-only replay latency and engine-work probe.
use std::collections::HashSet;
use std::fmt::Write as _;
use std::sync::Arc;
use std::time::Instant;

use history_semantics::CompiledRule;
use history_semantics::policy::{action_is, last_state_change, principal_is, resource_is};
use history_store::{History, Store};
use history_syntax::{Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr};
use junco_policy::{Action, LockEvent, LockPolicy};
use lock_policy_harness::{Agent, BYTES_PER_EVENT, PooledPath, check, entropy, granted_history};

type E = LockEvent<Agent, PooledPath>;
const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
const LABELS: [&str; 7] = [
    "edit_owner",
    "release_owner",
    "remove_owner",
    "edit_stale",
    "remove_stale",
    "edit_reader",
    "remove_reader",
];

fn foreign_on_r(action: Action) -> TestExpr<E> {
    TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(action, Comparison::Eq),
        principal_is(Comparison::Neq),
    ])
}

fn owned_by_other() -> RegexExpr<E> {
    let changes = [Action::Edit, Action::Release, Action::Remove];
    last_state_change(foreign_on_r(Action::Edit), stable(&changes))
}

fn read_by_other() -> RegexExpr<E> {
    let changes = [Action::Read, Action::Remove];
    last_state_change(foreign_on_r(Action::Read), stable(&changes))
}

fn stale_view() -> RegexExpr<E> {
    last_state_change(
        foreign_on_r(Action::Edit),
        TestExpr::and([
            stable(&[Action::Edit, Action::Remove]),
            TestExpr::or([
                resource_is(Comparison::Neq),
                action_is(Action::Read, Comparison::Neq),
                principal_is(Comparison::Neq),
            ]),
        ]),
    )
}

fn stable(changes: &[Action]) -> TestExpr<E> {
    TestExpr::or([
        resource_is(Comparison::Neq),
        TestExpr::and(
            changes
                .iter()
                .map(|&action| action_is(action, Comparison::Neq)),
        ),
    ])
}

fn rules(store: &Arc<Store<E>>) -> Vec<CompiledRule<E>> {
    [
        (Action::Edit, owned_by_other()),
        (Action::Release, owned_by_other()),
        (Action::Remove, owned_by_other()),
        (Action::Edit, stale_view()),
        (Action::Remove, stale_view()),
        (Action::Edit, read_by_other()),
        (Action::Remove, read_by_other()),
    ]
    .into_iter()
    .map(|(action, tail)| {
        CompiledRule::new(
            Arc::clone(store),
            Rule::new(
                RuleMode::Forbid,
                Head::new(
                    ComponentPattern::Variable("p".to_owned()),
                    ComponentPattern::Constant(action),
                    ComponentPattern::Variable("r".to_owned()),
                ),
                tail,
            ),
        )
        .expect("standalone rule compiles")
    })
    .collect()
}

fn counters(rule: &CompiledRule<E>) -> [usize; 6] {
    let c = rule.work_counters();
    [
        c.events,
        c.derivative_misses,
        c.event_classes,
        c.successor_hits,
        c.successor_misses,
        c.guard_hits,
    ]
}

#[derive(Clone, Default)]
struct Sample {
    check: u64,
    push: u64,
    work: [usize; 6],
    rule_ns: [u64; 7],
    rule_folded: [usize; 7],
}

fn percentile(values: impl Iterator<Item = u64>, percentile: usize) -> f64 {
    let mut values: Vec<_> = values.collect();
    values.sort_unstable();
    values[(values.len() * percentile).div_ceil(100).saturating_sub(1)] as f64
}

fn fit(xs: &[f64], ys: &[f64]) -> (f64, f64) {
    let xm = xs.iter().sum::<f64>() / xs.len() as f64;
    let ym = ys.iter().sum::<f64>() / ys.len() as f64;
    let xx = xs.iter().map(|x| (x - xm).powi(2)).sum::<f64>();
    let yy = ys.iter().map(|y| (y - ym).powi(2)).sum::<f64>();
    let xy = xs
        .iter()
        .zip(ys)
        .map(|(x, y)| (x - xm) * (y - ym))
        .sum::<f64>();
    (xy / xx, if yy == 0.0 { 0.0 } else { xy * xy / (xx * yy) })
}

fn measure(label: &str, events: &[E], store: &Arc<Store<E>>, repeats: usize) -> String {
    let n = events.len();
    let mut policy = LockPolicy::new(Arc::clone(store)).expect("policy compiles");
    let mut rules = rules(store);
    let mut samples = vec![Sample::default(); n * repeats];
    let mut totals = vec![0_u64; repeats];
    for (r, total) in totals.iter_mut().enumerate() {
        let mut h = History::new(Arc::clone(store)).expect("history");
        for (k, e) in events.iter().enumerate() {
            let s = &mut samples[k * repeats + r];
            let t = Instant::now();
            let granted = check(&mut policy, &h, e).expect("decision");
            s.check = t.elapsed().as_nanos().try_into().unwrap();
            assert!(granted, "{label}: denied at replay {r}, k={k}");
            let mut violated = false;
            for (i, rule) in rules.iter_mut().enumerate() {
                let before = counters(rule);
                let t = Instant::now();
                let a = rule.accepts_history(&h, e).expect("standalone decision");
                s.rule_ns[i] = t.elapsed().as_nanos().try_into().unwrap();
                let after = counters(rule);
                for j in 0..6 {
                    s.work[j] += after[j] - before[j];
                }
                s.rule_folded[i] = after[0] - before[0];
                violated |= a == Some(true);
            }
            assert!(
                !violated,
                "{label}: composite disagrees at replay {r}, k={k}"
            );
            let t = Instant::now();
            h.push(*e).expect("append");
            s.push = t.elapsed().as_nanos().try_into().unwrap();
            if k < 1024 {
                *total += s.check + s.push;
            }
        }
        assert_eq!(h.as_slice(), events);
    }
    let mut out = format!("# {label}\n");
    out.push_str("k_start,check_med_ns,check_p90_ns,push_med_ns,push_p99_ns,folded_mean,folded_max,deriv_miss_mean,classes_mean,succ_hit_mean,succ_miss_mean,guard_hit_mean,distinct_pr");
    for label in LABELS {
        write!(out, ",rule_{label}_med_ns").unwrap();
    }
    for label in LABELS {
        write!(out, ",rule_{label}_folded_mean").unwrap();
    }
    out.push_str(",check_mean_ns,read_fraction");
    for label in LABELS {
        write!(out, ",rule_{label}_mean_ns").unwrap();
    }
    out.push('\n');
    let mut centers = Vec::new();
    let mut medians = Vec::new();
    let width = n / 64;
    for start in (0..n).step_by(width) {
        let window = &samples[start * repeats..(start + width) * repeats];
        let mean =
            |i: usize| window.iter().map(|s| s.work[i]).sum::<usize>() as f64 / window.len() as f64;
        let med = percentile(window.iter().map(|s| s.check), 50);
        let pairs: HashSet<_> = events[start..start + width]
            .iter()
            .filter(|e| e.action != Action::Read)
            .map(|e| (e.principal, e.resource))
            .collect();
        write!(
            out,
            "{start},{med:.0},{:.0},{:.0},{:.0},{:.4},{},{:.4},{:.4},{:.4},{:.4},{:.4},{}",
            percentile(window.iter().map(|s| s.check), 90),
            percentile(window.iter().map(|s| s.push), 50),
            percentile(window.iter().map(|s| s.push), 99),
            mean(0),
            window.iter().map(|s| s.work[0]).max().unwrap(),
            mean(1),
            mean(2),
            mean(3),
            mean(4),
            mean(5),
            pairs.len()
        )
        .unwrap();
        for i in 0..7 {
            write!(
                out,
                ",{:.0}",
                percentile(window.iter().map(|s| s.rule_ns[i]), 50)
            )
            .unwrap();
        }
        for i in 0..7 {
            let mean =
                window.iter().map(|s| s.rule_folded[i]).sum::<usize>() as f64 / window.len() as f64;
            write!(out, ",{mean:.4}").unwrap();
        }
        let check_mean = window.iter().map(|s| s.check).sum::<u64>() as f64 / window.len() as f64;
        let read_fraction = events[start..start + width]
            .iter()
            .filter(|e| e.action == Action::Read)
            .count() as f64
            / width as f64;
        write!(out, ",{check_mean:.3},{read_fraction:.4}").unwrap();
        for i in 0..7 {
            let mean =
                window.iter().map(|s| s.rule_ns[i]).sum::<u64>() as f64 / window.len() as f64;
            write!(out, ",{mean:.3}").unwrap();
        }
        out.push('\n');
        centers.push(start as f64 + (width - 1) as f64 / 2.0);
        medians.push(med);
    }
    let logs: Vec<_> = centers.iter().map(|k| (k + 1.0).log2()).collect();
    let (log_slope, log_r2) = fit(&logs, &medians);
    let (linear_slope, linear_r2) = fit(&centers, &medians);
    writeln!(
        out,
        "# check first window {:.0} ns, last window {:.0} ns, ratio {:.4}",
        medians[0],
        medians[63],
        medians[63] / medians[0]
    )
    .unwrap();
    writeln!(out, "# log fit: {log_slope:+.3} ns per doubling (R²={log_r2:.6}); linear fit: {:+.3} ns per 1000 events (R²={linear_r2:.6})", linear_slope * 1000.0).unwrap();
    let total = percentile(totals.iter().copied(), 50) / 1000.0;
    writeln!(
        out,
        "# LockPolicy total check+push for k<1024, median over replays: {total:.3} µs"
    )
    .unwrap();
    for length in [16, 64, 256, 1024, 4096, 8192]
        .into_iter()
        .filter(|&l| l <= n)
    {
        let prefix = &samples[..length * repeats];
        let mean =
            |i: usize| prefix.iter().map(|s| s.work[i]).sum::<usize>() as f64 / prefix.len() as f64;
        let elapsed =
            prefix.iter().map(|s| s.check + s.push).sum::<u64>() as f64 / prefix.len() as f64;
        writeln!(out, "# prefix L={length}: check+push_mean_ns={elapsed:.3} folded_mean={:.4} classes_mean={:.4} guard_hit_mean={:.4}", mean(0), mean(2), mean(5)).unwrap();
    }
    let actions = [
        Action::Edit,
        Action::Release,
        Action::Remove,
        Action::Edit,
        Action::Remove,
        Action::Edit,
        Action::Remove,
    ];
    for r in 0..repeats {
        let mut previous: [_; 7] = std::array::from_fn(|_| std::collections::HashMap::new());
        for (k, e) in events.iter().enumerate() {
            for i in 0..7 {
                let expected = if e.action == actions[i] {
                    k - previous[i]
                        .insert((e.principal, e.resource), k)
                        .unwrap_or(0)
                } else {
                    0
                };
                assert_eq!(
                    samples[k * repeats + r].rule_folded[i],
                    expected,
                    "{label}: fold differs from exact binding reuse gap at k={k}, rule={i}, replay={r}"
                );
            }
        }
    }
    writeln!(
        out,
        "# every per-rule fold equals its exact binding reuse gap; no cursor misses after first use"
    )
    .unwrap();
    writeln!(
        out,
        "# verified {} grants and standalone-rule agreement",
        n * repeats
    )
    .unwrap();
    out
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: replay_curve N R");
    let n: usize = args[1].parse()?;
    let repeats: usize = args[2].parse()?;
    assert!(n >= 1024 && n.is_multiple_of(64) && repeats > 0);
    let history = granted_history(&entropy(SEED, n * BYTES_PER_EVENT), n)?;
    let bench = granted_history(&entropy(SEED, 1024 * BYTES_PER_EVENT), 1024)?;
    println!(
        "# prefix {} bench history",
        if history.as_slice()[..1024] == *bench.as_slice() {
            "matches"
        } else {
            "differs from"
        }
    );
    let store = Arc::clone(history.store());
    let mut csv = measure("lock trace", history.as_slice(), &store, repeats);
    let control = vec![LockEvent::new(Agent(0), Action::Edit, PooledPath(0)); n];
    csv.push_str(&measure("control", &control, &store, repeats));
    std::fs::create_dir_all("/tmp/junco-profile")?;
    std::fs::write("/tmp/junco-profile/curve.csv", &csv)?;
    print!("{csv}");
    Ok(())
}
