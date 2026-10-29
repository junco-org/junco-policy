# junco-policy

The workspace has two library packages: `junco-core` owns the generic Rust policy DSL,
compiler, evaluator, histories, and policy facades; `junco-policy` is its ownership-lock
consumer. Import generic APIs directly from `junco_core`. The root package exports only
`Action`, `LockEvent`, `LockPolicy`, and `lock_decision`; there are no generic compatibility
re-exports. The fuzz harness retains an independent no-surprise oracle, not another
production evaluator.

## Shared core and histories

`junco_core` provides `Rule`, `Head`, `TestExpr`, and `RegexExpr` over a caller-chosen
`Event`: a compact `Copy` value projecting to principal, action, and resource. Finite Frunk
`Coprod!` unions and generic approval-payload workloads remain supported. Component
equality determines policy matching, while history preserves each original event and
payload, including events with identical projections but different full values.

Create one `Arc<Store<E>>` for related histories and policies. Constants, candidates, and
appended events use the same coordinate-specific codebooks; decisions reuse numeric
history without re-encoding its raw events. A foreign-store history returns
`HistoryError::WrongHistoryOwner`. Runtime rules retain up to 16 residual cursors keyed
by history owner and bindings: unchanged histories reuse progress, append processes the
new suffix, and shortening invalidates the owner's cursors.

`History::new`, `from_events`, `push`, `truncate`, `rollback`, and `try_clone` are fallible.
`try_clone` shares the store but gets a fresh history identity. There is no infallible
`Clone`, `Default`, or `FromIterator` history constructor. Opaque checkpoints are tied to
their store and history: foreign checkpoints return `WrongCheckpointOwner`, and a
checkpoint beyond the current length returns `CheckpointBeyondHistory`, without mutation.
Compilation returns `CompileError`; evaluation and history operations return
`HistoryError`; `PolicyError` wraps these for the one-shot lock helper. Errors are not
denials and never become a successful append.

`TracePolicy` compiles ordered `TraceRule`s once and decides against caller-owned history
without appending. The first matching rule violation wins: Require rejects histories
outside its language, Forbid rejects those inside it, and nonmatching heads skip. Only
the selected violation invokes its diagnostic, once; grants and errors do not render
diagnostics. `Validator::builder(store)` uses the same engine but owns its history.
`permits` never appends; `check(Request<E, M>)` appends only on a successful grant and
preserves the event and opaque metadata. Denials and operational errors leave it unchanged.

## Lock policy

`LockPolicy` decides four actions per resource. `read` always grants and takes the last-reader
claim. `edit` acquires ownership; `release` relinquishes it and keeps the reader claim; `remove`
(an observed successful deletion) clears both claims. `edit` and `remove` are denied while another
principal owns the resource or last read it; `release` is denied only while another principal owns
it. Releasing an unowned resource grants.

The five Forbid rules keep this order: foreign-owner Edit, Release, Remove, then
foreign-last-reader Edit, Remove. Owner diagnostics therefore win over reader diagnostics.
The diagnostic history fold only renders the selected denial; it does not decide access.
Neither retained `LockPolicy::decide` nor one-shot `lock_decision` appends implicitly:

```rust
use std::sync::Arc;
use junco_core::{History, PolicyDecision, Store};
use junco_policy::{Action, LockEvent, LockPolicy};

fn example() -> Result<(), Box<dyn std::error::Error>> {
    let store = Arc::new(Store::<LockEvent<u32, u32>>::new()?);
    let mut history = History::new(store.clone())?;
    let mut policy = LockPolicy::new(store)?;
    let event = LockEvent::new(1, Action::Edit, 7);
    if matches!(policy.decide(&history, &event)?, PolicyDecision::Grant) {
        history.push(event)?; // Record only after the operation succeeds.
    }
    let checkpoint = history.checkpoint();
    let fork = history.try_clone()?;
    assert_eq!(fork.as_slice(), history.as_slice());
    history.rollback(checkpoint)?;
    Ok(())
}
```

## Features and verification boundary

Core defaults are empty. `runtime` enables evaluation and generic facades; `serde` enables
portable source serialization. `std` selects native locks and `cache` enables optional
precompilation; neither implies `runtime`. Runtime also supports native no_std + alloc.
The root lock consumer enables `runtime,std,cache`. `test-util` is a dev-only integration
probe feature, not a production dependency or a retained-prefix-cache switch.

Body proofs cover DSL structure/lowering, constant encoding under later codebook extensions,
the numeric compiler/evaluator, raw-to-numeric history correspondence, and cached lifecycle
and publication receipts. Native Eq/Hash coherence and stable Event projections are
conditional obligations, not universal proofs about user types. Map/container leaves,
locking, allocation, diagnostic callbacks and native facade packaging remain explicit
boundaries; root `LockEvent` is a native projection adapter.

Verification uses Rust `1.98.1`, Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, and matched
`vstd = 0.0.0-2026-10-04-0306`. The local `crates/junco-core/vendor` helper snapshots retain
upstream executable sources/contracts from verus-bumpalo
`36c8e8723d767934a502fc1d9cea0ba49cff54ab` and hashconsius
`58ab05c67c34201fa25f27c443cb5b45bc3a6c00`, with dependency/provenance adjustments for
the matched vstd. This is local source delivery, not publication of a new remote revision.


## Fuzzing

Linux and macOS only. libFuzzer generates lock traces and checks the policy for panics and
no-surprise violations. It runs until it finds a crash or you stop it, so bound it when you just
want a smoke run:

```sh
cargo +nightly fuzz run lock_policy
cargo +nightly fuzz run lock_policy -- -max_total_time=60
```

Arguments after `--` go to libFuzzer. Crashing inputs are written to `fuzz/artifacts/`, and the
corpus accumulates in `fuzz/corpus/`.

Requires the nightly toolchain and `cargo-fuzz` (`rustup toolchain install nightly`,
`cargo install cargo-fuzz`). Windows is not supported: its linker needs an `/include:main`
workaround to find libFuzzer's entry point, and this repository does not carry one.

The same generator (whose `Agent` is only a numeric lock-test principal) feeds deterministic
no-surprise property tests against the independent oracle; these need only stable Rust:

```sh
cargo test --release --manifest-path fuzz/Cargo.toml --lib
```

CI (`.github/workflows/ci.yml`) runs them plus a 60-second libFuzzer smoke on Ubuntu and macOS.

## Benchmarking

Criterion covers ordinary history scaling, cold replay versus warm residual progress, and two
adversarial precompilation workloads. The static rule table is compiled once per evaluation case,
outside the timed check loop, matching the retained policy a long-lived validator reuses across
checks. The `lock_policy` bench decides repeatedly over unchanged per-length histories, so it
reports warm-progress latency:

```sh
cargo bench --manifest-path fuzz/Cargo.toml --bench lock_policy
cargo bench --bench progress -- --noplot
cargo bench --bench validator -- stress_growing_residual --noplot
cargo bench --bench validator -- stress_many_rules --noplot
```

### Growing-residual stress

The policy language is $\Sigma^* \cdot Read \cdot \Sigma^{w+1}$. On an all-read history shorter
than the required suffix, every derivative adds another candidate suffix to the residual DAG, and
precompilation stops at the 64-state per-rule budget. This is also a DFA-state-explosion family:
the complete automaton grows exponentially with $w$.

Historical same-host medians against `origin/main` at `684911c` follow. They predate the
shared-core extraction and are not a latency comparison for that extraction:

| Window | Main compile | Precompiled | Compile cost |
|---:|---:|---:|---:|
| 4 | 2.053 µs | 92.984 µs | 45.3× |
| 8 | 2.598 µs | 138.210 µs | 53.2× |
| 12 | 2.898 µs | 141.110 µs | 48.7× |

| History/window | Main check | Precompiled check | Speedup |
|---:|---:|---:|---:|
| 8 | 4.255 µs | 1.454 µs | 2.93× |
| 16 | 11.224 µs | 8.506 µs | 1.32× |
| 32 | 39.923 µs | 36.954 µs | 1.08× |
| 64 | 174.310 µs | 166.650 µs | 1.05× |

The fixed state budget keeps window-8 and window-12 construction near 140 µs rather than following
the full exponential state space. Uncompiled frontier states use the exact transition-DAG path.
The benefit narrows as a longer measured path leaves the precompiled frontier.

### Many-rule stress

Every rule has the same matching head and a distinct absent principal witness. A 64-event history
therefore forces every rule to scan the complete nonterminal history; no rule can short-circuit the
rest of the policy table.

| Rules | Main compile | Precompiled | Compile cost | Main check | Precompiled check |
|---:|---:|---:|---:|---:|---:|
| 1 | 1.663 µs | 4.180 µs | 2.51× | 1.884 µs | 1.869 µs |
| 16 | 13.492 µs | 53.858 µs | 3.99× | 28.462 µs | 28.574 µs |
| 64 | 51.575 µs | 216.860 µs | 4.20× | 115.380 µs | 113.080 µs |
| 256 | 214.730 µs | 897.250 µs | 4.18× | 461.540 µs | 454.200 µs |
| 1,024 | 1.018 ms | 4.170 ms | 4.10× | 1.851 ms | 1.859 ms |

Compilation and evaluation remain linear in rule count. Precompilation costs about 4× at large rule
counts; steady evaluation is unchanged within roughly 2%. The runtime retains the existing
equal-event fast path before minterm classification, preventing a regression on repeated history
events.

These figures use 10 Criterion samples, a one-second warmup, and a three-second measurement window
on the documented Azure development host. They are regression evidence, not portable latency
claims. The HTML report is written to `fuzz/target/criterion/report/index.html`.
