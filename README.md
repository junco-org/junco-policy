# junco-policy

Capability validation for Junco, written in Rust. It owns the ownership-lock trace policy: the rule
table, its no-surprise oracle, and the harness that both the fuzzer and the benchmark drive.

## Lock policy

`LockPolicy` decides four actions per resource. `read` always grants and takes the last-reader
claim. `edit` acquires ownership; `release` relinquishes it and keeps the reader claim; `remove`
(an observed successful deletion) clears both claims. `edit` and `remove` are denied while another
principal owns the resource or last read it; `release` is denied only while another principal owns
it. Releasing an unowned resource grants.

## Events and history

Rules and validators are generic over a caller-chosen `Event`: a compact `Copy` value projecting
to principal, action, and resource. Callers use their own enums or finite Frunk `Coprod!` unions of
payload structs; `LockEvent<P, R>` is the built-in event of `LockPolicy`. Identities are caller IDs
with `Display` labels kept outside the evaluator, and equality is the event's full value equality.

Committed history is a tracked `History` owner. Each runtime rule keeps an LRU of 16 evaluated
residuals keyed by history owner and candidate bindings, so a decision over an unchanged or
append-extended history folds only the new suffix; any truncation or rollback invalidates that
owner's cursors. `Validator::permits` evaluates without appending.

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

The same generator feeds deterministic no-surprise property tests that need only stable Rust:

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

Same-host medians against `origin/main` at `684911c`:

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
