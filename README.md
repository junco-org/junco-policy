# junco-policy

Capability validation for Junco, written in Rust. It owns the git trace policy: the rule table, its
no-surprise oracle, and the harness that both the fuzzer and the benchmark drive.

## Policy analysis

`PolicyAnalyzer` answers questions about rule tables without running them on histories:

- `redundant(rule, policy)`: whether the policy's other rules deny everything `rule` denies;
- `at_least_as_strict(stricter, than)` and `covered(rule, by)`: whether one rule set denies
  everything another denies;
- `never_fires(rule)` and `always_fires(rule)`: rule vacuity;
- `tail_included(head, left, right)`: inclusion between two tails for every candidate the head
  matches.

Each question holds for every candidate, not just one: tails that compare history events with the
candidate's components are decided for all values of those components. A failed question returns a
concrete candidate and history that can be replayed through `TracePolicy`. `GitPolicy::rules()`
exposes the git table for analysis.

Every query searches breadth-first for a counterexample. Per state it branches over finitely many
classes of events, splitting on how the candidate compares with constants. `SearchOptions` selects
the derivative engine:

- `Strategy::Residual` (default) derives one Boolean formula over residual states for
  `left ∧ ¬right`. Intersection and complement stay Boolean at every step; concatenation attaches
  its suffix to whole conjunctive cubes so that their members share one split point. States are
  canonical BDDs, and `Subsumption::Implication` skips states implied by visited ones.
- `Strategy::Antichain` explores partial derivatives of `left` against subset-construction states
  of `right`, with intersections and complements below the root advanced by junco's Brzozowski
  derivatives, and skips states that a syntactic term simulation shows subsumed.
- `Strategy::Brzozowski` determinises `left ∩ ¬right` with junco's derivatives: a baseline.
- `Strategy::Simple` also determinises `left ∩ ¬right` by Brzozowski derivatives, but in its own
  expression syntax. Only local smart constructors simplify it (flat, sorted, deduplicated `∪`
  and `∩` with their units, absorbers and complementary pairs; `¬¬x = x`; `ε` and `∅` factors of
  binary concatenations; trivial stars), which is enough to keep every expression's derivatives
  finite. States are compared by identity only, so its counterexamples are shortest.

`Alphabet::Minterms` enumerates truth assignments instead of building letters directly, for
comparison. `tests/inclusion.rs` checks every configuration against an independent reference
semantics on random tails, and checks the simple strategy's counterexamples against the shortest
ones found by brute force.

## Fuzzing

Linux and macOS only. libFuzzer generates git traces and checks the policy for panics and
no-surprise violations. It runs until it finds a crash or you stop it, so bound it when you just
want a smoke run:

```sh
cargo +nightly fuzz run git_policy
cargo +nightly fuzz run git_policy -- -max_total_time=60
```

Arguments after `--` go to libFuzzer. Crashing inputs are written to `fuzz/artifacts/`, and the
corpus accumulates in `fuzz/corpus/`.

Requires the nightly toolchain and `cargo-fuzz` (`rustup toolchain install nightly`,
`cargo install cargo-fuzz`). Windows is not supported: its linker needs an `/include:main`
workaround to find libFuzzer's entry point, and this repository does not carry one.

The same generator feeds two deterministic checks that need only stable Rust and a C compiler
(libgit2 is built from source):

```sh
# no-surprise property tests over the modelled repository
cargo test --release --manifest-path fuzz/Cargo.toml --lib
# replays every granted operation against scratch repositories through libgit2
cargo test --release --manifest-path fuzz/Cargo.toml --test git_oracle
```

The replay covers 32 fixed traces plus 16 freshly seeded ones per run. A failure prints the seed
and retains the scratch repository; `JUNCO_FUZZ_SEED=0x… cargo test …` replays the exact traces.

CI (`.github/workflows/ci.yml`) runs both plus a 60-second libFuzzer smoke on Ubuntu and macOS.

## Benchmarking

Criterion covers ordinary history scaling plus two adversarial precompilation workloads. The static
rule table is compiled once per evaluation case, outside the timed check loop, matching the retained
policy a long-lived validator reuses across checks:

```sh
cargo bench --manifest-path fuzz/Cargo.toml --bench git_policy
cargo bench --bench validator -- stress_growing_residual --noplot
cargo bench --bench validator -- stress_many_rules --noplot
```

### Growing-residual stress

The policy language is $\Sigma^* \cdot Read \cdot \Sigma^{w+1}$. On an all-read history shorter
than the required suffix, every derivative adds another candidate suffix to the residual DAG. The
white-box test asserts that its structural node count increases after every measured event and that
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
