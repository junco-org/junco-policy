# Checking the proofs

Junco's runtime monitor and its policy analyzer are written in Rust and verified with Verus
against the denotational semantics of the paper. This guide says what is proved, under which
assumptions, what is trusted, where each result of the paper is mechanized, and how to re-run
the proofs. Paths are relative to the repository root.

## What is proved

All statements are over real events `E` and are stated in six interface files, which a reader
can check against the paper without reading the proofs:

| File | Defines |
|---|---|
| `crates/history-syntax/src/spec/events.rs` | what an event is: arity, projections, the rule syntax views |
| `crates/junco-core/src/spec/semantics.rs` | the paper's semantics: head matching, tests, tail languages, rule and policy violation |
| `crates/junco-core/src/spec/questions.rs` | the analysis questions (coverage, refinement, tail inclusion) and symbolic counterexamples |
| `crates/junco-core/src/spec/hypotheses.rs` | the assumptions on an event type |
| `crates/history-semantics/src/spec/monitor.rs` | what each monitor call does |
| `crates/history-analysis/src/spec/analyzer.rs` | what each analyzer query returns |

`docs/verification/INTERFACES.md` lists their definitions. The theorems below are restated as
Verus clients of these files in `crates/history-semantics/tests/reviewer.rs` (monitor) and
`crates/history-analysis/tests/reviewer.rs` (analyzer), which use public items only.

**Monitor.** For a policy $P$ (a sequence of rules), committed history $u$ and request $e$,
`Validator::check` returns one of:

- *grant*: no rule of $P$ is violated by $e$ after $u$, and the history becomes $u\,e$;
- *denial*: the history stays $u$, and the denial carries the index and mode of the first rule
  of $P$ that $e$ violates after $u$;
- *an error*: the history stays $u$, and the error is one of a fixed set of resource kinds
  (`resource_error`: graph budget or index overflow, or allocation, arena, identifier, revision
  or configured-limit exhaustion), never an input, unknown-identifier, ownership or invariant
  error.

The contract restricts the kind of error but does not prove that a resource was exhausted:
allocation failures come from trusted wrappers that may fail at any time, and each rule has a
fixed 100 KiB graph budget.
Every state reached by `check` and `rollback` from a new validator is trace safe: each committed
event was permitted by every rule against the history before it (`theorem_trace_safe`).
`Validator::permits` answers the same question without committing.

**Analyzer.** `PolicyAnalyzer` holds rules and, optionally, finite domains declared for some
event components. Its four queries answer, for every candidate and history inside the declared
domains:

| Query | Question |
|---|---|
| `tail_included(head, left, right)` | for every candidate matching `head`, is every history in `left` also in `right`? |
| `covered(rule, by)` | do the rules `by` deny every request that `rule` denies? |
| `redundant(rule, policy)` | does removing `rule` from `policy` change no decision? |
| `at_least_as_strict(p, q)` | does policy `p` deny every request that policy `q` denies? |

Each query terminates and returns `Holds`, a counterexample, `Exhausted`, or an error.

- `Holds` implies the property, with no further assumption.
- A counterexample is a candidate and a history whose values are constants or *fresh* values,
  meaning values distinct from every constant the analyzer knows. Every way of choosing the fresh
  values gives a real failure of the property. Fresh values occur only at components without a
  declared domain. A counterexample has such an instance, and so refutes the property, whenever
  each undeclared component has enough values besides the known constants; every infinite type
  does (`theorem_counterexample_has_instance`).
- A counterexample has a shortest history: among all counterexamples for `tail_included`; among
  the counterexamples whose candidate agrees with it on every known constant for the other
  queries; for `at_least_as_strict`, among those the same rule of `q` denies.
- The contracts make no claim about `Exhausted` (the implementation returns it when a search or
  compilation exceeds the graph budget). For identifiers the analyzer issued and well-formed,
  correctly tagged rules of the event's arity, an error is one of the resource kinds above; adding
  such a rule never fails with an input error. So if the property fails, a query that returns
  neither `Exhausted` nor an error returns a counterexample.

Rule vacuity (a rule that denies nothing, or denies every request its head matches) is decided
with `at_least_as_strict` (`theorem_vacuity_corollaries`). If `at_least_as_strict(p, q)` returns
`Holds`, a monitor for `q` permits every request inside the domains that a monitor for `p`
grants (`theorem_analyzer_to_monitor`).

**The paper's theorems.** `crates/history-semantics/src/verify/paper.rs` maps each result of
Sections 4 and 5 to its mechanized statement and proof, and `theorem_paper_index` proves them; the
analyzer's guarantees above are proved in `history-analysis`. The
executable code is verified against these statements: the derivative (`derivative_correct`) and
history fold (`residual_folds`) of the monitor, and the analyzer's search (`Search::run` ensures
`search_result`, which states Theorem `thm:search` for every answer other than `Exhausted`).

## Assumptions

- **Event types.** Every guarantee about a type `E` assumes `event_obligations::<E>()`: the
  projections are tagged with their component, the arity is between one and eight, every tuple
  of component values is an event, and component equality (as computed by `Eq`) is an
  equivalence that hashing respects. For the built-in tuple events (for example `(u32, u64)`) all
  of this is proved except the hashing law (`theorem_event_obligations_u32_u64`). The event types
  of the root crate and the benchmarks implement `Event` by hand in unverified code, so these
  laws are assumed for them.
- **Hashing.** `hash_coherent` (hashing respects equality) is an uninterpreted hypothesis. Five
  axioms state it for the analyzer's internal key types. The successor cache's trusted contract
  separately assumes that the derived hashing of its key type agrees with its equality.
- **Declared domains.** Analyzer results hold for requests and histories inside the declared
  domains; the monitor does not check membership. A declared domain must be nonempty.
- **Capacity.** Creating an analyzer, adding a rule and `tail_included` require that the
  constants fit the analyzer's 32-bit identifiers.
- **Toolchain.** Verus, Z3 and Rust at the versions below.

## What is trusted

`TRUST.md`, generated by `scripts/trust-scan.sh`, lists every place where a fact is assumed
rather than proved. There are no `admit`s or `assume`s. In the five crates it counts 19
`assume_specification`s for the standard library and `smallvec` (tested against the real
implementations by `scripts/spec-check.sh`), 70 `external_body` items at native boundaries
(interior-mutable tables, caches, callback adapters, hash-map wrappers), the five key axioms,
38 uninterpreted specification functions for native identities and views, 16 claims about
derived equality, and two iterator constructors whose termination is unchecked. The verified
helper crates `verus-bumpalo` and `hashconsius` add 17 items, listed separately. No algorithm of
the compiler, normalizer, derivative, matcher, evaluator or search is trusted. The root crate
(`src/`), which provides the lock and flow policies used in the evaluation, is not verified: it
calls the verified decision procedures and commits events itself.

## Differences from the paper

1. Events share one component type tagged with the coordinate, instead of a product of domains;
   `views_surjective` makes the two readings equivalent.
2. Rule variables are named and scoped rather than positional.
3. Equality of components is the type's specification-level equality (`eq_spec`).
4. Policies are sequences, and the monitor reports the first violated rule in source order.
5. The analyzer covers `require` rules as well as `forbid` rules, through the complement of the
   tail.
6. Declared finite domains are supported in addition to infinite domains.
7. Every search may stop with `Exhausted` at its graph budget; the paper's search always answers.
8. Refinement is reduced rule by rule, splitting each rule's head on the other policy's constants
   (`stmt_refines_iff_covers`, `stmt_policy_reduction`), without appending the candidate event as
   Proposition `prop:policy` does.
9. The implementation splits a compared component into one case per undecided constant and one
   case different from all of them, a coarser partition than $\mathrm{Split}$; the theorems hold
   for every partition with the properties of `def:split`.
10. The implemented simulation applies a subset of the rules of Figure `fig:simulation`.
11. Lemmas `lem:succ` and `lem:uniform` are one statement over successor cases
    (`stmt_successor_cases`); the implementation's cases are proved correct by
    `lemma_emitted_steps`.
12. The normalizing constructors are verified directly against the language of the expression
    they build, rather than through the paper's similarity relation.

## How to run

| Component | Version |
|---|---|
| Verus | release `0.2026.10.04.426d8b0` (`verus-0.2026.10.04.426d8b0-x86-linux.zip`, sha256 `624018662868563a7bec0dd07be5e4dd0c3d61124b4b55105765884bf2d4d1a0`) |
| Z3 | `4.16.0` (`z3-4.16.0-x64-glibc-2.39.zip`, sha256 `7288c49a5bd6dbafd7b0b0d1f65956b91672da24b08f09242919af159be3418e`) |
| Rust | `1.98.1-x86_64-unknown-linux-gnu` with components `rustc-dev` and `llvm-tools` |
| vstd | `0.0.0-2026-10-04-0306`, pinned in `Cargo.lock` |
| Platform | Linux x86-64 |

The quickest route is the `Dockerfile`, which installs exactly these versions:

```sh
docker build -t junco .
docker run --rm junco                    # verify every configuration
docker run --rm junco cargo verus verify --locked -p history-analysis \
    --no-default-features --features runtime,std --test reviewer
```

Without Docker:

```sh
rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu --profile minimal \
    --component rustc-dev --component llvm-tools --component rustfmt

# Download Verus and Z3, check their sha256, and verify every configuration.
scripts/verify-all.sh --download ~/junco-tools

# Or use an installed toolchain.
VERUS_DIST=/path/to/verus-x86-linux VERUS_Z3_PATH=/path/to/z3 scripts/verify-all.sh

# Print the commands without running them; pass arguments to Verus.
scripts/verify-all.sh --list
scripts/verify-all.sh -- --num-threads 8

# Tests, and the trusted-base inventory.
cargo test --locked --workspace --features junco-policy/test-util
scripts/trust-scan.sh > TRUST.md
```

Verus's memory use grows with the thread count; keep it near the number of cores when memory is
limited (with 16 threads on a 7 GB machine the verifier was killed with `SIGKILL`).

Expected results (each run also verifies the package's verified dependencies; the `--test` rows
count the client theorems only):

| Configuration (`cargo verus verify --locked ...`) | Verified, errors |
|---|---|
| `-p history-syntax --no-default-features` | 60, 0 |
| `-p history-syntax --features serde,std` | 60, 0 |
| `-p junco-core --no-default-features` | 204, 0 |
| `-p junco-core --features runtime,std,serde` | 288, 0 |
| `-p history-store --no-default-features --features runtime` | 289, 0 |
| `-p history-store --features runtime,std` | 289, 0 |
| `-p history-semantics --no-default-features --features runtime` | 1618, 0 |
| `-p history-semantics --features runtime,std,cache` | 1623, 0 |
| `-p history-semantics --features runtime,std,cache --test public_specs` | 19, 0 |
| `-p history-semantics --features runtime,std,cache --test reviewer` | 9, 0 |
| `-p history-analysis --no-default-features --features runtime` | 601, 0 |
| `-p history-analysis --no-default-features --features runtime,std` | 601, 0 |
| `-p history-analysis --no-default-features --features runtime,std --test reviewer` | 18, 0 |
