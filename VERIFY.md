# Checking the mechanized proofs

This is the current reviewer guide. Read the six public semantic surfaces below, the
[checked paper index](crates/history-semantics/src/verify/paper.rs), and the two public
reviewer clients. [TRUST.md](TRUST.md) is the generated trust inventory. Historical design
notes in [docs/history](docs/history/) are evidence of earlier snapshots, not current contracts.

## Reproduce

Pinned versions: Verus `0.2026.10.04.426d8b0`, Rust
`1.98.1-x86_64-unknown-linux-gnu` (with `rustc-dev` and `llvm-tools`), Z3 `4.16.0`,
and vstd `0.0.0-2026-10-04-0306` from `Cargo.lock`. The driver and
[CI](.github/workflows/ci.yml) pin the release assets and SHA256 digests.

```sh
# Install the pinned release assets, then run all configurations.
scripts/verify-all.sh --download ~/junco-tools -- --num-threads 64

# Existing installation; original eleven configurations followed by two reviewer targets.
VERUS_DIST=/path/to/verus-x86-linux VERUS_Z3_PATH=/path/to/z3 \
  scripts/verify-all.sh -- --num-threads 64

# Print commands without verification (still checks the toolchain).
scripts/verify-all.sh --list

# Optional selection and persistent independent Cargo target directories.
scripts/verify-all.sh --jobs 1 --target-root /path/to/targets \
  --only '--test reviewer' -- --num-threads 64

cargo verus verify --locked -p history-semantics --features runtime,std,cache \
  --test reviewer -- --num-threads 64
cargo verus verify --locked -p history-analysis --no-default-features \
  --features runtime,std --test reviewer -- --num-threads 64
```

The default driver remains sequential; `--jobs`, `--target-root`, and `--only` are
retained. Divide available threads between concurrent jobs; lower the thread count on
memory-constrained hosts. Module/function filtering uses `cargo verus focus`, not `verify`.
The driver fetches locked dependencies and reports verified/error counts per configuration.
Native tests are distinct evidence from Verus proofs. CI also runs workspace/fuzz tests,
formatting, clippy, and `scripts/spec-check.sh`. The latter exercises assumed std/smallvec
contracts against real implementations; it is not a proof of those assumptions.

## Verification evidence baseline

This is a **source-reported pre-reviewer baseline**, not a verification run performed while
editing this guide. Full-feature figures were reported by the integration owner at
`92f4e9d`/`e525e20`; syntax was cached from the same source. The no-default figures are
from an earlier foundation snapshot before final Track F additions. They are deliberately
not represented as a completed current thirteen-configuration gate. The integration owner
replaces this table with final observed results after integration.

| Configuration (`cargo verus verify --locked ...`) | Reported baseline |
|---|---|
| `-p history-syntax --no-default-features` | 63 verified, 0 errors; earlier foundation |
| `-p history-syntax --features serde,std` | 63 verified, 0 errors; same-source cached |
| `-p junco-core --no-default-features` | 239 verified, 0 errors; earlier foundation |
| `-p junco-core --features runtime,std,serde` | 323 verified, 0 errors |
| `-p history-store --no-default-features --features runtime` | 303 verified, 0 errors; earlier foundation |
| `-p history-store --features runtime,std` | 306 verified, 0 errors |
| `-p history-semantics --no-default-features --features runtime` | 1641 verified, 0 errors; earlier foundation |
| `-p history-semantics --features runtime,std,cache` | 1646 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache --test public_specs` | 21 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime` | No current figure supplied |
| `-p history-analysis --no-default-features --features runtime,std` | 626 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache --test reviewer` | Final integration result not yet recorded |
| `-p history-analysis --no-default-features --features runtime,std --test reviewer` | Final integration result not yet recorded |

The same handoff reports 198 workspace tests across 25 suites, two explicit instrumentation
counter tests, eight fuzz tests, and workspace/fuzz formatting and clippy passing; spec-check
reported 18 passing earlier at the same reduced assumed-spec boundary. These are historical
reported observations, not newly exercised checks or final reviewer-target evidence.

## Reviewer map and semantic definition counts

Count one explicitly public `spec fn` declaration in each named file, including public
closed `wf` methods and the uninterpreted `hash_coherent` declaration. Count helpers as well
as top-level propositions; do not count proof/exec functions, struct/enum/type declarations,
trait-spec methods without explicit `pub`, `View::view`, imports, or reexports. Thus these
are reproducible source-surface counts, **not verified-function counts** or a claim that a
reviewer must unfold every helper. At the integrated source baseline the counts are:

- **R1 — 6:** [events.rs](crates/history-syntax/src/spec/events.rs): `arity`, `event_view`,
  `well_tagged`, `projection_laws`, `surjectivity`, `event_laws`. This file also defines
  structural head/test/regex/rule views and Event/Arity trait specifications.
- **R2 — 12:** [semantics.rs](crates/junco-core/src/spec/semantics.rs): head matching,
  variable resolution, tests, whole-history `lang`, rule/policy denial, least violation,
  and head/test/regex/rule/borrowed-tail well-formedness.
- **R3 — 38:** [questions.rs](crates/junco-core/src/spec/questions.rs): 12 constant-context
  collectors; domains and six policy questions/removal operations; symbolic shape, known
  bounds, fresh names/capacity, real-event instances, profile/minimum predicates, and
  `coordinate_embedding`. Capacity lemmas are proof functions and excluded.
- **R4 — 5:** [hypotheses.rs](crates/junco-core/src/spec/hypotheses.rs): `eq_equivalence`,
  `hash_coherent`, `key_laws`, `monitor_hypotheses`, `analyzer_hypotheses`.
- **R5 — 12:** [monitor.rs](crates/history-semantics/src/spec/monitor.rs): opaque `wf`,
  ordered selection and decision specs, frame, check/permits/rollback/finish/registration,
  rollback-prefix observation, and `trace_safe`.
- **R6 — 11:** [analyzer.rs](crates/history-analysis/src/spec/analyzer.rs): opaque `wf`,
  semantic vocabulary size, rule-id projection/selection/validity, frame, escapes, and
  four query specifications. Public revealing lemmas connect native results/views without
  exposing codebooks, owner state, or allocator internals.

**P:** [paper.rs](crates/history-semantics/src/verify/paper.rs) is the actual **13-row**
public index, in paper-table order: language definition, one-step derivative, symbolic run,
matcher, similarity, finite residuals, alternative policy reduction, redundancy/vacuity,
decomposition, successors/uniformity, pruning, simulation soundness, and inclusion search.
Its adjacent `stmt_*`/`theorem_*` pairs, not historical tables or stale line anchors, are
the authoritative mapping. The policy row is explicitly an alternative to Proposition 5.2.

**T:** [monitor reviewer client](crates/history-semantics/tests/reviewer.rs) and
[analyzer reviewer client](crates/history-analysis/tests/reviewer.rs) consume only public
interfaces; [public_specs](crates/history-semantics/tests/public_specs.rs) retains the
lower-level public lifecycle/ownership clients. Reviewer theorem names:

- Monitor: `theorem_u8_hash_only_hypotheses`, `theorem_u32_hash_only_hypotheses`,
  `theorem_monitor_check_trace_safety`, `theorem_monitor_permits`.
- Analyzer: `theorem_covered`, `theorem_redundant`, `theorem_at_least_as_strict`,
  `theorem_tail_included`, `theorem_public_construction`,
  `theorem_declared_domain_monitor_bridge`, `theorem_s1_undeclared_finite_enum`;
  helper `lemma_declared_coordinate_zero`.

The S1 client registers an actual bool-variable target with false/true covering heads
and a singleton declared domain for the other coordinate. A returned counterexample
must fail fresh capacity specifically at the undeclared bool coordinate.

## Meaning of the guarantees

### Monitor

For real candidate `e`, committed history `h: Seq<E>`, and source rules in registration
order, `check` grants only if no rule is violated and appends exactly `e` with the request
metadata. Denial selects the least violated rule and leaves history unchanged. Error also
leaves history unchanged and is not `HistoryError::Invariant`. `permits` does not append:
a successful Boolean is exactly the absence of policy denial. Frames preserve source rules.
`finish` starts with empty history; successful owned rollback restores a prefix.
`trace_safe` states that every committed event was permitted by every rule against its own
strict prefix. Public `wf` consequences and append/prefix lemmas expose this safety without
revealing storage representation. A direct history append is not automatically a monitor
permission proof.

### Analyzer: A1–A6

All questions quantify over **real events**, with both candidate and every history event
inside declared domains. `Holds` soundness is unconditional on fresh capacity. A symbolic
counterexample always has well-formed shape, bounded known constants, and **every admissible
real-event instance** witnesses failure. Existence of an instance and explicit negation of
the queried property additionally require `counterexample_capacity` for that very result.
Consequently the non-Exhausted `Holds iff property` reading is conditional on capacity in the
counterexample branch, not an unconditional completeness claim for finite carriers.

- **A1/A2, covered:** a rule denial implies a covering-policy denial. An instance of a
  counterexample violates the selected rule and no covering rule.
- **A3, strictness:** `at_least_as_strict(P,Q)` means **Q denies implies P denies**, equivalently
  **P permits implies Q permits**. A counterexample is denied by a selected rule of Q and
  permitted by P. Redundancy checks coverage by the id-filtered policy.
- **A3, removal:** all occurrences of the target **id** are removed; arbitrary input order
  and duplicate ids are supported. Another id for the same source remains distinct. Holds
  preserves every decision after removal. A present-target counterexample changes a decision;
  an absent target retains coverage meaning and is not claimed to change a target-free policy.
- **A4, tails:** under a matching well-formed head, left membership implies right membership.
  Refutation instances satisfy left and not right. The returned history-length bound is
  global for this single inclusion. Domains and registered rules are unchanged.
- **A5, escapes/termination:** unit `Exhausted` makes **no claim**. It is not certified evidence
  that a byte budget was exceeded: budget and index/product overflow paths must not be
  confused with a theorem about a result's provenance. Errors exclude invariant failure,
  not all invalid-input/allocation/resource failures. Verified executable termination uses
  the finite reachable-item bound discharged for the implemented normalizer/search.
- **A6, minimum:** policy counterexamples have minimum history length **within their returned
  constant profile/split case**, not globally and not per rule across cases. Strictness uses
  the **same selected Q rule j** for correctness and the profile minimum. These are the exact
  PR #10 clauses integrated from `52118c4` through `0f40cb6`, not a stronger reinterpretation.

`Counterexample.known[i]` is bounded by literals of **all registered rules plus declared
domain values**; tail queries use their head, both tails, and domains. It is erased semantic
output, not a public historical codebook. Fresh capacity counts distinct names actually
used at each coordinate, with tag-correct, injective choices outside known equality classes.
An undeclared finite coordinate does not imply infinity: the finite-enum regression permits
Holds or a counterexample whose capacity fails at that coordinate, never a capacity-satisfying
refutation of a property true of all real events. No Event cardinality hook is required.

### Domain transfer to monitoring

Declared domains are assumptions on runtime inputs, not monitor checks. Analyzer-to-monitor
transfer requires the candidate **and every history event** to satisfy them. Under those
conditions coverage/strictness uses the same R2 denial as `Validator::permits`/`check`.
Outside-domain results make no runtime guarantee. Empty declared domains are rejected, not
used to obtain vacuous Holds results. Undeclared domains mean all correctly tagged values,
including finite carriers.

## Hypotheses and trust

R4's monitor bundle requires arity 1–8, faithful native projections, correctly tagged
projections, and component key laws: native equality obeys `eq_spec`, modeled equality is
reflexive/symmetric/transitive, and `hash_coherent` supplies stable coherent hashing and
faithful external-container behavior. The analyzer adds surjectivity: every well-tagged
tuple is some real event. Surjectivity is deliberately not required for monitor soundness.
Rules require scoped variables, correct arity and correctly tagged literals; borrowed tail
queries require the corresponding head/tails well-formedness. Stateful calls use opaque
`wf`; native rule ids are owner checked, and semantic index validity does not replace that
runtime check. Allocation and vocabulary/index limits remain fallible, not hidden assumptions
of infinite resources. Abstract successor/search theorems also state component-local atoms,
valid starting constraints and the finite-items termination premise; implementation links
discharge these for the executable search. No obsolete `infinite_type` premise is needed.

`lemma_u8_event_hypotheses` for `(u8,u8,u8)` and `lemma_u32_event_hypotheses` for
`(u32,u8,u8)` prove every non-hash conjunct from the verified tuple/equality implementation.
Each assumes **only `hash_coherent` for its tagged Component3 type**. No primitive-key or
component-compositional hash axiom is claimed. The five approved internal key introductions
are for Constraint, `(ConstraintId,RegexId)`, `(RegexId,RegexId)`, `(TestId,TestId)` and
`SmallVec<[RegexId;4]>`; they are trusted library facts, not user preconditions.

Besides Verus/vstd, Z3 and Rust, [TRUST.md](TRUST.md) inventories assumed std/smallvec
contracts, external native containers/locks/records/reservation/callback adapters, external
type/trait specifications, uninterpreted tokens, ignored derive claims, unchecked termination,
and unverified public execution candidates. It includes pinned `verus-bumpalo` and
`hashconsius` source inventories and successor LRU cache leaves. No analysis algorithm is
trusted. `Hash`/`Eq` panic, caught unwind, re-entry after panic, and unsafe client corruption
are out of scope; no poisoning/recovery theorem is claimed.

**Arc identity is restricted:** pinned Verus models Arc/reference values by referents; generic
Arc injectivity is false and is not assumed. Internal store identity relies on private,
non-Clone/non-Copy store construction, authoritative never-recycled ids and linear birth
resources; Arc clones share the owner allocation. The audited wrappers are restricted to
these live-owner invariants, not arbitrary user Arc values.

**Root `RulePolicy` is unverified glue:** `could_fire` filtering, per-event `TracePolicy`
construction, decide-then-append, audit-mode denied-event append, and error-to-deny conversion
are outside `Validator::check`'s theorem. Root custom Event projections additionally need
R1/R4 laws; analyzer use adds surjectivity. Benchmarks no longer enable test-util by default;
explicit instrumentation/replay-probe tests remain native evidence, not new verifier configs.

## Differences from the paper and paper-change checklist

No paper files are changed here. The following are scope qualifications, not claims that the
paper's stronger statements were mechanized:

1. Code uses one tagged component type instead of product domains; R1 hides this encoding
   behind real-event projections/surjectivity. Arity is 1–8. Named variables are scoped to
   head coordinates; equality is quotiented by `eq_spec`, not Rust value identity. Numeric
   candidate values fit `u64`; constant ids fit `u32`.
2. Both Forbid and Require rules are supported; Require denies the complement of tail
   membership. Candidate bindings do not append the candidate to the checked history.
3. Declared finite domains restrict analysis and transfer only under the runtime domain
   assumption above. Capacity qualifies refutation existence, not Holds soundness.
4. `GRAPH_BYTES` resource bounds and unit/no-claim Exhausted differ from an always-answering
   decision procedure. Policy queries stop at the first non-Holds case; Exhausted can hide
   a later refutation. State completeness only modulo capacity, exhaustion and errors.
5. **Proposition 5.2 (`prop:policy`) is not mechanized.** The implementation instead reduces
   refinement rule by rule to coverage, splits head constraints on constants, and checks
   constrained inclusion against firing denial tails in each case. The exact firing theorem
   and policy-search composition are genuine execution links, not an appended-candidate Den
   encoding. Section 5 should state this alternative procedure and one query per rule/case.
6. Vacuity has R3 refinement equivalences (empty policy / same-head universal forbid), not
   new executable never/always entry points. Redundancy uses the id/multiset interpretation.
7. Policy minimum means shortest within the returned case/profile; tail inclusion retains
   its single-query global history-length bound. Do not say global/per-rule policy minimum.
8. **Implemented simulation is soundness-only** relative to its `sim_step`/`test_step` rules.
   The paper's larger lifted-test relation is not decided by the code; lifted SumL/AndR
   rules are restricted to test/test cases. Do not describe this as merely “more rules” or
   relaxed side conditions. The paper should say sound and terminating, not decides its figure.
9. Successor/uniformity theorems specify semantic case families including partition properties,
   not Algorithm `alg:succ` itself. `lemma_emitted_steps` is the executable link. Pruning
   lookup implements a sound subset; required subsets are enumerated only up to four operands.
10. Finiteness assumes the descriptive Model normalization/successor/bound contract, instantiated
    for the implemented normalizer, not similarity alone. Normalizing constructors are verified
    directly; symbolic derivative/run statements precede normalization.
11. Update the paper's thirteen-row mapping from P, names/labels, hypotheses, trust inventory
    and final measured counts. Keep the alternative-reduction and simulation qualifications.
    RegExLib uses declared finite domains; AgentDojo goes through the unverified root glue.
    Do not infer the evaluation path is covered by the atomic Validator theorem.

Historical “missing differential coverage/strictness/duplicate/absent-target/Alice–Bob tests”
findings are stale: these already exist and are not duplicated by this documentation change.
The old private monitor/analyzer vocabulary, unestablishable infinity premise, obsolete
`expansion_ok` citation and old count tables are not current reviewer contracts. The archived
handoffs contain superseded Exhausted/token and primitive/component-axiom proposals; current
R4/R6 and the qualifications above control. [INTERFACES.md](docs/verification/INTERFACES.md)
is a compact factual navigation inventory, not a pending transition plan.
