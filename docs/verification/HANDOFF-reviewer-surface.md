# Handoff: a reviewer-readable mechanization, and fixes from the spec audit

## Goal

Refactor the Verus mechanization so that a reviewer can judge every guarantee by reading **about
six files**, and fix the specification problems found by the audit. At the end, a reviewer must be
able to see, without reading anything else:

1. what the monitor and the analyzer guarantee, stated over real events;
2. under which hypotheses, all of them dischargeable and shown satisfiable for a concrete event type;
3. what is trusted;
4. which mechanized statement corresponds to which paper result.

The evidence for every problem, with file:line references, is in
`docs/verification/REVIEWER-SURFACE-PLAN.md` (the **plan**). This handoff says what to build, in
which order, and what can run in parallel. Item names below (R1–R6, P, T, S1–S13, D1–D4) refer to
the plan.

Do not edit the paper. Produce the list of paper changes as part of the final report.

## Target claims

**Priority 1 (required).**

- **Monitor theorem** (plan §4), stated in R5 over `Seq<Rule<E>>` and `Seq<E>`: each `check`
  returns Grant (no rule violated, history extended by the candidate), Denied (history unchanged,
  least violated rule), or an error (history unchanged, not an invariant failure); `permits`
  likewise. **Trace safety** corollary: every committed event was permitted by every rule against
  its prefix. Proved as a Verus client in `history-semantics/tests/reviewer.rs`.
- **Analyzer theorems** (plan §5, A1–A5), stated in R6 over real events and declared domains:
  - `covered`, `redundant`, `at_least_as_strict`, `tail_included`: when the result is neither
    `Exhausted` nor `Err`, `Holds` holds iff the property holds;
  - every counterexample has an instance, and every instance is a pair of **real events** in the
    domains that witnesses the failure;
  - `Holds ⇒ property` needs no infinity or capacity hypothesis;
  - `Exhausted ⇒` some search's graph charge exceeded `GRAPH_BYTES`;
  - `Err` is never an invariant failure; every call terminates.
  Proved as a Verus client in `history-analysis/tests/reviewer.rs`.
- **Hypotheses** (R4): one bundle per guarantee, defined once, `pub open`, documented. A reviewer
  test proves the bundle for one concrete event type (e.g. `Component3<u8, u8, u8>`) and one event
  type with a `u32` coordinate, from the axioms listed in `TRUST.md`.
- **Layout** (plan §2): R1–R6, P and T exist; every definition that a public `requires`/`ensures`
  mentions is `pub open` (or `pub closed` with `pub` revealing lemmas); old duplicates are deleted.

**Priority 2.** Paper index P with every paper result as a `stmt_*`; naming and hygiene (plan §8);
trusted-base scan extended (D3); benchmarks built from a verified configuration (D2).

**Priority 3.** D1 and D4 (evaluation path and hand-written event projections), as documented
decisions below.

## Repository

`git@github.com:junco-org/junco-policy.git`, branch `handoff/reviewer-surface`: `main` at `1efa267`
(merge of PR #9) plus the plan and this file. Work on a new branch from it. Read first: the plan,
`VERIFY.md`, `TRUST.md`, and `crates/history-semantics/src/verify/refinement/mod.rs`.

## Coordination with the per-rule minimality PR

A separate PR adding **per-rule** minimality of policy-query counterexamples is about to be opened
(plan S8). It is out of scope here.

- Do not edit the minimality predicates (`*_minimal`, `*_ok`, `shortest_in_case`, `same_profile`)
  or the modules that PR adds.
- The owner of `history-analysis/src/analyzer.rs` (track F) rebases onto that PR when it merges,
  and R6 restates its minimality `ensures` without weakening them. Whichever lands second adapts.
- If the PR changes `covered_with` or the verdict predicates, track B's bridge lemmas must be
  re-checked after the rebase.

## What already exists (do not re-prove)

| Fact | Where |
|---|---|
| Executable `covered`, `redundant`, `at_least_as_strict` ensure `*_correct`, `cex_has_instance`, `¬covers`/`¬refines`, `no_internal_error` | `history-analysis/src/analyzer.rs` (≈ l.475–547) |
| `P ⊑ Q` iff `P` covers every rule of `Q`; redundancy iff covered | `refinement/semantics.rs`: `stmt_refines_iff_covers`, `stmt_redundant_iff_covered` |
| Covering iff one constrained inclusion per split case; composition with search outcomes | `refinement/inclusion.rs`: `stmt_policy_reduction`, `stmt_policy_search_composition` |
| Exact firing test on split cases | `history-analysis/src/verify/policy_firing.rs`: `lemma_head_firing_exact` |
| Search correctness, termination, minimality per query; executable `search_result` | `refinement/search.rs`: `stmt_search_correct`, `stmt_search_terminates`; `history-analysis/src/verify/search_exec.rs` |
| Typed ↔ numeric rule denial; genericity; fresh-value choice | `refinement/encoding.rs`: `stmt_front_end_denies`, `stmt_numeric_genericity`; `refinement/semantics.rs`: `stmt_genericity`; `refinement/analyzer.rs`: `stmt_choice_exists`, `lemma_choice_exists_mixed` |
| Typed DSL ↔ flat ↔ numeric semantics | `junco-core/src/verify/flatten.rs`: `flattening_preserves_semantics`; `history-semantics/src/compile.rs`: `lemma_flat_regex` |
| Matcher theorems | `history-semantics/src/verify/history_algebra.rs`: `theorem_symbolic_derivative_correct`, `theorem_matcher_correct`, `theorem_rule_decision`, `theorem_not_fired` |
| Monitor step relation | `history-semantics/src/validator.rs`: `check_result`, `lemma_check_result_facts` |
| Monitor client proofs | `history-semantics/tests/public_specs.rs` |

Reuse these. Most of the work is restating them over the new surface and re-pointing bridges, not
new search or reduction proofs.

## Decisions (defaults; report any you had to change)

1. **Semantics over events (S1).** R2/R3 quantify over `E` and `Seq<E>` through `event_view`, not
   over `Seq<E::Component>`. R1 adds a surjectivity law (every well-tagged component tuple is the
   view of some event), proved for the built-in tuple and coproduct events. Counterexample
   instances choose well-tagged values (`tag(f[i](n)) == i` in `choice_ok`).
2. **Fresh values (S2).** Replace `infinite_type`/`unrestricted_components_infinite` by a
   per-coordinate, quantitative `fresh_capacity(domains, known, i, k)`. Counterexample clauses are
   conditional on capacity for the counterexample's own fresh count; `Holds` clauses are
   unconditional (genericity). Provide lemmas discharging capacity for `u8`…`u64` and `nat`
   coordinates when `k` is below the type's size minus the known constants.
3. **Exhausted (S5).** Split `HistoryError::GraphLimit` into a budget error and an index/product
   overflow error; `charge`/`projected` ensure `Err(budget) ⇒ charged + bytes > budget`; the
   analyzer maps only the budget error to `Exhausted`. Fallback, only if this proves
   disproportionate: rename the variant `Unknown`, document every source, and report it.
4. **Hypotheses (S4).** One `hash_coherent<K>` (`uninterp`, documented as the faithfulness of the
   `external_body` hash containers). Laws about library-internal key types (`Constraint`,
   `(ConstraintId, RegexId)`, `(RegexId, RegexId)`, `(TestId, TestId)`, `SmallVec<[RegexId; 4]>`)
   become trusted axioms, one per type, listed in `TRUST.md`, not preconditions. Add a
   `PartialEqSpecImpl` for `Component2/3/4` (and coproducts) so `eq_spec` is defined for them.
5. **Redundancy (S7).** `redundant` requires `policy.contains(rule)` and ensures "removing every
   occurrence of `rule` changes no decision" directly. Document the id/multiset reading.
6. **Vacuity (S10).** No new entry points. Prove in R3 that `never_denies(d, r) ⇔ refines(d, [], [r])`
   and `always_denies(d, r) ⇔ refines(d, [r], [forbid head(r) Univ])`, so vacuity goes through
   `at_least_as_strict`. Delete `never_fires_ok`/`always_fires_ok` and the false module header.
7. **Ownership (S11).** `RuleId` carries its analyzer's id; queries return an error on mismatch.
   Make `RuleRuntime::resume_cursor`/`advance_cursor` `pub(crate)` unless the root crate needs
   them, in which case tag `BatchCursor` the same way.
8. **Domains (S9).** `domains_wf` requires nonempty declared domains; `Domains::with_domain`
   rejects an empty set the way it already rejects ill-tagged values. R6 documents that verdicts
   transfer to the monitor only for events inside the declared domains, and T states that bridge.
9. **Evaluation path (D1).** Do not change benchmark behavior. Document `RulePolicy` (root crate)
   as unverified glue in `VERIFY.md` and `TRUST.md`, listing exactly what it adds (`could_fire`
   filter, per-event `TracePolicy`, decide-then-append, audit-mode append, error-to-deny).
10. **Clean cutover.** Old definitions are deleted once migrated; no aliases or re-exports of the
    old names.

## Required work

Each track lists its plan items, the files it owns, and its output.

### Track 0 — Interface freeze (blocks everything; one agent)

- Create R1–R6 as files containing only `spec` definitions with doc comments: event laws and
  surjectivity (R1); typed semantics over `E` (R2); policy questions, domains, counterexample
  instances, `fresh_capacity` (R3); hypothesis bundles and axioms as `uninterp`/`spec` (R4);
  public views `ValidatorView {rules, history}` and `AnalyzerView {domains, rules}`, one opaque
  `wf` each, and the target contracts as spec predicates (`check_step`, `covered_spec`,
  `redundant_spec`, `at_least_as_strict_spec`, `tail_included_spec`) (R5, R6).
- Do not delete or change existing definitions yet. The new files must verify (spec-only).
- Output: the files, plus a short `docs/verification/INTERFACES.md` listing each new definition
  and the old definitions it will replace. All later tracks code against these names.

### Track A — Hypotheses (S4; R4)

Files: `junco-core/src/spec/hypotheses.rs`, `history-store/src/typed.rs` (obligations only),
`history-store/src/typed/map.rs`, `history-analysis/src/native.rs`,
`history-analysis/src/verify/{search_exec,simulation_exec,prune_exec}.rs` (obligation definitions
only), `history-syntax/src/event.rs` (`PartialEqSpecImpl`), `junco-core/src/verify/encoding.rs`
and `history-analysis/src/verify/typed_numeric.rs` (equivalence duplicates).

- Merge the two `NativeMap`/`hash_coherent`/`key_obligations` copies into one module.
- Replace `native_obligations` and `analyzer_obligations` with the R4 bundles; make the analyzer
  bundle include `projection_laws`.
- Turn internal-key laws into listed axioms; remove them from public preconditions.
- Prove the bundle for the two concrete event types (lemma used by T).

### Track B — Typed semantics over events (S1, S2, S12; R1–R3)

Files: `history-syntax/src/spec/events.rs`, `junco-core/src/spec/{semantics,questions}.rs`,
`junco-core/src/verify/dsl.rs`, `history-semantics/src/verify/refinement/semantics.rs`, the
instance half of `refinement/analyzer.rs` (`choice_ok`, `admissible`, `every_instance`,
`cex_has_instance`, `stmt_choice_exists`), `history-analysis/src/verify/{policy_bridge,typed_numeric,reconstruction,verdict}.rs`.

- Prove the new R2 equal to the existing typed DSL on events (it is the same definition applied
  to `event_view`), then switch the analyzer's semantics to R3 and delete `rule_status`/`rule_denies`.
- Re-prove `stmt_genericity` for tag-preserving renamings; add the tag clause to `choice_ok`;
  replace `stmt_choice_exists` by a `fresh_capacity` version; prove the capacity lemmas.
- Make scoping and arity (`rule_wf`) part of every rule in the views; propagate
  "well-formed ⇒ no `HeadArity`/`ComponentCoordinate`" from `flatten.rs` (S12).
- Re-point the bridge lemmas so that today's `*_correct` follow for the new semantics.

### Track C — Exhausted and errors (S5; part of S13)

Files: `junco-core/src/error.rs`, `history-store/src/graph.rs`, `junco-core/src/{kernel,flat}.rs`
(error sites), `history-analysis/src/{constraint,tables,search}.rs` (error contracts only).

- Split the error; specify `charge`/`projected`; carry "budget exceeded" through `search`'s error
  contract. Rename `no_internal_error` → `no_invariant_failure` everywhere (mechanical; coordinate
  the rename with all tracks by doing it first in this track, in one commit).

### Track D — Monitor surface (R5; S13 monitor parts)

Files: `history-semantics/src/spec/monitor.rs`, `history-semantics/src/validator.rs`,
`compiled_rule.rs` (`least_violation`, `ordered_result` move to R2), `policy/{trace,evaluate,rule,atoms}.rs`,
`history-store/src/history.rs` (visibility of accessors only).

- `Validator` gets the public view and opaque `wf`; `check`, `permits`, `rollback`, `finish`,
  `add_rule` ensure R5 predicates; semantic and frame clauses separated.
- `TracePolicy`/`CompiledPolicy` use the same predicates (no inlined `least_violation`).
- `TraceRule::clone` ensures source equality; `forbid`, `principal_is`, `resource_is` require
  arity 3.
- Depends on track 0 and on track A's bundle name (use the track-0 placeholder until A lands).

### Track E — Paper index and hygiene (P; plan §7 code side, §8)

Files: `history-semantics/src/verify/paper.rs`, `history_algebra.rs`, `finite_states.rs`,
`finite_impl.rs`, `refinement/{search,pruning,finiteness}.rs`, comments only in
`refinement/inclusion.rs`. Must not edit `refinement/semantics.rs` or `refinement/analyzer.rs`
(track B) or `history-analysis/src/analyzer.rs` (track F).

- `paper.rs`: one `stmt_*` per paper result in paper order, with the paper label and proving
  `theorem_*`. Convert `history_algebra.rs` theorems to the `stmt_`/`theorem_` convention; rename
  `theorem_matcher_correct` → `theorem_symbolic_run_correct`.
- Rename the (N0)–(S6) contract conditions to the paper's names; drop the unused
  `n_unrestricted` hypothesis of `stmt_search_correct`; factor the `*_finite_domains` duplicates;
  replace `Set::new(..).unwrap_or(Set::empty())` in stated definitions.
- Delete `expansion_ok`; remove hard-coded line references from doc comments; rename the extra
  `lang`s (`flat_lang`, `numeric_lang`) and split `history_specs.rs` (numeric regex algebra vs
  error predicates).

### Track F — Analyzer surface (R6; S3, S6, S7, S9, S10, S11; integrates minimality)

Files: `history-analysis/src/analyzer.rs`, `history-analysis/src/verify.rs` (`frontend`),
`history-analysis/src/spec/analyzer.rs`, the verdict half of `refinement/analyzer.rs`,
`refinement/inclusion.rs` (vacuity statement only).

- Public view and opaque `wf`; `new` ensures `self@.domains == d@`; `Domains` constructors verified
  with postconditions; capacities over the public view with a growth lemma (S6).
- Entry points ensure the R6 predicates (A1–A5): unconditional `Holds`, capacity-conditional
  counterexamples, `Exhausted` meaning from track C.
- `tail_included` gets the same counterexample shape, ensures `domains`/`rules` unchanged, and
  requires or ensures `head_tails_wf` (S3).
- Redundancy, vacuity, domains, ownership per decisions 5–8.
- Depends on tracks A, B, C. Rebase onto the minimality PR when it merges.

### Track G — Trusted base and builds (D2, D3, D4, D1)

Files: `scripts/trust-scan.sh`, `TRUST.md`, root `Cargo.toml` and `fuzz/Cargo.toml`
dev-dependencies, `benches/`, `fuzz/benches/`, root crate `src/model.rs`, `src/policy/flow/mod.rs`,
`src/policy/agent/mod.rs` (event impls only).

- Extend the trust scan: proof axioms (`external_body` proof fns such as `singleton_invariants`),
  `uninterp` specs (flag the four with meaning), `obeys_*_spec = true` on `external_derive` types,
  unannotated public exec items, and the helper crates `verus-bumpalo`/`hashconsius` at their
  pinned revisions. List the successor LRU cache as a trusted leaf of the search.
- Build benchmarks without `test-util` (move work counters and fault injection to a bench-only
  crate or feature not enabled by benches), or add a `test-util` configuration to
  `scripts/verify-all.sh`; prefer the former.
- Derive the root crate's event types from the verified tuple/coproduct impls where possible;
  otherwise list projection laws as a hypothesis for them.
- Document panicking user `Hash`/`Eq` as outside the trusted base, or poison the store on unwind.
- Independent of all other tracks.

### Track T — Reviewer theorems and docs (last)

Files: `history-semantics/tests/reviewer.rs`, `history-analysis/tests/reviewer.rs`, `VERIFY.md`,
`docs/`, `README.md` verification sections.

- Prove the monitor theorem with trace safety, and A1–A5 (A6 from the minimality PR), as Verus
  clients using only public items; prove the hypothesis bundles for the two concrete types;
  register both test targets in `scripts/verify-all.sh` and CI.
- Rewrite `VERIFY.md` as the single reviewer document (commands, one count table, reviewer map,
  hypotheses, differences, trust summary); move `SPEC.md`, `docs/verification/README.md`, both
  `HANDOFF-*.md`, `finiteness-*.md` and the plan to `docs/history/`. Regenerate `TRUST.md` and
  README anchors.
- Add to the differences list: one tagged component type in the code vs. product domains in the
  paper (now hidden by R1), named scoped variables, equality up to `eq_spec`, require rules
  covered, declared domains as an assumption on runtime inputs, `GRAPH_BYTES`/`Exhausted`.

## Constraints

- No `admit`, `assume`, `#[verifier::external]` on verified code, or `external_body` on analysis
  or semantics code. New trusted items are allowed only where decision 4 names them; each appears
  in `TRUST.md` with a one-line justification.
- Do not weaken any existing `ensures`. Statements may change form only as this handoff
  prescribes (semantics over events, capacity-conditional counterexamples, unconditional `Holds`,
  split errors).
- Do not touch the minimality predicates or modules (see Coordination).
- Keep each file's CRLF/LF line endings. Keep CI green at every merge: `cargo fmt --check`,
  `cargo clippy ... --all-targets -- -D warnings` (both workspace and `fuzz/`), `cargo test
  --locked --workspace`, `cargo test --locked --release --manifest-path fuzz/Cargo.toml --lib`,
  `scripts/spec-check.sh`, `scripts/verify-all.sh` (see `.github/workflows/ci.yml`). Clippy runs on
  the ghost-erased build: a two-arm `match` that becomes single-arm after erasure fails
  `single_match` (this broke PR #9's CI once).
- Benchmark numbers must not change except through D2's build change; report any change.

## Verification

- Install the pinned toolchain with `scripts/verify-all.sh --download <dir>`. Use
  `-- --num-threads <cores>`; lower it if Verus is killed for memory.
- Iterate per crate and module (`cargo verus verify --locked -p <crate> ...`,
  `--verify-module`/`--verify-function`); run the full `scripts/verify-all.sh` at every milestone.
- Differential tests (`history-analysis/tests/differential.rs`) must keep passing; add cases for
  S1 (an undeclared finite-enum coordinate where real events are covered: must return `Holds`),
  S9 (empty declared domain rejected), S11 (foreign `RuleId` rejected), and S5 (an index overflow
  is an error, not `Exhausted`).

## Work plan

No agent or resource limits. Critical path: **0 → B → F → T**.

| Milestone | Content | Depends on | Parallel with |
|---|---|---|---|
| M0 | Track 0: interface files and `INTERFACES.md` | — | G |
| M1 | Track A (hypotheses) | M0 | B, C, D, E, G |
| M2 | Track B (semantics over events, capacity, bridges) | M0 | A, C, D, E, G |
| M3 | Track C (errors; includes the `no_invariant_failure` rename, done first) | M0 | A, B, D, E, G |
| M4 | Track D (monitor surface) | M0; A's bundle at merge | B, C, E, F, G |
| M5 | Track E (paper index, hygiene) | M0 | A, B, C, D, F, G |
| M6 | Track F (analyzer surface; rebase on minimality PR) | A, B, C | D, E, G |
| M7 | Track G (trust scan, builds, event impls) | — | everything |
| M8 | Track T (reviewer theorems, docs) | A–F | G |

File ownership (one owner each; others hand over lemmas in separate modules):

| Files | Owner |
|---|---|
| `history-analysis/src/analyzer.rs`, `history-analysis/src/verify.rs` | F |
| `refinement/semantics.rs`, instance half of `refinement/analyzer.rs`, `history-analysis/src/verify/{policy_bridge,typed_numeric,reconstruction,verdict}.rs` | B (until M2 lands, then F) |
| `junco-core/src/error.rs`, `history-store/src/graph.rs` | C |
| `history-semantics/src/validator.rs`, `compiled_rule.rs`, `policy/*` | D |
| `history_algebra.rs`, `finite_*.rs`, `refinement/{search,pruning,finiteness}.rs` | E |
| obligation definitions, `native.rs`, `typed/map.rs` | A |
| `scripts/`, `TRUST.md`, `Cargo.toml` dev-dependencies, root crate `src/` | G |
| `VERIFY.md`, `docs/`, `tests/reviewer.rs` | T |

The `no_invariant_failure` rename (C) and the move of `least_violation` into R2 (D) touch many
files; land each as its own mechanical commit before the other tracks branch off M0's result, or
rebase all tracks immediately after.

## Acceptance

Priority 1:
1. `scripts/verify-all.sh` reports 0 errors in every configuration, including the two new
   `reviewer` targets; all CI jobs pass.
2. R1–R6 exist; no public contract mentions an `open(crate)`/`open(super)` definition; old
   duplicate definitions are gone.
3. The monitor theorem with trace safety and A1–A5 are proved as Verus clients from public items
   only, and the hypothesis bundles are proved for the two concrete event types.
4. Differential tests pass, including the four new cases.

Priority 2:
5. `paper.rs` lists every result of the paper's `tab:mechanization`; hygiene items of plan §8 are
   done; `TRUST.md` includes the new scan sections; benchmarks build from a verified feature set.

Priority 3:
6. D1 and D4 documented or fixed per decision 9 and track G.

## Final report

- The R1–R6 definitions a reviewer must read (count, by file) and the theorem names in T.
- Each decision above: kept or changed, and why.
- `TRUST.md` diff: every new trusted item with its justification.
- Verified-function counts per configuration.
- Whether the minimality PR was integrated, and the exact minimality clause R6 restates.
- **Paper changes needed**, as a checklist against plan §7 updated to the final code: statement
  names, the decision procedure in Section 5 (split cases, constrained inclusion), Prop
  `prop:policy` status, simulation figure vs. code, hypotheses, trusted base, counts, "decides" /
  "complete" wording, evaluation paths.
