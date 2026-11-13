# Reviewer-surface integration status

## Current wave

The atomic monitor/analyzer source is pushed at `e525e20`; all eleven configurations passed
with zero errors, as did workspace/fuzz native gates. The latest inbox (`bb1b19d`) correctly
identifies overbroad internal-key axioms in that version. Their five trusted introductions are
being narrowed to hash_coherent only; equality/equivalence/SmallVec view facts must be proved.
Reviewer clients T continue independently. Exhausted remains unit/no-claim and blocks nothing.

## Last checks actually run

- Pinned Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, Rust `1.98.1` reused from the previously
  checksum-verified installation.
- Completed Wave 0 full matrix: all eleven configurations passed, zero errors.
- Complete atomic full-feature merge gate at `92f4e9d` / published `e525e20`: all six passed.

  | Configuration | Verified functions | Errors |
  |---|---:|---:|
  | syntax `serde,std` | 63 (cached; prior same-source count) | 0 |
  | core `runtime,std,serde` | 323 | 0 |
  | store `runtime,std` | 306 | 0 |
  | semantics `runtime,std,cache` | 1646 | 0 |
  | semantics `public_specs` | 21 | 0 |
  | analyzer `runtime,std` | 626 | 0 |
- The subsequent all-eleven-configuration wave gate passed, zero errors (**338.63 seconds**).
  Those results predate the newly required hash-only trust narrowing; the repair gets a new
  verification gate, rather than treating the old broader contracts as final evidence.

- The first G/E gate found the removed finite-domain successor-theorem caller. Replacing it
  with the explicitly instantiated common theorem closed the downstream proof; no statement
  was weakened. The atomic analyzer gate is now green, including its native entry-point proofs.
- Default sequential driver crosscheck passed the original eleven configurations in
  **1075.16 seconds**, matching the parallel run's counts exactly. Final confirmation remains.
- Critical R6 correction: focused core questions/hypotheses **6/0**, analyzer spec **1/0**.
  A throwaway proof rejected a fabricated out-of-source known set (**1/0**); removed afterward.
- Latest atomic integration native gate: **198 workspace tests across 25 suites**,
  **2 explicit instrumentation tests**, **8 fuzz tests**; workspace and fuzz formatting,
  default/instrumentation/replay-probe Clippy with `-D warnings` passed. Instrumentation
  remains out of benchmarks.
- `scripts/spec-check.sh`: **18 passed**, including the reduced assumed-spec boundary.
- Staged foundation/monitor native package tests: **127 passed across 16 suites**.
  Both concrete public hypothesis clients passed (**2 verified, 0 errors**), taking only
  the component type's `hash_coherent` premise.
  The monitor worker also exercised grant/denial, read-only permits, rollback,
  foreign/future checkpoints, append-error atomicity and recovery in a removed executable.
- Additional foundation no-default gates passed: syntax **63**, core **239**, store **303**,
  semantics **1641**, all zero errors. These precede the final F owner/state additions.
- B's native bridge focuses passed **57/0** (typed/reconstruction), **62/0** (policy,
  verdict and minimality), **12/0** (source support), and **14/0** (table assembly).
  These are worker module results, not a claimed whole-analyzer result.

## Work in progress

R1–R6 and `INTERFACES.md`: `42ab190`, with scoped-equivalence and ownership clarification
`4c39737`. Invariant-failure rename: `54a58fe` (separate verified mechanical commit).
Least-violation relocation: `da1df1d` (separate mechanical commit); B's staged cutover now states
it over real events. PR #10's head is incorporated locally by `0f40cb6`; B/F preserve its exact
same-rule, returned-profile minimality and arbitrary-id removal guarantees.
The native analyzer view/callers are migrated atomically: actual source rules, retained exact
declared domains, query-local known contexts, and owner-checked rule ids. No compatibility
view or legacy-predicate shim is retained.

G's singleton-axiom/dead-std-spec removals, trust inventory, identity audit and instrumentation
build split are integrated. E's thirteen-row paper index and independent hygiene are integrated,
including its downstream successor caller. C's complete error split/callers and A/B event
foundations are staged and passed the gates above. D's complete monitor track is staged.
Native B/F proof closure and public adapters are now integrated in staging. T starts after the
running merge gate passes. Independent numeric-algebra naming hygiene is prepared separately
so it cannot invalidate or delay the active proof gate.

## Decisions and checks

- R6 preserves PR #10's absent-target coverage semantics; no membership precondition is added.
- Monitor hypotheses do not add surjectivity, which is unnecessary for its existing guarantee;
  analyzer hypotheses add it. This avoids weakening monitor soundness by adding a premise.
- `hash_coherent` remains the single uninterpreted user premise. Primitive and tagged-component
  key-axiom approval is **withdrawn**. A/G removed those introductions/approvals; concrete u8/u32
  witnesses prove all other laws with only their component's `hash_coherent` premise.
- `Counterexample::known` is now bounded by source literals plus declared domains: all registered
  rules for policy queries, current head/both tails for tail queries. Old unrelated interned values
  cannot inflate that context. Canonical collectors are shared with B, not duplicated.
- `Exhausted` is now a unit outcome and **makes no claim**. This uses the inbox's explicit
  fallback; raw arithmetic fields were forgeable. A true store-only token would require broad
  ghost-state/error propagation. Budget/index classification and charge diagnostics remain C's.
- The cardinality hook is cancelled. S1 accepts Holds or a finite-coordinate capacity failure,
  never a capacity-satisfying refutation. No new Event trait method will land.
- Exact declared-domain equality requires retaining the caller's domains in a ghost field:
  interning may quotient by `eq_spec`. Public vocabulary growth does not imply private historical
  codebook room; total bounded error handling replaces that artificial capacity precondition.

## Slowest observed proof functions

The full matrix ran with `--time`; supplementary full-feature runs used `--time-expanded
--output-json`. These are the ten largest recorded SMT-run function times, excluding vstd.
The first attempt stopped on two mechanical-edit type errors; those were corrected, and the
next run completed all changed crates. The verifier's qualified method name identifies its
receiver type, not necessarily its source: `derivative_step` is in semantics `symbolic.rs`, not
core `kernel.rs`. C's proof-only split is not claimed to be a paired performance improvement.

| Function | SMT-run seconds |
|---|---:|
| `junco_core::kernel::RegexId::derivative_step` | 79.781 |
| `history_analysis::search::Search::expand` | 21.355 |
| `junco_core::kernel::RegexId::set` | 17.163 |
| `history_semantics::normalize::Action::pair_step` | 16.321 |
| `junco_core::kernel::TransitionId::collect` | 14.574 |
| `history_semantics::normalize::verify::machine_pair_union_effect` | 13.504 |
| `history_semantics::normalize::Action::clean_step` | 13.190 |
| `junco_core::flatten::flatten_rule_parts` | 11.465 |
| `history_semantics::normalize::Action::step` | 9.526 |
| `history_semantics::progress::CompiledPair::collect_atoms` | 9.038 |

## PR #10

Open: https://github.com/junco-org/junco-policy/pull/10, head `52118c4`. It is mergeable and
has been merged **into this integration branch only**, by `0f40cb6`; it has not been merged
into `main`. It proves minimum length within the returned split case/profile, not per rule
across cases, and explicit removal semantics. Its separate full eleven-configuration gate
passed with analyzer counts 570/570, semantics counts 1615/1620, and 196 workspace tests.
B/F migrate that content exactly to the new vocabulary and remove superseded predicates.

## Inbox acknowledgements

**2026-11-13: Internal-key axioms may assert only hash_coherent** (`bb1b19d`): confirmed all
five introductions were too broad. Parent is narrowing their frozen interface to exactly
hash_coherent, removing the SmallVec view-equality assumption, and proving every equality
and equivalence conjunct separately. No additional equality/view axiom will be introduced.
No unprovable conjunct has yet been established; any genuine proof obstruction will be
reported explicitly instead of assumed. Concrete user-type hashing axioms remain forbidden.

**2026-11-13: Exhausted is not a blocker** (`baff915`): acknowledged. The unit/no-claim
fallback is already implemented and pushed in `a3a0313`; no wave or merge waits for a token.
The implementation retains C's budget/index distinction, but R6 makes no exhaustion claim.

**2026-11-13: No primitive or component-type key axioms** (`b8aee8a`): read, broadcast to every
worker, and applied. The earlier approval is removed from INTERFACES/status/shared instructions;
only decision 4's internal-key axioms remain. Concrete witnesses take only `hash_coherent`.

**2026-11-13: Surface review — fix before Wave 1 builds on R6** (`ed3cf35`): implemented
source-literal/domain bounds and R6 subset clauses, with focused checks passing. Forgeable
exhaustion numbers are removed using the explicit no-claim fallback. The Event hook is
cancelled; B committed its removal on the prerequisite branch.

**2026-11-13: Keep completed verify-all.sh work**: adopted; `5f0523d` remains. No additional
driver extension is allowed except registering the two reviewer targets. A final default-mode
confirmation of the original eleven sequential configurations remains required.
This supersedes **Abandon the changes to verify-all.sh**; that earlier instruction was read,
but its later amendment explicitly allows the already-completed and verified driver.

**2026-11-13: Track G additions (dead std spec; arc_identity fidelity)**: G confirmed the dead
mem::replace spec has only an unverified test-util caller and removes its orphan harness too.
Pinned probes show generic Arc/reference content equality loses allocation identity. For the
named store wrappers, existing linear registry births/non-recycled ids and private non-Clone
singleton construction prevent equal-content distinct live owners. G documents the restricted
invariant; no generic injectivity claim or identity-wrapper weakening is introduced.

G's singleton axiom removal passed the full-feature downstream merge gate. STATUS is pushed
at gates and at least every 30 minutes, and removed before the final PR.

## Publication

The remote already has `refs/heads/refactor` at `9fad0b9`, so Git rejects creation of the child
ref `refactor/reviewer-surface` with a directory/file conflict. The existing branch is not deleted
or changed. The local integration branch keeps the requested name; its remote publication is
`refactor-reviewer-surface`.
