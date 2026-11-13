# Reviewer-surface integration status

## Current wave

Wave 1 is running in isolated worktrees. Latest maintainer inbox incorporated: `b8aee8a`.
The critical surface review is being applied before B/F use the affected R6 contracts.
A/B/D/G/F-prep continue unaffected work; C and E have completed local handoffs awaiting
integration gates. The integration branch is `refactor/reviewer-surface`.

## Last checks actually run

- Pinned Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, Rust `1.98.1` reused from the previously
  checksum-verified installation.
- Completed Wave 0 full matrix: **all 11 configurations passed, 0 errors**. The full-feature
  merge gate passed syntax **55**, core **253**, store **287**, semantics **1620**, analyzer
  **571**, public client **21**. The all-config wave gate also passed no-default syntax **55**,
  core **169**, store **287**, semantics **1615**, analyzer **571**; unchanged configurations
  were cached. These counts precede the critical surface corrections below.
- Default sequential crosscheck of the completed driver passed the original eleven
  configurations in **1075.16 seconds**, matching the parallel run's counts exactly.
- Critical correction: focused core `spec::{questions,hypotheses}` has
  **6 verified, 0 errors**. R6's revised unit exhaustion/subset clauses are being checked.
- Workspace tests: **196 passed**; fuzz library tests: **8 passed**. Workspace and fuzz
  formatting and Clippy with `-D warnings` passed.
- The final Wave 0 native gate passed workspace/fuzz fmt and Clippy with `-D warnings`,
  **196 workspace tests** and **8 fuzz tests**. No subsequent native result is claimed yet.

## Work in progress

R1–R6 and `INTERFACES.md`: `42ab190`, with scoped-equivalence and ownership clarification
`4c39737`. Invariant-failure rename: `54a58fe` (separate verified mechanical commit).
Least-violation relocation: `da1df1d` (separate mechanical commit). The latter retains the old
typed meaning until B performs the semantic cutover; no compatibility lemma was added.
PR #10's head is incorporated locally by `0f40cb6`; B/F preserve its guarantees exactly.
The native analyzer view and its active callers require an atomic B/F cutover after A/C:
the old view includes component-tuple rules and accumulated known values, while R6 does not.
Retaining a compatibility view is not an acceptable workaround.

Worker handoffs: C has the budget/index split, an actual overflow regression, and a proof-only
derivative-cache helper. E has the thirteen-row paper index and independent hygiene. G has
singleton-axiom removal and the expanded trust scan; A has canonical key/equality boundaries;
B has actual-event lowering/capacity prerequisites. These are not claimed integration-complete.

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

**2026-11-13: No primitive or component-type key axioms** (`b8aee8a`): read, broadcast to every
worker, and applied. The earlier approval is removed from INTERFACES/status/shared instructions;
only decision 4's internal-key axioms remain. Concrete witnesses take only `hash_coherent`.

**2026-11-13: Surface review — fix before Wave 1 builds on R6** (`ed3cf35`): read and affected
work paused. Source-literal/domain bounds and R6 subset clauses are implemented, with focused
checking in progress. Forgeable exhaustion numbers are removed using the explicit no-claim
fallback. The Event hook is cancelled; B committed its removal on the prerequisite branch.

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

G's singleton axiom removal is ready for its store-only merge gate. STATUS is pushed at gates
and at least every 30 minutes, and removed before the final PR.

## Publication

The remote already has `refs/heads/refactor` at `9fad0b9`, so Git rejects creation of the child
ref `refactor/reviewer-surface` with a directory/file conflict. The existing branch is not deleted
or changed. The local integration branch keeps the requested name; its remote publication is
`refactor-reviewer-surface`.
