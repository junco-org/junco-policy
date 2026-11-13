# Reviewer-surface integration status

## Current wave

Wave 0's surface and both mechanical commits are complete; the final merge gate is running.
Integration branch: `refactor/reviewer-surface`. Latest handoff incorporated: `83de803`.
Seven isolated Wave 1 worktrees are prepared at `4c39737`; workers start when the merge gate
passes, without waiting for the full wave gate.

## Last checks actually run

- Pinned Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, Rust `1.98.1` reused from the previously
  checksum-verified installation.
- Focused `junco-core`, no default features, modules `spec::{semantics,questions,hypotheses}`:
  **5 verified, 0 errors**. These are the recursive specification definitions.
- Focused `history-analysis`, runtime without default features, module `spec::analyzer`:
  **1 verified, 0 errors**. All six surface files typecheck through this build.
- Before the minimality merge and relocation, full parallel matrix:
  **all 11 configurations passed, 0 errors**, 476.16 seconds.
- Full sequential baseline: **all 11 configurations passed, 0 errors**, 1075.16 seconds.
  Counts match exactly: syntax **55/55**, core **169/253**, store **287/287**, semantics
  **1609/1614**, public client **21**, analysis **564/564**.
- Workspace tests: **196 passed**; fuzz library tests: **8 passed**. Workspace and fuzz
  formatting and Clippy with `-D warnings` passed.
- After the minimality merge and relocation: workspace formatting, **196 workspace tests**, and
  workspace Clippy with `-D warnings` passed. The six-configuration full-feature Verus merge
  gate (including `public_specs`) is running; its results are not yet claimed.

## Work in progress

R1–R6 and `INTERFACES.md`: `42ab190`, with scoped-equivalence and ownership clarification
`4c39737`. Invariant-failure rename: `54a58fe` (separate verified mechanical commit).
Least-violation relocation: `da1df1d` (separate mechanical commit). The latter retains the old
typed meaning until B performs the semantic cutover; no compatibility lemma was added.
PR #10's head is incorporated locally by `0f40cb6` so B and F start from its strengthened
contracts. Existing executable contracts have not yet been migrated to R5/R6.

## Decisions and checks

- R6 preserves PR #10's absent-target coverage semantics; no membership precondition is added.
- Monitor hypotheses do not add surjectivity, which is unnecessary for its existing guarantee;
  analyzer hypotheses add it. This avoids weakening monitor soundness by adding a premise.
- The single `hash_coherent` token follows decision 4. Its required concrete witnesses cannot
  follow from axioms only for unrelated internal keys. The user explicitly approved scoped
  primitive-key axioms and compositional introductions for built-in tagged components; A will
  implement these and G will list every item with a justification. Arbitrary user Hash/Eq
  implementations are not assumed correct. No new trusted item has yet been added.
- S1's executable finite-enum case needs optional runtime type information. The frozen protocol
  uses verified `Event::coordinate_cardinality`, default `None`, and R1's `finite_coordinate`.
  B provides the method/contract; F activates finite search universes once all type equality
  classes are known, without changing the public undeclared domain or adding trust.
- Existing upstream comment/header repairs are not claimed as new fixes. The trust inventory
  already lists `singleton_invariants`; what is missing is its classification as a proof axiom.

## Slowest observed proof functions

The full matrix ran with `--time`; supplementary full-feature runs used `--time-expanded
--output-json`. These are the ten largest recorded SMT-run function times, excluding vstd.
The first attempt stopped on two mechanical-edit type errors; those were corrected, and the
next run completed all changed crates. C owns the dominant kernel proof sites; the remaining
hotspots are handed to their owning tracks where applicable, without weakening statements.

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

**2026-11-13: Track G additions (dead std spec; `arc_identity` fidelity)**, received at `83de803`:
read and acknowledged. G will first confirm the only `mem::replace` spec consumer is unverified
test-util code, then remove that dead trusted item. G will inspect the pinned Verus model of
`Arc<T>` and references and establish identity fidelity for every compared store/owner type.
If distinct allocations can have equal spec values, it must report the false-contract risk here
before changing an identity wrapper. No wrapper has been changed in response to this message.

The handoff's `singleton_invariants` elimination is also adopted for G: retain its fact in
`numeric_store_wf`, delete the axiom and its calls, and verify the store crate before merge.
Earlier `4be35d3` changes remain adopted: status/inbox communication, parallel/filterable gates,
no retained compatibility lemmas, and exact semantic migration of PR #10's clauses.
STATUS.md is updated and pushed at each gate and at least every 30 minutes, and removed before
the final PR.

## Publication

The remote already has `refs/heads/refactor` at `9fad0b9`, so Git rejects creation of the child
ref `refactor/reviewer-surface` with a directory/file conflict. The existing branch is not deleted
or changed. The local integration branch keeps the requested name; its remote publication is
`refactor-reviewer-surface`.
