# Reviewer-surface integration status

## Current wave

Wave 0, in progress. Integration branch: `refactor/reviewer-surface`.
Latest handoff incorporated: `4be35d3` (after `649cd5d`). No Wave 1 tracks have started;
they will branch only from the frozen integration interfaces and mechanical commits.

## Last checks actually run

- Pinned Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, Rust `1.98.1` reused from the previously
  checksum-verified installation.
- Focused `junco-core`, no default features, modules `spec::{semantics,questions,hypotheses}`:
  **5 verified, 0 errors**. These are the recursive specification definitions.
- Focused `history-analysis`, runtime without default features, module `spec::analyzer`:
  **1 verified, 0 errors**. All six surface files typecheck through this build.
- No full matrix or native CI gate has yet been completed on this refactor branch.

## Work in progress

R1–R6 and `docs/verification/INTERFACES.md` are written locally. Existing executable contracts
have not been migrated. The revised handoff now requires `verify-all.sh --jobs`, persistent
per-configuration `--target-root`, and variadic `--only` first; that scheduler and its comparison
with a sequential full run precede publication of the frozen interface commit. The invariant
predicate rename and least-violation relocation will each be separate commits.

## Decisions and checks

- R6 preserves PR #10's absent-target coverage semantics; no membership precondition is added.
- Monitor hypotheses do not add surjectivity, which is unnecessary for its existing guarantee;
  analyzer hypotheses add it. This avoids weakening monitor soundness by adding a premise.
- The single `hash_coherent` token follows decision 4. Reusing vstd's key-model token was tried
  and rejected because that module is unavailable in the no-std configuration. No new trusted
  axiom or external body has been introduced.
- Before freezing, the S1 runtime regression needs a design check: the present Event API supplies
  no finite-coordinate universe information. Capacity-qualified symbolic counterexamples alone
  do not imply that a fully covered finite-enum query returns Holds.
- Existing upstream comment/header repairs are not claimed as new fixes. The trust inventory
  already lists `singleton_invariants`; what is missing is its classification as a proof axiom.

## PR #10

Opened: https://github.com/junco-org/junco-policy/pull/10 (`52118c4`). It proves minimum length
within the returned split case/profile, not per rule across cases, and adds explicit removal
semantics. Its separate full eleven-configuration gate passed with analyzer counts 570/570,
semantics counts 1615/1620, and 196 workspace tests. It is not assumed merged into this branch.

## Inbox acknowledgements

`docs/verification/INBOX.md` at `4be35d3` contains no dated messages. The accompanying handoff
changes were read in full: status/inbox communication, parallel/filterable gates, no retained
compatibility lemmas, and exact migration of PR #10's clauses are adopted. STATUS.md will be
updated and pushed at each gate and at least every 30 minutes, and removed before the final PR.

## Publication

The remote already has `refs/heads/refactor` at `9fad0b9`, so Git rejects creation of the child
ref `refactor/reviewer-surface` with a directory/file conflict. The existing branch is not deleted
or changed. The local integration branch keeps the requested name; its remote publication is
`refactor-reviewer-surface`.
