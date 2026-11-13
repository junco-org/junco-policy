# Reviewer-surface integration status

## Current wave

Wave 0, in progress. Integration branch: `refactor/reviewer-surface`.
Latest handoff incorporated: `83de803` (after `4be35d3`). No Wave 1 tracks have started;
they will branch only from the frozen integration interfaces and mechanical commits.

## Last checks actually run

- Pinned Verus `0.2026.10.04.426d8b0`, Z3 `4.16.0`, Rust `1.98.1` reused from the previously
  checksum-verified installation.
- Focused `junco-core`, no default features, modules `spec::{semantics,questions,hypotheses}`:
  **5 verified, 0 errors**. These are the recursive specification definitions.
- Focused `history-analysis`, runtime without default features, module `spec::analyzer`:
  **1 verified, 0 errors**. All six surface files typecheck through this build.
- Full parallel matrix: **all 11 configurations passed, 0 errors**, 476.16 seconds.
- Full sequential baseline: **all 11 configurations passed, 0 errors**, 1075.16 seconds.
  Counts match exactly: syntax **55/55**, core **169/253**, store **287/287**, semantics
  **1609/1614**, public client **21**, analysis **564/564**.
- Workspace tests: **196 passed**; fuzz library tests: **8 passed**. Workspace and fuzz
  formatting and Clippy with `-D warnings` passed.

## Work in progress

R1–R6 and `docs/verification/INTERFACES.md` are written locally. Existing executable contracts
have not been migrated. The verification driver now supports `--jobs`, persistent
per-configuration `--target-root`, and variadic `--only`; its full parallel and sequential runs
agree. The invariant-predicate rename is being completed in a separate parent-owned worktree
while retaining its exact meaning. It and least-violation relocation get separate commits before
the frozen interface surface is pushed and dependent tracks start.

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
