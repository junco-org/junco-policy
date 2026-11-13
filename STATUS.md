# Audit fixes status

Base: main `7050ac3df9ed7594bb2d1635f4bd39d89bb4a3a4`; task and evidence read from handoff/audit-fixes `88c9774445f090c3fdecd876e2450ac3c0b0912b`.

Concurrent work: explicitly reported by user. This worker uses isolated `/tmp/junco-audit`; other workers' changes must not be overwritten or assigned inferred intent. Remote inspection found no fix/audit-* branch and no open audit-fix PR at initial check. No item is claimed completed without gate evidence.

| Item | State | Evidence / public statements |
|---|---|---|
| H1 | merged | [PR #13](https://github.com/junco-org/junco-policy/pull/13), merge commit `bce1df8511fc56919724e18bdbf5e610c8252bdb`; every CI check passed. Public statements detailed below. |
| H3 | merged | [PR #15](https://github.com/junco-org/junco-policy/pull/15), merge commit `bedc0c955dd9eb24e224126a456d6c84a6092d55`; all seven CI checks passed on exact head `2a6f942428173122cb0e546a62182ea219e28747`. Public statements detailed below. |
| H4 | in progress | Local gates passed; [PR #17](https://github.com/junco-org/junco-policy/pull/17), rebased head `55282cb` atop merged H3, awaits CI. Prior head passed every check. `stmt_search_correct` and its theorem require trace_steps_ok only for expanded nodes; public index uses the same statement. |
| H6 | merged | [PR #14](https://github.com/junco-org/junco-policy/pull/14), merge commit `4151cb0a66058e9ecbc7e787b23438b40f319192`; all CI passed. Public statements detailed below. |
| H5 | in progress | Monitor half passed: core **288**, store **289**, monitor **1624**, reviewer **9**, public_specs **19** verified, **0 errors**. Preserved as pushed commit `f898619` on `fix/audit-h5`. Analyzer half implemented; integrated proof gate running. Full workspace ghost-erased clippy/fmt passed, **200 tests passed**. Both runtime monitor and all-four-query analyzer smokes passed. UnknownId-as-check_step negative probe failed its postcondition as required (**0 verified, 1 error**); removed. |
| H2 | not started | |
| H7 | not started | |
| H8 | not started | |
| H9 | not started | |
| H10 | not started | |
| H11 | not started | |
| H12 | not started | |
| H13 | not started | |
| H14 | not started | |
| H15 | not started | Deferred unless all other items complete. |

Merged items: H1, PR #13, `bce1df8511fc56919724e18bdbf5e610c8252bdb`; H6, PR #14, `4151cb0a66058e9ecbc7e787b23438b40f319192`; H3, PR #15, `bedc0c955dd9eb24e224126a456d6c84a6092d55`.

H1 public statements:
- `counterexample_spec<E>` (`crates/history-analysis/src/spec/analyzer.rs`) now includes `forall i. 0 <= i < arity::<E>() && a.domains[i] is Some ==> fresh_used(cex,i) =~= ISet::empty()` and `undeclared_capacity::<E>(a,cex) ==> cex_has_instance::<E>(a.domains,a.known,cex)`; existing arity and every-instance validity clauses retained.
- New `undeclared_capacity<E>` (same file) is `forall i. 0 <= i < arity::<E>() && a.domains[i] is None ==> fresh_capacity::<E>(a.domains,a.known,i,fresh_used(cex,i).len())`.
- New `theorem_counterexample_has_instance<E>` (`crates/history-analysis/tests/reviewer.rs`): counterexample_spec plus capacity at every undeclared coordinate implies cex_has_instance.
- New `theorem_declared_fresh_rejected<E>` (same file): fresh_used contains a name at an in-range declared coordinate implies not counterexample_spec.
- New `lemma_declared_coordinate_zero<E>` (same file): counterexample_spec and an in-range declared coordinate imply fresh_used.len() == 0 and fresh_capacity for that length.

H6 changed public statements:
- `PolicyAnalyzer::add_rule` (`crates/history-analysis/src/analyzer.rs`): `result matches Ok(id) ==> rule_wf(rule@) && rule@.head.len() == arity::<E>() && head_coordinates_wf::<E>(rule@.head)`, in addition to the exact rule/known/domain/owner frame and stable index. Existing requires include event hypotheses.
- `ValidatorBuilder::add_rule` (`crates/history-semantics/src/validator.rs`): under `event_obligations::<E>()`, successful registration implies `rule_wf(source@) && source@.head.len() == arity::<E>() && head_coordinates_wf::<E>(source@.head)`, in addition to the existing source-order frame.
- `head_coordinates_wf` is the existing public predicate: exact arity, and every Constant(value) in head[i] has `E::coordinate_spec(value) == i`.
- Deleted unused `analyzer_wf` and `rule_constants_tagged` from `crates/history-analysis/src/spec/analyzer.rs`; no replacement unproved view invariant.

H3 changed public statements:
- `Denial<E>::index` (`crates/history-semantics/src/validator.rs`) is the zero-based source index of the first violated rule.
- `check_step<E,M>` (`crates/history-semantics/src/spec/monitor.rs`), denial arm: `least_violation(before.rules, request.event, before.history, denial.index as int) && denial.mode == before.rules[denial.index as int].mode`. Grant/error clauses and history frame retained.
- `stmt_matcher` (`crates/history-semantics/src/verify/paper.rs`) and `stmt_monitor_check` (`crates/history-semantics/tests/reviewer.rs`) identify the same exact index; executable/public reviewer clients consume it.

Verification: H1 library merge gate `history-analysis --no-default-features --features runtime,std`: **603 verified, 0 errors**; reviewer: **17 verified, 0 errors**. Ghost-erased clippy passed (`--all-targets -- -D warnings`); package tests **27 passed**. Final package fmt passed after removing the throwaway smoke example. Runtime smoke observed counterexample candidate `[Constant(C0(3)), Constant(C1(7))]`, empty history, both coordinates declared; concrete `(3,7), []` refutes All ⊆ Empty. No ensures weakened; no trusted items added; no paper or benchmark edits.

H6 gates: monitor **1624**, public_specs **19**, monitor reviewer **7**, analyzer **603**, analyzer reviewer **14** verified, all **0 errors**. Ghost-erased clippy passed; package tests **73 passed**; fmt passed. Runtime smoke exercised both analyzer and builder: lawful pair rule accepted; wrong head arity and mistagged head constants rejected with corresponding errors.

H3 gates before rebase: monitor **1624**, public_specs **19**, monitor reviewer **7**, analyzer **603**, analyzer reviewer **14** verified, all **0 errors**; ghost-erased clippy/fmt passed, **123 native tests passed**. Runtime smoke observed index=1 for the first of two same-mode violations after a nonviolating rule, committed history unchanged. Rebase resolved only additive interface-documentation conflict with H1; CI initially had no checks because of that conflict, now resolved.

H4 gates: monitor **1624**, public_specs **19**, analyzer **603**, analyzer reviewer **17** verified, all **0 errors**; ghost-erased clippy/fmt passed, **73 tests passed**. Runtime search smoke: All ⊆ All returned Holds; All ⊆ Empty returned a constant-only counterexample with empty history.

Rebased H6 composition gate passed: analyzer **603**, reviewer **17**, **0 errors**; subsequently all seven CI checks passed and PR #14 merged.

H5 runtime evidence: monitor permits/check granted `(3,7)`, committed it once, then permits/check denied `(9,7)` without appending; final history `[(3,7)]`. Analyzer registered two different constant-head rules; self-coverage and self-refinement returned `Holds`, redundancy and All ⊆ Empty returned real constant-only `(3,7), []` counterexamples. Throwaway examples removed. No item PR yet: analyzer proof acceptance is still pending.

Toolchain: downloaded pinned Z3 cannot execute on host glibc 2.31. Existing `/ssd0/zkent/junco-proof-tools/compat-verus` and `z3-compat` pass the script's pinned version checks; these are used for verification.

Inbox: acknowledged **2026-11-13: Port H1 and H6 from attempt A (PR #12) first**, fetched at handoff `cb24ee9`. Read A's reviewer source at `c441afd`; H1 has equivalent slot-domain exclusion and the declared-coordinate-zero lemma. H6 now precedes H3/H4/H5. No other A changes will be imported; no merge/rebase onto A. Initial inbox was empty. Poll at every gate and at least every 30 minutes; vacuity messages preempt all work.

Inbox additionally acknowledged **2026-11-13: Vacuity probe results (no blocker; priorities unchanged)** at handoff `5e6505f`. No inconsistency reported. Exact `pos_ac1_junk_cex_declared` source/contract run at H1 head: **expected postcondition failure**, **0 verified, 1 error** in probe; analyzer library **603 verified, 0 errors**. Result posted to PR #13; throwaway source removed. New H14 scope: show reachable `Ok` results, not only conditional client guarantees.

Inbox additionally acknowledged **2026-11-13: Submission cleanup PR; no plan ids in new text** at handoff `a25a1e7`. H1 remains unchanged. Will rebase open branches after cleanup merges, preserve cleanup-side comment wording and reapply semantic changes. New code/comments/docs use descriptive wording; item ids only in STATUS.md and PR titles. Last inbox fetch at this gate showed no new messages.

Delivery uses one branch/PR per item into main, and this separate status branch, as requested by user (superseding handoff's integration-PR instructions).
