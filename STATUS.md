# Audit fixes status

Base: main `7050ac3df9ed7594bb2d1635f4bd39d89bb4a3a4`; task and evidence read from handoff/audit-fixes `88c9774445f090c3fdecd876e2450ac3c0b0912b`.

Concurrent work: explicitly reported by user. This worker uses isolated `/tmp/junco-audit`; other workers' changes must not be overwritten or assigned inferred intent. Remote inspection found no fix/audit-* branch and no open audit-fix PR at initial check. No item is claimed completed without gate evidence.

| Item | State | Evidence / public statements |
|---|---|---|
| H1 | in progress | Local gates passed; [PR #13](https://github.com/junco-org/junco-policy/pull/13), head `73020d775580eafa6f91e959ef08d51ee0eb2f24`, awaits CI before merge. Changed `counterexample_spec`, new `undeclared_capacity` (`crates/history-analysis/src/spec/analyzer.rs`); new `theorem_counterexample_has_instance`, `theorem_declared_fresh_rejected`, `lemma_declared_coordinate_zero` (`crates/history-analysis/tests/reviewer.rs`). |
| H3 | in progress | Branch fix/audit-h3 from main while H1/H6 await CI; Denial.index added, check_step/paper index/reviewer/public_specs strengthened. Full monitor/downstream proof gates running. |
| H4 | not started | |
| H6 | in progress | Local gates passed; [PR #14](https://github.com/junco-org/junco-policy/pull/14), head `0e3c087`, awaits CI. Changed `PolicyAnalyzer::add_rule` (`crates/history-analysis/src/analyzer.rs`) and `ValidatorBuilder::add_rule` (`crates/history-semantics/src/validator.rs`): Ok implies rule_wf, exact event arity and correctly tagged head constants. Reviewer clients consume the clauses. Unused analyzer_wf/rule_constants_tagged removed. |
| H5 | not started | Monitor first, analyzer second. |
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

Merged items: none. PR numbers and merge commits: none.

Verification: H1 library merge gate `history-analysis --no-default-features --features runtime,std`: **603 verified, 0 errors**; reviewer: **17 verified, 0 errors**. Ghost-erased clippy passed (`--all-targets -- -D warnings`); package tests **27 passed**. Final package fmt passed after removing the throwaway smoke example. Runtime smoke observed counterexample candidate `[Constant(C0(3)), Constant(C1(7))]`, empty history, both coordinates declared; concrete `(3,7), []` refutes All ⊆ Empty. No ensures weakened; no trusted items added; no paper or benchmark edits.

H6 gates: monitor **1624**, public_specs **19**, monitor reviewer **7**, analyzer **603**, analyzer reviewer **14** verified, all **0 errors**. Ghost-erased clippy passed; package tests **73 passed**; fmt passed. Runtime smoke exercised both analyzer and builder: lawful pair rule accepted; wrong head arity and mistagged head constants rejected with corresponding errors.

Toolchain: downloaded pinned Z3 cannot execute on host glibc 2.31. Existing `/ssd0/zkent/junco-proof-tools/compat-verus` and `z3-compat` pass the script's pinned version checks; these are used for verification.

Inbox: acknowledged **2026-11-13: Port H1 and H6 from attempt A (PR #12) first**, fetched at handoff `cb24ee9`. Read A's reviewer source at `c441afd`; H1 has equivalent slot-domain exclusion and the declared-coordinate-zero lemma. H6 now precedes H3/H4/H5. No other A changes will be imported; no merge/rebase onto A. Initial inbox was empty. Poll at every gate and at least every 30 minutes; vacuity messages preempt all work.

Inbox additionally acknowledged **2026-11-13: Vacuity probe results (no blocker; priorities unchanged)** at handoff `5e6505f`. No inconsistency reported. Exact `pos_ac1_junk_cex_declared` source/contract run at H1 head: **expected postcondition failure**, **0 verified, 1 error** in probe; analyzer library **603 verified, 0 errors**. Result posted to PR #13; throwaway source removed. New H14 scope: show reachable `Ok` results, not only conditional client guarantees.

Delivery uses one branch/PR per item into main, and this separate status branch, as requested by user (superseding handoff's integration-PR instructions).
