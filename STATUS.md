# Audit fixes status

Base: main `7050ac3df9ed7594bb2d1635f4bd39d89bb4a3a4`; task and evidence read from handoff/audit-fixes `88c9774445f090c3fdecd876e2450ac3c0b0912b`.

Concurrent work: explicitly reported by user. This worker uses isolated `/tmp/junco-audit`; other workers' changes must not be overwritten or assigned inferred intent. Remote inspection found no fix/audit-* branch and no open audit-fix PR at initial check. No item is claimed completed without gate evidence.

| Item | State | Evidence / public statements |
|---|---|---|
| H1 | merged | [PR #13](https://github.com/junco-org/junco-policy/pull/13), merge commit `bce1df8511fc56919724e18bdbf5e610c8252bdb`; every CI check passed. Public statements detailed below. |
| H3 | merged | [PR #15](https://github.com/junco-org/junco-policy/pull/15), merge commit `bedc0c955dd9eb24e224126a456d6c84a6092d55`; all seven CI checks passed on exact head `2a6f942428173122cb0e546a62182ea219e28747`. Public statements detailed below. |
| H4 | merged | [PR #17](https://github.com/junco-org/junco-policy/pull/17), merge commit `184383710b2b0918b3567869d998185940a3454d`; all seven CI checks passed on exact head `55282cb79f2b4472ee5e1da37c0aa5b4e220bbd9`. Public statement detailed below. |
| H6 | merged | [PR #14](https://github.com/junco-org/junco-policy/pull/14), merge commit `4151cb0a66058e9ecbc7e787b23438b40f319192`; all CI passed. Public statements detailed below. |
| H5 | merged | [PR #19](https://github.com/junco-org/junco-policy/pull/19), merge commit `8b326a683d0ca4db998ab0959250fb92fc81f717`; all seven CI checks passed on exact head `a11905aaf633f72c0ad37700c8fb3e5c377d4afc`. Core **288**, store **289**, monitor cache/no-cache **1624/1619**, monitor reviewer **9**, public_specs **19**, analyzer **603**, analyzer reviewer **19** verified, **0 errors**. Workspace fmt/clippy and **200 tests** passed. Public statements below. |
| H2 | merged | [PR #21](https://github.com/junco-org/junco-policy/pull/21), merge commit `5e10a8cd7419c9beaddd5208877c2db7a398500b`; all seven CI checks passed on exact head `6562d5462ea1dadfd1a01ccdda3306033fc3e4a4`. Full smoke **100 instances / 180 concrete counterexamples**; measured run **84,234**, no fresh declared-coordinate values. Unit probe passed; removed. Analyzer **603**, reviewer **17** verified, **0 errors**; workspace fmt/clippy and **200 tests** passed. Before/after data below. No public Verus statement changed. |
| H7 | in progress | [PR #22](https://github.com/junco-org/junco-policy/pull/22), head `b78cf89`: all local code gates passed; CI running. Monitor cache/no-cache **1628/1623**, public_specs **21**, monitor reviewer **11**, analyzer **603**, analyzer reviewer **19**, all **0 errors**. Workspace/fuzz clippy and **200/8 tests** passed; actual AgentDojo self-test passed. Both event-replay modes completed **1024 tasks / 219 denials**, **0 mismatches/errors**. **Do not merge:** paired live scoring remains blocked by actual provider HTTP **403 Forbidden**; event-only replay is not utility/attack evidence. |
| H8 | in progress | Isolated `fix/audit-h8` from main `8b326a6`; canonical lock/flow vocabularies and evaluated identities moved into verified syntax; SMT/RE# migrated to tuples. Concrete hash-only hypothesis lemmas integrated. First proof gate stopped at four ambiguous eq_spec calls; first erased clippy gate reported manual-equality/derived-hash and match-style diagnostics. No successful gate or new trust claimed; integration repair pending. |
| H9 | not started | |
| H10 | not started | |
| H11 | not started | |
| H12 | not started | |
| H13 | not started | |
| H14 | not started | |
| H15 | not started | Deferred unless all other items complete. |

Merged items: H1, PR #13, `bce1df8511fc56919724e18bdbf5e610c8252bdb`; H6, PR #14, `4151cb0a66058e9ecbc7e787b23438b40f319192`; H3, PR #15, `bedc0c955dd9eb24e224126a456d6c84a6092d55`; H4, PR #17, `184383710b2b0918b3567869d998185940a3454d`; H2, PR #21, `5e10a8cd7419c9beaddd5208877c2db7a398500b`; H5, PR #19, `8b326a683d0ca4db998ab0959250fb92fc81f717`.

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

H4 changed public statement:
- `stmt_search_correct` (`crates/history-semantics/src/verify/refinement/search.rs`) is now `forall d,g0,r,s,q0,cases_of,t,outcome. satisfiable(d,g0) && initial_ok(q0,r,s) && trace_steps_ok(d,cases_of,t) && trace_wf(d,g0,q0,cases_of,t) && trace_outcome(t,outcome) ==> outcome_ok(d,g0,r,s,outcome)`. No global steps_ok-for-every-Item premise remains.
- `theorem_search_correct` (same file) proves this statement via lemma_search_correct; `stmt_thm_search` and `theorem_paper_index` (`crates/history-semantics/src/verify/paper.rs`) use it unchanged.

Verification: H1 library merge gate `history-analysis --no-default-features --features runtime,std`: **603 verified, 0 errors**; reviewer: **17 verified, 0 errors**. Ghost-erased clippy passed (`--all-targets -- -D warnings`); package tests **27 passed**. Final package fmt passed after removing the throwaway smoke example. Runtime smoke observed counterexample candidate `[Constant(C0(3)), Constant(C1(7))]`, empty history, both coordinates declared; concrete `(3,7), []` refutes All ⊆ Empty. No ensures weakened; no trusted items added; no paper or benchmark edits.

H6 gates: monitor **1624**, public_specs **19**, monitor reviewer **7**, analyzer **603**, analyzer reviewer **14** verified, all **0 errors**. Ghost-erased clippy passed; package tests **73 passed**; fmt passed. Runtime smoke exercised both analyzer and builder: lawful pair rule accepted; wrong head arity and mistagged head constants rejected with corresponding errors.

H3 gates before rebase: monitor **1624**, public_specs **19**, monitor reviewer **7**, analyzer **603**, analyzer reviewer **14** verified, all **0 errors**; ghost-erased clippy/fmt passed, **123 native tests passed**. Runtime smoke observed index=1 for the first of two same-mode violations after a nonviolating rule, committed history unchanged. Rebase resolved only additive interface-documentation conflict with H1; CI initially had no checks because of that conflict, now resolved.

H4 gates: monitor **1624**, public_specs **19**, analyzer **603**, analyzer reviewer **17** verified, all **0 errors**; ghost-erased clippy/fmt passed, **73 tests passed**. Runtime search smoke: All ⊆ All returned Holds; All ⊆ Empty returned a constant-only counterexample with empty history.

Rebased H6 composition gate passed: analyzer **603**, reviewer **17**, **0 errors**; subsequently all seven CI checks passed and PR #14 merged.

H5 runtime evidence: monitor permits/check granted `(3,7)`, committed it once, then permits/check denied `(9,7)` without appending; final history `[(3,7)]`. Analyzer registered two different constant-head rules; self-coverage and self-refinement returned `Holds`, redundancy and All ⊆ Empty returned real constant-only `(3,7), []` counterexamples. Negative probe claiming check_step for UnknownId failed its postcondition (**0 verified, 1 error**). All throwaway sources removed.

H5 merged public statements for citation:
- `resource_error` (`crates/junco-core/src/spec/semantics.rs`): exactly GraphBudget, GraphIndex, AllocationFailed, ArenaExhausted, IdExhausted, RevisionExhausted and Limit. `rule_constants_tagged<E>` (same file) requires each constant extracted for coordinate i to have `E::coordinate_spec(value) == i`.
- `check_step` and `permits_result` (`crates/history-semantics/src/spec/monitor.rs`): their Err arm is `resource_error(error)`, preserving the grant/denial and exact-index meaning.
- `Validator::check` and `Validator::permits` (`crates/history-semantics/src/validator.rs`): under existing well-formedness precondition and event_obligations, `result matches Err(error) ==> resource_error(error)`.
- `ValidatorBuilder::add_rule` (same file): event_obligations, rule_wf, exact event arity and rule_constants_tagged imply `result is Ok || (result matches Err(CompileError::Runtime(error)) && resource_error(error))`; original success/frame clauses retained.
- `PolicyAnalyzer::{covered,redundant,at_least_as_strict}` (`crates/history-analysis/src/analyzer.rs`): under existing requires and ids_owned for all query ids, `result matches Err(error) ==> resource_error(error)`. Invalid ids retain exact UnknownId classification.
- `PolicyAnalyzer::add_rule` (same file): under existing capacity/wf/event requires, rule_wf + exact arity + rule_constants_tagged imply Ok or Runtime(resource_error); original success/frame clauses retained.
- `PolicyAnalyzer::tail_included` (same file): under existing capacity/wf/event requires, head_tails_wf + exact arity + rule_constants_tagged for both source rules imply Ok or Runtime(resource_error). Success additionally implies head_coordinates_wf(head), retaining head_tails_wf and exact arity.
- `theorem_monitor_resource_errors` (`crates/history-semantics/tests/reviewer.rs`): check_step/permits_result imply resource-only errors and exclude UnknownId. Executable `valid_rule_registration` consumes the builder guarantee.
- Executable `resource_checked_registration` and `resource_checked_tail_inclusion` (`crates/history-analysis/tests/reviewer.rs`) consume valid-input classification; `analyzer_client` now consumes resource classification of the three owned-id queries.

H2 measurements: geometric means of per-instance Criterion mean estimates, microseconds, on the same local Xeon E7-8867 v4 host and Rust 1.98.1. Both runs used 50 flat samples, 500 ms warm-up, 2 s measurement targets. After-run validation is excluded from measured intervals; per-iteration clock/cache effects are explicitly disclosed, no statistical attribution claimed.

| Instances | Count | Before (µs) | After (µs) | Change |
|---|---:|---:|---:|---:|
| sat | 90 | 3921.646 | 3934.784 | +0.34% |
| unsat | 10 | 888.158 | 813.993 | −8.35% |
| all | 100 | 3380.419 | 3361.173 | −0.57% |

All per-instance mean/median/95%-CI values: `benches/smt/counterexample-timings.csv` on `fix/audit-h2`; baseline JSONs: `/tmp/junco-audit-bench/criterion/regexlib_subset/*/*/{before-declared-units,after-declared-units}/estimates.json`. No paper files or pre-existing figure data changed. No new public Verus statement in H2: benchmark configuration/validation only.
H2 citation: no new or changed public Verus statement. `benchmark_regexlib_subset` (`benches/smt/main.rs`) uses the existing `PolicyAnalyzer::tail_included` contract with `{()}` domains at coordinates 0 and 2 and the complete representative alphabet at coordinate 1, and checks every returned counterexample with the concrete matcher. Data and method are in `benches/smt/counterexample-timings.csv` and `benches/smt/README.md` at merge commit `5e10a8c`.

H7 prerequisites/evidence: installed Python 3.12.12 + agentdojo 0.1.34 at `/tmp/junco-audit-agentdojo-python`; actual `--self-test` passed (real worker/scorer and scripted native P/Q isolation). Existing configured GitHub credential was tried without disclosure; the real provider invocation returned HTTP 403. Failed-run score fields are not usable benchmark utility/attack values. Configured GITHUB_TOKEN and harness token cache were absent; inspected local corpora were event-only, with no genuine P/Q scripts found in the inspected locations (broader search inconclusive). Fresh provider access or genuine replay scripts are needed. No credentials were committed or printed; temporary auth runner removed.

H7 timing evidence: all 24 lock-policy warm read-only decision cases rerun before/after; geometric mean **703.940 ns → 735.967 ns (+4.55%)**. Per-case mean/median/95%-CI values are in `fuzz/benches/lock-policy/verified-commit-timings.csv` on PR #22; this does not measure changed ingestion latency. Actual event-only replay time (I/O excluded): enforce **138.960894 ms**, audit **136.313456 ms**. No paired utility, attack success or deny-prefix counterfactual score is claimed.

Inbox re-fetched on direct user request: all three messages above reread; no new message. Concurrent changes remain owned by their authors; no inferred intent.


Toolchain: downloaded pinned Z3 cannot execute on host glibc 2.31. Existing `/ssd0/zkent/junco-proof-tools/compat-verus` and `z3-compat` pass the script's pinned version checks; these are used for verification.

Inbox: acknowledged **2026-11-13: Port H1 and H6 from attempt A (PR #12) first**, fetched at handoff `cb24ee9`. Read A's reviewer source at `c441afd`; H1 has equivalent slot-domain exclusion and the declared-coordinate-zero lemma. H6 now precedes H3/H4/H5. No other A changes will be imported; no merge/rebase onto A. Initial inbox was empty. Poll at every gate and at least every 30 minutes; vacuity messages preempt all work.

Inbox additionally acknowledged **2026-11-13: Vacuity probe results (no blocker; priorities unchanged)** at handoff `5e6505f`. No inconsistency reported. Exact `pos_ac1_junk_cex_declared` source/contract run at H1 head: **expected postcondition failure**, **0 verified, 1 error** in probe; analyzer library **603 verified, 0 errors**. Result posted to PR #13; throwaway source removed. New H14 scope: show reachable `Ok` results, not only conditional client guarantees.

Inbox additionally acknowledged **2026-11-13: Submission cleanup PR; no plan ids in new text** at handoff `a25a1e7`. H1 remains unchanged. Will rebase open branches after cleanup merges, preserve cleanup-side comment wording and reapply semantic changes. New code/comments/docs use descriptive wording; item ids only in STATUS.md and PR titles. Last inbox fetch at this gate showed no new messages.

Delivery uses one branch/PR per item into main, and this separate status branch, as requested by user (superseding handoff's integration-PR instructions).
