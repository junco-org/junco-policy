# Audit slice: VacuityProbes (Verus probes at PR head 969449b)

Worktree: `/tmp/audit-VacuityProbes` (detached at 969449b; probe files uncommitted, throwaway).
Toolchain: `scripts/verify-all.sh --download` → Verus 0.2026.10.04.426d8b0, Z3 4.16.0, Rust 1.98.1 (sha256-checked).
Toolchain + cargo target dir moved to `/home/zak/.cache/audit-vp/` (see Setup notes). Logs: `/home/zak/.cache/audit-vp/*.log`.

## Verdict summary

- **No BLOCKER found.** Every `ensures false` probe (13 of them across axioms, hypothesis bundles, and the premises of every reviewer theorem that has `requires`), plus 3 other must-fail probes (`neg_p4a`, `neg_th2` ×2), **fails** to verify with `postcondition not satisfied` (no timeouts/rlimit). No inconsistency between the five key axioms, the R4 witnesses, `group_kernel_views` and the vstd groups (seq/set/vec/laws_cmp/laws_eq/hash/array/slice).
- **Premises are satisfiable by concrete witnesses** (not just "not refutable"): theorem_analyzer_to_monitor (nontrivial 2-rule policy, refinement Holds, both validators grant), covered_spec Holds, covered_spec Counterexample, theorem_vacuity_corollaries (v_always = Holds), run_ok/theorem_trace_safe (2-step run: grant then denial). `hash_coherent::<Component2<u32,u64>>()` is neither provable nor refutable.
- **Spec non-triviality holds on undeclared domains**: Holds arms of tail_included_spec / covered_spec / at_least_as_strict_spec are provably false when the property fails; a bogus counterexample (instance exists but is not a failure) is rejected; non-shortest counterexamples are rejected (A4 `shortest`, A6 `minimal_in_case`); check_step rejects Grant when a rule is violated and Denied when none is; trace_safe is false on a history containing a forbidden event.
- **MAJOR confirmed by Verus (AnalyzerClaims request):** with a declared domain at coordinate 0 whose value is known, the junk counterexample (all `Fresh(0)`, empty history) satisfies the Counterexample arm of `covered_spec` and `tail_included_spec` **for any rule/policy/tails**, including a rule that is provably covered (`covers(...)` proved in the same lemma). It has no admissible instance and fails `capacity_for`, so every clause of `counterexample_spec`/`minimal_in_case`/`shortest` is vacuous. Concrete `(u32,u64)` instance verified under `hash_coherent` only. Consequence: on analyzers with declared domains (the eval declares domains, per AnalyzerClaims), R6 does not guarantee a returned Counterexample refutes anything; paper appendix.tex:856-859 ("capacity only on undeclared components suffices") overclaims. Fix: add to `counterexample_spec` "no `Fresh` at any declared coordinate" (`forall i. domains[i] is Some ==> fresh_used(cex,i) is empty`), which the analyzer proves internally (`reconstruction::slot_domain`, per AnalyzerClaims) but does not export; or weaken the paper.
- **MAJOR confirmed by Verus (MonitorClaims request):** a `check` that always returns `Err(HistoryError::AllocationFailed)` satisfies `check_frame`, `check_step` and the reviewer-facing `stmt_monitor_check`; and `check_step(v, req, Err(GraphBudget{limit:0}))` holds for every `v`, `req` (generic `E`, `M`). The monitor contract says nothing about when a decision (vs. a non-Invariant error) is returned — the monitor analogue of the known `Exhausted` issue.
- **Counts reproduced:** semantics reviewer target **7 verified, 0 errors** (VERIFY.md: 7); analysis reviewer target **14 verified, 0 errors** (VERIFY.md: 14). Libraries along the way: history-syntax 60, junco-core (runtime,std) 287, history-store 289, history-semantics (runtime,std) 1619, history-semantics (runtime,std,cache) 1624, history-analysis 603 — all 0 errors, matching VERIFY.md rows. Two helper crates: 56 and 36 verified; a 2060-verified run precedes history-syntax ([INFERENCE] vstd, it follows `Compiling vstd`).

## Setup notes (reproducibility)

- `/tmp` is a 3.9 GB tmpfs (RAM-backed). With the Verus download (2.2 GB) and target dir on `/tmp`, the first run was **OOM-killed** while verifying history-semantics (`signal: 9, SIGKILL`, log line "process didn't exit successfully ... history_semantics"). Moving `/tmp/verus-dl` and `target/` to `/home/zak/.cache/audit-vp/` (disk) fixed it. Recommend VERIFY.md mention memory: ~3–4 GB free needed for history-semantics with default threads on 2 cores.
- Per-probe cost: once the dependency crates are verified and cached, `cargo verus verify --locked -p <pkg> --features ... --test <new_test_file>` re-verifies only the new test crate (≈4–7 s). Partial selectors (`--verify-module`, `--verify-function`) are rejected by `cargo verus verify` ("Partial verification must use `cargo verus focus`"); use `cargo verus focus -p <pkg> ... -- --verify-module <m>`.
- Env: `PATH=/home/zak/.cache/audit-vp/verus-dl/verus-dist/verus-x86-linux:$PATH RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu VERUS_Z3_PATH=/home/zak/.cache/audit-vp/verus-dl/z3/z3-4.16.0-x64-glibc-2.39/bin/z3`, cwd `/tmp/audit-VacuityProbes`.

## Commands and observed output

| # | Command | Observed |
|---|---|---|
| 5a | `cargo verus verify --locked -p history-analysis --no-default-features --features runtime,std --test reviewer` | exit 0; `1619 verified, 0 errors` (history-semantics), `603 verified, 0 errors` (history-analysis), `14 verified, 0 errors` (tests/reviewer.rs); deps cached from an earlier run that reported 2060/60/56/36/287/289 all 0 errors. Wall 1195 s (incl. 5b-probes). |
| 5b | `cargo verus verify --locked -p history-semantics --features runtime,std,cache --test reviewer` | exit 0; `287`, `289`, `1624 verified, 0 errors`, `7 verified, 0 errors` (tests/reviewer.rs). Wall ≈1100 s. |
| A | `cargo verus verify --locked -p history-analysis --no-default-features --features runtime,std --test vacuity_probes` | exit 101 (expected); **`16 verified, 12 errors`**; all 12 errors are `postcondition not satisfied` on exactly the 12 `neg_*` functions; every `pos_*` and helper lemma verified. |
| S | `cargo verus verify --locked -p history-semantics --features runtime,std,cache --test vacuity_probes` | exit 101 (expected); **`6 verified, 4 errors`**; the 4 errors are `postcondition not satisfied` on exactly the 4 `neg_*` functions; all 6 `pos_*` verified. |
| PIF | `cargo verus focus --locked -p history-semantics --features runtime,std,cache -- --verify-module verify::refinement::search` (probe added to lib file search.rs) | see PaperIndexFidelity section |

## Per-probe results

Legend: NEG = must FAIL (a pass would be a BLOCKER); POS = should verify.

### Probe 1 — axiom consistency (file A)
| Function | Kind | Result | Verdict |
|---|---|---|---|
| `neg_p1_key_axioms_consistent` (broadcast use group_internal_key_axioms + group_kernel_views + vstd set/vec/laws_cmp/laws_eq/std_specs::hash groups, module-level seq/array/slice groups; asserts all instantiated: hash_coherent for (RegexId,RegexId), (TestId,TestId), SmallVec<[RegexId;4]>, obeys_eq_spec, a.eq_spec(&a)) | NEG | failed: postcondition not satisfied (line 92) | consistent (no false derivable) |
| `neg_p1b_key_axioms_with_u32_u64_hypotheses` (same groups + `requires hash_coherent::<Component2<u32,u64>>()` + `lemma_u32_u64_event_hypotheses()`) | NEG | failed (line 108) | consistent |
| `pos_p1c_smallvec_eq_exec` (exec: `SmallVec::new() == SmallVec::new()` asserted true) | POS | verified | SmallVec axiom + assume_specification(new) give the expected exec equality |
| `neg_p1d_smallvec_eq_exec` (same + `ensures false`) | NEG | failed (line 129) | exec specs + axiom consistent |
| TrustHypotheses P2: `neg_th2_hash_coherent_provable` (`ensures hash_coherent::<C>()`, key axioms in scope) | NEG | failed (line 499) | token not provable |
| TrustHypotheses P2: `neg_th2_hash_coherent_refutable` (`ensures !hash_coherent::<C>()`) | NEG | failed (line 505) | token not refutable → satisfiable premise |

### Probe 2 — hypotheses satisfiable (files A, S)
| Function | Kind | Result |
|---|---|---|
| `neg_p2a_hash_coherent_u32_u64` (requires hash_coherent C; lemma; asserts event_obligations, analyzer_obligations, views_surjective) | NEG | failed (line 142) |
| `neg_p2b_event_obligations_u32_u64` (requires event_obligations::<(u32,u64)>, plus a well_tagged witness to fire views_surjective) | NEG | failed (line 152) |
| `neg_p2c_analyzer_obligations_u32_u64` | NEG | failed (line 160) |
| `neg_p2d_event_obligations_generic<E>` | NEG | failed (line 166) |
| `neg_p2e_all_concrete_witnesses` (hash_coherent for Component2<u32,u64>, Component3<u8,u8,u8>, Component3<u32,u8,bool>; all three witness lemmas + key axioms) | NEG | failed (line 173) |
| `neg_p2m_hash_coherent_u32_u64` (semantics crate) | NEG | failed (S line 200) |
Verdict: no bundle is refutable by Z3; combined with Probe 1/TH2 there is no evidence of vacuity. (Satisfiability in the semantic sense is not *proved*—`hash_coherent` is uninterpreted—but nothing in the axioms constrains it to false.)

### Probe 3 — reviewer theorem premises (files A, S)
| Function | Kind | Result |
|---|---|---|
| `neg_p3a_analyzer_to_monitor_premises<E,M>` (exact requires of analysis `theorem_analyzer_to_monitor`) | NEG | failed (line 195) |
| `pos_p3b_analyzer_to_monitor_witness` — concrete: a.rules = [forbid (7,y).All, forbid (x,9).All], p=[0,1], q=[0], domains [None,None], request (1,2), both results `Ok(Grant)`; proves `at_least_as_strict_spec(a,p,q,Holds)` (i.e. refines), in_domains, both check_step, result_p Grant | POS | verified |
| `pos_p3c_covered_holds_witness` (forbid (x,y).All covered by itself; covered_spec Holds) | POS | verified |
| `pos_p3d_covered_counterexample_witness` (rule forbid (x,y).All, by = [], cex ((C0 1,C1 1),[]); full covered_spec Counterexample incl. counterexample_spec, every_instance, cex_has_instance, !covers, minimal_in_case) | POS | verified |
| `pos_p3e_vacuity_corollaries_witness` (rules [r7, forbid_all(r7.head)], v_never = Exhausted, v_always = Holds) | POS | verified |
| `neg_p3m_trace_safe_premises<E,M>` (run_ok, 0<=k<len) | NEG | failed (S line 61) |
| `neg_p3m_monitor_check_premises<E,M>` (check_frame ∧ check_step) | NEG | failed (S line 70) |
| `neg_p3m_analyzer_to_monitor_premises<E,M>` (semantics `theorem_analyzer_to_monitor`) | NEG | failed (S line 85) |
| `pos_p3m_run_witness` — concrete run: rules [forbid (7,y).All]; Check((1,2)) → Grant, then Check((7,0)) → Denied{mode: Forbid}; proves run_ok and trace_safe of the final state | POS | verified |
A1–A6 theorems have no `requires`; their antecedents (`covered_spec`/`at_least_as_strict_spec` with Holds/Counterexample) are shown satisfiable by p3b–p3e. Note: `Step`, `step_ok`, `run_ok`, `stmt_monitor_check` were copied verbatim from tests/reviewer.rs (test crates cannot import each other).

### Probe 4 — spec non-triviality (files A, S)
| Function | Kind | Result |
|---|---|---|
| `pos_p4a_tail_holds_rejected`: `!tail_included_spec(av([]), [C0 5, y], All, Empty, Holds)` | POS | verified |
| `neg_p4a_tail_holds_accepted`: same with `ensures tail_included_spec(...)` | NEG | failed (line 321) |
| `pos_p4b_tail_bogus_cex_rejected`: `!tail_included_spec(.., All, All, Counterexample(((5,0),[])))` (instance exists but right=All, so not a failure) | POS | verified |
| `pos_p4c_tail_nonshortest_cex_rejected`: cex with history length 1 rejected when (5,0),[] already fails (`shortest`) | POS | verified |
| `pos_p4d_covered_holds_rejected`: `!covered_spec(av([forbid (5,y).All]), 0, [], Holds)` | POS | verified |
| `pos_p4e_covered_nonminimal_cex_rejected`: covered cex with history length 1 rejected (A6 `minimal_in_case`/`shortest_in_case`) | POS | verified |
| `pos_p4f_strict_holds_rejected`: `!at_least_as_strict_spec(av([forbid (x,y).All]), [], [0], Holds)` | POS | verified (after adding trigger hints) |
| `pos_p4m_check_step_no_grant_when_violated`: for all `r` matching `Ok(Grant(_))`, `!check_step(v, (7,0), r)` with v.rules = [forbid (7,y).All] | POS | verified |
| `pos_p4m_check_step_no_denial_when_permitted`: for all `r` matching `Ok(Denied(_))`, `!check_step(v, (1,0), r)` | POS | verified |
| `pos_p4m_trace_safe_nontrivial`: `!trace_safe({rules:[forbid (7,y).All], history:[(7,0)]})` | POS | verified |
| `pos_p4m_check_step_err_always_allowed<E,M>`: `check_step(v, req, Err(GraphBudget{limit:0}))` for all v, req | POS (observation) | verified — Err (non-Invariant) is allowed in every state |
Verdict: Holds/Grant/Denied arms are non-trivial; Counterexample arms are non-trivial **on undeclared coordinates** (see AC probes for declared ones).

### Probe 5 — wf reachable / exec clients
Both reviewer targets verify with the documented counts (7 and 14, 0 errors), so `monitor_client`, `monitor_client_u32_u64`, `analyzer_client`, `analyzer_client_u32_u64` verify against the public contracts: `PolicyAnalyzer::new` returns `Self` (not `Result`) with `ensures result.wf()`, so analyzer wf is reachable by any terminating call (no `exec_allows_no_decreases_clause` per TRUST.md; its loops carry `decreases`). Caveat (observed in contracts, not probed): every later postcondition in both clients is under `result matches Ok(..)` — `Store::new()?`, `builder.add_rule(rule)?`, `builder.finish()?` (monitor) and `add_rule(rule)?` (analyzer) may return `Err` without restriction (`add_rule` ensures only `result is Err ==> rules unchanged` and `no_invariant_compile_failure`), so the clients do not show that an `Ok` state (hence `Validator::wf`) is ever reached; and each query's `Ok(v)` arm may never occur (`covered` ensures only `no_invariant_failure` + `Ok ==> spec`). This is the same "errors are unconstrained" pattern as MC1.

### AnalyzerClaims request — junk counterexample at a declared coordinate (file A)
```
pos_ac1_junk_cex_declared<E>(a, rule, by, head, left, right, x)
  requires eq_equivalence::<E::Component>(), arity::<E>() >= 1, a.domains.len() == arity, a.known.len() == arity,
           a.domains[0] == Some({x}), a.known[0].contains(x)
  ensures  covered_spec(a, rule, by, Counterexample(junk)) && tail_included_spec(a, head, left, right, Counterexample(junk))
           && !cex_has_instance(a.domains, a.known, junk) && !capacity_for(a.domains, a.known, junk)
  where junk = CexView { candidate: Seq::new(arity, |i| Fresh(0)), history: [] }
```
**VERIFIED.** `pos_ac2_junk_cex_for_covered_rule` (adds `rule < a.rules.len()`, `by = [rule]`; ensures `covers(a.domains, rules_of(a,[rule]), a.rules[rule])` **and** `covered_spec(a, rule, [rule], Counterexample(junk))`) **VERIFIED.** `pos_ac3_junk_cex_concrete` ((u32,u64), domains `[Some({C0 3}), None]`, known `[{C0 3}, {}]` (= `declared_sets(domains)` ∪ rule constants for r = forbid (x,y).All), rules `[forbid (x,y).All]`, premise `hash_coherent::<Component2<u32,u64>>()` only) **VERIFIED.**
Severity: MAJOR (R6 materially weaker than presented whenever a domain is declared). Paper: appendix.tex:856-859 (capacity on undeclared components); "decides"/"only correct verdicts" claims (main.tex:104, intro.tex:94 per AnalyzerClaims). Artifact: crates/history-analysis/src/spec/analyzer.rs:145-151 (`counterexample_spec`), 155-167 (`covered_spec`), 220-231 (`tail_included_spec`); crates/junco-core/src/spec/questions.rs:168-177 (`choice_ok` requires `in_domain` and `!eq known`, unsatisfiable at a declared coordinate whose values are all known — which `new` makes the case: `known == declared_sets(domains)`). Fix: export `forall|i| 0 <= i < arity && domains[i] is Some ==> fresh_used(cex, i) =~= ISet::empty()` in `counterexample_spec` (or require `cex_has_instance` unconditionally when no undeclared coordinate is fresh); otherwise reword the paper.

### MonitorClaims request — always-Err satisfies check's contract (file S)
```
pos_mc1_always_error_satisfies_contract<E, M>(before, request)
  ensures check_frame(before, before, request, Err(AllocationFailed)),
          check_step(before, request, Err(AllocationFailed)),
          stmt_monitor_check(before, request, Err(AllocationFailed))
{}
```
**VERIFIED.** Severity MAJOR per MonitorClaims (paper's monitor "completeness"/"equivalence" says nothing about when Err is returned). Artifact: crates/history-semantics/src/spec/monitor.rs:43-53 (`Err(error) => !(error is Invariant)`).

### PaperIndexFidelity request — premise of `search::stmt_search_correct` (lib, throwaway, now removed)
Placed after `theorem_search_correct` in crates/history-semantics/src/verify/refinement/search.rs (a named domain `probe_d2()` was needed because Verus rejects `seq![..]` inside a trigger; the `exists` needed a named predicate for a trigger):
```rust
// THROWAWAY audit probes (PaperIndexFidelity request).
pub open spec fn probe_d2() -> NDomains { seq![Option::<Set<nat>>::None, None] }

pub proof fn probe_scc(cases_of: spec_fn(Item) -> Set<Case>)
    ensures !(forall|i: Item| #[trigger] steps_ok(probe_d2(), i, cases_of(i))),
{
}

pub open spec fn probe_all_steps_ok(cases_of: spec_fn(Item) -> Set<Case>) -> bool {
    forall|i: Item| #[trigger] steps_ok(probe_d2(), i, cases_of(i))
}

pub proof fn probe_scc_exists()
    ensures exists|cases_of: spec_fn(Item) -> Set<Case>| #[trigger] probe_all_steps_ok(cases_of),
{
}
```
Command: `cargo verus focus --locked -p history-semantics --features runtime,std,cache -- --verify-module verify::refinement::search`.
Observed: `27 verified, 2 errors (partial verification with --verify-*)`; both errors `postcondition not satisfied` (lines 1106 `probe_scc`, 1115 `probe_scc_exists`). The rest of the module (incl. `theorem_search_correct`) verified.
Verdict: **inconclusive, as predicted** — Z3 can neither refute nor establish `forall|i: Item| steps_ok(d, i, cases_of(i))` without manual witnesses. A proof of unsatisfiability would need a manual fresh-value/pigeonhole argument (finite `Set<Case>` and finite `Constraint = Set<Literal>` mention finitely many constants; for an ill-scoped state like `Test(And[x0 = θ0, x0 = θ1])` choose θ = (v,v) and θ' = (v,v') with v, v' outside those constants; θ and θ' satisfy the same literals, so the case covering (θ,(v,0)) must also be uniformly realizable at θ', forcing e0 = v = v' if α contains both atoms; if α omits one atom, `successor_ok` fails because nullability of `next` is θ-independent) [INFERENCE: argument not mechanized]. Report status: "premise not dischargeable automatically; plausibly unsatisfiable because `forall i: Item` ranges over ill-scoped states"; affects only the paper-index statement, since the executable path uses `lemma_search_correct` with `trace_steps_ok`.
The lib file was restored afterwards (the worktree's only changes are the two untracked test files).

## Findings (consolidated, for the parent)

1. **MAJOR — R6 Counterexample arms are vacuous at declared coordinates** (Verus-confirmed, pos_ac1–ac3). Paper appendix.tex:856-859; artifact crates/history-analysis/src/spec/analyzer.rs:145-167, 220-231; crates/junco-core/src/spec/questions.rs:168-188. Evidence: `counterexample_spec` = `cex_arity ∧ every_instance ∧ (capacity_for ⇒ cex_has_instance)`; with `domains[0] = Some({x})`, `known[0] ∋ x`, `choice_ok` at coordinate 0 needs `in_domain({x}, f(0))` and `!f(0).eq_spec(&x)` — unsatisfiable, so no instance and no capacity. Fix: export "no `Fresh` at declared coordinates" in `counterexample_spec`.
2. **MAJOR — monitor contract allows `Err` (non-Invariant) in every state** (Verus-confirmed, pos_mc1 and pos_p4m_check_step_err_always_allowed). Artifact crates/history-semantics/src/spec/monitor.rs:51 (`Err(error) => !(error is Invariant)`). Paper wording per MonitorClaims.
3. **MINOR — the reviewer exec clients do not show `Ok` is reachable.** All client postconditions are under `result matches Ok(...)`; constructors `Store::new`, `ValidatorBuilder::add_rule`/`finish`, `PolicyAnalyzer::add_rule` may return `Err` unconditionally. "wf reachable" is established for `PolicyAnalyzer::new` (returns `Self`, ensures `wf()`), not for `Validator` (only reachable via `finish()?`). [observed in contracts; not separately probed]
4. **MINOR (doc) — VERIFY.md resource note**: on this 7.8 GB machine with `/tmp` as tmpfs, verification of history-semantics was OOM-killed until the Verus download and target dir were moved off tmpfs. VERIFY.md:43 already notes SIGKILL at 16 threads; it could add that the ~2.2 GB unpacked toolchain plus target must not live on a RAM-backed `/tmp`.
5. **MINOR — `stmt_search_correct` premise likely unsatisfiable** (PaperIndexFidelity's claim; Verus probe inconclusive as above).

## Checked and found accurate
- Five key axioms are mutually consistent with vstd groups and R4 witnesses (neg_p1, neg_p1b, neg_p1d fail).
- `hash_coherent::<Component2<u32,u64>>()` neither provable nor refutable (neg_th2 ×2 fail).
- event_obligations / analyzer_obligations (concrete (u32,u64), generic E, and all three concrete witness lemmas together) not refutable (neg_p2a–e, neg_p2m fail).
- Premises of theorem_trace_safe, theorem_monitor_check, both theorem_analyzer_to_monitor (semantics and analysis), theorem_vacuity_corollaries are not contradictory (neg fail) and have concrete witnesses (pos_p3b–e, pos_p3m_run_witness).
- Holds arms of tail_included/covered/at_least_as_strict are false when the property fails (pos_p4a, p4d, p4f; neg_p4a fails).
- Counterexample arms reject non-failures and non-shortest counterexamples on undeclared domains (pos_p4b, p4c, p4e).
- check_step rejects Grant on a violated rule and Denied on a permitted candidate; trace_safe is non-trivial (pos_p4m_*).
- VERIFY.md counts reproduced: 7 (semantics reviewer), 14 (analysis reviewer), 60, 287, 289, 1619, 1624, 603; all 0 errors.

## Worktree / artifacts
- Kept as evidence: worktree `/tmp/audit-VacuityProbes` (detached 969449b; only untracked `crates/history-analysis/tests/vacuity_probes.rs`, `crates/history-semantics/tests/vacuity_probes.rs`, and a `target` symlink); toolchain + target at `/home/zak/.cache/audit-vp/` (≈2.8 GB, on disk); logs `a-reviewer.log`, `a-probes-final.log`, `s-reviewer.log`, `s-probes.log`, `s-search-probe.log` there. Remove with `git -C /home/zak/work/main worktree remove --force /tmp/audit-VacuityProbes && rm -rf /home/zak/.cache/audit-vp` when no longer needed.
- Re-run: `. /home/zak/.cache/audit-vp/env.sh` then the commands in the table above.

## Probe source A: crates/history-analysis/tests/vacuity_probes.rs
```rust
//! THROWAWAY vacuity probes (audit). `neg_*` must FAIL to verify; `pos_*` must verify.
#![cfg(all(verus_keep_ghost, feature = "runtime"))]
#![allow(unused_imports)]

extern crate alloc;

use history_analysis::spec::analyzer::*;
use history_analysis::verify::analyzer_obligations;
use history_analysis::verify::key_axioms::*;
use history_semantics::spec::monitor::{ValidatorView, check_step};
use history_semantics::validator::Decision;
use history_syntax::event::{Component2, Component3};
use history_syntax::spec::events::*;
use history_syntax::{Event, RuleMode};
use junco_core::event::{Grant, Request};
use junco_core::kernel::{RegexId, TestId};
use junco_core::spec::hypotheses::*;
use junco_core::spec::questions::*;
use junco_core::spec::semantics::*;
use junco_core::verify::hypotheses::*;
use junco_core::HistoryError;
use smallvec::SmallVec;
use vstd::prelude::*;
use history_syntax::event::specs::EventSpec;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::array::group_array_axioms, vstd::slice::group_slice_axioms};

pub type C = Component2<u32, u64>;
pub type E2 = (u32, u64);

pub open spec fn var(n: char) -> PatternView<C> { PatternView::Variable(seq![n]) }
pub open spec fn k0(v: u32) -> PatternView<C> { PatternView::Constant(Component2::C0(v)) }
pub open spec fn k1(v: u64) -> PatternView<C> { PatternView::Constant(Component2::C1(v)) }
pub open spec fn forbid(head: HeadView<C>, tail: RegexView<C>) -> RuleView<C> {
    RuleView { mode: RuleMode::Forbid, head, tail }
}
pub open spec fn inf2() -> DomainsView<C> { seq![None::<Set<C>>, None::<Set<C>>] }
pub open spec fn none_known() -> Seq<Set<C>> { seq![Set::<C>::empty(), Set::<C>::empty()] }
pub open spec fn av(rules: Seq<RuleView<C>>) -> AnalyzerView<C> {
    AnalyzerView { domains: inf2(), rules, known: none_known() }
}
/// forbid (x, y) . All : violated by every candidate.
pub open spec fn r_all() -> RuleView<C> { forbid(seq![var('x'), var('y')], RegexView::All) }
/// forbid (7, y) . All
pub open spec fn r7() -> RuleView<C> { forbid(seq![k0(7), var('y')], RegexView::All) }
/// forbid (x, 9) . All
pub open spec fn r9() -> RuleView<C> { forbid(seq![var('x'), k1(9)], RegexView::All) }
pub open spec fn cc(a: u32, b: u64) -> ComponentsView<C> {
    seq![ValueView::Constant(Component2::C0(a)), ValueView::Constant(Component2::C1(b))]
}
pub open spec fn any_f() -> FreshChoice<C> {
    seq![|n: nat| Component2::<u32, u64>::C0(0u32), |n: nat| Component2::<u32, u64>::C1(0u64)]
}

proof fn lemma_in_domains(c: E2, h: Seq<E2>)
    ensures in_domains::<E2>(inf2(), c, h),
{
    assert(event_view(c).len() == 2);
    assert forall|i: int| 0 <= i < history_view(h).len() implies #[trigger] event_in(inf2(), history_view(h)[i]) by {
        assert(history_view(h)[i] == event_view(h[i]));
    }
}

proof fn lemma_constant_cex_admissible(cex: CexView<C>, known: Seq<Set<C>>)
    requires known.len() == 2, cex_arity(cex, 2),
        forall|i: int| 0 <= i < 2 ==> #[trigger] cex.candidate[i] is Constant,
        forall|j: int, i: int| 0 <= j < cex.history.len() && 0 <= i < 2 ==> #[trigger] cex.history[j][i] is Constant,
    ensures admissible::<E2>(inf2(), known, cex, any_f()),
{
    assert forall|i: int| 0 <= i < 2 implies choice_ok::<E2>(#[trigger] any_f()[i], fresh_used(cex, i), known[i], inf2()[i], i) by {
        assert forall|n: nat| !fresh_used(cex, i).contains(n) by {
            if fresh_used(cex, i).contains(n) {
                if exists|j: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
                    && #[trigger] cex.history[j][i] == ValueView::<C>::Fresh(n) {
                    let j = choose|j: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
                        && #[trigger] cex.history[j][i] == ValueView::<C>::Fresh(n);
                    assert(cex.history[j][i] is Constant);
                } else {
                    assert(cex.candidate[i] is Constant);
                }
            }
        }
    }
}

// ===================== Probe 1: axiom consistency =====================

proof fn neg_p1_key_axioms_consistent()
    ensures false,
{
    broadcast use {group_internal_key_axioms, junco_core::kernel::verify::group_kernel_views,
        vstd::set::group_set_lemmas, vstd::std_specs::vec::group_vec_axioms,
        vstd::laws_cmp::group_laws_cmp, vstd::laws_eq::group_laws_eq,
        vstd::std_specs::hash::group_hash_axioms};
    assert(hash_coherent::<(RegexId, RegexId)>());
    assert(hash_coherent::<(TestId, TestId)>());
    assert(hash_coherent::<SmallVec<[RegexId; 4]>>());
    assert(<SmallVec<[RegexId; 4]> as PartialEqSpec>::obeys_eq_spec());
    let a = arbitrary::<SmallVec<[RegexId; 4]>>();
    assert(a.eq_spec(&a));
}

proof fn neg_p1b_key_axioms_with_u32_u64_hypotheses()
    requires hash_coherent::<C>(),
    ensures false,
{
    broadcast use {group_internal_key_axioms, junco_core::kernel::verify::group_kernel_views,
        vstd::set::group_set_lemmas, vstd::std_specs::vec::group_vec_axioms,
        vstd::laws_cmp::group_laws_cmp, vstd::laws_eq::group_laws_eq,
        vstd::std_specs::hash::group_hash_axioms};
    lemma_u32_u64_event_hypotheses();
    assert(event_obligations::<E2>());
    assert(<SmallVec<[RegexId; 4]> as PartialEqSpec>::obeys_eq_spec());
}

/// Positive: exec `==` on SmallVec follows the axiom (two empty vectors are equal).
fn pos_p1c_smallvec_eq_exec() {
    broadcast use group_internal_key_axioms;
    let a: SmallVec<[RegexId; 4]> = SmallVec::new();
    let b: SmallVec<[RegexId; 4]> = SmallVec::new();
    let e = a == b;
    assert(e);
}

fn neg_p1d_smallvec_eq_exec()
    ensures false,
{
    broadcast use group_internal_key_axioms;
    let a: SmallVec<[RegexId; 4]> = SmallVec::new();
    let b: SmallVec<[RegexId; 4]> = SmallVec::new();
    let e = a == b;
    assert(e);
}

// ===================== Probe 2: hypotheses satisfiable =====================

proof fn neg_p2a_hash_coherent_u32_u64()
    requires hash_coherent::<C>(),
    ensures false,
{
    lemma_u32_u64_event_hypotheses();
    assert(event_obligations::<E2>());
    assert(analyzer_obligations::<E2>());
    assert(views_surjective::<E2>());
}

proof fn neg_p2b_event_obligations_u32_u64()
    requires event_obligations::<E2>(),
    ensures false,
{
    let xs = seq![Component2::<u32, u64>::C0(1u32), Component2::<u32, u64>::C1(2u64)];
    assert(well_tagged::<E2>(xs));
}

proof fn neg_p2c_analyzer_obligations_u32_u64()
    requires analyzer_obligations::<E2>(),
    ensures false,
{
}

proof fn neg_p2d_event_obligations_generic<E: Event>()
    requires event_obligations::<E>(),
    ensures false,
{
}

proof fn neg_p2e_all_concrete_witnesses()
    requires hash_coherent::<C>(), hash_coherent::<Component3<u8, u8, u8>>(),
        hash_coherent::<Component3<u32, u8, bool>>(),
    ensures false,
{
    broadcast use group_internal_key_axioms;
    lemma_u32_u64_event_hypotheses();
    lemma_u8_triple_event_hypotheses();
    lemma_u32_mixed_event_hypotheses();
}

// ===================== Probe 3: reviewer theorem premises satisfiable =====================

/// theorem_analyzer_to_monitor (analysis/tests/reviewer.rs): premises => false must fail.
proof fn neg_p3a_analyzer_to_monitor_premises<E: Event, M>(
    a: AnalyzerView<E::Component>, p: Seq<nat>, q: Seq<nat>,
    vp: ValidatorView<E>, vq: ValidatorView<E>, request: Request<E, M>,
    result_p: Result<Decision<E, M>, HistoryError>, result_q: Result<Decision<E, M>, HistoryError>,
)
    requires
        at_least_as_strict_spec::<E>(a, p, q, InclusionView::Holds),
        vp.rules == rules_of(a, p), vq.rules == rules_of(a, q), vq.history == vp.history,
        in_domains::<E>(a.domains, request.event, vp.history),
        check_step(vp, request, result_p), check_step(vq, request, result_q),
        result_p is Ok && result_p->Ok_0 is Grant,
    ensures false,
{
}

/// Concrete witness for every premise of theorem_analyzer_to_monitor, with nontrivial rules:
/// a.rules = [forbid (7,y).All, forbid (x,9).All], p = [0,1], q = [0], request (1,2) granted by both.
proof fn pos_p3b_analyzer_to_monitor_witness() {
    let a = av(seq![r7(), r9()]);
    let p = seq![0nat, 1nat];
    let q = seq![0nat];
    let req = Request::<E2, ()> { event: (1u32, 2u64), metadata: () };
    let g = Decision::<E2, ()>::Grant(Grant { event: (1u32, 2u64), metadata: () });
    let result_p = Ok::<Decision<E2, ()>, HistoryError>(g);
    let result_q = Ok::<Decision<E2, ()>, HistoryError>(g);
    let vp = ValidatorView::<E2> { rules: rules_of(a, p), history: Seq::empty() };
    let vq = ValidatorView::<E2> { rules: rules_of(a, q), history: Seq::empty() };
    assert(rules_of(a, p) =~= seq![r7(), r9()]);
    assert(rules_of(a, q) =~= seq![r7()]);
    assert(refines::<E2>(a.domains, rules_of(a, p), rules_of(a, q))) by {
        assert forall|c: E2, h: Seq<E2>| in_domains::<E2>(a.domains, c, h) && policy_permits(rules_of(a, p), c, h)
            implies #[trigger] policy_permits(rules_of(a, q), c, h) by {
            if policy_denies(rules_of(a, q), c, h) {
                let i = choose|i: int| 0 <= i < rules_of(a, q).len() && #[trigger] rule_violated(rules_of(a, q)[i], c, h);
                assert(i == 0);
                assert(rule_violated(rules_of(a, p)[0], c, h));
            }
        }
    }
    assert(at_least_as_strict_spec::<E2>(a, p, q, InclusionView::Holds));
    lemma_in_domains((1u32, 2u64), Seq::empty());
    assert(in_domains::<E2>(a.domains, req.event, vp.history));
    // (1,2) matches neither head
    assert(!head_matches(r7().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req.event)[0]));
    }
    assert(!head_matches(r9().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r9().head[1], event_view(req.event)[1]));
    }
    assert(policy_permits(vp.rules, req.event, vp.history)) by {
        if policy_denies(vp.rules, req.event, vp.history) {
            let i = choose|i: int| 0 <= i < vp.rules.len() && #[trigger] rule_violated(vp.rules[i], req.event, vp.history);
            assert(i == 0 || i == 1);
        }
    }
    assert(policy_permits(vq.rules, req.event, vq.history)) by {
        if policy_denies(vq.rules, req.event, vq.history) {
            let i = choose|i: int| 0 <= i < vq.rules.len() && #[trigger] rule_violated(vq.rules[i], req.event, vq.history);
            assert(i == 0);
        }
    }
    assert(check_step(vp, req, result_p));
    assert(check_step(vq, req, result_q));
    assert(result_p is Ok && result_p->Ok_0 is Grant);
}

/// Witness: covered_spec Holds (rule forbid (x,y).All covered by itself).
proof fn pos_p3c_covered_holds_witness() {
    let a = av(seq![r_all()]);
    assert(rules_of(a, seq![0nat]) =~= seq![r_all()]);
    assert forall|c: E2, h: Seq<E2>| in_domains::<E2>(a.domains, c, h) && #[trigger] rule_violated(a.rules[0], c, h)
        implies policy_denies(rules_of(a, seq![0nat]), c, h) by {
        assert(rule_violated(rules_of(a, seq![0nat])[0], c, h));
    }
    assert(covered_spec::<E2>(a, 0, seq![0nat], InclusionView::Holds));
}

/// Witness: covered_spec Counterexample (A1/A2/A6 premise) for forbid (x,y).All by the empty
/// policy, cex = ((C0 1, C1 1), []).
proof fn pos_p3d_covered_counterexample_witness() {
    let a = av(seq![r_all()]);
    let by = Seq::<nat>::empty();
    let cex = CexView { candidate: cc(1, 1), history: Seq::<ComponentsView<C>>::empty() };
    let p = rules_of(a, by);
    assert(p =~= Seq::<RuleView<C>>::empty());
    let r = a.rules[0];
    let fails = uncovered::<E2>(p, r);
    lemma_constant_cex_admissible(cex, a.known);
    let c = (1u32, 1u64);
    let h = Seq::<E2>::empty();
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    assert(cex_has_instance::<E2>(a.domains, a.known, cex));
    assert(head_matches(r.head, event_view(c)));
    assert(rule_violated(r, c, h));
    lemma_in_domains(c, h);
    assert(!covers::<E2>(a.domains, p, r));
    assert forall|f: FreshChoice<C>, c2: E2, h2: Seq<E2>|
        admissible::<E2>(a.domains, a.known, cex, f) && #[trigger] instantiates::<E2>(cex, f, c2, h2)
        implies in_domains::<E2>(a.domains, c2, h2) && fails(c2, h2) by {
        lemma_in_domains(c2, h2);
        assert(head_matches(r.head, event_view(c2)));
        assert(rule_violated(r, c2, h2));
    }
    assert(every_instance::<E2>(a.domains, a.known, cex, fails));
    assert(counterexample_spec::<E2>(a, cex, fails));
    assert(minimal_in_case::<E2>(a.domains, a.known, cex, fails));
    assert(covered_spec::<E2>(a, 0, by, InclusionView::Counterexample(cex)));
}

/// Witness: theorem_vacuity_corollaries premises with v_always = Holds.
proof fn pos_p3e_vacuity_corollaries_witness() {
    let a = av(seq![r7(), forbid_all(r7().head)]);
    assert(a.rules[1] == forbid_all(a.rules[0].head));
    assert(at_least_as_strict_spec::<E2>(a, Seq::empty(), seq![0nat], InclusionView::Exhausted));
    assert(rules_of(a, seq![0nat]) =~= seq![r7()]);
    assert(rules_of(a, seq![1nat]) =~= seq![r7()]);
    assert(at_least_as_strict_spec::<E2>(a, seq![0nat], seq![1nat], InclusionView::Holds));
}

// ===================== Probe 4: spec non-triviality =====================

/// A4 Holds is false when inclusion fails: head (5, y), left = All, right = Empty.
proof fn pos_p4a_tail_holds_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(head, event_view(c)));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!lang(RegexView::<C>::Empty, head, event_view(c), history_view(h)));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::Empty, InclusionView::Holds));
}

proof fn neg_p4a_tail_holds_accepted()
    ensures tail_included_spec::<E2>(av(Seq::empty()), seq![k0(5), var('y')], RegexView::All, RegexView::Empty, InclusionView::Holds),
{
}

/// A4 Counterexample is false when inclusion holds (right = All): a bogus cex is rejected.
proof fn pos_p4b_tail_bogus_cex_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let cex = CexView { candidate: cc(5, 0), history: Seq::<ComponentsView<C>>::empty() };
    lemma_constant_cex_admissible(cex, a.known);
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::All, InclusionView::Counterexample(cex)));
}

/// A4 minimality is real: a cex of history length 1 is rejected when a length-0 failure exists.
proof fn pos_p4c_tail_nonshortest_cex_rejected() {
    let a = av(Seq::empty());
    let head = seq![k0(5), var('y')];
    let cex = CexView { candidate: cc(5, 0), history: seq![cc(5, 0)] };
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(head, event_view(c)));
    assert(lang(RegexView::<C>::All, head, event_view(c), history_view(h)));
    assert(!lang(RegexView::<C>::Empty, head, event_view(c), history_view(h)));
    assert(tail_fails::<E2>(head, RegexView::All, RegexView::Empty)(c, h));
    assert(!tail_included_spec::<E2>(a, head, RegexView::All, RegexView::Empty, InclusionView::Counterexample(cex)));
}

/// A1 Holds is false when the rule is not covered (empty policy, forbid (5,y).All).
proof fn pos_p4d_covered_holds_rejected() {
    let r = forbid(seq![k0(5), var('y')], RegexView::All);
    let a = av(seq![r]);
    let c = (5u32, 0u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(head_matches(r.head, event_view(c)));
    assert(rule_violated(a.rules[0], c, h));
    assert(rules_of(a, Seq::<nat>::empty()) =~= Seq::<RuleView<C>>::empty());
    assert(!covered_spec::<E2>(a, 0, Seq::empty(), InclusionView::Holds));
}

/// A6 minimality is real: a covered cex of history length 1 is rejected when the same
/// candidate already fails with the empty history.
proof fn pos_p4e_covered_nonminimal_cex_rejected() {
    let a = av(seq![r_all()]);
    let by = Seq::<nat>::empty();
    let cex = CexView { candidate: cc(1, 1), history: seq![cc(1, 1)] };
    let p = rules_of(a, by);
    assert(p =~= Seq::<RuleView<C>>::empty());
    lemma_constant_cex_admissible(cex, a.known);
    let c = (1u32, 1u64);
    let h = seq![(1u32, 1u64)];
    assert(event_view(c) =~= event_of(cex.candidate, any_f()));
    assert(history_view(h) =~= history_of(cex, any_f()));
    assert(instantiates::<E2>(cex, any_f(), c, h));
    let h0 = Seq::<E2>::empty();
    lemma_in_domains(c, h0);
    assert(same_profile(a.known, event_view(c), event_view(c)));
    assert(head_matches(a.rules[0].head, event_view(c)));
    assert(rule_violated(a.rules[0], c, h0));
    assert(uncovered::<E2>(p, a.rules[0])(c, h0));
    assert(!shortest_in_case::<E2>(a.domains, a.known, c, 1, uncovered::<E2>(p, a.rules[0])));
    assert(!covered_spec::<E2>(a, 0, by, InclusionView::Counterexample(cex)));
}

/// A3 Holds is false when refinement fails: [] does not refine [forbid (x,y).All].
proof fn pos_p4f_strict_holds_rejected() {
    let a = av(seq![r_all()]);
    let c = (1u32, 1u64);
    let h = Seq::<E2>::empty();
    lemma_in_domains(c, h);
    assert(rules_of(a, Seq::<nat>::empty()) =~= Seq::<RuleView<C>>::empty());
    assert(rules_of(a, seq![0nat]) =~= seq![r_all()]);
    assert(head_matches(r_all().head, event_view(c)));
    assert(rule_violated(rules_of(a, seq![0nat])[0], c, h));
    assert(policy_permits(rules_of(a, Seq::<nat>::empty()), c, h));
    assert(policy_denies(rules_of(a, seq![0nat]), c, h));
    assert(!policy_permits(rules_of(a, seq![0nat]), c, h));
    assert(!refines::<E2>(a.domains, rules_of(a, Seq::<nat>::empty()), rules_of(a, seq![0nat])));
    assert(!at_least_as_strict_spec::<E2>(a, Seq::empty(), seq![0nat], InclusionView::Holds));
}

// ===================== AnalyzerClaims request: junk cex at a declared coordinate =====================

pub open spec fn junk_cex<E: Event>() -> CexView<E::Component> {
    CexView::<E::Component> { candidate: Seq::new(arity::<E>(), |i: int| ValueView::<E::Component>::Fresh(0)), history: Seq::empty() }
}

/// POS (should verify if the claim holds): with domains[0] = {x} and x known, the all-Fresh(0)
/// counterexample has no admissible instance and no capacity, so it satisfies the
/// Counterexample arms of covered_spec and tail_included_spec for ANY rule/policy/tails.
proof fn pos_ac1_junk_cex_declared<E: Event>(a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>,
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>, x: E::Component)
    requires junco_core::spec::hypotheses::eq_equivalence::<E::Component>(), arity::<E>() >= 1,
        a.domains.len() == arity::<E>(), a.known.len() == arity::<E>(),
        a.domains[0] == Some(Set::<E::Component>::empty().insert(x)), a.known[0].contains(x),
    ensures ({ let cex = junk_cex::<E>();
        covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex))
        && tail_included_spec::<E>(a, head, left, right, InclusionView::Counterexample(cex))
        && !cex_has_instance::<E>(a.domains, a.known, cex) && !capacity_for::<E>(a.domains, a.known, cex) }),
{
    broadcast use {vstd::iset::group_iset_lemmas, vstd::set::group_set_lemmas};
    let cex = junk_cex::<E>();
    assert(cex.candidate[0] == ValueView::<E::Component>::Fresh(0));
    assert(fresh_used(cex, 0).contains(0nat));
    assert(fresh_used(cex, 0) =~= ISet::<nat>::empty().insert(0nat));
    assert(fresh_used(cex, 0).len() == 1);
    // no admissible choice
    assert forall|f: FreshChoice<E::Component>| !admissible::<E>(a.domains, a.known, cex, f) by {
        if admissible::<E>(a.domains, a.known, cex, f) {
            assert(choice_ok::<E>(f[0], fresh_used(cex, 0), a.known[0], a.domains[0], 0));
            assert(in_domain(a.domains[0], f[0](0nat)));
            let w = choose|w: E::Component| Set::<E::Component>::empty().insert(x).contains(w) && f[0](0nat).eq_spec(&w);
            assert(w == x);
            assert(!f[0](0nat).eq_spec(&x));
        }
    }
    assert(!cex_has_instance::<E>(a.domains, a.known, cex));
    // no capacity at coordinate 0
    assert(!fresh_capacity::<E>(a.domains, a.known, 0, 1)) by {
        if fresh_capacity::<E>(a.domains, a.known, 0, 1) {
            let vs = choose|vs: Seq<E::Component>| #[trigger] vs.len() == 1
                && (forall|i: int, j: int| 0 <= i < j < vs.len() ==> !vs[i].eq_spec(&vs[j]))
                && forall|i: int| 0 <= i < vs.len() ==> E::coordinate_spec(#[trigger] vs[i]) == 0
                    && in_domain(a.domains[0], vs[i]) && misses(a.known[0], vs[i]);
            assert(in_domain(a.domains[0], vs[0]));
            let w = choose|w: E::Component| Set::<E::Component>::empty().insert(x).contains(w) && vs[0].eq_spec(&w);
            assert(w == x);
            assert(misses(a.known[0], vs[0]));
        }
    }
    assert(!capacity_for::<E>(a.domains, a.known, cex));
    assert(cex_arity(cex, arity::<E>()));
}

/// POS bonus: simultaneously the rule IS covered (by == [rule]), yet the Counterexample arm holds.
proof fn pos_ac2_junk_cex_for_covered_rule<E: Event>(a: AnalyzerView<E::Component>, rule: nat,
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>, x: E::Component)
    requires junco_core::spec::hypotheses::eq_equivalence::<E::Component>(), arity::<E>() >= 1,
        a.domains.len() == arity::<E>(), a.known.len() == arity::<E>(),
        a.domains[0] == Some(Set::<E::Component>::empty().insert(x)), a.known[0].contains(x),
        rule < a.rules.len(),
    ensures
        covers::<E>(a.domains, rules_of(a, seq![rule]), a.rules[rule as int]),
        covered_spec::<E>(a, rule, seq![rule], InclusionView::Counterexample(junk_cex::<E>())),
{
    pos_ac1_junk_cex_declared::<E>(a, rule, seq![rule], head, left, right, x);
    assert(rules_of(a, seq![rule]) =~= seq![a.rules[rule as int]]);
    assert forall|c: E, h: Seq<E>| in_domains::<E>(a.domains, c, h) && #[trigger] rule_violated(a.rules[rule as int], c, h)
        implies policy_denies(rules_of(a, seq![rule]), c, h) by {
        assert(rule_violated(rules_of(a, seq![rule])[0], c, h));
    }
}

/// POS: the premises of pos_ac2 are satisfiable for (u32, u64) with domains [Some({C0 3}), None]
/// and the analyzer view `new`/`add_rule` would produce (known[0] = declared set).
proof fn pos_ac3_junk_cex_concrete()
    requires hash_coherent::<C>(),
{
    lemma_u32_u64_event_hypotheses();
    let x = Component2::<u32, u64>::C0(3u32);
    let a = AnalyzerView::<C> { domains: seq![Some(Set::<C>::empty().insert(x)), None::<Set<C>>],
        rules: seq![r_all()], known: seq![Set::<C>::empty().insert(x), Set::<C>::empty()] };
    assert(a.known[0].contains(x));
    pos_ac2_junk_cex_for_covered_rule::<E2>(a, 0, r_all().head, RegexView::All, RegexView::All, x);
    assert(covers::<E2>(a.domains, rules_of(a, seq![0nat]), a.rules[0]));
    assert(covered_spec::<E2>(a, 0, seq![0nat], InclusionView::Counterexample(junk_cex::<E2>())));
}

// ===================== TrustHypotheses request P2: hash_coherent neither provable nor refutable =====================

proof fn neg_th2_hash_coherent_provable()
    ensures hash_coherent::<C>(),
{
    broadcast use group_internal_key_axioms;
}

proof fn neg_th2_hash_coherent_refutable()
    ensures !hash_coherent::<C>(),
{
    broadcast use group_internal_key_axioms;
}

} // verus!

#[test]
fn compiles() {}
```

## Probe source S: crates/history-semantics/tests/vacuity_probes.rs
```rust
//! THROWAWAY vacuity probes (audit). `neg_*` must FAIL to verify; `pos_*` must verify.
#![cfg(all(verus_keep_ghost, feature = "runtime"))]
#![allow(unused_imports)]

extern crate alloc;

use history_semantics::spec::monitor::{
    ValidatorView, check_frame, check_step, permits_result, rollback_step, trace_safe,
};
use history_semantics::validator::verify::{
    lemma_check_preserves_trace_safe, lemma_rollback_preserves_trace_safe,
};
use history_semantics::validator::{Decision, Validator};
use history_syntax::event::Component2;
use history_syntax::spec::events::*;
use history_syntax::{Event, RuleMode};
use junco_core::event::{Grant, Request};
use junco_core::spec::hypotheses::{event_obligations, hash_coherent};
use junco_core::spec::questions::{DomainsView, in_domains, refines};
use junco_core::spec::semantics::*;
use junco_core::verify::hypotheses::lemma_u32_u64_event_hypotheses;
use junco_core::HistoryError;
use vstd::prelude::*;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

pub type C = Component2<u32, u64>;
pub type E2 = (u32, u64);

pub open spec fn var(n: char) -> PatternView<C> { PatternView::Variable(seq![n]) }
pub open spec fn k0(v: u32) -> PatternView<C> { PatternView::Constant(Component2::C0(v)) }
/// forbid (7, y) . All
pub open spec fn r7() -> RuleView<C> {
    RuleView { mode: RuleMode::Forbid, head: seq![k0(7), var('y')], tail: RegexView::All }
}

// Copied verbatim from crates/history-semantics/tests/reviewer.rs (not importable across test crates).
pub enum Step<E: Event, M> {
    Check(Request<E, M>, Result<Decision<E, M>, HistoryError>),
    Rollback(Result<(), HistoryError>),
}
pub open spec fn step_ok<E: Event, M>(before: ValidatorView<E>, after: ValidatorView<E>, step: Step<E, M>) -> bool {
    match step {
        Step::Check(request, result) => check_frame(before, after, request, result)
            && check_step(before, request, result),
        Step::Rollback(result) => rollback_step(before, after, result),
    }
}
pub open spec fn run_ok<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>) -> bool {
    &&& states.len() == steps.len() + 1
    &&& states[0].history == Seq::<E>::empty()
    &&& forall|k: int| 0 <= k < steps.len() ==> step_ok(states[k], states[k + 1], #[trigger] steps[k])
}

// ===================== Probe 3: reviewer theorem premises =====================

proof fn neg_p3m_trace_safe_premises<E: Event, M>(states: Seq<ValidatorView<E>>, steps: Seq<Step<E, M>>, k: int)
    requires run_ok(states, steps), 0 <= k < states.len(),
    ensures false,
{
}

proof fn neg_p3m_monitor_check_premises<E: Event, M>(
    before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>,
    result: Result<Decision<E, M>, HistoryError>,
)
    requires check_frame(before, after, request, result), check_step(before, request, result),
    ensures false,
{
}

proof fn neg_p3m_analyzer_to_monitor_premises<E: Event, M>(
    domains: DomainsView<E::Component>, p: ValidatorView<E>, q: ValidatorView<E>,
    request: Request<E, M>, result_p: Result<Decision<E, M>, HistoryError>,
    result_q: Result<Decision<E, M>, HistoryError>,
)
    requires
        refines::<E>(domains, p.rules, q.rules),
        q.history == p.history,
        in_domains::<E>(domains, request.event, p.history),
        check_step(p, request, result_p), check_step(q, request, result_q),
        result_p is Ok && result_p->Ok_0 is Grant,
    ensures false,
{
}

/// Concrete 2-state run: validator over [forbid (7,y).All], Check((1,2)) granted, then
/// Check((7,0)) denied with mode Forbid. run_ok holds and the final state is trace safe.
proof fn pos_p3m_run_witness(msg: alloc::string::String) {
    let rules = seq![r7()];
    let s0 = ValidatorView::<E2> { rules, history: Seq::empty() };
    let s1 = ValidatorView::<E2> { rules, history: seq![(1u32, 2u64)] };
    let req1 = Request::<E2, ()> { event: (1u32, 2u64), metadata: () };
    let res1 = Ok::<Decision<E2, ()>, HistoryError>(Decision::Grant(Grant { event: (1u32, 2u64), metadata: () }));
    let req2 = Request::<E2, ()> { event: (7u32, 0u64), metadata: () };
    let denial = history_semantics::validator::Denial::<E2> { mode: RuleMode::Forbid, event: (7u32, 0u64), message: msg };
    let res2 = Ok::<Decision<E2, ()>, HistoryError>(Decision::Denied(denial));
    let states = seq![s0, s1, s1];
    let steps = seq![Step::Check(req1, res1), Step::Check(req2, res2)];
    // step 1: grant
    assert(!head_matches(r7().head, event_view(req1.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req1.event)[0]));
    }
    assert(policy_permits(s0.rules, req1.event, s0.history)) by {
        if policy_denies(s0.rules, req1.event, s0.history) {
            let i = choose|i: int| 0 <= i < s0.rules.len() && #[trigger] rule_violated(s0.rules[i], req1.event, s0.history);
            assert(i == 0);
        }
    }
    assert(s1.history == s0.history.push(req1.event));
    assert(step_ok(states[0], states[1], steps[0]));
    // step 2: denial
    assert(head_matches(r7().head, event_view(req2.event)));
    assert(rule_violated(s1.rules[0], req2.event, s1.history));
    assert(least_violation(s1.rules, req2.event, s1.history, 0));
    assert(step_ok(states[1], states[2], steps[1]));
    assert(run_ok(states, steps));
    assert(trace_safe(s1)) by {
        assert(s1.history.take(0) =~= Seq::<E2>::empty());
        assert(s1.history[0] == req1.event);
    }
}

// ===================== Probe 4: check_step forbids Grant on a violated rule =====================

proof fn pos_p4m_check_step_no_grant_when_violated() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: Seq::empty() };
    let req = Request::<E2, ()> { event: (7u32, 0u64), metadata: () };
    assert(head_matches(r7().head, event_view(req.event)));
    assert(rule_violated(v.rules[0], req.event, v.history));
    assert forall|r: Result<Decision<E2, ()>, HistoryError>| r matches Ok(Decision::Grant(_))
        implies !check_step(v, req, r) by {
        assert(policy_denies(v.rules, req.event, v.history));
    }
}

/// Also: Denied is rejected when no rule is violated.
proof fn pos_p4m_check_step_no_denial_when_permitted() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: Seq::empty() };
    let req = Request::<E2, ()> { event: (1u32, 0u64), metadata: () };
    assert(!head_matches(r7().head, event_view(req.event))) by {
        assert(!head_pattern_matches(r7().head[0], event_view(req.event)[0]));
    }
    assert forall|r: Result<Decision<E2, ()>, HistoryError>| r matches Ok(Decision::Denied(_))
        implies !check_step(v, req, r) by {
        if check_step(v, req, r) {
            let i = choose|i: int| #[trigger] least_violation(v.rules, req.event, v.history, i);
            assert(least_violation(v.rules, req.event, v.history, i));
            assert(i == 0);
        }
    }
}

/// Err is accepted by check_step in every situation except Invariant (observation, not a bug probe).
proof fn pos_p4m_check_step_err_always_allowed<E: Event, M>(v: ValidatorView<E>, req: Request<E, M>)
    ensures check_step(v, req, Err(HistoryError::GraphBudget { limit: 0 })),
{
}

/// trace_safe is not trivially true: a history containing a forbidden event is not trace safe.
proof fn pos_p4m_trace_safe_nontrivial() {
    let v = ValidatorView::<E2> { rules: seq![r7()], history: seq![(7u32, 0u64)] };
    assert(v.history.take(0) =~= Seq::<E2>::empty());
    assert(head_matches(r7().head, event_view(v.history[0])));
    assert(rule_violated(v.rules[0], v.history[0], v.history.take(0)));
    assert(!trace_safe(v));
}

// ===================== MonitorClaims request: always-Err meets check's contract =====================

// Copied verbatim from crates/history-semantics/tests/reviewer.rs.
pub open spec fn stmt_monitor_check<E: Event, M>(
    before: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>,
) -> bool {
    match result {
        Ok(Decision::Grant(grant)) => grant.event == request.event
            && forall|i: int| 0 <= i < before.rules.len()
                ==> !rule_violated(#[trigger] before.rules[i], request.event, before.history),
        Ok(Decision::Denied(denial)) => denial.event == request.event && exists|i: int|
            0 <= i < before.rules.len()
            && rule_violated(#[trigger] before.rules[i], request.event, before.history)
            && denial.mode == before.rules[i].mode
            && forall|j: int| 0 <= j < i ==> !rule_violated(#[trigger] before.rules[j], request.event, before.history),
        Err(error) => !(error is Invariant),
    }
}

proof fn pos_mc1_always_error_satisfies_contract<E: Event, M>(before: ValidatorView<E>, request: Request<E, M>)
    ensures check_frame(before, before, request, Err(HistoryError::AllocationFailed)),
        check_step(before, request, Err(HistoryError::AllocationFailed)),
        stmt_monitor_check(before, request, Err(HistoryError::AllocationFailed)),
{}

// ===================== Probe 2 (semantics side) =====================

proof fn neg_p2m_hash_coherent_u32_u64()
    requires hash_coherent::<C>(),
    ensures false,
{
    lemma_u32_u64_event_hypotheses();
}

} // verus!

#[test]
fn compiles() {}
```
