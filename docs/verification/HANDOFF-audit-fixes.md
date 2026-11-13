# Handoff: fixes from the post-merge claims audit

## Goal

PR #11 merged the reviewer-readable mechanization (`main` at `7050ac3`). An audit of the paper's
claims against it (2026-11-13) found statements that are weaker than they look, a vacuous paper
index entry, an evaluation that runs outside the guaranteed API, and gaps in the trusted-base
accounting. Fix the artifact so that every claim below is a verified property of the code the
evaluation runs, or is recorded as an explicit, documented hypothesis.

Evidence for every item, with file:line references at `969449b` (the PR head, identical to the
merged tree), is in `docs/verification/audit/`:

| File | Scope |
|---|---|
| `audit/monitor.md` | monitor contracts, R2/R5, evaluation front ends, table rows (findings M-F1…F10) |
| `audit/analyzer.md` | R3/R6, analyzer contracts, reviewer clients (A-F1…F11) |
| `audit/paper-index.md` | `paper.rs` and the refinement layer against the paper's results (P-F1…F8) |
| `audit/trust.md` | `TRUST.md`, axioms, hypotheses, benchmark builds, spec-check (T-F1…F12) |
| `audit/probe_unit_fresh.rs` | runtime probe for A-F1 (drop into `crates/history-analysis/tests/`) |

Paper line numbers in the audit files refer to the paper repository, which is not part of this
repository; ignore them except as context. Do not edit the paper. Produce the list of paper
changes in the final report.

Results of the Verus vacuity probes (axiom consistency, satisfiability of the hypotheses and of
the reviewer theorems' premises, non-triviality of the specs) were still running when this
handoff was written. They will arrive as an inbox message; treat any probe that proves `false`
as a Priority 1 item that preempts everything else.

## Items

Item ids are used in the inbox, `STATUS.md` and the final report.

### Priority 1: statements that are weaker than presented

- **H1. Counterexamples at declared coordinates** (A-F2). `counterexample_spec`
  (`spec/analyzer.rs`) does not exclude fresh values at declared coordinates, so with any
  declared domain a counterexample with a fresh value there satisfies every `*_spec` vacuously,
  even when the property holds. Add to `counterexample_spec`:
  `forall|i| 0 <= i < arity::<E>() && a.domains[i] is Some ==> fresh_used(cex, i) =~= empty`,
  discharged from `reconstruction::slot_domain` (already proved internally). Then restate the
  capacity condition so that it ranges over undeclared coordinates only, and prove in R6 or T:
  `counterexample_spec ∧ (∀ undeclared i. fresh_capacity(…, i, |fresh_used(cex, i)|)) ⇒
  cex_has_instance`.
- **H2. Instantiable counterexamples in the RegExLib benchmark** (A-F1). The benchmark's event
  type `Component3<(), u8, ()>` leaves the two unit coordinates undeclared, so the analyzer
  returns counterexamples with fresh values where `()` has no fresh value (reproduced by
  `audit/probe_unit_fresh.rs`). Declare `{()}` domains for coordinates 0 and 2 in
  `benches/smt/main.rs` (after H1), and make the benchmark check every returned counterexample:
  no `Fresh` at a declared coordinate, and one concrete instance is a real non-inclusion (by the
  existing brute-force or regex check). Re-run and report the timings.
- **H3. A denial identifies its rule** (M-F1). `Denial` carries only the mode. Add the index of
  the first violated rule (`index: usize`) and make R5's `check_step` state
  `least_violation(before.rules, request.event, before.history, denial.index as int)` together
  with the mode. Update `public_specs`, the reviewer clients and the root crate's callers.
- **H4. The paper index's search statement is vacuous** (P-F1). `stmt_search_correct`
  requires `steps_ok` for every `Item`, which cannot hold with two or more unrestricted
  components. Restate it with the premise the executable discharges (`trace_steps_ok`, i.e. the
  quantified `lemma_search_correct`), make `stmt_thm_search` and `theorem_paper_index` use it,
  and delete the old statement.
- **H5. Errors are classified** (M-F2, A-F3, A-F5; S12 of the previous plan). Today every
  non-`Invariant` error is allowed in every state for both the monitor and the analyzer, so
  "complete up to resource limits" is not a verified property. Define in R2 (or R4) one
  `pub open spec fn resource_error(e: HistoryError) -> bool` (graph budget, index overflow,
  allocation failure, identifier/revision exhaustion; decide the exact list from the error
  paths in `audit/monitor.md` F2 and `audit/analyzer.md` F3) and prove:
  - `Validator::check`/`permits`: `Err(e) ⇒ resource_error(e)` under the event hypotheses;
  - `covered`/`redundant`/`at_least_as_strict`/`tail_included`: with owned ids, the capacity
    preconditions and well-formed input, `Err(e) ⇒ resource_error(e)`;
  - `add_rule` (both the analyzer's and `ValidatorBuilder`'s) and `tail_included` never reject a
    rule that is `rule_wf`, has head length `arity::<E>()` and correctly tagged constants (no
    `HeadArity`, `ComponentCoordinate` or scope error); state the converse (H6) too.
  If some path cannot be classified, report it with the reason instead of weakening the
  definition.
- **H6. Rule well-formedness in the public contracts** (A-F4, M-F6). The analyzer's `add_rule`
  does not promise head length `arity::<E>()`; the builder's `add_rule` promises neither
  `rule_wf` nor the arity. Add both (under the event hypotheses where needed). Connect
  `PolicyAnalyzer::wf()` to R6's `analyzer_wf` with a public lemma, or delete `analyzer_wf` and
  the unused `rule_constants_tagged`.

### Priority 2: the evaluation runs what is verified

- **H7. Evaluation paths** (M-F3, T-F2). The benchmarks call `CompiledPolicy::decide` and
  `TracePolicy::decide` (crate-internal contracts outside R5) and commit histories in unverified
  code; AgentDojo runs `FlowPolicy` in audit mode, so denied events are appended and tool calls
  proceed whatever the monitor decides (`benches/agentdojo/camel.rs:221`, `:775-790`).
  - Make the lock and flow front ends decide and commit through `Validator::check` (or give
    `CompiledPolicy::decide`/`TracePolicy::decide` public R5 contracts with a reviewer theorem
    relating them to `policy_permits`/`least_violation`, and move the commit into verified code).
    Choose, record the decision, and keep the benchmark numbers comparable; report any change.
  - Run AgentDojo in enforcement mode (a denied tool call is not executed and not appended).
    Report the attack and utility numbers in both modes.
  - Keep the per-event rule filter, error-to-deny and audit mode only as documented unverified
    glue, listed in `TRUST.md`.
- **H8. Hypotheses for the evaluated event types** (T-F1, A-F10). `LockEvent`, `FlowEvent`
  and the bench-local `Char` (RegExLib) and `Symbol` (RE#) implement `Event` by hand, so all of
  `event_obligations` is assumed for the measured system. Replace `Char`/`Symbol` with built-in
  tuple events where possible, and give `LockEvent`/`FlowEvent` verified `EventSpecImpl` and
  `PartialEqSpecImpl` (in a verified crate if the root crate cannot host them), with lemmas
  proving `event_obligations` from `hash_coherent` alone, as for `(u32, u64)`.
- **H9. Benchmark builds in the verified matrix** (T-F3). The benches build `junco-core`
  with `{runtime,std}` and `history-syntax` with `{std}`; neither is a row of
  `scripts/verify-all.sh`. Either add those rows or change the dev-dependency features to
  verified rows. The CooperBench replay harness that produces `figures/bench/cooperbench.dat` is
  not in the repository: add it, or say in `VERIFY.md` where it lives and which build it uses.

### Priority 3: trusted base, index hygiene, docs

- **H10. Trusted contracts that assume unstated facts.**
  - The successor cache (`history-store/src/cache.rs:78-110`) promises exact lookup by
    `class_key` with no hashing premise (T-F5, M-F9): add a `hash_coherent`/`key_laws` premise
    for `EventClass` or state it as a listed axiom.
  - `TraceRule::clone` (`policy/trace.rs:301-317`) assumes the component type's `Clone` is the
    identity (T-F7): weaken the contract to what `cloned` gives, or add the hypothesis to R4.
  - `NativeBooks::with_books` encodes the lock invariant that interned tables only grow
    (T-F10): document it in `TRUST.md` as such.
- **H11. `TRUST.md` and the trust scan** (T-F4, T-F9, T-F12). Count only genuinely trusted
  derived-equality claims (10 of the 16 are verified), fix the `unannotated_pub_fn`
  description, add a section for the `cfg(not(verus_keep_ghost))` sites, include the helper
  crates' full inventory in the summary, and fix `TRUST.md:403` (`check_step` does not cover
  `TracePolicy::decide`).
- **H12. spec-check** (T-F8). The wrappers are hand restatements, some weaker than the
  specifications they test, against an older vstd pin. Pin the verified vstd, make each wrapper's
  contract identical to its `assume_specification` (check this mechanically in
  `scripts/spec-check.sh`), and run it.
- **H13. Paper index and table identifiers** (M-F4, M-F5, P-F2, P-F5…F8, A-F7).
  - In `paper.rs`, separate the executable chain (`accepts_history`, `lemma_typed_result`,
    `residual_folds`, `derivative_correct`, `lemma_dsl_violation`) from results mechanized
    independently over the abstract model (`theorem_symbolic_derivative_correct`,
    `theorem_symbolic_run_correct`, `theorem_rule_decision`). Either use
    `lemma_derivative_correct_is_symbolic_derivative` to connect the executable derivative to the
    paper's δ, or delete it.
  - Drop `theorem_not_fired` from the index, or mark it definitional.
  - Cite `theorem_impl_items_bound`/`lemma_running_items_bound` for termination; drop or
    document the post hoc `finitely_many_items`/`traces_bounded` conjuncts of `search_result`.
  - Delete the dead `implemented_steps_ok`; fix the genericity comment in `encoding.rs:164-166`
    (or prove the policy-level statement); add an event-level counterpart of
    `stmt_vacuity_reductions` or point the index at `theorem_vacuity_corollaries`.
- **H14. Reviewer clients that exercise the guarantees** (A-F6, M-F8).
  - Analyzer: a client that declares a domain with `with_domain` (discharging `domains_wf` and
    `constructor_capacity`), adds two different rules, and queries one against the other.
  - Delete `theorem_a5_no_invariant_failure` (it restates its premise).
  - Monitor: add `event_obligations ∧ trace_safe(old@) ⇒ trace_safe(final@)` to
    `check`/`rollback`, so trace safety is a postcondition rather than only a ghost induction.
- **H15. `VERIFY.md` rewrite.** The current file is not readable by a reviewer. Rewrite it
  after the items above land, in about two pages:
  1. *What is proved*, stated in words and formulas, each with its theorem name and file:
     the monitor theorem and trace safety; the analyzer's verdicts, counterexamples and
     minimality; what `Exhausted` and errors mean (after H5).
  2. *Assumptions*, one sentence each: the event-type laws, `hash_coherent`, declared domains,
     capacity, the toolchain.
  3. *What is trusted*: totals from `TRUST.md` and what each kind means; link `TRUST.md`.
  4. *Paper ↔ Verus*: one table, paper label → statement → file, matching `paper.rs`.
  5. *Differences from the paper*: a numbered list, one or two sentences each.
  6. *How to run*: the commands and the expected counts.
  No plan or track identifiers (R1–R6, A1–A6, S-, D-, H-items), no history of the work, at most
  two or three code names per sentence. Move definition inventories to the doc comments of the
  interface files or to `INTERFACES.md`.

## Repository and communication

`git@github.com:junco-org/junco-policy.git`, branch `handoff/audit-fixes`: `main` at `7050ac3`
plus this file and `docs/verification/audit/`. Work on `fix/audit-fixes` (integration branch)
and track branches `track/h<N>`; open one PR at the end.

- **Inbox:** messages are added to `docs/verification/INBOX.md` on the handoff branch, newest
  first. Poll at least every 30 minutes and at every gate. A message takes precedence over this
  file and over earlier messages. Never push to the handoff branch.
- **Status:** keep `STATUS.md` at the root of the integration branch, pushed at least every 30
  minutes and at every gate: items done and in progress, last gate results with counts,
  blockers, deviations, and an acknowledgement of each inbox message. Remove it before opening
  the PR.

## Constraints

- No `admit`, `assume`, `#[verifier::external]` on verified code, or new `external_body` in
  analysis or semantics code. New trusted items only where an item above names one; each is
  listed in `TRUST.md` with a one-line justification.
- Do not weaken any `ensures`. H1 and H5 strengthen statements; if one cannot be proved as
  stated, stop that item and report it rather than proving a weaker form.
- Keep each file's line endings. Every gate and the final commit pass all of CI
  (`.github/workflows/ci.yml`); clippy runs on the ghost-erased build.
- Benchmark numbers may change only through H2, H7, H8 and H9; report every change with the
  before and after values.
- Toolchain, gate tiers and parallel verification: as in `docs/history/HANDOFF-reviewer-surface.md`
  § Verification and § Gates (`scripts/verify-all.sh --download <dir>`; inner loop, merge gate,
  wave gate). Do not modify `scripts/verify-all.sh` except to register configurations that H9
  adds.

## Work plan

| Wave | Items | Notes |
|---|---|---|
| 1 | H1, H3, H4, H6, H10, H11, H12 | independent; H1 and H6 both touch `analyzer.rs` (one owner) |
| 2 | H5, H2, H8, H9 | H5 after H6; H2 after H1; H8 before H7 |
| 3 | H7, H13, H14 | H7 after H3, H5 and H8 |
| 4 | H15, final gate | last |

File ownership within a wave: one owner per file; others hand over lemmas in separate modules.
`history-analysis/src/analyzer.rs` and `spec/analyzer.rs`: H1/H6/H5 owner. `validator.rs` and
`spec/monitor.rs`: H3/H5 owner. `paper.rs` and `refinement/`: H4/H13 owner. `TRUST.md`,
`scripts/`: H11/H12 owner. `benches/`, root `src/`: H2/H7/H8/H9 owner.

## Acceptance

1. All CI jobs pass on the final commit, including every configuration of
   `scripts/verify-all.sh`; report verified-function counts per configuration.
2. H1: a reviewer theorem proves the instance statement of H1, and a probe stating a
   counterexample with a fresh value at a declared coordinate fails to satisfy
   `counterexample_spec`.
3. H2: the RegExLib benchmark checks an instance of every counterexample; `probe_unit_fresh`
   reports no fresh value at a unit coordinate.
4. H3, H5, H6: the new clauses are in the public contracts and used by the reviewer clients; a
   probe shows that returning a non-resource error (e.g. `UnknownId` for an owned id, or
   `HeadArity` for a well-formed rule of the right arity) violates the contracts.
5. H4: `stmt_search_correct` has a premise that `lemma_trace_query_ok` discharges for the
   executable, and `theorem_paper_index` uses it.
6. H7–H9: every benchmark runs the guaranteed API in a verified configuration on event types
   whose hypotheses are proved modulo `hash_coherent`, or the exception is documented in
   `VERIFY.md` with the reason.
7. H10–H15 done or each deviation reported.

## Final report

- Per item: done, changed (how and why), or not done (why).
- New and removed trusted items, with justifications; the `TRUST.md` totals before and after.
- Verified-function counts per configuration; benchmark numbers before and after (H2, H7–H9).
- **Paper changes needed**, as a checklist against the audit files: statement names, the monitor
  and analyzer guarantee wording ("complete", "names the first violated rule", counterexample
  instances), hypotheses for the evaluated event types, evaluation paths and audit mode, trusted
  base and counts, table rows of `tab:mechanization`.
