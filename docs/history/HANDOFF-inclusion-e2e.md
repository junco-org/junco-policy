# Handoff: verified soundness and completeness of the policy analyzer

## Goal

Prove, in Verus, that the **implemented** policy analyzer is sound and complete for policy
refinement and rule redundancy, modulo `Exhausted`, and (last priority) that its counterexamples
are minimal. All work must serve this. Model-level statements are needed only as ingredients of
the executable proofs; nothing is needed for the paper's Proposition 5.2 (denial expressions with
an appended candidate event), which is not implemented. Do not edit the paper.

Today the inclusion *search* is verified as code, and so is the single-query API
`PolicyAnalyzer::tail_included`, but no code answers refinement or redundancy, and the proved
reductions from those questions to inclusion are not connected to any code.

## Target claim

Same form as the monitor's guarantee (`Validator::check` ensures `check_result`,
`crates/history-semantics/src/validator.rs:371`). For `at_least_as_strict(p, q)`, `covered(rule, by)`
and `redundant(rule, policy)`, under `analyzer_obligations` (equality/hashing laws), the verified
postconditions must give:

**Priority 1: soundness and completeness modulo `Exhausted`.**
- **Soundness:** `Ok(Holds) ⇒ refines(domains, P, Q)` (resp. `covers`, redundancy).
- **Completeness:** `Ok(Counterexample(cex)) ⇒ ¬refines(domains, P, Q)` (resp. `¬covers`), witnessed by every admissible instance of `cex`: `Q` denies it and `P` permits it. State the negation explicitly in the postcondition or a named corollary, derived with `stmt_choice_exists`; cover declared finite domains, or state the infinite-domain hypothesis explicitly.
- **Only escapes:** the call terminates (loops with `decreases`); the only non-answers are `Ok(Exhausted)` (graph budget) and resource errors. As for the monitor, `Err` is never an internal error (`no_internal_error` / `no_internal_compile_error`, `junco-core/src/verify/history_specs.rs:16-22`). `tail_included` does not currently ensure this; add it there too.

**Priority 2 (last): minimality.** A counterexample is of minimum length among candidates in the
same case (`shortest_in_case`, `same_profile`; per-case minimality is the intended spec,
`VERIFY.md` item 5). Do it in parallel if it does not slow priority 1 (see Work plan); otherwise
after. If it does not land, priority 1 ships without it.

To make the split explicit, factor each existing contract in
`crates/history-semantics/src/verify/refinement/analyzer.rs` as
`*_ok = *_correct && *_minimal` (e.g. `covered_correct`: `Holds ⇒ covers`, counterexample ⇒
`every_instance(uncovered(p, r))` and `¬covers`; `covered_minimal`: `shortest_in_case`). Entry
points first ensure `*_correct`; `*_minimal` is added when proved.

## Repository

`git@github.com:junco-org/junco-policy.git`, branch `handoff/verus-proofs` (`main` at `33b68ca`
plus this file). Work on a new branch from it; file and line references below are to that state.
Pre-verification reference code: `origin/feat/inclusion-simulation` (`e2aa01e`). Read
`VERIFY.md` first ("Differences between the paper and the mechanization", items 5-10) and
[archived SPEC.md](SPEC.md).

## What already exists (do not re-prove)

All in `crates/history-semantics/src/verify/refinement/` unless noted.

| Fact | Statement |
|---|---|
| **Executable search, verified from any start item** | `history-analysis/src/search.rs` `search(language, universes, constraint)` ensures `search_result` (`history-analysis/src/verify/search_exec.rs:1397`): `outcome_ok` for its start constraint (Holds ⇒ inclusion; Refuted ⇒ every realization is a counterexample, none shorter) and a bounded well-formed model trace. Do not touch it. |
| `P ⊑ Q` iff `P` covers every rule of `Q` (typed) | `semantics.rs`: `stmt_refines_iff_covers` |
| Rule redundant iff covered by the others (typed) | `semantics.rs`: `stmt_redundant_iff_covered` |
| Covering iff one constrained inclusion per split case (numeric) | `inclusion.rs:135`: `stmt_policy_reduction` (cases: any family with `split_ok(head_constraint(R.head), head_pairs(P), cases)`; right side `firing_denials(d, P, Γ')`); proof `lemma_policy_reduction` (`inclusion.rs:524`) |
| Model search correctness, minimality, termination | `search.rs`: `stmt_search_correct` (`outcome_ok`, l.251), `stmt_search_terminates` |
| Typed rule denial = numeric rule denial, any mode | `encoding.rs:137`: `stmt_front_end_denies` |
| Numeric genericity / fresh values | `encoding.rs:211`: `stmt_numeric_genericity`; `analyzer.rs`: `stmt_choice_exists` |
| Verified exec `split` with `split_contract` | `history-analysis/src/constraint.rs:451` |
| Exec `Constraint::entails` (**sound only**: `result ==> entails`) | `history-analysis/src/constraint.rs` (after `Constraint::head`, ~l.265) |
| Typed contracts | `refinement/analyzer.rs`: `covered_ok`, `redundant_ok`, `at_least_as_strict_ok` (header l.1-27 lists the intended `ensures`) |
| Verified exec `tail_included` (template) | `history-analysis/src/analyzer.rs:386-` and `decide` (~l.551); bridging lemmas in `history-analysis/src/verify/verdict.rs` (`decision_ready` l.372, `tail_input_wf`, `difference_source`, `tail_verdict`, `lemma_holds`, `lemma_refutation_input`) and `verify/typed_numeric.rs` |

An **unverified** implementation of these queries existed before the verification work:
`git show e2aa01e:crates/history-analysis/src/analyzer.rs` (l.300-530: `add_rule`, `covered`,
`covered_with`, `redundant`, `at_least_as_strict`, `decide`, `counterexample`). Use it as the
algorithmic reference: split the rule's head constraint on the head constants of `by`; per case,
union the denials of the rules of `by` whose head constraint the case entails; decide
`denial(rule) & ¬union` from the case; stop at the first non-`Holds`.

## Required work

### R1. Model-level composition (ingredient)

In `refinement/inclusion.rs` (or a new `refinement/policy.rs`), prove the composition of
`stmt_policy_reduction` with `outcome_ok`: for unrestricted `d`, policy `p`, rule `R`, a case family
with `split_ok(d, head_constraint(R.head), head_pairs(p), cases)`, and per case `Γ'` an outcome
satisfying `outcome_ok(d, Γ', denial(R), firing_denials(d, p, Γ'), ·)`:
- all `Holds` ⇒ `n_covers(d, p, R)`;
- `Refuted(g, letters)` for case `Γ'` ⇒ every admissible `θ ⊨ g` with events following `letters` gives `n_rule_denies(R, θ, w) ∧ ¬n_policy_denies(p, θ, w)`.
- (Priority 2) and no such pair with `θ ⊨ Γ'` is shorter.

Factor the counterexample-transfer argument out of `lemma_policy_reduction` (rules of `p` whose
head `Γ'` does not entail cannot fire, because `Γ'` decides their head constants) rather than
duplicate it.

### R2. Generalize `decide` (history-analysis)

`decide`/`decision_ready` require `constraint_of(g) == head_constraint(template_head(left))` and take
`TailInput` (two tails, one head). Generalize:
- Precondition: `g` well formed, codes known, satisfiable, member of a `split_ok` family for the left rule's head constraint (or entailing it).
- Input: a left denial (forbid tail, or `Not(tail)` for `require`) and a right side that is a union of denials of rules with *different heads and modes*. Generalize `TailInput`/`difference_source`/`tail_verdict`.
- Keep `tail_included` as a client with `g` = head constraint; its contract keeps holding and gains `no_internal_error`.

### R3. Exact firing test

`Constraint::entails` is verified sound only; selecting firing rules with it is safe for `Holds`
but makes counterexamples potentially spurious, which breaks completeness. Prove that it is exact
when the case comes from `split` on `head_pairs(by)` and the other side is a head constraint
(equalities only), or compute firing directly from register views with an exact postcondition.

### R4. Typed ↔ numeric bridge for policies

Lift `stmt_front_end_denies` to sequences of rules (pointwise over `by`, plus the left rule) and
connect typed `covers`/`uncovered`/`policy_denies` to `n_covers`/`n_policy_denies` restricted to one
case. Show the exec result satisfies `covered_correct`, including the explicit `¬covers`. Reuse
the `tail_included_ok` machinery (`every_instance`, `admissible`, `cex_values_ok`,
`stmt_choice_exists`).

### R5. Executable entry points (history-analysis/src/analyzer.rs)

- `covered(rule, by)` → `covered_correct`; loop over `split` cases with `decreases`, stop at the first non-`Holds`.
- `redundant(rule, policy)` → `redundant_correct` (`covered` against `policy` without every occurrence of `rule`, via `stmt_redundant_iff_covered`).
- `at_least_as_strict(p, q)` → `at_least_as_strict_correct`, via `stmt_refines_iff_covers`; counterexample from the first uncovered rule of `q`; explicit `¬refines`.
- `no_internal_error` on all three and on `tail_included`.

API shape: the specs index rules through `AnalyzerView.rules` and `add_rule` (`ensures
final(self)@.rules == old(self)@.rules.push(rule@) && id@ == old(self)@.rules.len() &&
rule_wf(rule@)`), but the exec `PolicyAnalyzer` stores no rules (`constants`, `universes` only).
**Default: add the rule store and `add_rule`** (as the pre-verification API did), extending
`analyzer_state_wf` and the view; stored encodings must stay valid as the constant book grows
(`enc::lemma_lowering_extends`). If that is disproportionately costly, take `&Rule<E>`/`&[Rule<E>]`
directly like `tail_included` and change the specs to take rule views; report it.

Generalize the capacity preconditions (`query_capacity`, `encode_capacity`, `resource_capacity`)
to many rules.

Not required: `never_fires`/`always_fires` entry points (vacuity is already decidable through the
verified `tail_included` with right side `Empty`/left side `All`).

### R6. Minimality (priority 2)

- Model: the per-case "no shorter" clause of R1 (from `no_cex_shorter` in `outcome_ok`).
- Bridge: a typed pair with the same profile (`same_profile`) as the returned candidate satisfies the same case constraint (the case decides every head constant, all of which are known constants), so numeric per-case minimality transfers to `shortest_in_case`.
- Add `*_minimal` to the entry points' `ensures`, completing `*_ok`.

### R7. Tests and docs

- Extend `crates/history-analysis/tests/differential.rs` (currently `tail_included` vs brute force) to `covered`/`at_least_as_strict` vs brute-force enumeration over small domains and bounded histories.
- Regression case from the paper (`inclusion.tex` l.129-142 in `junco-org/paper`): `Q = {R: head (a, edit, f), tail r}`, `P = {R1: head ("Alice", edit, f), tail r1; R2: head (a, edit, f), tail r2}` with a history in `r` and `r1` but not `r2`; `covered(R, P)` must refute with agent ≠ Alice, and must hold when that history is also in `r2`.
- Update `VERIFY.md` (item 7 "Only `tail_included` is executable", item 9, the results table, verified-function counts), regenerate `TRUST.md` with `scripts/trust-scan.sh`, update the header comment of `refinement/analyzer.rs`.

## Constraints

- No `admit`, `assume`, new `external_body`, or `#[verifier::external]` on analysis code. The `TRUST.md` diff may contain only justified native-boundary items.
- Existing statements keep their meaning (`stmt_search_correct`, `stmt_policy_reduction`, `tail_included_ok`; `tail_included` only gains `no_internal_error`). Splitting `*_ok` into `*_correct && *_minimal` is allowed.
- Keep each file's CRLF/LF line endings.

## Verification

- Install the pinned toolchain with `scripts/verify-all.sh --download <dir>` (checks sha256; prints the required `rustup` toolchain). Resources are not a constraint: use `-- --num-threads <cores>`. Verus memory grows with thread count (`VERIFY.md`); on SIGKILL, lower the threads.
- Iterate with single-crate runs (`cargo verus verify --locked -p history-analysis ...`, Verus `--verify-module`/`--verify-function`); run the full `scripts/verify-all.sh` after each milestone.
- `cargo test --workspace` must pass.

## Work plan

No agent or resource limits. Critical path: M2 → M3 → M4.

| Milestone | Content | Depends on | Parallel with |
|---|---|---|---|
| M0 | Fix interfaces: R1 statement (name, hypotheses), generalized `decide` `requires`/`ensures`, rule-store view and `analyzer_state_wf` extension, `*_correct`/`*_minimal` split | — | — |
| M1 | R1 (priority-1 part), R3 | M0 | M2, M5 |
| M2 | R2; `tail_included` re-verified with `no_internal_error` | M0 | M1, M5 |
| M3 | R4 (`*_correct`, explicit `¬covers`/`¬refines`) | M1, M2 | M5 |
| M4 | R5 entry points ensuring `*_correct`; R7 | M2, M3 | M5 |
| M5 | R6 minimality, in its own modules, against the M0 interfaces; merged into the entry points last | M0 (statements), M1/M3 (to discharge) | M1-M4 |

M5 must not block or destabilize M1-M4: it lives in separate modules and only adds `ensures`
clauses at the end. If it is not ready when M4 lands, ship M4.

One worker owns `history-analysis/src/verify/verdict.rs` and `analyzer.rs`; others hand it lemmas
in separate modules.

## Acceptance

Priority 1 (required):
1. `scripts/verify-all.sh` reports 0 errors in every configuration.
2. Verified exec `covered`, `redundant`, `at_least_as_strict` ensuring `*_correct`, including explicit `¬covers`/`¬refines` for counterexamples, termination, and `no_internal_error`; `tail_included` also ensures `no_internal_error`.
3. Differential and regression tests pass; `VERIFY.md`/`TRUST.md` updated.

Priority 2:
4. The same entry points also ensure `*_minimal` (hence the full `*_ok`).

Final report: names of the entry-point contracts and of the R1 composition lemma, any spec
changes, new trusted items, verified-function counts, and whether priority 2 landed.
