# Audit: paper index fidelity (PaperIndexFidelity)

Paper: /home/zak/paper/pldi2027 (working tree). Artifact: 969449b (worktree /tmp/audit-PaperIndexFidelity, removed after the audit).
Scope: Table tab:mechanization rows "Mechanized results they rest on" plus the completeness row, appendix "Derivatives"/"Search"/"Policy queries" (appendix.tex:928-990), `verify/paper.rs`, `verify/refinement/*`, and the exec glue in `history-analysis/src/{search.rs,verify/search_exec.rs}`.

## Summary

- No BLOCKER found. I found no table row whose paper claim is false for the implementation.
- 1 MAJOR: the abstract `stmt_search_correct` that the paper index uses for Thm. search has a premise that is never discharged and, under the intended semantics, cannot be satisfied in the main configuration. The implementation goes through `lemma_search_correct` instead, which has a premise it actually establishes.
- MINOR issues: a stale identifier (`verify::dsl::lang`), helper or definitional identifiers listed as mechanized results (`theorem_not_fired`, `lemma_running_outcome`, `stmt_checks_discard`), termination conjuncts in `search_result` that are trivially true and say nothing about termination, wording on genericity, dead bridge code.
- `theorem_paper_index` is a genuine conjunction of the stmts, not `ensures true`. Several conjuncts are definitional, though (listed below).
- Termination (Q3): discharged for the executable. `Search::run` has `decreases bound.len()-next`, where `bound` comes from `theorem_impl_items_bound` and is fixed before the loop, independent of the memory budget. The paper's claim holds.
- Thm. search both directions (Q4): mechanized for the executable through `search_result`. Holds implies inclusion. A refutation is realizable, every instance is a counterexample, and no counterexample is shorter.
- Search description (Q6) matches the code: the split, the `ENUMERATED_PARTS = 4` subset enumeration versus the exact-parts lookup, and component-wise syntactic entailment.

## Findings

### F1 — MAJOR — `stmt_search_correct` (cited for Thm. search) has an undischargeable global premise; the implementation uses a different lemma

- Paper: appendix.tex:912-914 (Table row "Search: `search_result`, `lemma_running_outcome`, `stmt_search_correct` — Thm. search"); paper.rs:24, 228-243 (`stmt_thm_search` := `stmt_search_correct` ∧ …).
- Artifact: crates/history-semantics/src/verify/refinement/search.rs:262-269
  ```rust
  pub open spec fn stmt_search_correct() -> bool {
      forall|d, g0, r, s, q0, cases_of, t, outcome|
          satisfiable(d, g0) && initial_ok(q0, r, s)
              && (forall|i: Item| #[trigger] steps_ok(d, i, cases_of(i)))   // <-- every Item
              && trace_wf(..) && trace_outcome(t, outcome)
              ==> outcome_ok(d, g0, r, s, outcome)
  }
  ```
  `steps_ok` (search.rs:83-97) requires, for item `i`, a **finite** `Set<Case>` that covers every admissible `(θ, e)` with `θ ⊨ i.constraint` exactly once. Each case must have a residual that is correct up to language (`successor_ok`) and must be uniformly realizable for every `θ ⊨ c.constraint`. The premise ranges over *all* `Item`s, and `Item.state` is an arbitrary `Regex<model::Test>`, including states with non-local atoms. Take `d = [None, None]` and `q = Test(And[Eq(c0, Var c0), Eq(c0, Var c1)])`. Pairs `θ=(v,v), e=(v,0)` (residual ε) must be covered for infinitely many `v`. An assignment that omits either atom breaks `successor_ok`: some realizer has the other atom false, the residual is ∅, and nullability is independent of θ. An assignment with both atoms true is uniformly realizable only if the case constraint forces `θ0 = θ1`. Literals `x_c = k` / `x_c ≠ k` cannot express that with finitely many cases. So under the intended semantics no `cases_of` satisfies the premise, and `stmt_search_correct` is vacuous for every `d` with two unrestricted components. [INFERENCE: hand argument, not machine-checked. A formal disproof is probably blocked because out-of-range literals read `θ[k]`, k ≥ len, which is unspecified in vstd. Either way the premise cannot be discharged.]
- `theorem_search_correct` is referenced only from paper.rs:240 (`git grep`). The executable uses `lemma_search_correct` (search.rs:1025-1030), whose premise is `trace_steps_ok` (steps_ok only for expanded nodes, search.rs:772-776). `search_exec::lemma_trace_query_ok` (search_exec.rs:1123-1135) establishes that premise from the ghost archive via `lemma_emitted_steps`.
- Impact: the paper's claim for the implementation is still true through `search_result`. But the "paper-shaped" statement that the index presents for Thm. search is, in practice, empty.
- Fix (code): restate `stmt_search_correct` with `trace_steps_ok(d, cases_of, t)` in place of `forall|i| steps_ok(..)`, i.e. the quantified `lemma_search_correct`. Alternatively, cite `lemma_search_correct` in the table and paper.rs:24. Probe request sent to VacuityProbes (see bottom).

### F2 — MINOR — the termination conjuncts of `search_result`/`lemma_running_outcome` are trivial; the real termination evidence is elsewhere

- Paper: paper.rs:24 ("for the executable, `theorem_impl_search_bounded` and `search_exec::lemma_running_outcome`"). Appendix Table row "Search" lists `lemma_running_outcome`. This is fine as a correctness identifier.
- Artifact: search_exec.rs:1276-1290, 1328-1338. They ensure `finitely_many_items(archive_cases(s.archive@), start)` and `exists bound. traces_bounded(.., archive_cases(s.archive@), bound)`. `archive` is a ghost `Map<Item, Set<Case>>` built by inserts from `Map::empty()` (search.rs:120), keyed only by *expanded* items. Items reachable through `archive_cases` are therefore always finite, so these conjuncts are post hoc and say nothing about termination.
- The real termination proof is search.rs:196-214: `let ghost bound = choose|f| items_bound_ok(universes,start,f)`, discharged by `finiteness::theorem_impl_items_bound(...)` before the loop, with `decreases bound.len()-next` and `lemma_running_items_bound` as the per-iteration bound. The Table's completeness row (appendix.tex:895-897) cites exactly these, which is correct.
- Fix: in paper.rs:24 and the refinement docs, cite `theorem_impl_items_bound` + `lemma_running_items_bound` (and `Search::run`'s `decreases`) for executable termination. Optionally drop the `finitely_many_items`/`traces_bounded` conjuncts from `search_result`, or document them as post hoc.

### F3 — MINOR — stale identifier `verify::dsl::lang` in the Table

- Paper: appendix.tex:900 ("Semantics & `verify::dsl::lang`, `rule_violated`").
- Artifact: at 969449b the only definition is `junco_core::spec::semantics::lang` (crates/junco-core/src/spec/semantics.rs:151, R2). `junco_core::verify::dsl` only *imports* it privately (crates/junco-core/src/verify/dsl.rs:3 `use crate::spec::semantics::{lang, rule_views, test_sem};`), and history-syntax's `verify::dsl` has no `lang`.
- Fix: write `spec::semantics::lang` (R2) in the Table.

### F4 — MINOR — Thm. matcher step 1 (`theorem_not_fired`) is a definitional tautology

- Paper: appendix.tex:906-907 (Rule decision row cites `theorem_not_fired`).
- Artifact: history_algebra.rs:231-239. `stmt_not_fired` = `(∀θ. ¬head_match(head, request, θ)) ⇒ ¬pair_lang(..)`, where `pair_lang` *is defined as* `∃θ. head_match(..) ∧ numeric_lang(..)` (junco-core/src/verify/history_specs.rs:701-704). The proof body is empty (`{ }`). `stmt_rule_decision` is likewise about the spec-level `symbolic_run` (unnormalized δ over `SrcTest`), not the executable. The executable link is `CompiledRule::accepts_history` + `lemma_dsl_violation`, which are also in the row.
- Fix: none needed in code. In prose, avoid presenting `theorem_not_fired` as content: "step 1 holds by definition of `pair_lang`".

### F5 — MINOR — genericity: the paper says "decisions"; the mechanized statement is single-rule violation, not used by any guarantee

- Paper: appendix.tex:941-944 ("a genericity theorem shows that decisions are invariant under renamings of codes that fix a rule's constants").
- Artifact: encoding.rs:216-220 (`stmt_numeric_genericity`: `n_rule_denies(rule, θ, w) == n_rule_denies(rule, f∘θ, f∘w)` with `f` injective on the pair's values, fixing `n_rule_codes(rule)`, and not mapping a value onto a fixed code unless they are equal). semantics.rs:76-84 (`stmt_genericity`, typed, `rule_violated_view`, `rule_wf`, tag-preserving renamings fixing `rule_constants(rule)`). Both are stated for **one rule**; the doc comment says "policies follow pointwise", but that is not proved. `theorem_genericity`/`theorem_numeric_genericity` are referenced only by paper.rs:344-345. The renaming lemmas (`enc::lemma_lang_rename`, `lemma_test_rename`) *are* used, in symbolic_language.rs:861-903 (atoms_complete with u64 valuations), but the stmt itself is not. The comment at encoding.rs:164-166 ("Together with `stmt_front_end_denies` this transfers a numeric verdict to every typed pair…") describes a use that does not happen: counterexample instances go through `reconstruction`.
- Fix (paper): "…a genericity theorem shows that rule violation is invariant under renamings of values that fix the rule's constants". Fix (code): correct the encoding.rs:164-166 comment.

### F6 — MINOR — `stmt_successor_cases` is never instantiated for the implementation; its bridge is dead code

- Paper: appendix.tex:973-976 ("Verus proves this for the implemented enumeration (`lemma_emitted_steps`), and for every family of cases with the properties of Definition split whose residuals are correct (`stmt_successor_cases`)"). As written this is accurate.
- Artifact: `history-analysis/src/verify.rs:1855 implemented_steps_ok` is the only non-index caller of `theorem_successor_cases` (verify.rs:1882), and `implemented_steps_ok` has no caller (`git grep`). The executable uses `lemma_emitted_steps` (search.rs:545), which does not need `atoms_complete`. `stmt_successor_cases` additionally assumes `atoms_local`, `atoms_bounded` and `atoms_complete`, which the paper's sentence does not mention ("every family … whose residuals are correct").
- Fix: delete `implemented_steps_ok` (dead), or keep it and mention it. Optionally mention the atom-locality/completeness premises in the paper sentence.

### F7 — MINOR — table identifiers that are glue or definitions rather than results

- `stmt_checks_discard` (pruning.rs:146-151) only unfolds `may_discard` given `stmt_prune_sound`. It is fine as glue, but it is not part of Lem. prune.
- `lemma_running_outcome` and `search_result` are `pub(crate)` in history-analysis (search_exec.rs:1276, 1328). The guarantee is `Search::run`'s `ensures … search_result(..)` (search.rs:186-191), proved by `lemma_search_result` (search_exec.rs:1341). Citing "`Search::run` ensuring `search_result`" would match the pattern of the other rows.
- `stmt_prop_policy` (paper.rs:191-201) is named after `prop:policy`, but its content is `stmt_policy_reduction` ∧ `stmt_policy_search_composition`. The doc says "not mechanized as stated", which agrees with appendix.tex:811. Naming only.

### F8 — MINOR — simulation: "applies the rules of Figure simulation"

- Paper: appendix.tex:979-980.
- Artifact: pruning.rs:6-10 and `sim_step`/`test_step` (pruning.rs:88-128). The code's relation is a sub-relation of the Figure's: on tests, `SumL/SumR/AndL/AndR` are read only when both sides are lifted tests, and the side conditions `k ≥ 2` and `a+b ≥ 1` are dropped. Soundness is unaffected.
- Fix (optional): "applies a subset of the rules of Figure~\ref{fig:simulation}".

## Q1 — per-table-identifier verdicts

| Identifier | Location | States the cited paper result? | Premises discharged for implementation? | Verdict |
|---|---|---|---|---|
| `derivative_correct` | symbolic.rs:3264-3269 | Lem. sderiv up to language: `transition_lang(out, e, w) == regex_lang(root, [e]+w)` for `event_wf(θ)` (u64 codes) | Ensured by `RegexId::derivative` and the cache (symbolic.rs:335, 425, 582, 630) | OK |
| `residual_folds` | progress.rs:2704-2710 | `L(to) = {w | events·w ∈ L(from)}`; this is the appendix's "residual reached after u" | Spec predicate in fold postconditions | OK (predicate, `open(crate)`) |
| `lemma_derivative_correct_is_symbolic_derivative` | symbolic.rs:3272-3278 | Links the runtime derivative to the spec δ by language | requires `derivative_correct` | OK |
| `theorem_symbolic_derivative_correct` | history_algebra.rs:137-158 | Lem. sderiv for the spec δ, any `sem` (⊇ every θ) | No premises | OK |
| `theorem_symbolic_run_correct` | history_algebra.rs:180-199 | Thm. sderiv (nullable(δ*(r,u)) ⇔ u ∈ L) | No premises | OK |
| `CompiledRule::accepts_history`, `lemma_dsl_violation` | compiled_rule.rs:524, 247 | Thm. matcher for the executable | Not audited in depth (MonitorClaims slice) | — |
| `theorem_not_fired` | history_algebra.rs:231-239 | Step 1; definitional | — | F4 |
| `theorem_rule_decision` | history_algebra.rs:203-227 | Steps 2-3 for the spec-level run | — | OK (spec-level) |
| `lemma_emitted_steps` | search_exec.rs:554-655 | Lems. succ+uniform as `steps_ok` for the implemented enumeration (satisfiable, entailing cases; residual correct up to language; uniform realizability; every pair in exactly one case) | Called in `expand` (search.rs:545) with `successor_ok` per record | OK |
| `stmt_successor_cases` | search.rs:145-154 | Same, for any `split_ok` family over `domain_pairs` (= Π_q without declared domains) | Extra premises `atoms_local/bounded/complete`; only bridge is dead | OK, F6 |
| `stmt_decomposition` | pruning.rs:59-63 | Eq. decomposition (P = non-complement ∧-operands, N = +-operands of complemented ones) | None needed | OK |
| `stmt_prune_sound` | pruning.rs:79-85 | Lem. prune: dead ⇒ no witness; `dominated` (Γ'⊨Γ, P⊆P', ∀n∃n'. n≤n') ⇒ W(J)⊆W(I) | `sim_sound(le)`; executable instantiates `le := lang_le` (simulation_exec.rs:31-33), so soundness is trivial and memo pairs are proved inside `lang_le` (`memo_wf`, simulation_exec.rs:64-79) | OK |
| `stmt_checks_discard` | pruning.rs:146-151 | Glue to `may_discard` | — | F7 |
| `stmt_sim_rules_sound` | pruning.rs:133-137 | Lem. simulation rule by rule (all 13 Figure rules) under sound premises | Used by `lemma_rule`/`lemma_padding` with semantic premises, so no induction on derivations is needed | OK, F8 |
| `stmt_test_rules_sound` | pruning.rs:139-142 | ≤_t rules | Used in `lemma_test_rule` | OK |
| `search_result` | search_exec.rs:1328-1338 | Thm. search for Holds/Refuted: `outcome_ok` ∀ r,s with `initial_ok`, and the trace exists | Ensured by `Search::run` (search.rs:190); `initial_ok` proved in `decide` (analyzer.rs:1390-1399) | OK; termination conjuncts trivial (F2) |
| `lemma_running_outcome` | search_exec.rs:1276-1290 | Helper | — | F2, F7 |
| `stmt_search_correct` | search.rs:262-269 | Thm. search shape, but global premise `∀ Item. steps_ok` | Never discharged; under the intended semantics unsatisfiable for ≥2 unrestricted components | **F1 MAJOR** |
| `stmt_search_terminates` | search.rs:303-307 | Conditional termination | Condition discharged for the executable via `items_bound_ok` (stronger, run-independent) | OK |
| `stmt_reachable_states_finite` | finiteness.rs:97-104 | Lem. finite-states for every `Model` satisfying the contract (bounded by `m.succ`) | `m_impl().contract()` by `theorem_impl_contract` | OK |
| `theorem_impl_contract` | finite_impl.rs:949-961 | m_impl satisfies (N0)-(N5), (S0)-(S6) | No premises | OK |
| `theorem_impl_finitely_many_items` | finiteness.rs:577-587 | finitely_many_items for cases following m_impl steps | Used only via `theorem_impl_search_bounded` → post hoc archive (F2) | OK |
| `theorem_impl_items_bound` | finiteness.rs:591-600 | One finite item set for every `cases_of` that follows m_impl and adds literals only over atoms/domains | `regex_nf(start.state)` is in `running` | OK |
| `lemma_running_items_bound` | search_exec.rs:1887-1900 | queue ≤ \|f\| | Called every iteration (search.rs:219, 251) | OK |
| `stmt_refines_iff_covers` | semantics.rs:30-33 | P ⊑ Q ⇔ ∀ R∈Q. covers(P,R) (typed, R3) | Used in policy_bridge.rs:224 | OK |
| `stmt_redundant_iff_covered` | semantics.rs:37-42 | covers(others,R) ⇔ removing R changes no decision in domains | Used in policy_removal.rs:100 | OK |
| `stmt_policy_reduction` | inclusion.rs:145-152 | "Policy queries" paragraph: coverage ⇔ per split case, `denial(R) ⊑_Γ' Σ firing denials` | Executable uses the same `lemma_policy_reduction` (analyzer.rs:891) | OK |
| `stmt_vacuity_reductions` | inclusion.rs:208-216 | App. policy-reduction vacuity as `⊑_{Γ_R}` inclusions (numeric NRule, uses `denial`, so it covers `require` too) | Index only; typed counterpart `stmt_vacuity_via_refinement` used in tests/reviewer.rs:21, 277 | OK |
| genericity (`stmt_genericity`, `stmt_numeric_genericity`) | semantics.rs:76-84, encoding.rs:216-220 | Single-rule invariance | Index only | F5 |

## Q2 — `theorem_paper_index`
paper.rs:303-348 ensures 21 conjuncts (`stmt_lem_*`, `stmt_thm_*`, `stmt_matcher`, `stmt_app_policy_reduction`, `stmt_prop_policy`, `stmt_paper_split_ok`, genericity, front end) and calls each theorem. It is not `ensures true`. Conjuncts with little or no content: `stmt_not_fired` (definitional, F4); `stmt_matcher` (paper.rs:110-126; its first clause unpacks `check_step` + `least_violation`); `stmt_vacuity_via_refinement` (near-definitional); `stmt_checks_discard` (glue); `stmt_search_correct` (premise undischargeable, F1).

## Q3 — termination
Discharged for the executable. search.rs:196-214 fixes `bound` from `theorem_impl_items_bound(ndomains(universes), regex_primitives, start)` before the loop, keeps `items_bound_ok(universes,start,bound)` as an invariant, and uses `decreases bound.len()-next`. `lemma_running_items_bound` gives `items.len() ≤ bound.len()`. Inner loops of `expand` have `decreases` (search.rs:354-443), and the simulation recursion has `decreases` (simulation.rs:85, 155, 189, 335). history-analysis has no `exec_allows_no_decreases_clause` (git grep; the two in the repo are in policy/evaluate.rs and history-store). The measure does not involve `GRAPH_BYTES`; a budget overrun only exits early with `Err(GraphBudget)`, which becomes `Exhausted` (analyzer.rs:1375-1408). So "termination proof … does not depend on the memory limit" (implementation.tex:79-81) holds.

## Q4 — Theorem search for every answer other than Exhausted
`outcome_ok` (search.rs:237-251):
- Holds ⇒ `included_under(d, g0, r, s)` (soundness).
- Refuted(g, letters) ⇒ g is realizable in the domains; every θ ⊨ g has a following history; every following (θ, u) is an `inclusion_cex`; and `no_cex_shorter(d,g0,r,s,|letters|)` (minimality among counterexamples with θ ⊨ g0).

Completeness follows: the only answers are Holds/Refuted/Exhausted/Err. Both directions are mechanized for the executable via `Search::run` → `search_result`. Pruning is covered by `may_discard` in `trace_wf`.

## Q5 — claims without a counterpart, or identifiers pointing at helpers
- No paper statement claimed as mechanized lacks a counterpart. Prop. policy is honestly declared unmechanized (appendix.tex:811). "Recursion decides ≤" is declared unmechanized (appendix.tex:676-678). Finiteness for the paper's `N` is honestly "by construction" (appendix.tex:214-228).
- Identifiers that are helpers or definitions: `theorem_not_fired`, `stmt_checks_discard`, `lemma_running_outcome`, `residual_folds`/`derivative_correct` (predicates, acceptable). Stale identifier: `verify::dsl::lang` (F3).
- Not checked: appendix.tex:937-939 ("normalizing constructors are verified directly … postcondition states its result has the language of the expression it builds"). It is outside this slice.

## Q6 — Search description vs. code
- Split: constraint.rs:955-1066 `split_register`. A component is split only when its register is compared (`register`) and is still `Differs`. It yields one `Equals(c)` per compared constant not yet decided, plus one `Differs(old ∪ those)`. With a declared domain it yields one `Equals` per remaining domain value and no "different" case. Matches appendix.tex:963-965.
- Domination: prune.rs:483-516 enumerates all `2^|parts|` subsets when `parts.len() ≤ ENUMERATED_PARTS = 4` (prune.rs:35), otherwise looks up exactly `parts` (prune.rs:557 `self.groups.get(parts)`). `parts` are the new item's required parts, i.e. P', so this is "P ⊆ P′ only when |P′| ≤ 4, otherwise P = P′". Constraint entailment is per register and syntactic (constraint.rs:264-271). Matches appendix.tex:977-980.

## Claims checked and accurate
- appendix.tex:930-935: derivative correct for every residual/θ/event, plus the iterated version (`derivative_correct`, `residual_folds`). Only extra hypothesis: u64 codes, which matches Scope.
- appendix.tex:947-959: the policy reduction matches `stmt_policy_reduction`/`firing_denials`/`head_pairs`, including "shortest within that case" (`n_no_uncovered_shorter`).
- appendix.tex:966-972: the succ/uniform statement over cases, residual up to language (`steps_ok`).
- appendix.tex:982-984: termination from Lem. finite-states for the implemented normalizer; Thm. search for non-Exhausted answers.
- appendix.tex:988-990: counterexample = constraint + assignments; every realization is a shortest counterexample (`outcome_ok` Refuted).
- appendix.tex:873-876: `stmt_vacuity_reductions` and `stmt_vacuity_via_refinement` say what is claimed.
- appendix.tex:676-678: every simulation rule is proved sound; the recursion terminates.
- appendix.tex:224-228: `theorem_impl_contract` and `lemma_impl_successor_abstracts` exist with the described role.
- implementation.tex:54: the derivative is verified against Lem. sderiv (`derivative_correct` in `RegexId::derivative`).
- implementation.tex:79-81: the termination proof covers pruning/simulation and is independent of the memory limit.
- paper.rs:1-4: `theorem_paper_index` proves every row, so renaming breaks it.
- Every identifier in Table rows 900-920 exists at 969449b except `verify::dsl::lang` (F3).

## Probe requests (sent to VacuityProbes)
1. Place after `theorem_search_correct` in crates/history-semantics/src/verify/refinement/search.rs:
   ```rust
   proof fn probe_scc_unsat(cases_of: spec_fn(Item) -> Set<Case>)
       ensures !(forall|i: Item| steps_ok(seq![Option::<Set<nat>>::None, None], i, cases_of(i))) {}
   ```
   and, as the dual, try to prove `exists|cases_of: spec_fn(Item)->Set<Case>| forall|i: Item| steps_ok(seq![None,None], i, cases_of(i))`. Expected: neither verifies automatically. The negative needs the hand argument in F1, and out-of-range literals (`Component(k≥2)`) read `θ[k]`, which vstd leaves unspecified. Either outcome confirms that the premise of `stmt_search_correct` cannot be discharged.
