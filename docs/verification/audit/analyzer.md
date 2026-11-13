# Audit: analyzer-side claims vs PR #11 head 969449b (AnalyzerClaims)

The artifact worktree `/tmp/audit-AnalyzerClaims` (detached at 969449b) is **kept as evidence**. Its only change is the untracked runtime probe `crates/history-analysis/tests/probe_unit_fresh.rs`, which was built and run with `cargo +1.98.1 test -p history-analysis --test probe_unit_fresh`. No Verus run. I sent Verus probe requests to VacuityProbes (pos_ac1..3, see the end of this report).

Code paths below are relative to the artifact root. Paper paths are relative to `/home/zak/paper/pldi2027`.

---

## Findings

### F1 MAJOR (BLOCKER if §7.3 is read as a verified refutation claim): the eval's 90 "rejections" are counterexamples with no instance under R3
- **Paper:**
  - `eval.tex:25-27`: "the inclusion experiments call the verified `tail_included` directly; all benchmarks are built in a configuration that Verus verifies".
  - `eval.tex:378-387`: "Characters are the action component of events whose domain is declared finite … correctly rejecting inclusion in 90 cases".
  - These combine with the counterexample-validity claims at `appendix.tex:850-859`, `implementation.tex:20-23`, `main.tex:104-105` and `intro.tex:94-95`.
- **Artifact:**
  - `benches/smt/regexlib_subset.rs:13-15`: `type Component = Component3<(), u8, ()>`. Coordinates 0 and 2 have the unit type: exactly one value each.
  - `benches/smt/main.rs:20-36`: the head pins `C0(())` and `C2(())`. Only coordinate 1 gets `with_domain`, so coordinates 0 and 2 stay *undeclared*.
  - `analyzer.rs:1597-1611`: a coordinate that a letter leaves unmatched gets `Slot::Fresh(fresh)`.
  - `questions.rs:168-178` (`choice_ok`): a fresh value must satisfy `!f(n).eq_spec(&k)` for every known `k`. `known[0]` contains `C0(())`, the head constant (`tail_constants`, `analyzer.rs` spec l.72).
  - So no admissible `f` exists, `fresh_capacity(…,0,k≥1)` is false, `cex_has_instance` is false, and every clause of the Counterexample arm of `tail_included_spec` holds vacuously.
- **Runtime evidence (observed):** the probe uses the eval's event shape on `[a]+ ⊑ ε` and prints
  `Counterexample { candidate: [Constant(C0(())), Constant(C1(97)), Constant(C2(()))], history: [[Fresh(0), Constant(C1(97)), Fresh(1)]] }` and `fresh at a unit-typed coordinate: true`.
- **Consequence:**
  - In the configuration the paper evaluates, the verified contract says nothing about any returned counterexample: it is not proved to be a refutation, and no instance exists by R3's own definition.
  - "Correctly rejecting" is checked only by the benchmark's `assert_eq!(matches!(verdict, Holds), instance.included)` (`main.rs:41-46`) against dataset labels.
  - The library itself warns about this situation (`analyzer.rs:165-168`: "treated as infinite, it could yield counterexamples that need a value the type does not have").
  - The paper's condition "which holds for every infinite type" (`appendix.tex:859`) is not met: `()` is finite and undeclared.
- **Fix:**
  - Code: in `benches/smt/main.rs`, also `with_domain(Component(0), &[Component3::C0(())])` and `with_domain(Component(2), &[Component3::C2(())])`. Re-run the timings, since there are more constants.
  - Paper: or say that the 90 rejections are checked against the dataset labels and that the event type's unit components are outside the capacity condition.
  - Fixing the bench is only sufficient together with F2.

### F2 MAJOR: R6 doesn't rule out fresh values at declared coordinates, so with any declared domain a junk counterexample satisfies every `*_spec`
- **Paper:**
  - `appendix.tex:856-859`: "A counterexample has an instance … whenever each component *without a declared domain* has at least as many values as the constants known … plus the fresh values".
  - `appendix.tex:803-804`: "Each guarantee below is a Verus postcondition".
- **Artifact:**
  - `questions.rs:227-232`: `capacity_for` quantifies over **all** coordinates (`forall|i| 0 <= i < arity ==> fresh_capacity(domains, known, i, fresh_used(cex, i).len())`). Its doc says "(zero at declared coordinates)", but nothing enforces that.
  - At a declared coordinate, `known[i] ⊇ declared set`: `new` ensures `known == declared_sets(domains)` (`verify.rs:3532-3536`) and `known` only grows (`known_with`).
  - So `fresh_capacity(…, i, k)` with `k ≥ 1` requires a value that is both `in_domain` and `misses(known[i])`, which is impossible. Equivalently, `capacity_for` holds only if `fresh_used(cex, i)` is empty at every declared `i`.
  - `counterexample_spec` (`spec/analyzer.rs:145-150`) and the four `*_spec`s never promise that emptiness.
  - It *is* proved internally: `reconstruction.rs:208-215` `slot_domain` has `Fresh(_) => domain is None`, used in the `counterexample` loop invariants at `analyzer.rs:1554` and `analyzer.rs:1584`. It is not exported.
- **Consequence:**
  - For any analyzer with a declared coordinate, `Counterexample(cex)` where `cex` puts `Fresh(0)` at that coordinate satisfies the Counterexample arms of `covered_spec`, `redundant_spec`, `at_least_as_strict_spec` and `tail_included_spec` vacuously. For `tail_included_spec` with an empty history, `shortest(…, 0, …)` is trivially true.
  - This holds even when coverage, refinement or inclusion is true. The appendix sentence is stronger than the postcondition.
  - The "decides" claims (`main.tex:104`, `intro.tex:94` "only correct verdicts") fail for declared-domain configurations: "Holds iff property" for non-Exhausted answers is not a consequence of R6.
- **Probe: VERIFIED by VacuityProbes** (`/tmp/audit-VacuityProbes/crates/history-analysis/tests/vacuity_probes.rs` at 969449b; `cargo verus verify -p history-analysis --no-default-features --features runtime,std --test vacuity_probes`, 0 errors in these fns; details in `local://audit-VacuityProbes.md`):
  - `pos_ac1_junk_cex_declared`: generic, with the exact requires/ensures given at the end. The Counterexample arms of `covered_spec` and `tail_included_spec` hold, with `!cex_has_instance` and `!capacity_for`.
  - `pos_ac2_junk_cex_for_covered_rule`: adds `by == [rule]`. Proves `covers(...)` **and** `covered_spec(..., Counterexample(junk))`, so a "refuting" counterexample coexists with true coverage.
  - `pos_ac3_junk_cex_concrete`: `(u32,u64)`, domains `[Some({C0 3}), None]`, known `[{C0 3}, {}]`, rules `[forbid (x,y) All]`, under `hash_coherent` only.
- **Fix:**
  - Code: add `&&& forall|i: int| 0 <= i < arity::<E>() && a.domains[i] is Some ==> fresh_used(cex, i) =~= ISet::empty()` to `counterexample_spec`, discharged from `slot_domain`.
  - Paper: or state the condition over all components ("…and a counterexample uses no fresh value at a declared component").

### F3 MAJOR: "complete up to resource limits" / "decides … within its resource limits" is not a verified property
- **Paper:**
  - `main.tex:59-62`: "An inclusion procedure, sound and complete up to resource limits".
  - `main.tex:104-105`: "the verified analyzer decides refinement, redundancy, and vacuity within its resource limits".
  - `intro.tex:91-95`: "verified to return only correct verdicts".
  - `implementation.tex:16-19`: "Analyzer completeness: every query terminates, so when the property fails, the query returns a counterexample, `Exhausted`, or an error…". This is a true statement, but it only says the query returns something; it is not completeness.
  - The appendix is honest (`appendix.tex:846-849`: "The contracts make no claim about when either is returned"), so the abstract and conclusion contradict the appendix.
- **Artifact:**
  - `covered`/`redundant`/`at_least_as_strict` ensure only `no_invariant_failure(result)` (`analyzer.rs:666, 723, 754`). That is defined as `!(result matches Err(HistoryError::Invariant{..}))` (`junco-core/src/verify/history_specs.rs:16-18`).
  - They also ensure `!ids_owned ==> Err(UnknownId)`, and `Ok ==> *_spec`. Nothing says "owned ids ⇒ Ok", or that an `Err` is a resource error.
  - `tail_included` (`analyzer.rs:1156`) and `add_rule` (`analyzer.rs:623`) ensure only `no_invariant_compile_failure`.
  - `Exhausted => true` is in every `*_spec` (known context).
  - A contract-satisfying implementation may return `Err(GraphIndex)` or `Exhausted` on every query.
- **Every Err path, from reading the code (not proved exhaustive):**
  - `UnknownId`: `check_id`/`check_ids` (`analyzer.rs:691`). An input error, not a resource limit.
  - `GraphIndex`: `split` and constraint tables (`constraint.rs:1130, 1365, 1467, 1509`), `Tables::push/difference/denial` (`tables.rs:335, 346`), search (`search.rs`, header l.10).
  - `IdExhausted`: constraint ids (`constraint.rs:370`), fresh values (`analyzer.rs:1515, 1605`), constants (`analyzer.rs:448-454`). The last is excluded by the capacity preconditions according to the comment at l.1301.
  - `invalid_atom_set`: `SymbolicLanguage::compile` (`history-semantics/src/symbolic_language.rs:291`). Its `HistoryError` variant is not identified here.
  - Any non-budget error from compile/search passed through by `decide` (`analyzer.rs:1381, 1407`).
  - `add_rule`/`tail_included`: `CompileError::{HeadArity, ComponentCoordinate}` are possible for well-scoped rules. `flatten_rule_parts` excludes `VariableComponentConflict`, `UnboundVariable` and `InvalidPolicy` only for scoped inputs (`flatten.rs:444-451`), and `add_rule` does not propagate even that.
  - [INFERENCE] Every path is a resource or input error, so the code plausibly *is* complete up to resource limits, but that is not verified.
- **Fix:**
  - Paper: in the abstract and conclusion, say "sound; its counterexamples are verified … ; it returns `Exhausted` or an error at resource limits (unverified)".
  - Code: or add `ids_owned(...) ==> (result is Err ==> result->Err_0 is GraphIndex || result->Err_0 is IdExhausted)`, where provable.

### F4 MINOR: `analyzer_wf` is dead, and "adding a rule rejects … heads of the wrong arity" is not in `add_rule`'s contract
- **Paper:** `appendix.tex:1000-1003`: "adding a rule rejects tail variables that its head does not bind and heads of the wrong arity".
- **Artifact:**
  - `add_rule` Ok ensures `rule_wf(rule@)` (`analyzer.rs:621`). `rule_wf` is generic in `C` and gives only `1 <= head.len() <= MAX_ARITY` plus scoping (`semantics.rs:185-187`); it says nothing about `== arity::<E>()`.
  - `spec/analyzer.rs:49-57` `analyzer_wf` ("Open consequences of the opaque `PolicyAnalyzer::wf`", including `a.rules[i].head.len() == arity`) is referenced nowhere. No lemma connects `wf()` to `analyzer_wf(self@)`.
  - `rule_constants_tagged` (l.79) is also unused.
  - The tail-variable half is proved. Wrong-arity rejection is proved only for `tail_included`, which ensures `head@.len() == arity` on Ok.
- **Fix:** add `head.len() == arity::<E>()` to `add_rule`'s Ok clause, and either add a public `lemma_wf_view(&self) requires self.wf() ensures analyzer_wf(self@)` or delete `analyzer_wf` and `rule_constants_tagged`.

### F5 MINOR: well-formed rules and queries may be rejected with no stated cause (S12, still open)
- **Artifact:** `add_rule` ensures nothing about which `CompileError` arises for a `rule_wf`, correctly tagged rule of the right arity. `docs/history/REVIEWER-SURFACE-PLAN.md:259-269` lists this as S12 and its fix is not applied. The same holds for `tail_included` on `head_tails_wf` input.
- **Paper:** no explicit acceptance claim. This matters only through F3's "decides".
- **Fix:** propagate "`rule_wf` ∧ arity ∧ tagged ⇒ no `HeadArity`/`ComponentCoordinate`/scope error" from `flatten.rs`.

### F6 MINOR: reviewer theorems mostly restate the specs; the exec client is thin
- **Artifact (`crates/history-analysis/tests/reviewer.rs`):**
  - `theorem_a1_covered_decision`, `theorem_a3_refinement`, `theorem_a3_redundancy` and `theorem_a5_escapes` have empty bodies: they unfold `*_spec`.
  - `theorem_a5_no_invariant_failure` (l.217-222) `requires no_invariant_failure(result) ensures result matches Err(e) ==> !(e is Invariant)` restates its premise. Its parameters `a`, `rule` and `by` are unused.
  - A2, A4 and A6 only instantiate `fails`.
  - `analyzer_client` (l.360-405) uses only `Domains::infinite()`. It never calls `with_domain`, so the declared-domain `new` preconditions (`domains_wf`, `constructor_capacity`) are never discharged by a client.
  - It queries only `covered(id,[id])`, `redundant(id,[id])` and `at_least_as_strict([id],[id])`: trivial self-queries, with a rule that is always in the policy.
  - Every ensures clause is guarded by `Ok`, and `add_rule` may always fail. So the client shows that the preconditions are satisfiable, not that a verdict is reachable.
  - `analyzer_client_u32_u64` re-exports only `covered`.
- **Paper:** `appendix.tex:867-871` "every guarantee is restated as a theorem about the public interface … so that no guarantee holds vacuously". Accurate for the hypotheses, but it overstates what the restatements add.
- **Fix:** add a client that calls `with_domain` (and proves `domains_wf` from its postcondition plus `to_set` lemmas), and distinct-policy queries. Or soften the wording to "the theorems' premises are satisfiable".

### F7 MINOR: `stmt_vacuity_reductions` is about the numeric encoding, not events
- **Paper:** `appendix.tex:873-876`: "Verus also proves that the vacuity checks of App. policy-reduction reduce to inclusions under the rule's head constraint (`stmt_vacuity_reductions`)". This follows `appendix.tex:867-868` "All analysis results are stated over events".
- **Artifact:** `history-semantics/src/verify/refinement/inclusion.rs:208-216` quantifies over `d: NDomains, rule: NRule` with `n_rule_denies` and `included_under(..., denial(rule), Regex::Empty)`. Its doc says "No executable vacuity query exists".
- The statement matches the appendix equations (`appendix.tex:363-368`; `denial` = tail or complement, consistent with forbid-only), but only at the numeric level.
- The typed half (`stmt_vacuity_via_refinement`, `inclusion.rs:221-226`) and `theorem_vacuity_corollaries` (`reviewer.rs:268-298`) do establish the "is a refinement question that `at_least_as_strict` answers" part.
- **Fix:** add "(on the numeric encoding)" after `stmt_vacuity_reductions`.

### F8 MINOR: the paper uses two different "case" notions for minimality
- **Paper:**
  - `appendix.tex:957-959`: "its counterexample is shortest within that case", where the case is the split constraint Γ′ on P's head constants.
  - `appendix.tex:862-865`: "its case, those whose candidate agrees with it on equality with every constant known to the analyzer".
  - `inclusion.tex:571`: "Each counterexample is then shortest for its own inclusion", which is about the Den-form per-rule inclusion. The implementation is only per split case, which `app:mech-diff` discloses.
- **Artifact:** `same_profile`/`minimal_in_case` (`questions.rs:238-270`) use all of `known`. That is a finer partition than Γ′, so the exported claim is weaker than "within Γ′". The paper's top-level bullet (`appendix.tex:860-865`) matches the code exactly.
- **Fix:** in `appendix.tex:959`, say "shortest among candidates agreeing with it on every known constant".

### F9 MINOR: error list in the Implementation section
- **Paper:** `implementation.tex:67-70`: "`Exhausted` when compilation or a search exceeds its graph budget …; an index overflow is reported as an error".
- **Artifact:** F3 lists the other paths: `IdExhausted` (constraint ids, fresh values), `UnknownId`, compile errors and `invalid_atom_set`.
- **Fix:** "resource and identifier overflows and invalid ids are reported as errors".

### F10 MINOR [INFERENCE]: the eval's event type has no discharged obligations
- **Paper:** `eval.tex:25-27`.
- **Artifact:** `analyzer_obligations::<Char>()` (`event_laws` + `key_laws`) is a precondition of `new` and `tail_included`. The benchmark is plain Rust (`benches/smt`), and `junco-core/src/verify/hypotheses.rs:72-123` has lemmas only for tuple types, none for the custom `Char`. The laws plausibly hold (e.g. `views_surjective` is witnessed by `Char(b)`), but no proof is given.
- **Fix:** add `lemma_char_event_hypotheses`, or note that the bench's event type satisfies the laws by inspection.

### F11 MINOR (semantics note): `redundant` on a policy that does not contain the rule
- `redundant_spec` (`spec/analyzer.rs:188-198`): if `!policy.contains(rule)`, `without_rule(policy, rule) == policy`.
  - `Holds` ⇒ `covers(policy, rule)`, and `removal_preserves_decisions` is trivially true.
  - A Counterexample refutes `covers(policy, rule)` but not the stated property ("removing the rule changes no decision"), which holds.
- The paper bullet (`appendix.tex:853-855`) correctly restricts the removal reading to "a policy that contains the rule". The generic "every instance … is a concrete failure of the property" (`appendix.tex:851`, `implementation.tex:20-21`) is then about coverage, not removal.
- **Fix:** add "(for a rule outside the policy, coverage by the policy)".

---

## Answers to the brief's questions
1. **Definitions and directions.**
   - `refines(d,P,Q)` (`questions.rs:73-78`): permitted by P ⇒ permitted by Q, which equals Def. policy-refinement's "Q denies ⇒ P denies" (`inclusion.tex:68-77`), restricted to `in_domains`.
   - `at_least_as_strict(stricter, than)` ⇒ `refines(stricter, than)` (`analyzer.rs:751-757`), matching `appendix.tex:835-836` "the first policy refines the second".
   - The vacuity calls `([], [r])` and `([r], [forbid h Univ])` match `appendix.tex:837-840` and `inclusion.tex:83-85`.
   - `covers` matches P∖{R} ⊑ {R}. `never_denies` and `always_denies` match the paper.
   - The counterexample arm "pair the second policy denies and the first permits" matches `uncovered(pp, qq[j])`.
   - Redundant on an absent rule: see F11.
2. **Counterexample validity.**
   - `every_instance` is sound but vacuous when there is no admissible choice. The paper's capacity condition differs from `capacity_for` at declared coordinates (F2).
   - Fresh at declared coordinates is not excluded by R6, although it is excluded internally (`slot_domain`).
   - In the eval configuration the counterexamples are uninstantiable (F1, observed).
3. **Minimality.**
   - `tail_included`: `shortest` over all domain pairs, as in the paper.
   - Policy queries: `minimal_in_case` over the profile on all known constants, matching the top-level bullet; `appendix.tex:959` differs (F8).
   - `at_least_as_strict`: per the same rule `qq[j]`, as in the paper.
4. **Completeness.** Not verified (F3, Err list included). The appendix wording is honest; the abstract, conclusion and intro are not. `add_rule`/`tail_included` may reject well-formed inputs (F5).
5. **Vacuity.** `stmt_vacuity_via_refinement` plus `theorem_vacuity_corollaries` establish `appendix.tex:836-840` (the semantic iff plus the Holds direction; the counterexample direction follows from the `at_least_as_strict_spec` refutation clause and the iff). `stmt_vacuity_reductions` establishes `appendix.tex:873-875`, but numerically (F7).
6. **Reviewer theorems.** Largely restatements; the client is thin (F6).
7. **Domains.**
   - Nonemptiness is enforced: `with_domain` returns `Err(Empty)` (`analyzer.rs:223`), and `new` requires `domains_wf` (`values.len() > 0`, tagged; `questions.rs:61-67`).
   - `in_domains` is nonempty under `event_laws` (`views_surjective`, `history-syntax/src/spec/events.rs:39-49`) plus reflexive `eq_spec` (R4 `eq_equivalence`). So declaring domains cannot make everything vacuous; I did not run a Verus probe for this.
   - Declaring domains does open the junk-counterexample gap of F2.

## Claims checked and found accurate
- `appendix.tex:830-836`: the soundness bullets for tail inclusion, coverage, redundancy and refinement match the Holds arms of the four `*_spec`s.
- `appendix.tex:841-849`: the completeness bullet is honest (it states that the contracts make no claim about Err/Exhausted).
- `appendix.tex:851-855`: the per-query descriptions of counterexample instances match `tail_fails`/`uncovered`/`removal_fails`.
- `appendix.tex:860-865`: the minimality bullet matches `shortest`/`minimal_in_case`/the per-`qq[j]` existential.
- `implementation.tex:20-23`: "whenever the component types have enough values to instantiate it" is consistent with `capacity_for`, but see F1 and F2 for its practical scope.
- `implementation.tex:24-26`: minimality wording is accurate.
- `implementation.tex:67-70`: the code matches the prose. `decide` maps exactly `GraphBudget` to `Exhausted` (`analyzer.rs:1375-1408`); this is unverified prose (known context).
- `implementation.tex:72-77`: `covered`/`redundant`/`at_least_as_strict` exist, split per case (`analyzer.rs:835-889`), and vacuity goes through `at_least_as_strict`.
- `appendix.tex:946-956`: the per-rule, per-case split description matches `covered_with`/`policy_difference` (head atoms of `by`, `case.entails(head)` selection, denial union).
- `appendix.tex:1005-1006`: require rules are handled by complement, via `tables.denial(&numeric, mode)`.
- `appendix.tex:1008-1010`: declared domains are nonempty, and results are restricted to `in_domains`.
- `appendix.tex:993-995`: the 32-bit constant ids match `add_rule_capacity`/`query_capacity` (≤ `u32::MAX`).
- Termination: the exec loops carry `decreases`, and search uses `theorem_impl_items_bound`/`lemma_running_items_bound` (`search.rs:199-251`). The names in the `tab:mechanization` completeness row exist.
- `tab:mechanization`: `stmt_refines_iff_covers`, `stmt_redundant_iff_covered`, `stmt_policy_reduction` and `stmt_vacuity_reductions` all exist (`refinement/semantics.rs:30-42`, `refinement/inclusion.rs:145, 208`).
- `theorem_analyzer_to_monitor` (`reviewer.rs:300-326`) is a meaningful bridge from `at_least_as_strict` Holds to `Validator` permit inside the domains.
- `RuleId` owner tagging prevents cross-analyzer ids, except when `owner == 0` on allocator exhaustion (`analyzer.rs:589`). That case is harmless for soundness: the specs index `self@.rules`.

## Probe requests (sent to VacuityProbes; it acked them as pos_ac1..3 in `/tmp/audit-VacuityProbes/crates/history-analysis/tests/vacuity_probes.rs`)
The probe goes in `crates/history-analysis/tests/reviewer.rs` (or a sibling test file), with the same imports plus `ValueView`:
```rust
proof fn probe_junk_cex_declared<E: Event>(a: AnalyzerView<E::Component>, rule: nat, by: Seq<nat>,
    head: HeadView<E::Component>, left: RegexView<E::Component>, right: RegexView<E::Component>, x: E::Component)
    requires eq_equivalence::<E::Component>(), arity::<E>() >= 1,
        a.domains.len() == arity::<E>(), a.known.len() == arity::<E>(),
        a.domains[0] == Some(Set::<E::Component>::empty().insert(x)), a.known[0].contains(x),
    ensures ({ let cex = CexView::<E::Component> {
            candidate: Seq::new(arity::<E>(), |i: int| ValueView::<E::Component>::Fresh(0)), history: Seq::empty() };
        covered_spec::<E>(a, rule, by, InclusionView::Counterexample(cex))
        && tail_included_spec::<E>(a, head, left, right, InclusionView::Counterexample(cex))
        && !cex_has_instance::<E>(a.domains, a.known, cex) && !capacity_for::<E>(a.domains, a.known, cex) })
```
Variant: add `by == seq![rule]`, `rule < a.rules.len()` and ensure `covers(...)` as well, to show that a "refuting" counterexample can coexist with true coverage.
