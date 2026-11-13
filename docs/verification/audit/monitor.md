# Audit: monitor-side claims vs PR #11 head 969449b (MonitorClaims)

All artifact paths are at commit 969449b. All paper paths are under /home/zak/paper/pldi2027 (working tree, including the user's uncommitted edits).
Unless marked [INFERENCE], I read every finding directly in the code. I did not run Verus; one probe request (P1) went to VacuityProbes.

## Findings

### F1 — MAJOR (strictly, a false paper sentence): a denial does not "name the first violated rule"; it reports only that rule's mode
- Paper: appendix.tex:825 "otherwise it denies, naming the first violated rule". The same idea appears in paper.rs:16 and in the stmt_matcher doc (paper.rs:107: "denies naming the first violated rule").
- Artifact: validator.rs:35-42. `Denial` has only `mode: RuleMode`, `event: E` and `message: String`. It has no index or rule identity.
  - The message is one of two fixed strings chosen by mode (validator.rs:208-215, `denial_message` at :421-427).
  - R5 monitor.rs:48-50: `Ok(Decision::Denied(denial)) => exists|i| least_violation(before.rules, …, i) && denial.mode == before.rules[i].mode`.
  - So a caller learns only Require or Forbid. If two rules share a mode, nothing tells the caller which one fired.
- VERIFY.md is accurate here ("denial names the first violated rule by mode"). The paper dropped "by mode".
- Fix, either one:
  - Paper: "otherwise it denies, reporting the mode of the first violated rule (in source order)".
  - Code: add `index: usize` to `Denial` and make `check_step` say `least_violation(before.rules, request.event, before.history, denial.index as int)`.
  - In both cases, also disclose that policies are ordered sequences (see F6).

### F2 — MAJOR: the "completeness" in "Monitor soundness and completeness" is empty: any non-Invariant error is allowed in every state
- Paper:
  - implementation.tex:10-13, "Monitor soundness and completeness: the monitor grants a candidate exactly when the policy permits it …, unless it reports an error".
  - appendix.tex:822-829 ("It may instead return an error …").
  - intro.tex:88-90, "a correctness proof of equivalence to our denotational semantics".
  - main.tex:57-58, "proven in Verus to agree with that semantics".
  - appendix.tex:870-871, "so that no guarantee holds vacuously".
- Artifact: monitor.rs:51 `Err(error) => !(error is Invariant)`. check_frame (monitor.rs:37) only says that an `Err` leaves the history unchanged.
  - No contract says when an error may occur. A `check` whose body is `Err(HistoryError::AllocationFailed)` meets the whole `Validator::check` contract (probe P1).
  - Errors that really occur on the decision path:
    - `GraphBudget`/`GraphIndex`. compiled_rule.rs:585-634 recompiles once on these errors; if the fresh `RuleRuntime` also exceeds `MAX_GRAPH_BYTES` (100 KiB, limits.rs), the `?` at :594/:617 passes the error up.
    - Allocation failures (validator.rs:628-636 shows `AllocationFailed` from append).
    - `IdExhausted`/`RevisionExhausted` from candidate encoding and push.
  - [INFERENCE] If one rule's fold of a fixed long history does not fit even a fresh graph, every later `check` against that history errors, so the monitor can never grant again.
- Gap with the analyzer text: the analyzer bullet (appendix.tex:846-849) says "The contracts make no claim about when either is returned". The monitor bullet has no such sentence. Also, no reviewer client proves that `Ok(Grant)` is reachable: `monitor_client` and `validator_transaction` only state `result matches Ok(..) ==> …`.
- Fix:
  - Rename to "Monitor soundness" (or "decision correctness").
  - Add: "The contract makes no claim about when an error is returned; errors include graph-budget exhaustion after one recompilation and allocation/identifier exhaustion."
  - Replace "equivalence" in intro.tex:89 with "agreement of every returned decision".
  - Optional code change: give a spec for which `HistoryError` variants `check` may return under `Unmetered`.

### F3 — MAJOR: the evaluation does not run the guaranteed API (`Validator::check`), and the commit step and event-type hypotheses are unverified there
- Paper:
  - eval.tex:22-27, "call the verified monitor through unverified front ends … all benchmarks are built in a configuration that Verus verifies".
  - appendix.tex:1045-1049, "All but the last [hypotheses] are proved for the built-in tuple event types".
  - main.tex conclusion (:102-108).
- Artifact:
  - `LockPolicy` (src/policy/lock/mod.rs:286, :310) calls `CompiledPolicy::decide`. `FlowPolicy = RulePolicy<FlowEvent>` (src/policy/flow/mod.rs:130) calls `TracePolicy::decide` through `RulePolicy::check` (src/policy/rules.rs:112-189).
  - Neither calls `Validator::check`.
  - `CompiledPolicy::decide` does not append (evaluate.rs:491). Its contract, `policy_decision_result` (evaluate.rs:99-124), is `pub open(crate)` and is not part of R5.
  - The front ends and benches append histories with unverified code, e.g. fuzz/benches/dogwood/main.rs:535, :551, :655, :696 `history.push(*event)`.
  - The CaMeL policy runs in audit mode (benches/agentdojo/camel.rs:221 `.audit()`). TRUST.md:400-405 says audit mode "also appends denied events" and that errors are turned into `Deny`.
  - So `trace_safe` / "every committed history satisfies the policy" (appendix.tex:828-829) does not hold for the evaluated runs. In AgentDojo, a "block" may come from a compile or history error converted to `Deny` [INFERENCE: depends on whether any error occurred].
  - `LockEvent` (src/model.rs:71) and `FlowEvent` (src/policy/flow/mod.rs:87-91, "Hypothesis (D4): this crate is not verified, so `event_laws::<FlowEvent…>` (R1) is assumed, not proved") implement `Event` in the unverified root crate. For the evaluated event types, `event_laws` and `key_laws` are assumed, not only `hash_coherent`.
- VERIFY.md:145-147 and :198-202 and TRUST.md:398-407 disclose all of this. The paper does not.
- Fix: eval.tex:22-27 should say:
  - the experiments call `CompiledPolicy::decide` / `TracePolicy::decide`, whose verified contract gives the first-violation decision without committing;
  - commit, audit-mode appends, error-to-deny and the per-event rule filter are unverified glue;
  - the event types' `event_laws` are hypotheses, not theorems.
  
  Also qualify appendix.tex:1049.
- Artifact-side wording error: TRUST.md:403 says "The verified `check_step` covers each `TracePolicy::decide`". `check_step` is defined over `ValidatorView`/`Decision`; `TracePolicy::decide` is covered by `trace_decision_result`/`policy_decision_result`, not `check_step` (MINOR).

### F4 — MAJOR: Table tab:mechanization "Mechanized results they rest on" lists theorems the top-level monitor guarantee does not rest on
- Paper: appendix.tex:899-907. The Derivatives row lists `theorem_symbolic_derivative_correct`, `theorem_symbolic_run_correct` and `lemma_derivative_correct_is_symbolic_derivative`. The Rule decision row lists `theorem_not_fired` and `theorem_rule_decision`.
- Artifact: a grep over crates/ shows:
  - `theorem_not_fired`, `theorem_rule_decision`, `theorem_symbolic_derivative_correct` and `theorem_symbolic_run_correct` are used only in verify/paper.rs and verify/history_algebra.rs.
  - `lemma_derivative_correct_is_symbolic_derivative` (symbolic.rs:3272-3278) is never called.
  - These theorems are stated over the numeric model `Regex<L>`/`numeric_lang`/`pair_lang` (history_algebra.rs:137-239). They are an independent mechanization of the paper's δ.
  - The executable's proof chain is: `Validator::check` → `first_violation_with` → `CompiledRule::accepts_history_with_limits` (`decision_result`/`dsl_result`) → `lemma_typed_result` (compiled_rule.rs:302-355) → `RuleRuntime::accepts` / `numeric_result` (runtime.rs:554-574) → `residual_folds` (progress.rs:2704) and `derivative_correct` (symbolic.rs:3264) → `compile::verify::source_regex` / encoding lemmas. It does not pass through the history_algebra theorems.
- Fix: split each row into "executable chain" (`derivative_correct`, `residual_folds`, `accepts_history`, `lemma_dsl_violation`, `lemma_typed_result`) and "paper result mechanized independently over the abstract model" (`theorem_symbolic_*`, `theorem_not_fired`, `theorem_rule_decision`). Alternatively, rename the section heading.

### F5 — MINOR: the numeric `stmt_thm_matcher` is weaker than Thm. matcher, and `theorem_not_fired` holds by definition
- Paper: regex.tex:232-236, "Algorithm returns violates(R,e,u) … Running it for every rule … computes the policy decision".
- Artifact:
  - history_algebra.rs:203-208. `stmt_rule_decision` equates `pair_lang` (tail membership under the head substitution) with nullability. Neither the rule mode nor the violation appears, so step 3 is missing.
  - The policy-level sentence is absent from `stmt_thm_matcher` (paper.rs:92-96).
  - `stmt_not_fired` (history_algebra.rs:231-239) has an empty proof body, because `pair_lang` is defined as `exists theta. head_match && …` (junco-core verify/history_specs.rs:701-704).
  - The full theorem holds only at the R5 level (`check_step` with `least_violation`).
- Fix: in paper.rs:15 and in the table, state that the numeric rows give steps 1-2 (tail membership), and that the mode step and the policy step are in `check_step` / `lemma_dsl_violation`. Optionally add a numeric `stmt_violation` with the mode.

### F6 — MINOR: R2 representation differences the paper does not mention
- Policies are `Seq<RuleView>` in source order, with `least_violation` (semantics.rs:255-260). The paper says "a finite *set*" (bg.tex:150, :192). F1's "first" only makes sense with this order. Not mentioned in app:mech-diff.
- On rules that are not well-scoped, unresolved atoms are false for both `=` and `≠` (semantics.rs:111-120), and out-of-range atom components are false (semantics.rs:127). So `=` and `≠` are not complementary on such rules.
  - The paper (appendix.tex:1000-1003) says "adding a rule rejects tail variables that its head does not bind and heads of the wrong arity".
  - `ValidatorBuilder::add_rule`'s public contract (validator.rs:115-122) does not state this. It ensures only `rules() == old.rules().push(source@)`, with no `rule_wf(source@)` and no head length == arity.
  - Rejection happens internally: `compiled_wf` → `source::flattened` → `head_scoped` (junco-core verify/flatten.rs:164-171); `scope.rs:74-99` returns `UnboundVariable`; compiled_rule.rs:317 asserts head length == arity under the hypotheses. [INFERENCE: I did not trace that `regex_represents` implies `regex_scoped`.]
  - The analyzer does expose `rule_wf` (analyzer.rs:621; R6 `analyzer_wf`).
  - Fix: add `event_obligations::<E>() ==> (result is Ok ==> rule_wf(source@) && source@.head.len() == arity::<E>())` to `add_rule`, or reword the paper to "the compiler rejects …".
- Constants are values of the tagged union `E::Component`, so an atom or head constant can carry another coordinate's tag. Such a head never matches, and such an atom `=` is always false. The paper has c ∈ D_i. [INFERENCE: I did not check whether `constants_in_domain` rejects such constants.] This is harmless but not disclosed.
- Events need not be products. `views_surjective` is required (events.rs:39-41) but injectivity is not, so `E` may carry fields the policy cannot see (validator.rs tests: `Document.payload`). Grants and histories carry the full `E`. This is harmless; optionally add one sentence to the Scope paragraph.

### F7 — MINOR: stale identifier in the table
- appendix.tex:900 "`verify::dsl::lang`". No `lang` exists in any `verify::dsl` module. The definition is `junco_core::spec::semantics::lang` (R2, semantics.rs:151); junco-core/src/verify/dsl.rs only imports it.
- Fix: write `spec::semantics::lang`, `rule_violated` (R2).

### F8 — MINOR: trace safety is a meta-level induction, not an executable postcondition
- Artifact: tests/reviewer.rs:107-147. `run_ok` and `theorem_trace_safe` work over ghost sequences of `ValidatorView`s.
  - `Validator::wf` (validator.rs:410-413) does not include `trace_safe`, and `check`/`rollback` do not ensure `trace_safe(final(self)@)`.
  - Coverage is still complete:
    - The only public view-changing methods are `check` (→ `Step::Check`) and `rollback` (→ `Step::Rollback`). `check_with` is private.
    - `permits` ensures `final@ == old@`, so it is a stutter step that a run can omit. `finish` gives an empty history and the rules from `builder.rules()`.
    - `reset_work_events` is test-util only, unverified, and changes only counters [INFERENCE].
  - `Step::Check` needs `check_step`, which holds only under `event_obligations` (validator.rs:181).
  - `monitor_client` (reviewer.rs:190-221) shows one real step.
- Paper appendix.tex:828-829, "Every committed history therefore satisfies the policy at each of its events", is justified for `Validator` under the hypotheses. It is not justified for the evaluated front ends (F3).
- Optional fix: add `event_obligations::<E>() && trace_safe(old(self)@) ==> trace_safe(final(self)@)` to the `check`/`rollback` ensures, which makes the property direct.

### F9 — MINOR: trusted bodies on the matcher and evaluator path, against the "no part of … matcher or evaluator is a trusted body" sentence
- Paper: implementation.tex:91-92 and appendix.tex:1037-1038.
- Artifact:
  - `CompiledRule::same_owner` is `external_body` (compiled_rule.rs:433-442; `Arc::ptr_eq` ⇒ `*left == *right && **left == **right`) inside the rule evaluator.
  - history-store cache.rs:69-112 `successor_get`/`successor_put` are `external_body` with *unconditional* ensures that native `LruCache<EventClass,…>` lookup agrees with `class_key` (a view of `SmallVec<[u64;2]>`).
    - This makes the monitor's derivative memoization trust `EventClass` Hash/Eq faithfulness.
    - It is the same fact as the SmallVec axiom, but it sits in a monitor-side body, not in an `axiom fn`, and is not under `hash_coherent`.
  - cache.rs:129-139 `HistoryCursor::position` (`external_body`) selects the incremental residual cursor.
  - policy/evaluate.rs:69, :161 (callbacks / field unpacking, disclosed).
  - All of these are counted and disclosed in TRUST.md as wrappers. But the sentence "axioms … concern the analyzer's internal key types" (implementation.tex:85-87) can suggest that the monitor depends on no such equality facts.
- Fix: one clause, e.g. "the monitor's successor and cursor caches are trusted wrappers whose contracts assume faithful equality of their (integer/SmallVec) keys".

### F10 — MINOR: the wording "recompiles a fresh lazy one" is slightly off
- appendix/implementation.tex: "On exhaustion the monitor discards the graph and recompiles a fresh lazy one".
- compiled_rule.rs:588-594 calls `RuleRuntime::new(…, cfg!(feature = "cache"), …)`. With `cache` enabled (the configuration that verifies with 1624 items), the replacement is precompiled and falls back to lazy only on budget (runtime.rs:508-525).
- The paper also omits that a second exhaustion becomes an error (see F2).

## Claims checked and found accurate
- bg.tex Def. violates (bg.tex:176-187) vs R2 `rule_violated` (semantics.rs:204-238):
  - `require` ⇒ ¬inside and `forbid` ⇒ inside (`violated_by`, :179-181);
  - an unmatched head never violates (`rule_evaluation_view` None);
  - the tail is evaluated over the committed history, excluding the candidate (`history_view(history)`, :227-231).
- Def. policy-violates ⇔ `policy_denies` exists (semantics.rs:241-245); permitted ⇔ `policy_permits` (:248-252).
- Def. unify vs `head_matches` (semantics.rs:40-52): a constant matches by `eq_spec`, a variable always matches, and length must equal arity. The valuation comes from the candidate's own coordinate (`resolve_pattern`, :55-65), which matches "x_i occurs only at position i" given `head_scoped` (:34-37) and `pattern_scoped` (:68-73).
- Component tests (bg.tex:48-72) vs `test_sem`/`atom_sem`/`comparison_sem`: on well-scoped rules, `≠` is the complement of `=`, and And/Or are n-ary with the right empty cases (junco-core verify/dsl.rs `lemma_empty_operators`).
- Def. regex-lang vs `lang` (semantics.rs:151-174): Empty/All/Epsilon/Test/Union/Intersect/Not match the paper. Concat is n-ary. Star is a flatten of any number of parts, which is equivalent to the paper's u_1…u_k. Not complements over all words, which is irrelevant for the monitor because it only evaluates well-shaped histories.
- `Validator::check` contract (validator.rs:178-186):
  - unconditional `check_frame`: rules unchanged; a Grant appends exactly `request.event` and keeps the metadata; a Denial or an `Err` leaves the history unchanged;
  - under `event_obligations`, `check_step`: Grant ⇒ `policy_permits`; Denied ⇒ the least violation's mode; `Err` ⇒ not `Invariant`;
  - so, given an Ok result, it grants iff no rule is violated.
- The appendix says these are under the app:trust hypotheses. `event_obligations` (R4 hypotheses.rs:40-42) matches the appendix.tex:1045-1049 list (projections, arity 1..8, surjectivity, `eq_spec` equivalence, `obeys_eq_spec`, `hash_coherent`).
- The R5 view is tied to exec state, not uninterpreted:
  - history = `History.events@`, an owned `Vec` (history.rs:199-200, :834-836);
  - rules = views of the source rules, via the `add_rule` ensures `rules()==old.rules().push(source@)` and the `finish` ensures `validator@.rules == self.rules()`;
  - `Validator::history()` ensures `result@ == self@.history`.
- The ordered scan is correct: `first_violation_with` loop invariant plus `ordered_result` (compiled_rule.rs:190-197) gives `least_violation` or `policy_permits`.
- `lemma_dsl_violation` (compiled_rule.rs:247-257) correctly links `Some(inside)` with the mode to `rule_violated`.
- `theorem_trace_safe` / `run_ok` are a sound induction (reviewer.rs:125-147, with `lemma_check_preserves_trace_safe` and `lemma_rollback_preserves_trace_safe`, validator.rs:431-460), and every public mutating `Validator` method fits `Step::Check`/`Step::Rollback` (see F8).
- `derivative_correct` (symbolic.rs:3264-3269) states the language form of Lem. sderiv for the executable derivative graph. `residual_folds` (progress.rs:2704-2710) states the residual-after-u language. Together these match appendix.tex:928-935.
- `stmt_symbolic_derivative_correct` / `stmt_symbolic_run_correct` (history_algebra.rs:137-199) faithfully state Lem. sderiv and Thm. sderiv for the paper's δ (Def. sderiv matches `symbolic_derivative`, :24-48). Their proofs are not trivial.
- No `external_body`, `assume_specification` or `admit` in symbolic.rs, progress.rs, runtime.rs, normalize.rs, compile.rs or validator.rs (grep). The trusted leaves on the path are those listed in F9.
- On budget exhaustion the monitor recompiles (compiled_rule.rs:585-634); implementation.tex:110-111 is accurate, apart from F2 and F10.
- `theorem_monitor_check` / `theorem_monitor_permits` unfold `check_step` and `permits_result` with `rule_violated`. They restate their premises by design and are not vacuous.
- `monitor_client` has the satisfiable premise `event_obligations` (discharged for `(u32,u64)` under `hash_coherent`) and a non-trivial conclusion: a head match ⇒ not Grant.
- `theorem_analyzer_to_monitor` (reviewer.rs:154-175) has the correct direction: p refines q ⇒ p's grant is permitted by q.
- The `--test reviewer` count of 7 and the `public_specs` count of 19 match VERIFY.md:68-69 and appendix.tex:1064-1066.
- `absurd_nil` (`external_body`, `ensures false`, history-syntax event.rs:201-205) takes Frunk's uninhabited `CNil` and is unreachable at runtime. It is a counted trusted item, not a monitor soundness issue.

## Probe requests (also sent to VacuityProbes)
- P1. In crates/history-semantics/tests/reviewer.rs, inside `verus!{}`:
  ```
  proof fn probe_always_error_satisfies_contract<E: Event, M>(before: ValidatorView<E>, request: Request<E, M>)
      ensures check_frame(before, before, request, Err(HistoryError::AllocationFailed)),
          check_step(before, request, Err(HistoryError::AllocationFailed)),
          stmt_monitor_check(before, request, Err(HistoryError::AllocationFailed)),
  {}
  ```
  Expected result: it verifies. That shows that an always-erroring `check` meets the full contract (F2).
