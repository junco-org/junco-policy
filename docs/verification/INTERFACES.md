# Reviewer interface files

The six files below are the reviewer surface of the mechanization: the definitions a reader of the
paper checks against Sections 3–5, and the only places where the meaning of a theorem is fixed.
Every other file may import from them. The flow is strictly downward: events → semantics →
questions/hypotheses → monitor/analyzer → `verify/paper.rs` and the `reviewer.rs` tests.

| Interface | File | Contents | Paper |
|---|---|---|---|
| Events | `crates/history-syntax/src/spec/events.rs` | `arity`, `projection_laws`, `event_view`, `well_tagged`, `views_surjective`, `event_laws`; the `*View` types and `View` impls of the owned DSL | `sec:events`, `sec:rules` |
| Semantics | `crates/junco-core/src/spec/semantics.rs` | scoping (`head_scoped`, `regex_scoped`), `head_matches`, `test_sem`, `lang`, `violated_by`, `rule_wf`, `head_tails_wf`; over events: `history_view`, `rule_views`, `rule_evaluation`, `rule_violated`, `policy_denies`, `policy_permits`, `least_violation` | `def:violates`, `def:policy-violates` |
| Analysis questions | `crates/junco-core/src/spec/questions.rs` | `DomainsView`, `in_domain`, `in_domains`, `domains_wf`; `refines`, `covers`, `never_denies`, `always_denies`, `forbid_all`, `tails_included`; `ValueView`, `CexView`, `InclusionView`, `admissible`, `instantiates`, `cex_has_instance`, `every_instance`, `fresh_capacity`, `capacity_for`; `same_profile`, `shortest`, `shortest_in_case`, `minimal_in_case`; the constant extractors `pattern_constant`, `test_constants`, `regex_constants`, `head_constants`, `rule_constants` | `def:policy-refinement`, `app:policy-reduction`, `thm:search` |
| Hypotheses | `crates/junco-core/src/spec/hypotheses.rs` | `hash_coherent`, `eq_equivalence`, `key_laws`, `event_obligations` | assumptions on event types |
| Monitor specification | `crates/history-semantics/src/spec/monitor.rs` | `ValidatorView`, `check_frame`, `check_step`, `permits_result`, `rollback_step`, `trace_safe` | `thm:matcher` at the level of `Validator` |
| Analyzer specification | `crates/history-analysis/src/spec/analyzer.rs` | `AnalyzerView`, `known_with`, `tail_constants`, capacities, `rules_of`/`without_rule`, `uncovered`/`tail_fails`, `undeclared_capacity`, `counterexample_spec`, `covered_spec`, `removal_preserves_decisions`, `redundant_spec`, `at_least_as_strict_spec`, `tail_included_spec` | coverage, counterexamples, redundancy, tail inclusion, minimality |

## Conventions

- Every predicate over an analyzer or monitor is stated over real events `E` (the semantics'
  `rule_violated`/`policy_permits` through `event_view`), never over internal numeric encodings.
  The encodings stay in the `verify/` trees and are connected by refinement proofs.
- Component equality is `PartialEqSpec::eq_spec`; representation equality never appears in a
  reviewer-facing statement.
- The `Exhausted` verdict is vacuous in every `*_spec`; when it is returned is stated in prose in the
  analyzer specification's header.
- The hypotheses' `hash_coherent` is the single uninterpreted hashing hypothesis. Nothing discharges it for a
  user component type: the reviewer theorems carry `hash_coherent::<C>()` as a premise, and the
  concrete witnesses prove every other conjunct of the bundles. Only the library's internal key
  types take it by axiom (`history_analysis::verify::key_axioms`, listed in TRUST.md).
- `AnalyzerView::known` is fixed by the contracts (`new`, `add_rule`, `tail_included`; see the analyzer
  specification's header), so capacity is relative to exactly the constants of the inputs.
- `counterexample_spec` excludes fresh values at declared coordinates. Its instance guarantee
  requires `undeclared_capacity` only at undeclared coordinates; declared coordinates need no
  spare values. `theorem_counterexample_has_instance` and `theorem_declared_fresh_rejected`
  in `crates/history-analysis/tests/reviewer.rs` expose these two guarantees.
- `stmt_search_correct` requires `trace_steps_ok`: complete successor cases for expanded
  trace nodes only. This is the premise `lemma_trace_query_ok` discharges for the executable;
  `stmt_thm_search` and `theorem_paper_index` use this same non-global search statement.

## Reading order for a reviewer

1. Events (`crates/history-syntax/src/spec/events.rs`): what an event is; check `event_view` and `event_laws` against `sec:events`.
2. Semantics (`crates/junco-core/src/spec/semantics.rs`): `lang`, `rule_violated`, `least_violation`; check against `def:violates` and
   `def:policy-violates`.
3. Monitor specification (`crates/history-semantics/src/spec/monitor.rs`): `check_step` is Theorem `thm:matcher` for `Validator::check`; `trace_safe` is what a
   committed history satisfies.
4. Analysis questions (`crates/junco-core/src/spec/questions.rs`) and analyzer specification
   (`crates/history-analysis/src/spec/analyzer.rs`): the questions and what `Holds`/`Counterexample` promise; `counterexample_spec` and
   `minimal_in_case` are the per-case minimality notions over events.
5. `crates/history-semantics/src/verify/paper.rs` collects the theorems that instantiate
   the monitor and analyzer specifications with the implementation; `tests/reviewer.rs` in `history-semantics` and `history-analysis`
   are the end-to-end statements the CI verifies.
