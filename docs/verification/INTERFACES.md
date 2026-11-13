# Reviewer interface files (R1–R6)

The six files below are the reviewer surface of the mechanization: the definitions a reader of the
paper checks against Sections 3–5, and the only places where the meaning of a theorem is fixed.
Only the integration owner edits them during the reviewer-surface refactor; every other file may
import from them. The flow is strictly downward: R1 → R2 → R3/R4 → R5/R6 → `verify/paper.rs` and the
`reviewer.rs` tests.

| Id | File | Contents | Paper |
|---|---|---|---|
| R1 | `crates/history-syntax/src/spec/events.rs` | `arity`, `projection_laws`, `event_view`, `well_tagged`, `views_surjective`, `event_laws`; the `*View` types and `View` impls of the owned DSL | `sec:events`, `sec:rules` |
| R2 | `crates/junco-core/src/spec/semantics.rs` | scoping (`head_scoped`, `regex_scoped`), `head_matches`, `test_sem`, `lang`, `violated_by`, `rule_wf`, `head_tails_wf`; over events: `history_view`, `rule_views`, `rule_evaluation`, `rule_violated`, `policy_denies`, `policy_permits`, `least_violation` | `def:violates`, `def:policy-violates` |
| R3 | `crates/junco-core/src/spec/questions.rs` | `DomainsView`, `in_domain`, `in_domains`, `domains_wf`; `refines`, `covers`, `never_denies`, `always_denies`, `forbid_all`, `tails_included`; `ValueView`, `CexView`, `InclusionView`, `admissible`, `instantiates`, `cex_has_instance`, `every_instance`, `fresh_capacity`, `capacity_for`; `same_profile`, `shortest`, `shortest_in_case`, `minimal_in_case`; the constant extractors `pattern_constant`, `test_constants`, `regex_constants`, `head_constants`, `rule_constants` | `def:policy-refinement`, `app:policy-reduction`, `thm:search` |
| R4 | `crates/junco-core/src/spec/hypotheses.rs` | `eq_equivalence`, `hash_respects_eq`, `key_laws`, `event_obligations` | plan S4, decision 4 |
| R5 | `crates/history-semantics/src/spec/monitor.rs` | `ValidatorView`, `check_frame`, `check_step`, `permits_result`, `rollback_step`, `trace_safe` | `thm:matcher` at the level of `Validator` |
| R6 | `crates/history-analysis/src/spec/analyzer.rs` | `AnalyzerView`, `analyzer_wf`, `known_with`, `tail_constants`, capacities, `rules_of`/`without_rule`, `uncovered`/`tail_fails`, `counterexample_spec`, `covered_spec`, `removal_preserves_decisions`, `redundant_spec`, `at_least_as_strict_spec`, `tail_included_spec` | A1–A6 |

## Conventions

- Every predicate over an analyzer or monitor is stated over real events `E` (R2's
  `rule_violated`/`policy_permits` through `event_view`), never over internal numeric encodings.
  The encodings stay in the `verify/` trees and are connected by refinement proofs.
- Component equality is `PartialEqSpec::eq_spec`; representation equality never appears in a
  reviewer-facing statement.
- The `Exhausted` verdict is vacuous in every `*_spec`; A5 (when it is returned) is prose in R6's
  header (recorded as a deviation from the handoff's target A5 in STATUS.md).
- R4 has no uninterpreted conjunct: `KeyHash::hash_spec` is a spec function of the key and
  `hash_respects_eq` is proved per key type in `junco_core::verify::hypotheses`; the hash
  containers are verified code over hashconsius's `index::Buckets`
  (`history_store::keyed::KeyedMap`). The concrete reviewer theorems are premise-free.
- `AnalyzerView::known` is fixed by the contracts (`new`, `add_rule`, `tail_included`; see R6's
  header), so capacity is relative to exactly the constants of the inputs.
- `counterexample_spec` excludes fresh values at declared coordinates. Its instance guarantee
  requires `undeclared_capacity` only at undeclared coordinates; declared coordinates need no
  spare values. `theorem_counterexample_has_instance` and `theorem_declared_fresh_rejected`
  in `crates/history-analysis/tests/reviewer.rs` expose these two guarantees.

## Reading order for a reviewer

1. R1: what an event is; check `event_view` and `event_laws` against `sec:events`.
2. R2: `lang`, `rule_violated`, `least_violation`; check against `def:violates` and
   `def:policy-violates`.
3. R5: `check_step` is Theorem `thm:matcher` for `Validator::check`; `trace_safe` is what a
   committed history satisfies.
4. R3 + R6: the questions and what `Holds`/`Counterexample` promise; `counterexample_spec` and
   `minimal_in_case` are PR #10's minimality notions over events.
5. `crates/history-semantics/src/verify/paper.rs` (Track T) collects the theorems that instantiate
   R5/R6 with the implementation; `tests/reviewer.rs` in `history-semantics` and `history-analysis`
   are the end-to-end statements the CI verifies.
