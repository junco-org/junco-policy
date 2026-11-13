# Reviewer-surface interfaces

Integration branch: `refactor/reviewer-surface`, based on the updated handoff at `83de803`.
This document fixes the shared vocabulary before the implementation tracks branch. Track 0 adds
specifications without migrating existing executable contracts; the later tracks complete the
cutover. A track that cannot implement an interface stops and reports the concrete mismatch to
the integration owner. It does not redefine the interface locally.

## Canonical files and definitions

| Surface | Definitions | Replaces at cutover |
|---|---|---|
| R1 `history-syntax/src/spec/events.rs` | `arity`, `event_view`, `well_tagged`, `projection_laws`, `surjectivity`, `finite_coordinate`, `event_laws`; `PatternView`, `HeadView`, `AtomView`, `TestView`, `RegexView`, `RuleView` | Event spec definitions in `event::specs` and structural view declarations in `verify::dsl`. The temporary R1 view imports are replaced by the actual declarations, not retained as aliases. |
| R2 `junco-core/src/spec/semantics.rs` | `head_matches`, `resolve`, `test_sem`, `lang`, `rule_violated`, `policy_denies`, `least_violation`, `head_wf`, `test_wf`, `regex_wf`, `rule_wf`, `head_tails_wf` | Typed DSL denotation, the duplicate policy status/denial semantics, and compiled-rule least-violation logic. Lower-level component/numeric interpreters get distinct names. |
| R3 `junco-core/src/spec/questions.rs` | `Domains`, `domains_wf`, `event_in_domains`, `in_domains`, `covers`, `refines`, `without_rule`, `redundant_in`, `never_denies`, `always_denies`, `tails_included`; `SymbolicValue`, `Counterexample`, `symbolic_event_wf`, `counterexample_wf`, `fresh_names`, `fresh_count`, `fresh_capacity`, `counterexample_capacity`, `value_of`, `choice_ok`, `instance`, `has_instance`, `every_instance` | Policy questions and counterexample-instance semantics over unconstrained component tuples. |
| R4 `junco-core/src/spec/hypotheses.rs` | `eq_equivalence`, `hash_coherent`, `key_laws`, `monitor_hypotheses`, `analyzer_hypotheses` | Both hash/key-obligation copies, native/analyzer bundles, and duplicate equivalence predicates. Library-internal key laws are not user preconditions. |
| R5 `history-semantics/src/spec/monitor.rs` | `ValidatorView`, `Validator::wf`, `validator_frame`, `check_step`, `permits_spec`, `rollback_spec`, `finish_spec`, `trace_safe` | Private monitor views and mixed semantic/storage clauses in `check_result` and policy wrappers. |
| R6 `history-analysis/src/spec/analyzer.rs` | `GRAPH_BYTES`, `AnalyzerView`, `PolicyAnalyzer::wf`, `QueryResult`, `rules_of`, `valid_ids`, `analyzer_frame`, `escapes`, `covered_spec`, `redundant_spec`, `at_least_as_strict_spec`, `tail_included_spec` | Private analyzer views and repeated executable correctness clauses. PR #10's minimality/removal content is migrated exactly to this vocabulary; obsolete predicates and compatibility bridges are deleted before merge. |

The separate least-violation move preserves the old typed denotation exactly and changes its
history argument to `Seq<E>`; callers apply the storage history accessor. Its R2 body temporarily
uses the old typed `rule_violated`. B cuts that body and every consumer over to the canonical R2
denotation while deleting the old interpreter. No compatibility lemma or old-name re-export is
introduced.

## Semantic state and result adapters

- `ValidatorView<E>` has exactly `rules: Seq<Rule<E>>` and `history: Seq<E>`.
- `AnalyzerView<E>` has exactly `domains: Domains<E::Component>` and `rules: Seq<Rule<E>>`.
  Stored codebooks, owner identities, capacities and numeric proof state stay behind the opaque
  native `wf` and public preservation/revealing lemmas. Native owner checks are not encoded as
  membership in the semantic rule-index list.
- R2/R3 quantify over candidates `E` and histories `Seq<E>`. Wrong-tag tuples are not events.
  `rule_wf` includes source arity, scoping and literal coordinate tags, sufficient to justify the
  absence of `HeadArity` and `ComponentCoordinate` errors for well-formed inputs.
- R3 counterexamples carry their finite `known` context. It is part of the symbolic result, not
  an extra analyzer-state field. An instance uses one shared, injective, correctly tagged fresh
  choice across the candidate and history. Capacity is measured by the number of distinct names
  actually used at each coordinate, not by the largest numeric name.
- F supplies public native-state/result adapters to these models. In particular, the
  `QueryResult::Exhausted { charged, requested }` evidence must come from the actual failed graph
  charge propagated by C; choosing arbitrary numbers that exceed the budget is not a valid
  implementation. Index/product overflow remains an error. The canonical runtime budget must
  have one definition at cutover.
- Every query spec states unconditional `Holds` soundness. Counterexample shape and the
  every-real-instance failure clause are unconditional; only existence and explicit negation
  require `counterexample_capacity` for that returned result. Errors exclude `Invariant`, not
  all resource/input failures.
- `redundant_spec` keeps PR #10's coverage meaning for an absent target, unconditional decision
  preservation for Holds, and decision-changing counterexamples when the target occurs. No
  membership precondition is added. Filtering removes every matching id; another id registering
  the same source rule remains a distinct rule.
- `tail_included_spec` preserves domains and rules and includes the existing global history-length
  bound over real events. Policy-query minimality is not redefined here: R6 must additionally
  restate PR #10's exact per-case/profile clause and removal clause when it is integrated.

The S1 executable regression additionally needs conservative runtime type information: the
current projection-only `Event` API cannot distinguish two finite types with identical observed
constants but different unseen values. B adds `Event::coordinate_cardinality(index: usize) ->
Option<usize>`, defaulting to `None`, with the verified external-trait contract
`obeys_projection_spec() && result == Some(n) ==> finite_coordinate::<Self>(index as nat, n as nat)`.
This is optional metadata, not a declared domain or a new trusted assertion. A custom finite
event proves its override. F uses a finite effective search universe only when all those equality
classes have been interned; the public undeclared domain remains `None`. Unknown metadata keeps
the existing symbolic search. B owns the native trait addition and its R1 contract; F owns its
activation in the analyzer. No existing native method contract is weakened.

## Hypothesis choices

The monitor bundle does not require surjectivity: existing monitor soundness needs native
projection correctness and faithful component equality/hashing, not construction of events from
symbolic tuples. The analyzer bundle adds surjectivity. This avoids weakening monitor guarantees
by adding an unnecessary premise.

`hash_coherent` is the single uninterpreted faithfulness token specified by decision 4.
The pinned vstd `obeys_key_model` cannot replace it in all configurations: its module is gated
behind `std` and the no-default-features core configuration rejects the reference. The user
explicitly approved narrowly scoped primitive-key axioms and compositional introductions for
the built-in tagged-component types, in addition to decision 4's internal-key axioms. A lists
and justifies every new trusted introduction in TRUST.md through G; it does not introduce an
axiom for arbitrary user Hash/Eq. Concrete public witness lemmas are
`lemma_u8_event_hypotheses` for `(u8, u8, u8)` and `lemma_u32_event_hypotheses` for
`(u32, u8, u8)`, each establishing both bundles. Neither analysis nor semantics gains an
external body.

## Ownership and merge protocol

Track A owns R4 and obligation definitions. Track B owns R1–R3 and the typed/numeric bridges;
A's equivalence-only changes in `typed_numeric.rs` are coordinated separately. C owns error
variants and error contracts, D owns R5 and monitor/policy implementations, and F owns R6 and
analyzer state/results. F-prep changes no A1–A5 proof obligations before A/B/C merge. E owns the
paper index and specified hygiene files; G owns builds/trust scanning and root event adapters.
T starts only after D/F and uses only public items.

The rename and least-violation relocation are separate integration commits before Wave 1. Each
track gets its own worktree and target directory, shares `CARGO_HOME`, and iterates with module/
function filters. Merge gates cover the full-feature changed crates and downstream crates,
including `public_specs` when semantics changes. Wave gates cover all eleven configurations
concurrently, with persistent per-configuration targets, plus workspace/fuzz native checks.
The next wave starts after its prerequisite merge gates; the previous wave gate may continue
concurrently. Only the integration owner runs the full verification script.

All tracks preserve line endings and existing guarantees and add no trust outside decision 4
and the scoped key introductions explicitly approved above.
PR #10 proves minimum history length within the returned case/profile, not across all cases for
one rule. Its predicates/proofs may move or change representation, but their semantic content is
preserved exactly. Same-concept equivalence lemmas are temporary migration aids only: remove
them and the superseded definitions before merge. Retain genuine implementation-to-model links
and classify each remaining relation lemma in the final report.

## Findings rechecked at the updated baseline

S1–S6 and S9/S11/S12 remain present in the current definitions and executable contracts. PR #10
addresses S7/S8 on its branch; it is not assumed merged. S10's false executable-contract header
was already corrected by `649cd5d`, while the dead vacuity predicates and missing linking theorem
remain. Several stale comments and README anchors were already repaired upstream; they are not
new fixes in this refactor. `expansion_ok` and `covered_with_ok` still exist and are explicitly
marked unused. The trust inventory already lists `singleton_invariants`; the missing distinction
is that it is a proof axiom, not that its declaration was absent from the 105-item inventory.
Each track rechecks its remaining plan findings before changing them and reports stale findings.
