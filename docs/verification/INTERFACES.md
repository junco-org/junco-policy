# Reviewer-surface interfaces

Integration branch: `refactor/reviewer-surface`, incorporating maintainer inbox through `b8aee8a`.
This document fixes the shared vocabulary before the implementation tracks branch. Track 0 adds
specifications without migrating existing executable contracts; the later tracks complete the
cutover. A track that cannot implement an interface stops and reports the concrete mismatch to
the integration owner. It does not redefine the interface locally.

## Canonical files and definitions

| Surface | Definitions | Replaces at cutover |
|---|---|---|
| R1 `history-syntax/src/spec/events.rs` | `arity`, `event_view`, `well_tagged`, `projection_laws`, `surjectivity`, `event_laws`; `PatternView`, `HeadView`, `AtomView`, `TestView`, `RegexView`, `RuleView` | Event spec definitions in `event::specs` and structural view declarations in `verify::dsl`. The temporary R1 view imports are replaced by the actual declarations, not retained as aliases. |
| R2 `junco-core/src/spec/semantics.rs` | `head_matches`, `resolve`, `test_sem`, `lang`, `rule_violated`, `policy_denies`, `least_violation`, `head_wf`, `test_wf`, `regex_wf`, `rule_wf`, `head_tails_wf` | Typed DSL denotation, the duplicate policy status/denial semantics, and compiled-rule least-violation logic. Lower-level component/numeric interpreters get distinct names. |
| R3 `junco-core/src/spec/questions.rs` | `Domains`, `domains_wf`, `event_in_domains`, `in_domains`, `covers`, `refines`, `without_rule`, `redundant_in`, `never_denies`, `always_denies`, `tails_included`; canonical pattern/test/regex/head/rule constant collectors, `knowable_constants`, `tail_knowable_constants`, `known_within`; `SymbolicValue`, `Counterexample`, `symbolic_event_wf`, `counterexample_wf`, `fresh_names`, `fresh_count`, `fresh_capacity`, `counterexample_capacity`, `value_of`, `choice_ok`, `instance`, `has_instance`, `every_instance` | Policy questions and counterexample-instance semantics over unconstrained component tuples; structural constant collectors move here rather than being duplicated. |
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
  an extra analyzer-state field. `known_within` requires coordinate-wise subset of
  `knowable_constants(domains, all_registered_rules)` for policy queries, or
  `tail_knowable_constants(domains, head, left, right)` for tail queries. Those sets contain
  exactly source literals at that coordinate plus declared domain values. Historical interned
  values from unrelated queries are not allowed to inflate the bound.
  An instance uses one shared, injective, correctly tagged fresh choice across the candidate and
  history. Capacity counts distinct names actually used, not the largest numeric name.
- F supplies public native-state/result adapters. `QueryResult::Exhausted` is a unit variant and
  `escapes(Exhausted)` is true: **Exhausted makes no claim**. This is the maintainer's explicit
  fallback. Arithmetic `charged`/`requested` fields were forgeable and are removed. A genuine
  store-only token would require broad ghost-state/error propagation through charge, the store
  trait and search wrappers; no substitute token or fabricated arithmetic witness is introduced.
  C still separates budget errors from index/product overflow and proves charge diagnostics.
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

No `Event::coordinate_cardinality` method is added. The maintainer cancelled that extension.
For an undeclared finite-enum coordinate whose real events are covered, the S1 regression accepts
`Holds` or a counterexample whose capacity fails at that coordinate, never a capacity-satisfying
refutation. The mathematical capacity lemmas require no runtime type metadata.

## Hypothesis choices

The monitor bundle does not require surjectivity: existing monitor soundness needs native
projection correctness and faithful component equality/hashing, not construction of events from
symbolic tuples. The analyzer bundle adds surjectivity. This avoids weakening monitor guarantees
by adding an unnecessary premise.

`hash_coherent` remains the single uninterpreted hashing hypothesis. The maintainer withdrew the
earlier primitive-key and `Component2/3/4` compositional-axiom approval; those introductions are
not allowed. Decision 4's five internal-key introductions may assume **only hash_coherent**;
native equality, equivalence and view reflection must be proved. The ordered-parts key uses
a locally owned PartsKey wrapper because the external SmallVec model supplies no equality
specification; its one hashing introduction replaces the former SmallVec introduction.
Each remaining assumption is listed and justified in TRUST.md.
Public `lemma_u8_event_hypotheses` for `(u8, u8, u8)` and
`lemma_u32_event_hypotheses` for `(u32, u8, u8)` prove arity, projection, surjectivity and equality
laws and take only `hash_coherent::<E::Component>()` as their premise. No arbitrary user Hash/Eq
implementation is assumed correct, and neither analysis nor semantics gains an external body.

## Ownership and merge protocol

Track A owns R4 and obligation definitions. `eq_equivalence(eq, domain)` is the canonical
equivalence law on a carrier: native keys use the full carrier, numeric encodings instantiate
one carrier per coordinate. B owns R1–R3 and the typed/numeric bridges, including all edits to
`typed_numeric.rs`; A hands B its equivalence consolidation instead of editing that file.
C owns error variants and error contracts; D owns R5 and monitor/policy implementations; F owns
R6 and analyzer state/results. The native analyzer view and its active semantic callers cannot
cut over independently without shims, so B and F perform that representation/entry-contract
cutover in one atomic integration batch after A/C prerequisites. F-prep continues independent
domain-constructor and verified owner work. E owns the paper index and specified hygiene files;
G owns builds/trust scanning and root event adapters. T starts after D/F using only public items.

To keep one owner per file, B alone edits `history-syntax/src/event.rs` while moving EventSpec.
A puts `PartialEqSpecImpl` in `history-syntax/src/spec/equality.rs` and owns its registration in
`spec/mod.rs`. The implementations remain in their defining crate, without an orphan-rule
workaround or alias.

The rename and least-violation relocation are separate integration commits before Wave 1. Each
track gets its own worktree and target directory, shares `CARGO_HOME`, and iterates with module/
function filters. Merge gates cover the full-feature changed crates and downstream crates,
including `public_specs` when semantics changes. Wave gates cover all eleven configurations
concurrently, with persistent per-configuration targets, plus workspace/fuzz native checks.
The next wave starts after its prerequisite merge gates; the previous wave gate may continue
concurrently. Only the integration owner runs the full verification script.

All tracks preserve line endings and existing guarantees and add no trust outside decision 4.
PR #10 proves minimum history length within the returned case/profile, not across all cases for
one rule. Its predicates/proofs may move or change representation, but their semantic content is
preserved exactly. Same-concept equivalence lemmas are temporary migration aids only: remove
them and the superseded definitions before merge. Retain genuine implementation-to-model links
and classify each remaining relation lemma in the final report.

## Findings rechecked at the updated baseline

S1–S6 and S9/S11/S12 were present in the baseline definitions/contracts. PR #10 head `52118c4`
is now incorporated by `0f40cb6`; its S7/S8 guarantees are preserved during migration. S10's
false executable-contract header was already corrected upstream; dead vacuity predicates and
the typed linking theorem remain part of F/B's cutover. Existing upstream comment/anchor repairs
are not new fixes here. E has removed the genuinely unused `expansion_ok` and `covered_with_ok`
on its branch. The old trust inventory already listed `singleton_invariants`; G eliminates that
axiom rather than merely reclassifying it.
Each track rechecks its remaining plan findings before changing them and reports stale findings.
