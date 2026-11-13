# Plan: a reviewer-readable verification surface, and fixes from the spec audit

Baseline: `main` at `1efa267` (merge of PR #9; same tree as PR head `d7d9d53`). Paper: `junco-org/paper`, `pldi2027/`.
Line numbers refer to that baseline and drift; symbol names are authoritative.

Method: eight read-only audits of the specifications, the executable contracts, the trusted base,
the documentation, and the paper (Sections 3, 5, 6 and the appendix). Nothing was compiled or
verified while writing this plan. Every finding below cites code that was read; items marked
*[inference]* were not traced end to end.

Goal: a reviewer reads **about six files** and knows exactly (1) what the monitor and the analyzer
guarantee, (2) under which hypotheses, (3) what is trusted, and (4) how each paper result maps to a
mechanized statement. Nothing outside those files should be needed to judge whether the
guarantees are the intended ones.

---

## 1. Where things stand

| Question a reviewer asks | Today |
|---|---|
| What does the monitor guarantee? | Spread over `check_result` → `denial_at` → `least_violation` → `rule_violated`, all `open(crate)`/`open(super)`; mixed with frame, codebook and revision clauses; no trace-level statement. |
| What does the analyzer guarantee? | `*_correct` in `history-semantics/src/verify/refinement/analyzer.rs`, plus extra clauses repeated in each entry point's `ensures`; about 93 definitions across 4 crates; several preconditions `open(crate)` or `closed`. |
| Under which hypotheses? | 21 named predicates (`native_obligations`, `analyzer_obligations`, `key_obligations` ×2, `hash_coherent` ×2, `search_obligations`, …) stating 9 distinct laws; the leaf `hash_coherent` is `uninterp` and cannot be established. |
| What is trusted? | `TRUST.md` lists 105 items but misses an `external_body` proof axiom, 27 `uninterp` specs, unannotated public exec code, and the helper crates. |
| Which statement is which paper result? | Three conventions (`history_algebra.rs` theorems, `stmt_*`/`theorem_*`, `finite_states.rs`), four functions called `lang`, five overlapping docs with four different count tables. |

The proofs themselves look sound: no `admit`/`assume`, no new trusted items in PR #9, the
`cfg(verus_keep_ghost)` / `cfg(not(verus_keep_ghost))` pairs differ only in ghost arguments, and no
spec mirrors the code it verifies. The problems are in **what the top-level statements say** and in
**how hard it is to see that**.

---

## 2. Target layout

Crate order is `history-syntax → junco-core → history-store → history-semantics → history-analysis`.
Each reviewer file lives in the lowest crate that can state it.

| # | File (new or renamed) | Contents | Replaces |
|---|---|---|---|
| R1 | `history-syntax/src/spec/events.rs` | `Event` spec methods, `arity`, `event_view`, projection laws, a **surjectivity law** (every well-tagged component tuple is the view of an event), `well_tagged`, rule/head/test/regex view types. | `event.rs` spec parts, `verify/dsl.rs` view types |
| R2 | `junco-core/src/spec/semantics.rs` | The single denotational semantics of the paper's Section 3, over **events `E`**: `head_matches`, `test_sem`, `lang`, `rule_violated`, `policy_denies`, `least_violation`. | `junco-core/src/verify/dsl.rs` (semantic part), `semantics.rs` `rule_status`/`rule_denies`/`policy_denies`, `compiled_rule.rs` `least_violation` |
| R3 | `junco-core/src/spec/questions.rs` | The paper's Section 5 questions over events: `Domains`, `in_domains`, `refines`, `covers`, `redundant_in`, `never_denies`, `always_denies`, `tails_included`, `Counterexample` and its instances, `shortest_in_case`. | `refinement/semantics.rs`, the instance/verdict half of `refinement/analyzer.rs` |
| R4 | `junco-core/src/spec/hypotheses.rs` | Every hypothesis and trust token, each documented once: event laws, key laws (one `hash_coherent`), user bundles, library-internal key laws, fresh-value capacity, capacity bounds. | `native_obligations`, `analyzer_obligations`, both `key_obligations`/`hash_coherent`, `search_obligations`, `memo_obligations`, `parts_key_obligations`, `eq_equivalence`, `equality_laws`, `typed_numeric::equivalence`, `infinite_type`, `unrestricted_components_infinite` |
| R5 | `history-semantics/src/spec/monitor.rs` | Public abstract view of `Validator` (`rules: Seq<Rule<E>>`, `history: Seq<E>`), one opaque `wf`, the step relation `check_step`, and the **monitor theorem** (Section 4 below). | `check_result`, `denial_at`, `validator_*` accessors, `trace_decision_result`/`policy_decision_result` semantic clauses |
| R6 | `history-analysis/src/spec/analyzer.rs` | Public abstract view of `PolicyAnalyzer` (`domains`, `rules`), one opaque `wf`, the meaning of each verdict, and the **analyzer theorems** (Section 5 below). | `covered_correct`, `redundant_correct`, `at_least_as_strict_correct`, `tail_included_ok`, `*_minimal`, `constructor_result`, `valid_ids`, `rule_ids`, views |
| P | `history-semantics/src/verify/paper.rs` | One `stmt_*` per paper result, in paper order, each with its paper label in the doc comment and the proving `theorem_*` named. Proofs stay where they are. | the `tab:mechanization` mapping scattered over `history_algebra.rs`, `refinement/*`, `finite_states.rs`, `finite_impl.rs` |
| T | `history-semantics/tests/reviewer.rs`, `history-analysis/tests/reviewer.rs` | Verus **client** proofs that use only the public surface: the monitor trace-safety theorem, the analyzer decision theorem, and non-vacuity witnesses for a concrete event type (e.g. `Component3<u8, u8, u8>` and one `u32` event). | `tests/public_specs.rs` (monitor only, no paper theorems) |

Docs shrink to two: `VERIFY.md` (how to run; reviewer map pointing at R1–R6, P, T; differences
from the paper; hypotheses; trusted base summary) and generated `TRUST.md`. Move `SPEC.md`,
`docs/verification/README.md`, `HANDOFF-inclusion-e2e.md` and `finiteness-*.md` to
`docs/history/` or delete them; they contain `/tmp`/`/home` paths, agent names, "OPEN" statuses,
and four disagreeing count tables.

### Conventions for the surface files

1. Everything a public contract mentions is `pub open spec`, or `pub closed spec` with `pub` lemmas
   that reveal it. No `open(crate)`/`open(super)` in a public `requires`/`ensures`.
2. Each stateful object has **one** abstract view with only semantic fields, and **one** opaque
   `wf`. Plumbing (codebooks, arenas, revisions, ids, ghost resource locations) stays behind `wf`,
   with public preservation lemmas.
3. Contracts state semantic clauses and frame clauses separately (`check_step` vs
   `validator_frame`); messages, revisions and capacity bookkeeping are not in the semantic clause.
4. One definition per concept, one name per definition. No two functions named `lang`,
   `head_matches`, `RegexView`, `TestView`, `EventView` or `Constraint` in different crates.
5. Every surface definition has a doc comment that gives its meaning in one sentence and the paper
   label it corresponds to. No `file.rs:NNN` references in doc comments.
6. Every paper result is a `stmt_*` predicate proved by a `theorem_*`; the matcher theorems in
   `history_algebra.rs` move to this convention.
7. No `Set::new(..).unwrap_or(Set::empty())` in stated definitions; use `ISet` or prove finiteness
   where the set is built.
8. Hypotheses that the user must discharge are separated from hypotheses the library discharges
   about its own internal types.

---

## 3. Fixes to the specifications (do these before or with the layout)

Severity: **HIGH** = a top-level guarantee is vacuous, false for real inputs, or about something
other than the running code; **MED** = weaker than documented; **LOW** = confusing.

### S1 (HIGH). The analyzer's semantics quantify over values that are not events

`covers`, `refines`, `tails_included`, `shortest`, `cex_values_ok` (`refinement/semantics.rs:67-167`)
quantify over `Seq<E::Component>` with `event_in`/`in_domain` checking only length and declared
domains. `E::Component` is a tagged enum with one variant per coordinate, and no clause requires
`coordinate_spec(x[i]) == i`. `choice_ok` (`refinement/analyzer.rs:111`) likewise lets a "fresh"
value at coordinate *i* be a value of another coordinate.

- `Holds ⇒ covers` still implies coverage for real events (the model has more pairs).
- `Counterexample ⇒ ¬covers` can be witnessed only by an ill-tagged pair. Example: event
  (principal, `Action` enum, resource), action coordinate undeclared, rule with an action variable,
  covering policy with one rule per action. Real events are covered; the model has a "fresh action"
  (a principal value in the action slot) and the analyzer reports a counterexample whose proved
  `¬covers` holds only in the model.

**Fix.** State R3 over events: `covers(d, P, r) = ∀ c: E, h: Seq<E>. in_domains(d, c, h) ∧
rule_violated(r, c, h) ⇒ policy_denies(P, c, h)`, reusing the monitor's `rule_violated` (this also
deletes the duplicate `rule_status`/`rule_denies`). Instances of a symbolic counterexample must be
built from well-tagged values (add `tag(f[i](n)) == i` to `choice_ok`) and turned into events by
the surjectivity law in R1. `stmt_genericity` must also preserve tags.

### S2 (HIGH). The infinity hypothesis is about the wrong type and is unprovable

`unrestricted_components_infinite` (`refinement/analyzer.rs:134`) requires
`infinite_type::<E::Component>()` if any coordinate is undeclared.

- `Set` in the pinned vstd is finite-only (`axiom_is_finite`), so `infinite_type::<T>()` is false for
  every fixed-width or finite type, including the tests' `Access` (`u32`, enum, `u32`) and the
  RegExLib benchmark's `Component3<(), u8, ()>`. With an undeclared coordinate, the policy queries'
  precondition then cannot hold and their contracts say nothing.
- `String` cannot be a component (`Component: Copy`), so no shipped component type satisfies it.
- No lemma proves `infinite_type` for any type, not even `nat`.
- When it does hold (e.g. a `&'static str` coordinate), it can hold because of a *different*
  coordinate's variant (S1).

**Fix.** Replace it with a per-coordinate, quantitative hypothesis in R4:
`fresh_capacity(d, known, i, k)`: coordinate *i*'s tagged values outside the known constants
number at least *k*. A counterexample uses finitely many fresh values per coordinate
(`fresh_used`), so the contract becomes
`Counterexample(c) ⇒ (∀i. fresh_capacity(d, known, i, fresh_count(c, i))) ⇒ instance exists ∧ ¬covers`,
and a lemma discharges `fresh_capacity` for `u32`/`u64`/`nat` coordinates when *k* is small.
`Holds ⇒ covers` should need **no** infinity premise: genericity maps any finite-type pair into
the abstract model. Today the premise is a `requires` even for using `Holds`, although `SPEC.md:75`
says `Holds` is sound for every component type.

### S3 (HIGH). `tail_included` counterexamples can be vacuous (still open after PR #10)

`tail_included` (`history-analysis/src/analyzer.rs:~893-905`) ensures only `tail_included_ok`, whose
`Counterexample` arm is `every_instance ∧ shortest` (`refinement/analyzer.rs:~336-348`).
`every_instance` quantifies over admissible instantiations, so it holds when none exist, and
`shortest` is trivially true when the inclusion holds. The contract therefore permits
`Counterexample` for a true inclusion. This is the only analyzer entry point the paper lists
(`appendix.tex`, Table `tab:mechanization-impl`), and the 90 satisfiable RegExLib results are
counterexamples. The policy queries add `cex_has_instance ∧ ¬covers`; `tail_included` does not.

**Fix.** Give `tail_included` the same shape as the policy queries (with S2's hypothesis):
`Counterexample(c) ⇒ instance exists ∧ ¬tails_included`. Also require or ensure
`head_tails_wf(head, left, right)` (scoping; see S12) and ensure that `domains` and `rules` are
unchanged (today a client knows nothing about `final(self)@.domains` or `.rules` after the call).

### S4 (HIGH). The monitor's and analyzer's hypotheses cannot be established

- `native_obligations` (`history-store/src/typed.rs:1135`, `open(super)`) contains
  `key_obligations`, whose `hash_coherent` (`typed/map.rs:22`) is `pub(crate) uninterp`. No lemma or
  axiom ensures it for any type. Every semantic clause of the monitor (`check_result`'s grant and
  deny clauses, `permits`, `ordered_result`, compiled-equals-source) is `native_obligations ==> …`.
- `Component2/3/4` derive `PartialEq` under `external_derive` with no `PartialEqSpecImpl`
  *[inference]*, so `obeys_eq_spec`/`eq_spec` are uninterpreted for every event built on them, and
  the orphan rule prevents users from adding the impl.
- `analyzer_obligations` (`history-analysis/src/verify.rs:2535`, `open(crate)`) uses a **second**
  `hash_coherent` (`native.rs:23`) unrelated to the first, omits `projection_laws` (which
  `native_obligations` includes; `SPEC.md` says they are the same), and adds `search_obligations`,
  `memo_obligations`, `parts_key_obligations`: hash/eq laws about the library's own internal key
  types (`Constraint`, `(RegexId, RegexId)`, `SmallVec<[RegexId; 4]>`), which no user can name.

**Fix (R4).** One `hash_coherent<K>` (`uninterp`, documented as "the `external_body` hash-map
contracts are faithful for `K`"), one `eq_equivalence<T>`, one `key_laws<K>`. User bundle
`event_obligations<E>() = event_laws<E> ∧ key_laws<E::Component>`, used by both monitor and
analyzer. Library-internal key laws become **trusted axioms per internal type** (listed in
`TRUST.md`) rather than preconditions. Add `PartialEqSpecImpl` for `ComponentN`. Add a reviewer
test (T) that proves `event_obligations` for a concrete event type from those axioms, so the
hypothesis is shown satisfiable.

### S5 (MED). `Exhausted` carries no claim and is produced by more than the budget

All verdict predicates have `Exhausted => true`; the analyzer maps every
`HistoryError::GraphLimit` to `Ok(Exhausted)` (`history-analysis/src/analyzer.rs:~1093, ~1119`).
`GraphLimit` specs give only `Err ⇒ GraphLimit` (`history-store/src/graph.rs:1571-1586`), never
"budget exceeded", and `GraphLimit` is also returned for index and Cartesian-product overflow via
`graph_index_overflow()` with `limit: MAX_GRAPH_BYTES` (100 KiB, not the analyzer's 16 MiB):
`junco-core/src/error.rs:109`, `kernel.rs:111`, `flat.rs:560,607`, `constraint.rs:1130,1365,1466,1507`,
`tables.rs:335,346`. An analyzer that always returned `Exhausted` would verify.

**Fix.** Split the error (`GraphBudget` vs `IndexOverflow`), have `charge`/`projected` ensure
`Err(GraphBudget) ⇒ charged + bytes > budget`, and state in R6
`Exhausted ⇒ some search's graph charge exceeded GRAPH_BYTES`. If that is too costly, rename the
variant `Unknown` and document every source; then the paper must not attribute it to the budget.
Also document that the policy queries stop at the first non-`Holds` case, so an `Exhausted` case
hides a later refutation.

### S6 (MED). The analyzer API cannot be used by a verified client

`new` requires `domains_wf` and `constructor_capacity` (`closed`) and ensures `constructor_result`
(`closed`, revealing lemma `pub(crate)`); `Domains::infinite`/`with_domain` are unverified and
unspecified (`analyzer.rs:~103-140`); `analyzer_state_wf`, `add_rule_capacity`, `query_capacity`,
`valid_ids`, `domains_wf` and every `View` are `open(crate)`. No Verus client can establish the
preconditions of `new`, `add_rule`, `covered` or `tail_included`, or chain two `add_rule` calls.
`self@.domains` is rebuilt from interned ids; its relation to the caller's `Domains` is hidden in
`constructor_result`.

**Fix (R6).** Public view `{domains, rules}`; `new` ensures `self@.domains == d@`, `self@.rules == []`
and `self.wf()`; `Domains` constructors get `#[verus_verify]` and postconditions; capacities are
stated over the public view with a public growth lemma. Prove the T client.

### S7 (MED). Redundancy is checked as coverage of an id-filtered list

`redundant_correct = covered_correct(without_rule(policy, rule))` (`refinement/analyzer.rs:~231`).
`stmt_redundant_iff_covered` is about `others.push(rule)`, and nothing composes the two. The query
does not require `rule ∈ policy`; if absent, `Holds` means "adding the rule changes nothing". A
second copy of the same rule under another id makes each copy redundant (multiset semantics).

**Status: largely addressed by PR #10** (`policy_removal.rs`). `redundant` there additionally
ensures `redundant_decisions_ok`: `Holds` ⇒ removing every occurrence of the target id preserves
every decision; a counterexample ⇒ removal changes a decision when the target occurs; arbitrary
order and duplicate ids are handled. An absent target keeps the coverage meaning (no
`contains` precondition). R6 restates this; document the id/multiset reading.

### S8 (MED). Minimality is not ensured by the policy queries (handled by PR #10)

At `1efa267` no entry point ensures `*_minimal`; `covered_minimal`, `redundant_minimal`,
`at_least_as_strict_minimal` and the `*_ok` conjunctions are unused. Those predicates specify
minimality per split case (`shortest_in_case`), because `covered_with` returns the first refuted
case. `tail_included` claims global `shortest`, which is right for a single search but
meaningless while S3 stands.

**Status.** PR #10 (`proof/policy-analyzer-minimality`, open) makes `covered`, `redundant` and
`at_least_as_strict` ensure `*_ok`, i.e. `*_correct` plus minimality **within the returned
candidate's case/constant profile** (`shortest_in_case`), not across cases and not per rule: its
own smoke run returns a two-event counterexample in one case while another case has a one-event
one. It is out of scope for this plan: do not edit the minimality predicates or their proofs.
R6 restates the `*_ok` clauses without weakening them, and the paper must say "shortest within its
split case".

### S9 (MED). Declared finite domains are an unchecked assumption about runtime inputs

`refines`, `covers`, `tails_included` quantify over pairs inside the declared domains. The monitor
never checks domains (`check_result`, `rule_violated`). A `Holds` under a declared domain says
nothing about runtime events outside it. An **empty** declared domain (`with_domain(c, [])`,
allowed by `domains_wf`) makes every query return `Holds` vacuously.

**Fix.** Reject empty domains in `domains_wf` and at runtime. State in R3/R6 and in the paper that
analyzer verdicts transfer to the monitor only for histories and candidates inside the declared
domains; optionally prove that bridge as a reviewer theorem.

### S10 (MED). Vacuity has no executable entry point and no linking theorem (still open after PR #10)

`never_denies`/`always_denies` (typed) are not linked to `stmt_vacuity_reductions` (numeric,
constrained form) or to `tail_included`. `never_fires_ok`/`always_fires_ok` are dead, and the
`refinement/analyzer.rs` header (`:10-29`) documents `never_fires`/`always_fires` contracts that
do not exist (and uses `v.inclusion@` where the code uses `v@`).

**Fix.** Either add `never_fires`/`always_fires` entry points with contracts in R6, or prove in R3
`never_denies(d, r) ⇔ refines(d, [], [r])` and `always_denies(d, r) ⇔ refines(d, [r], [forbid h Univ])`
and route both through `at_least_as_strict`. Delete the dead predicates and fix the header.

### S11 (MED). `RuleId` and `BatchCursor` are not tied to their owner

`RuleId` is a bare `Copy` index (`valid_ids` accepts ids from another analyzer; the body indexes
`self.rules[id.0]`). `RuleRuntime::resume_cursor`/`advance_cursor` are `pub`, require ghost
compatibility conditions, and `BatchCursor` does not record its runtime. Unverified callers get
panics or answers about a different rule or history.

**Fix.** Tag ids and cursors with an owner id checked at runtime (error on mismatch), or make the
cursor API `pub(crate)`.

### S12 (LOW). DSL edge cases are silent

An unscoped variable or out-of-range coordinate makes both `Eq` and `Neq` false
(`dsl.rs:50-121`), unlike the paper (`bg.tex`, duality of tests) and unlike the numeric layer
(`kernel.rs:1398-1410`). A head of the wrong arity never fires. `add_rule` contracts do not promise
that such rules are rejected (`HeadArity`, `ComponentCoordinate` may be returned for well-formed
rules without a stated cause; `flatten.rs:111-112` proves more than is propagated).

**Fix.** Make `rule_wf` (scoping + arity) part of every rule in the view, ensured by `add_rule`, and
propagate "well-formed ⇒ no `HeadArity`/`ComponentCoordinate`". Document the named-variable
encoding as a difference from the paper.

### S13 (LOW). Smaller contract gaps

- `TraceRule::clone` (`policy/trace.rs:~305`) ensures only the diagnostic id, not
  `trace_rule_source(result) == trace_rule_source(*self)`.
- `forbid`, `principal_is`, `resource_is` (`policy/rule.rs:104-110`, `policy/atoms.rs:65-80`) hard-code
  arity 3 without `requires arity::<E>() == 3`.
- `no_internal_error` excludes only `HistoryError::Invariant`; name it `no_invariant_failure` and
  list the remaining causes per entry point.
- `permits` ensures `no_internal_error` unconditionally while `check`/`finish`/`add_rule` need
  `native_obligations`; document why or align.
- `stmt_search_correct` carries `n_unrestricted(d)`, which its proof does not use.

---

## 4. Monitor theorem (to be stated in R5 and proved in T)

Fix an event type `E` with arity `k` and projection `π = event_view`. Assume
`event_obligations<E>()` (R4). For a rule `r = (m, η, τ)`, candidate `e`, committed history `h ∈ E*`,
`viol(r, e, h)` is `rule_violated` (R2).

Let `R = [r₀ … r_{n−1}]` be the rules passed to `add_rule`, in order. After `finish()` the history
is empty. Every `check(e, μ)` returns exactly one of:

1. `Grant(e, μ)`, with `h' = h · e` and `∀ i < n. ¬viol(rᵢ, e, h)`;
2. `Denied(d)`, with `h' = h`, `d.event = e`, `d.mode = r_j.m` where `j = min{ i | viol(rᵢ, e, h) }`;
3. `Err(x)`, with `h' = h` and `x` not an invariant failure.

`permits(e)` returns `Ok(b)` only if `b ⇔ ∀ i. ¬viol(rᵢ, e, h)`, and leaves `h` unchanged.
`rollback(cp)` only truncates to an owned checkpoint's prefix.

**Corollary (trace safety).** On every reachable state, `∀ j < |h|. ∀ i. ¬viol(rᵢ, h_j, h_{<j})`.
This is not stated anywhere today.

Definitions needed: R1 (`event_view`, laws), R2 (`head_matches`, `lang`, `rule_violated`,
`least_violation`), R4 (`event_obligations`), and the R5 view `{rules, history}`. Nothing else.

`TracePolicy`/`CompiledPolicy` restate the same theorem with an inlined `least_violation`; have
them use R5's predicates.

---

## 5. Analyzer theorems (to be stated in R6 and proved in T)

Notation: `D` the declared domains (undeclared coordinate = all tagged values of that
coordinate); `E_D`, `H_D` events and histories in `D`; `viol` from R2.
`Cov_D(P, r) ⇔ ∀ c ∈ E_D, h ∈ H_D. viol(r, c, h) ⇒ ∃ r' ∈ P. viol(r', c, h)`.

- **A1 (decision).** If `covered(r, P)` returns `Ok(v)` with `v ≠ Exhausted`, then
  `v = Holds ⇔ Cov_D(P, r)`. The `⇒` direction needs no infinity hypothesis; the `⇐` direction
  needs S2's fresh-value capacity for the returned counterexample.
- **A2 (real counterexamples).** If `v = Counterexample(x)`, an instantiation exists, and every
  instantiation is a pair of real events `(c, h) ∈ E_D × H_D` with `viol(r, c, h)` and no rule of `P`
  violated.
- **A3 (refinement, redundancy).** `at_least_as_strict(P, Q)`: `Holds ⇔ ∀ (c, h) ∈ E_D × H_D.
  permits(P) ⇒ permits(Q)`; a counterexample is a real pair denied by some `q ∈ Q` and by no rule
  of `P`. `redundant(r, P)` with `r ∈ P`: `Holds ⇔` removing `r` changes no decision on `E_D × H_D`.
- **A4 (tail inclusion).** `tail_included(η, ℓ, ρ)`: `Holds ⇔ ∀ (c, h)` real with `η` matching `c`,
  `h ∈ L(ℓ) ⇒ h ∈ L(ρ)`; a counterexample is real and of minimum `|h|`.
- **A5 (escapes).** `Exhausted ⇒` a search exceeded `GRAPH_BYTES` (S5). `Err` is never an
  invariant failure. Every call terminates.
- **A6 (minimality, from PR #10).** A policy-query counterexample is shortest among candidates in
  its returned split case (constant profile); restate PR #10's `*_ok` clauses exactly.
- **Non-vacuity (T).** For one concrete event type: the hypotheses hold; `new`, two `add_rule`s and
  each query are callable; one query is shown to return each of `Holds` and `Counterexample`
  *(as a test, not a proof)*.

---

## 6. Code that runs but is not what was verified

### D1 (MED). The AgentDojo evaluation goes through unverified glue

The paper states the monitor guarantee for `Validator::check`. AgentDojo calls `FlowPolicy::check`
= `RulePolicy::check` (`src/policy/rules.rs:110-163`, root crate, in no verify configuration). It
pre-filters rules with the unverified `could_fire`, builds a `TracePolicy` per distinct event,
decides and appends in two steps, appends **denied** events in audit mode, and turns compile and
history errors into synthetic denials. `events.rs:142-145` pushes non-`Contact` events without a
check.

**Fix.** Route the evaluation through `Validator::check`, or state the guarantee for
`TracePolicy::decide` and list `RulePolicy` as unverified glue in the paper and `TRUST.md`.

### D2 (MED). Benchmarks build with `test-util`, which no verify configuration covers

Root and `fuzz` `[dev-dependencies]` enable `history-semantics/test-util`, which turns on extra
`?` returns and counters inside the verified `fold` loop (`progress.rs:257-268`), a guard toggle
(`:285-288`), an injected time-limit path (`:173-181`), and fault injection in reservation leaves
(`observation.rs:9-49`, `typed/map.rs:58-60`). It also exposes setters that overwrite the graph
byte charge from unverified code (`runtime.rs:857-863`, `compiled_rule.rs:660-666`).

**Fix.** Build benchmarks without `test-util` (move probes into a bench-only crate), or add a
`test-util` configuration to `scripts/verify-all.sh`.

### D3 (MED). The trusted base is under-reported

- `singleton_invariants` (`history-store/src/store.rs:1285`) is an `external_body` **proof** fn, i.e. an
  axiom; `trust-scan.sh` counts it as an ordinary wrapper, and the paper's "no assume or admit"
  hides it. It is redundant and can be eliminated: `HistoryStore::new` already ensures
  `singleton_valid`, and its callers already require `numeric_store_wf`, which only `new`
  establishes; folding `singleton_valid` into `numeric_store_wf` removes the need for it.
- 27 `uninterp` specs are not listed; four carry meaning (`hash_coherent` ×2,
  `snapshot_published`, `diagnostic_output`).
- `obeys_eq_spec`/`obeys_cmp_spec = true` on `external_derive` types (`RegexId`, `TestId`,
  `TransitionId`, `kernel.rs:66-68, 959-964`) are unchecked *[inference]*.
- Unannotated public exec code is unverified and not listed (`impl Domains`, `test-util` mutators,
  `Debug`/`PartialEq` impls).
- `verus-bumpalo` and `hashconsius` are not scanned, yet the normalizer's hash-consing and arenas
  use them; the search's successor path also uses the trusted LRU cache
  (`history-store/src/cache.rs:69-110`), contradicting "the search's only trusted leaves are
  hash-map and hash-set adapters".
- Mutex wrappers assume their lock invariant on every acquire while running user `Hash`/`Eq`;
  a panic mid-update followed by a caught unwind re-enters with a broken invariant *[inference]*.

**Fix.** Extend `trust-scan.sh` with sections for proof axioms, `uninterp` specs, `external_derive`
spec claims, unannotated public exec items, and the helper crates; document panicking user
`Hash`/`Eq` as out of scope or poison the store.

### D4 (MED). Event types used in the evaluation have hand-written projections

`src/model.rs:67-90`, `flow/mod.rs:87-115`, `agent/mod.rs:120-142` implement `Event` by hand without
`EventSpecImpl`; every guarantee for them rests on unverified `component`/`coordinate`. The paper
lists only "equality and hashing laws". **Fix.** Derive these events from the verified tuple/
coproduct impls, or list projection laws as a hypothesis.

---

## 7. Paper ↔ mechanization

| Paper item | Mechanization | Action |
|---|---|---|
| Section 3 definitions (events, tests, `L_θ`, rules, policy violation) | Same as `junco_core::verify::dsl` on scoped rules; differences: one tagged component type (S1), named scoped variables (S12), equality up to `eq_spec`, arity 1–8. History order and concatenation match. | Map `L_θ` to the typed `lang` (R2), list `n_lang` as its encoding. Add the four differences to `app:mech-diff`. |
| `def:policy-refinement`, `⊑` | `refines`; same direction. | Consider a different symbol for policies: `⊑` is language inclusion for expressions but "at least as strict" for policies, so Prop `prop:policy` reads backwards. |
| Prop `prop:policy` (`Den(P)`, `φ_h ∧ π = x`, appended candidate) | **Not mechanized.** No `Den` or appended-candidate encoding exists. `stmt_refines_iff_covers` + `stmt_policy_reduction` prove a different characterization. | Mark it "not mechanized" in `tab:mechanization` (today † "equivalent" overclaims), or define `den` and prove it in Verus. |
| Per-rule decomposition into split cases (`Γ_R`, split on head constants of `P`, firing rules) and constrained inclusion `r ⊑_Γ s` | Mechanized (`split_ok`, `head_pairs`, `firing_denials`, `stmt_policy_reduction`, `stmt_policy_search_composition`) and executed (`covered_with`); exact firing test proved (`lemma_head_firing_exact`). | **State it in Section 5**: define constrained inclusion, state the split-case reduction as the decision procedure, explain why the firing test is exact. Today it appears only in `app:mech-diff` and `implementation.tex`, which cites Section 5 for material Section 5 lacks. |
| "The analyzer executes the inclusion query, not the reductions" (`implementation.tex`, `appendix.tex`), `\todo{If proof of policy inclusion works, fix}`, Table `tab:mechanization-impl` listing only `tail_included`, "the executed search starts from a head constraint with only equalities" | False at PR #9. | Describe `covered`, `redundant`, `at_least_as_strict`, their contracts and hypotheses; drop the sentence and the todo. |
| Vacuity formulas (`r·lift(φ_h ∧ π = x) ⊑ Emp`, …) | `stmt_vacuity_reductions`: constrained form, both modes, no appended event. | Mark † and describe the constrained form; see S10. |
| Redundancy `P∖{R} ⊑ {R}` | Same at policy level; executable meaning weaker (S7). | Note multiset/id reading. |
| "Each counterexample shortest for its own inclusion" (`inclusion.tex`) | PR #10 proves minimality only within the returned split case, not per rule or globally (S8). | Say "shortest within its split case". |
| `fig:simulation`, `lem:simulation` ("memoized recursion decides ≤") | Code's relation is **smaller**: lifted-test `SumL`/`AndR` apply only when both sides are tests (`history-analysis/src/simulation.rs` `derive`). Example: `⟨φ₁∨φ₂⟩ ≤ ⟨φ₁⟩·Univ + ⟨φ₂⟩·Univ` is derivable in the Figure, rejected by the code *[inference]*. Soundness proved; "decides" is not. | Restrict the Figure's lifted-test rules or add the case to `derive`/`sim_step`; say "sound and terminating". Fix `app:mech-diff` ("relaxed side conditions") and `VERIFY.md` difference 4 ("more rules"), both wrong. |
| `alg:succ`, `lem:succ`, `lem:uniform` | `stmt_successor_cases` over a semantic case family (adds a partition property); the executable is proved against it by `lemma_emitted_steps`; `alg:succ` itself is not mechanized. | Keep †. `VERIFY.md` should cite `lemma_emitted_steps`, not the unused `expansion_ok` (delete it). |
| `def:pruning` domination | Executable lookup is a sound subset (subsets enumerated only for `|P| ≤ 4`). | One sentence in `app:pruning`. |
| `lem:finite-states` | Stated for any `Model` meeting the (N)/(S) contract, instantiated only for the implemented normalizer. The paper's `app:finiteness` describes the conditions in prose and calls `C(q)` `Bound(q)`. | Add †; give the conditions descriptive names in code. |
| `thm:search` | Starts from any satisfiable `Γ₀`; symbolic counterexample; `Exhausted`; termination conditional on `finitely_many_items`, discharged for the code. | Documented; drop the unused `n_unrestricted` hypothesis. |
| `thm:sderiv` / `thm:matcher` | `theorem_matcher_correct` states `thm:sderiv`; `thm:matcher` is `theorem_rule_decision`, over numeric `pair_lang`. | Rename `theorem_matcher_correct` → `theorem_symbolic_run_correct`; link the typed monitor to it in P. |
| Abstract/intro: "sound and complete", "decides refinement, redundancy, and vacuity", "reduces … to one query" | Executable is sound, and complete modulo `Exhausted` and resource errors; one query per covered rule per split case; vacuity not executable. | Reword accordingly. |
| "Other differences": three components; 32-bit candidate values in the analyzer | Arity 1–8; candidates bounded by `u64`; 32 bits bound constant ids. | Rewrite. |
| Hypotheses: "equality and hashing laws" | Also projection laws and arity; hashing law is an uninterpreted token (S4). | List all, call the hash law a trusted assumption. |
| Trusted base: "71 external_body + 20 assume_specification", "no assume or admit", "only trusted leaves of the search are hash adapters" | See D3. | Update after the extended trust scan. |
| Verified-function counts (247/285/1580/483) | `VERIFY.md` at PR #9: 164·248 / 287 / 1609·1614 / 563, plus `public_specs` 21. | Regenerate from `verify-all.sh`, cite configurations. |
| RegExLib evaluation | Uses declared finite domains (`benches/smt/main.rs:33-35`), covered by `*_finite_domains` statements, not the paper's theorem; relies on `tail_included` (S3). | Say so in the evaluation. |
| Monitor evaluation (AgentDojo) | Runs unverified `RulePolicy` (D1), built with `test-util` (D2). | Say which API each experiment uses. |
| Require rules | Paper treats forbid only; mechanization handles require via `denial = ¬tail`. | Note as a strength in `app:mech-diff`. |
| Labels | `def:status` (cited by `semantics.rs`, `VERIFY.md`) does not exist; `ex:policy-inclusion` is referenced but undefined; `sec:refinement`, "Proposition Policy reduction", `app:antichains` are stale in code comments. | Fix references both sides. |

---

## 8. Documentation and naming cleanup

- Delete or archive: `SPEC.md`, `docs/verification/README.md`, `HANDOFF-inclusion-e2e.md`,
  `finiteness-notes.md`, `finiteness-fix-evidence.md`.
- `VERIFY.md` keeps: commands, one count table, the reviewer map (R1–R6, P, T), hypotheses (pointing
  at R4), differences, trusted-base summary (pointing at `TRUST.md`).
- Remove hard-coded line references from doc comments (dozens have drifted, e.g. `encoding.rs:4`,
  `implementation.rs:84-136`, `search.rs:59`) and regenerate README anchors (`pair_lang`, `lang`,
  `public_compiled_decision`, `retained_history_lifecycle` all point at wrong lines).
- Dead specs: `never_fires_ok`, `always_fires_ok`, `denies_fn`, `grants_matching`, `expansion_ok`,
  `head_tails_wf` (unless S3 uses it). Leave `*_minimal`/`*_ok` to PR #10.
- Near-duplicate `*_finite_domains` statements: factor the shared body.
- Names: one `lang` on the surface (others `flat_lang`, `numeric_lang`, `kernel_lang`);
  `check_result` → `check_step`; `raw_events` → `events`; `history_specs.rs` → split into the
  numeric regex algebra and the error predicates; `Constraint` spec alias vs exec struct; imports
  `refinement::analyzer as verdict` / `search as paper` clash with local modules.
- `public_compiled_decision` (cited by the paper as the one-rule matcher guarantee) is a
  `pub(crate)` harness nothing calls; cite `CompiledRule::accepts_history` or `Validator::permits`.

---

## 9. Suggested order

1. **R4 + S4**: consolidate hypotheses and make them dischargeable for one concrete type (T
   witness). Every later statement depends on them.
2. **R1–R3 + S1 + S2 + S12**: one typed semantics over events, per-coordinate fresh capacity.
   Re-prove `stmt_genericity` with tags, then the bridge lemmas in `history-analysis/src/verify/policy_bridge.rs`.
3. **R6 + S3, S5–S7, S9–S11**: analyzer surface and contracts; then the T analyzer theorems.
4. **R5**: monitor surface and trace-safety corollary; point `TracePolicy`/`CompiledPolicy` at it.
5. **P**: paper index; rename and convert `history_algebra.rs` theorems.
6. **D1–D4**: evaluation path, feature set, trust scan.
7. **Docs and paper**: Sections 7 and 8.

Each step should end with `scripts/verify-all.sh` at zero errors and a `TRUST.md` diff that
contains only the items this plan names.
