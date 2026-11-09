# Specification of policy-refinement analysis (draft for freeze)

Status: **all 23 frozen statement proofs complete; SymbolicLanguage contracts verified;
analyzer port and executable implementation link in progress.** The only new trusted leaves
are the approved native hashbrown wrappers described in §11.
Spec module: `crates/history-semantics/src/verify/refinement/` (registered in `verify/mod.rs`;
compiled only under `verus_keep_ghost` + `runtime`, like the rest of `verify`). Every theorem is a
`stmt_*` spec function returning the proposition, with a public
`proof fn theorem_* … ensures stmt_*()` verified against it. No `admit`, `assume`, or
`external_body` occurs in the refinement module.

Repository: `/home/zak/junco-policy-inclusion` (uncommitted). Paper: `/home/zak/paper/pldi2027`.
File references below: `bg` = `bg.tex`, `inc` = `inclusion.tex`, `rx` = `regex.tex`, `app` = `appendix.tex`.

---------------------------------------------------------------------------------------------------

## 0. The top-level statement

For every query of `PolicyAnalyzer<E>` (`crates/history-analysis/src/analyzer.rs`), a returned
`Ok(verdict)` satisfies the query's predicate in `refinement/analyzer.rs`, read against the typed
semantics of `refinement/semantics.rs`:

| query | `Holds` means | `Counterexample(cex)` means | `Exhausted` |
|---|---|---|---|
| `at_least_as_strict(P, Q)` | `refines(D, P, Q)`: every pair permitted by P is permitted by Q (inc:7-14) | for every admissible instantiation of its fresh values: P permits it and some rule R of Q denies it; no shorter such pair for R among candidates with the same constant profile | no claim |
| `covered(R, by)` | `covers(D, by, R)` (app:447) | R denies, no rule of `by` denies; shortest in its candidate case | no claim |
| `redundant(R, P)` | `covers(D, P∖{R}, R)` (app:452) | as `covered` | no claim |
| `never_fires(R)` | `never_denies(D, R)` (app:454) | R denies it; globally shortest | no claim |
| `always_fires(R)` | `always_denies(D, R)` | R matches the candidate and grants; globally shortest | no claim |
| `tail_included(h, l, r)` | `tails_included(D, h, l, r)` | matches `h`, history in `l` not `r`; globally shortest | no claim |

Only `tail_included` exists on this branch; all other query rows and `add_rule` are spec-only
until those queries return to `main`.

`Err(_)` carries no claim. Planned exec postconditions (once `history-analysis` is put under
Verus; see Q1):

```rust
pub fn at_least_as_strict(&self, stricter: &[RuleId], than: &[RuleId]) -> (r: Result<Verdict<E>, HistoryError>)
    requires analyzer_wf(self@),
    ensures r matches Ok(v) ==> at_least_as_strict_ok(self@, ids(stricter@), ids(than@), v.inclusion@);
// likewise covered_ok, redundant_ok, never_fires_ok, always_fires_ok, tail_included_ok (final(self)@),
// add_rule: Ok(id) ==> final(self)@.rules == old(self)@.rules.push(rule@) && rule_wf(rule@)
```

Key definitions (`refinement/analyzer.rs`):

```rust
pub enum InclusionView<P, A, R> { Holds, Counterexample(CexView<P, A, R>), Exhausted }
pub struct AnalyzerView<P, A, R> { domains: DomainsView<P,A,R>, rules: Seq<RuleView<P,A,R>>,
    known_principals: Set<P>, known_actions: Set<A>, known_resources: Set<R> }
pub open spec fn admissible(a, cex, f: FreshChoice<P,A,R>) -> bool   // fresh numbers ↦ distinct values, ≠ known constants, in domain
pub open spec fn every_instance(a, cex, fails) -> bool                // every admissible instantiation fails
pub open spec fn shortest(a, n, fails) / shortest_in_case(a, c, n, fails) -> bool
pub open spec fn at_least_as_strict_ok(a, p: Seq<nat>, q: Seq<nat>, v) -> bool   // and covered_ok, …
pub open spec fn stmt_choice_exists<P, A, R>() -> bool   // infinite types ⇒ an admissible choice exists
```

Design decisions in the top layer:
- **Counterexamples are symbolic** (`Value::Fresh(n)`), so their meaning quantifies over
  instantiations: *every* admissible choice of distinct values outside the known constants yields
  a failing pair. With infinite component types a choice exists (`stmt_choice_exists`); for a
  finite type (e.g. `u32`) with too few spare values the claim is vacuous, not false.
- **`Holds` is sound for every component type**, not only infinite ones, by genericity
  (`semantics::stmt_genericity`, `encoding::stmt_numeric_genericity`): a pair over any type maps
  injectively into the numeric model fixing the constants.
- **Minimality** is per inclusion query, as the paper says (inc:97-100). For `covered` /
  `redundant` / `at_least_as_strict` the search runs per candidate case, so the claim is: no
  shorter failing pair *for the same rule R* among candidates that agree with the returned
  candidate on equality with every known constant (`same_profile`, a refinement of every case
  partition the analyzer uses). For the single-search queries it is global.
- **Exhaustion is explicit**: `Exhausted` (max_items, or `GraphLimit` from compile or search) and
  `Err` never claim anything.
- **Termination**: every query returns — the graph budget bounds the states a search can create,
  so termination of the Rust loops does not depend on Lemma 4.2. *Not being `Exhausted`* for
  large enough limits needs finitely many reachable items (`search::stmt_search_terminates`),
  which is **open for the implementation** (§5).
- **Declared finite domains** (`Domains::with_*`): `DomainsView` carries them, and every
  predicate quantifies over the declared values. The paper's theorems cover only infinite domains
  (bg:14-18); the finite-domain variants are separate statements (`*_finite_domains`) and an
  extension the paper does not claim (Q3).

---------------------------------------------------------------------------------------------------

## 1. Layer 0 — semantics (`refinement/semantics.rs`)

Reuses the verified typed DSL semantics `junco_core::verify::dsl` (`head_matches`, `lang`,
`test_sem`; valuation = the candidate, history oldest-first without the candidate) and the
syntax views `history_syntax::verify::dsl::{RuleView, HeadView, RegexView}`.

```rust
pub enum Status { NotFired, Satisfied, Violated }                         // bg:113-121
pub open spec fn violated_by(mode: RuleMode, inside: bool) -> bool
pub open spec fn rule_status(rule: RuleView<P,A,R>, candidate: TEvent<P,A,R>, history: Seq<TEvent<P,A,R>>) -> Status
pub open spec fn rule_denies(rule, candidate, history) -> bool            // status is Violated
pub open spec fn policy_denies(policy: Seq<RuleView<P,A,R>>, c, h) -> bool  // bg:123-126 (some rule violated)
pub open spec fn policy_permits(policy, c, h) -> bool
pub struct DomainsView<P,A,R> { principal: Option<Set<P>>, action: Option<Set<A>>, resource: Option<Set<R>> }
pub open spec fn infinite_type<T: PartialEq>() -> bool;  infinite_domains(d) -> bool   // bg:14
pub open spec fn rule_wf(rule) -> bool                                    // head_scoped ∧ regex_scoped (bg:111, bg:28)
pub open spec fn refines(d, p, q) / covers(d, p, rule) / never_denies(d, rule)
    / always_denies(d, rule) / tails_included(d, head, left, right) -> bool
// statements
pub open spec fn stmt_refines_iff_covers<P,A,R>() -> bool                // app:450
pub open spec fn stmt_redundant_iff_covered<P,A,R>() -> bool             // app:452-453
pub open spec fn stmt_genericity<P,A,R>() -> bool                        // renaming invariance (new; not in the paper)
```

`theorem_rule_decision` (`verify/history_algebra.rs:169`) is over the *numeric* paper-shaped model
(`history_specs::{Head, SrcTest, pair_lang}`) and is not linked to the typed DSL or to the compiled
template (SemanticsSurvey §2). The top layer therefore uses the typed DSL semantics, which is the
one `compiled_rule::dsl_result` refers to, and states its own `rule_status`; the mode was never
specified in Verus before (it is applied natively in `validator.rs:146-149`, `policy/evaluate.rs:107-110`).

## 2. Layer 1 — encoding (`refinement/encoding.rs`)

The analyzer interns typed constants as numeric codes (`ConstId`, from 0) and searches numeric
expressions over `nat` components with kernel tests (`junco_core::kernel::verify::{Test, gsem}`).
A numeric valuation is the **whole** encoded candidate (`Subst` with all three components), not
the runtime's head bindings (0 at unbound components).

**Reuse (revised).** The typed-to-numeric bridge is the existing verified front end, which the
analyzer already calls (`add_rule`, `analyzer.rs:301-312`): `flatten_rule`
(`junco_core::verify::flatten`: `flattened`, `flattening_preserves_semantics`, `flattening_client`),
`lower_flat` with the analyzer's `Constants: FlatEncoder` (`junco_core::verify::encoding`:
`Codebook`, `maps_wf`, `lowering`, `event_encoded`, `word_encoded`,
`lemma_dsl_later_maps_preservation`), and the graph compiler (`crate::compile`:
`lemma_flat_head`, `lemma_flat_regex`, `compile`'s `regex_lang(root) == source_regex(…)`).
An earlier draft of this layer redefined its own coding (`Coding`, `encode_*`, `coding_ok`,
`stmt_encode_denies`, `stmt_encode_lang`); those are removed.

```rust
pub open spec fn n_lang(theta: Subst, r: Regex<model::Test>, w: Seq<EventView>) -> bool  // lang(gsem(θ), r, w)
pub struct NHead { principal: Option<nat>, action: Option<nat>, resource: Option<nat> }
pub struct NRule { mode: RuleMode, head: NHead, tail: Regex<model::Test> }
pub open spec fn n_rule_denies(rule: NRule, theta, w) -> bool;  n_policy_denies(p, theta, w) -> bool
pub struct NDomains { principal: Option<Set<nat>>, action: …, resource: … }
pub open spec fn n_theta_ok(d, theta) -> bool      // event_wf(θ) (u64) ∧ in domain; history events are unbounded nat
// link to the verified front end
pub open spec fn rule_view<E: Event>(rule: Rule<E>) -> RuleView<…>
pub open spec fn front_end_ok<E: Event>(rule, flat, template: FlatPair<u64>, maps, domain) -> bool
    // fl::flattened ∧ enc::lowering ∧ enc::constants_in_domain
pub open spec fn represents(n: NRule, mode, template) -> bool   // same mode/head codes; n_lang == source_regex
pub open spec fn stmt_source_regex_local() -> bool   // NEW: source_regex reads θ only at bound components
pub open spec fn stmt_front_end_denies<E: Event>() -> bool
    // typed rule_denies == n_rule_denies; proof = composition of the existing lemmas above
    //   + stmt_source_regex_local; conditional on maps_wf and the pair being encoded
pub open spec fn stmt_numeric_genericity() -> bool     // injective renaming fixing the rule's codes preserves denial
```

New obligations in this layer: `stmt_source_regex_local` (moves the runtime's head-binding results
to the analyzer's whole-candidate valuation), `n_rule_denies` (the mode), and
`stmt_numeric_genericity` (fresh values). The rest is composition of proved lemmas. Tails
(`tail_included`) are the `Forbid` case. The remaining native obligation is that the analyzer's
`Constants` satisfies the `FlatEncoder` contract (`obeys_encoding_spec`, `maps_wf`); it currently
cannot, because it issues code 0 (Q9).


## 3. Layer 2 — constraints and constrained inclusion (`refinement/inclusion.rs`)

```rust
pub struct Literal { component: Component, value: nat, equal: bool }     // x_c = v / x_c ≠ v (inc:44-45)
pub type Constraint = Set<Literal>;
pub open spec fn sat_by(theta, g) / satisfiable(d, g) / entails(d, g1, g2) / decides(d, g, c, v) -> bool  // inc:46-52
pub type Pairs = Set<(Component, nat)>;
pub open spec fn split_ok(d, g, pi: Pairs, cases: Set<Constraint>) -> bool   // what Split guarantees (inc:53-58)
pub open spec fn paper_split(d, g, pi) -> Set<Constraint>;  stmt_paper_split_ok() -> bool
pub open spec fn included_under(d, g, r, s) -> bool                           // r ⊑_Γ s (inc:60-65, Def 5.1)
pub open spec fn inclusion_cex(d, g, r, s, theta, w) -> bool;  no_cex_shorter(d, g, r, s, n) -> bool
pub open spec fn head_constraint(h: NHead) -> Constraint                      // Γ_R (inc:79)
pub open spec fn denial(rule: NRule) -> Regex<model::Test>                     // ρ_R (inc:80)
pub open spec fn head_pairs(p: Seq<NRule>) -> Pairs                            // Π (app:462)
pub open spec fn firing_denials(d, p, g1) -> Regex<model::Test>               // Σ_{Γ'⊨Γ_R'} ρ_R'
pub open spec fn n_covers(d, p, rule) -> bool
pub open spec fn stmt_policy_reduction() -> bool                               // Prop B.1 (app:461-481), eq:policy-reduction (inc:87-92)
pub open spec fn stmt_vacuity_reductions() -> bool                             // never/always fires (app:454)
```

`stmt_policy_reduction` is stated for **any** case family with `split_ok`, so it applies to the
code's `split` (≤ n+1 options per register, `constraint.rs:236-281`) as well as the paper's.

## 4. Layer 3 — search (`refinement/search.rs`)

```rust
pub struct Item { constraint: Constraint, state: Regex<model::Test> }        // (Γ, q) (inc:153)
pub open spec fn witness(d, item, theta, w) -> bool                           // W(I) (inc:156-159)
pub type Assignment = Map<model::Primitive, bool>;                            // α, domain = atoms
pub open spec fn realizes(theta, e, alpha) -> bool                            // inc:172-174
pub open spec fn atom_pairs(atoms) -> Pairs                                   // Π_q (inc:183-184)
pub open spec fn successor_ok(q, alpha, next) -> bool   // L_θ(next) = e⁻¹L_θ(q) when (θ,e) realizes α
pub struct Case { constraint: Constraint, alpha: Assignment, next: Regex<model::Test> }
pub open spec fn steps_ok(d, item, cases: Set<Case>) -> bool                 // Lemma 5.3's conclusion
pub open spec fn paper_steps(d, item, atoms, cases_split, next) -> ISet<Case> // Steps(Γ,q) (inc:186-189)
pub open spec fn atoms_complete(q, atoms) -> bool
pub open spec fn stmt_successor_cases() -> bool                               // Lemma 5.3 (inc:197-209, app:486-518)
pub open spec fn stmt_successor_cases_finite_domains() -> bool              // extension (Q3)
pub struct Node { item: Item, parent: Option<(nat, Assignment)>, depth: nat }
pub struct Trace { nodes: Seq<Node>, expanded: nat }                          // search.rs `items`, `next`
pub enum Outcome { Holds, Refuted(Constraint, Seq<Assignment>), Exhausted }
pub open spec fn may_discard(d, nodes, j, depth) -> bool   // ∅ state, no witnesses, or W(J) ⊆ W(K), d(K) ≤ depth
pub open spec fn trace_wf(d, g0, q0, cases_of: spec_fn(Item) -> Set<Case>, t: Trace) -> bool  // Alg 5.4 (inc:232-253)
pub open spec fn trace_outcome(t, outcome) -> bool;  follows(d, letters, theta, u) -> bool
pub open spec fn outcome_ok(d, g0, r, s, outcome) -> bool    // sound, realizable, minimum length
pub open spec fn initial_ok(q0, r, s) -> bool                // L(q0) = L(r & ¬s)
pub open spec fn stmt_search_correct() -> bool               // Thm 5.5 soundness/completeness/minimality (inc:257-262, app:675-741)
pub open spec fn stmt_search_correct_finite_domains() -> bool
pub open spec fn reachable_item(cases_of, start, n, j) -> bool;  finitely_many_items(cases_of, start) -> bool
pub open spec fn stmt_search_terminates() -> bool            // Thm 5.5 termination, CONDITIONAL on finitely_many_items
```

The search is specified by **traces** (inserted items in insertion order, never removed, with
parents and depths), which is the data the Rust search keeps, rather than by a deterministic
algorithm: the enumeration order of cases and letters is left free, and insertion-time
discarding is specified semantically (`may_discard`), so pruning is a separate layer.

## 5. Layer 4 — pruning (`refinement/pruning.rs`)

```rust
pub open spec fn lang_le(x, y) -> bool;  sim_sound(le) -> bool;  test_sim_sound(tle) -> bool   // app:544-546
pub open spec fn required(q, p) / excluded(q, n) -> bool                         // dec(q) = (P, N) (app:528-534)
pub open spec fn stmt_decomposition() -> bool                                     // eq:decomposition (app:536-541)
pub open spec fn dead(le, q) -> bool;  dominated(d, le, j, i) -> bool            // Def B.3 (app:543-558)
pub open spec fn stmt_prune_sound() -> bool                                       // Lemma B.4 (app:564-582)
pub open spec fn sim_step(le, tle, x, y) -> bool;  test_step(tle, x, y) -> bool  // the code's rules
pub open spec fn stmt_sim_rules_sound() / stmt_test_rules_sound() -> bool        // Lemma B.6 (app:650-665)
pub open spec fn stmt_checks_discard() -> bool                                    // checks ⇒ may_discard
```

## 6. Layer 5 — finiteness (`refinement/finiteness.rs`, `verify/finite_states.rs`)

```rust
pub open spec fn abs_state(g: model::Graph, id: nat) -> Regex<model::Test>      // = lift_regex: the canonical-state abstraction
pub open spec fn stmt_lift_injective() -> bool                                    // interning ⇒ injective on a wf graph
pub open spec fn step_abstracts(m: Model<Regex<model::Test>>, before, q, after, v) -> bool
pub open spec fn instantiation_ok(m, states_of_tails) -> bool                     // m.contract() ∧ tails are states
pub open spec fn stmt_reachable_states_finite() -> bool                           // = theorem_finite_reachable (proved)
pub open spec fn cases_from_atoms(d, cases_of, atoms_of) -> bool
pub open spec fn stmt_items_from_states() -> bool                                 // app:680-689
```

Abstract model: `Model<S>` with (N0)–(N5), (S0)–(S6) and the proved `theorem_finite_reachable`
(Lemma 4.2, rx:129-137, app:90-425). Canonical states: the raw lift `lift_regex(g, id)` (operands
in id order). Within one well-formed graph the lift is injective (unique nodes), and extension
keeps it (`lemma_lift_stable_under_extends`), so the search's visited set over ids is a set over
abstract states. Across runs operand order may differ; the plan therefore changes two clauses of
`Model` (spec change to `finite_states.rs`, proof phase):
1. `nset` becomes a relation `nset(inter, X, v)` (the implementation's set output depends on
   interning order), and `nset_closed`/`built` quantify over all related outputs;
2. "a set state is determined by its operands" becomes "finitely many set states have operands in
   a given finite set" (true for duplicate-free operand sequences).
`lit`/`prod`/`succ` of the instance are the largest relations allowed by (S0)–(S6), so the exec
obligation is: the transition built by `derivative(q)` has literal and product values in them,
and `interpret`/`successor` return a value in `succ(q)` or `q` itself (`step_abstracts`).

**Status: OPEN for the implementation.** The audit (agent `ExtendedProofAudit`, harness
`/tmp/audit/repo`) found (S3) false: & distributes over a union containing a conditional; both
branches become equal and `local_if` collapses `If(t,a,a)` to `a`; the union combinator's
`collect` merges leaves into one *union-valued* leaf (`normalize.rs:3158-3187`, reached from
`normalize.rs:4301` and the distribution / De Morgan / Append / Clean rebuilds); a later fold step
intersects that leaf with another literal. Counterexample `q = (¬ε·φ) & ((¬ε)* + ¬(ψ + ¬ε·ψ))`.
(S0)–(S2), (S4)–(S6) held on ~500k states. So Lemma 4.2's current proof covers the model
normalizer only.

Since then (agent `FinitenessResearch`, `/tmp/finite-proof/partial-result.tex`): for the
implemented successor, complement depth and a continuation rank never increase; reachable star
nodes and non-head concatenation factors are subterms of `N(r0)`; concatenations have bounded
length. Union/intersection nesting is not yet bounded, and the bounds above do not imply
finiteness (an unreachable family of distinct normal forms satisfies them). The audit's large orbit
saturates at 211,357 states with nesting depth ≤ 7. A proof-or-disproof agent (`FinitenessProof-2`,
`/tmp/finite-proof-2/`) is running. Hence:
- **termination of the implemented search is stated only conditionally** (`stmt_search_terminates`
  under `finitely_many_items`), and for the paper's model normalizer via Lemma 4.2;
- the Rust loops still return (graph budget), possibly with `Exhausted`.

## 7. Layer 6 — implementation refinement (`refinement/implementation.rs`)

```rust
pub enum RegisterView { Equals(nat), Differs(Set<nat>) }
pub struct ConstraintView { principal: RegisterView, action: RegisterView, resource: RegisterView }
pub open spec fn constraint_of(g: ConstraintView) -> Constraint
pub enum ClassView { Constant(nat), Register }
pub struct LetterView { principal/action/resource: Option<ClassView>, reg_*: ClassView }
pub open spec fn letter_holds(l, p) -> bool;  letter_assignment(l, atoms) -> Assignment   // Letter::holds, truth
pub open spec fn impl_cases(g, atoms, steps: Set<(ConstraintView, LetterView, nat)>) -> Set<Case>
pub open spec fn expansion_ok(d, g, gamma, q, atoms, steps) -> bool   // per-expansion obligation (search.rs:159-184)
pub enum SlotView { Code(nat), Fresh(nat) }
pub open spec fn reconstruction_ok(d, gamma, letters, candidate, history, known) -> bool   // analyzer.rs:533-568
pub open spec fn covered_with_ok(d, p, rule, cases, query) -> bool    // analyzer.rs:460-497, tables.rs
```

Already verified and reused: `derivative_correct`, `successor_entries_wf` (successor language),
`atoms_wf` (atom completeness), `CompiledPair::compile` (root language), `guard_wf`.

## 8. How the layers compose (executable implementation link pending)

1. Query → numeric: `stmt_front_end_denies` + `stmt_numeric_genericity` turn a typed query into
   numeric `n_covers` / `included_under` queries, for every component type.
2. Policy → inclusions: `stmt_policy_reduction` with the code's cases (`covered_with_ok`).
3. Inclusion → search: `initial_ok` from `compile`; `expansion_ok` per expansion
   (`stmt_successor_cases[_finite_domains]` + `successor_entries_wf` + `atoms_wf`); pruning by
   `stmt_checks_discard` (`stmt_prune_sound`, `stmt_sim_rules_sound`, `stmt_test_rules_sound`).
4. Search → outcome: the Rust search's `items`/`next` form a trace with `trace_wf`;
   `stmt_search_correct` gives `outcome_ok`.
5. Outcome → verdict: `reconstruction_ok` + layer 1 give `every_instance` and the minimality
   clauses of `analyzer.rs`.
6. Non-exhaustion (optional, completeness under resources): `stmt_items_from_states` + finiteness
   (§6, open).

## 9. Paper ↔ spec/code differences

1. **Valuations.** Paper: θ ∈ Event is the candidate (bg:32). Typed DSL: same. Numeric runtime:
   `Subst` = head bindings with 0 at unbound components; analyzer's numeric valuation is the whole
   candidate. Spec uses the whole candidate at the numeric layer.
2. **Domains.** Paper: arity n, all Dᵢ infinite. Code: arity 3; typed component types may be
   finite (`u32`); numeric θ is `u64`-bounded (`event_wf`), history events unbounded `nat`;
   declared finite domains are supported (`Domains::with_*`) — outside the paper's theorems.
3. **Unscoped tail variables** resolve to `None` in the DSL, making both `=` and `≠` false
   (breaks the duality of bg:50-54). **Resolved:** every analyzed rule passes through the verified
   `flatten_rule` (`add_rule`, and `tail_included` for both tails), whose contract
   (`flattening_client`) gives `head_scoped ∧ regex_scoped` on success, so `rule_wf` always holds.
4. **Rule status / mode / policy decision** are not specified in Verus anywhere; the native code
   uses an ordered `Vec` and reports the first violation (same deny/permit answer).
5. **Split** emits ≤ n+1 cases per register (equal to one undecided constant, or different from
   all), not the paper's 2ⁿ literal combinations minus unsatisfiable ones; the families are
   equivalent partitions (`split_ok`). With finite domains the register is enumerated over all
   declared values whenever it is compared at all.
6. **Exhaustion.** Paper's search always returns `holds` or a counterexample; code adds
   `Exhausted` (max_items, graph budget). Table construction overflow (`tables.rs:79-90`) returns
   `Err(GraphLimit)` instead of `Exhausted`; `covered_with`/`at_least_as_strict` stop at the first
   `Exhausted` even if a later case would refute.
7. **Simulation.** Code (uncommitted `simulation.rs`) has recursive test rules (And/Or on either
   side), `Star(a) ≤ Star(b)` via `x ≤ b`, and multi-`Univ` padding; paper Fig. `fig:simulation`
   (app:600-648) has set-inclusion `Conj`/`Disj` and single `PadL`/`PadR`. Spec follows the code.
8. **Domination enumeration**: subsets of required parts only when |P'| ≤ 4 (incompleteness only).
9. **Constant codes start at 0** (analyzer `Constants`, `analyzer.rs:141-170`), but the
   `FlatEncoder` contract it implements requires nonzero codes (`encoded`: `id > 0`; `maps_wf`),
   as does `history_specs::term_wf`. So `Constants` violates the contract it implements (it is
   native, so nothing checks it), and the existing encoding lemmas cannot be instantiated for it
   as is (Q9). Separately, the difference pair's head is `[Any;3]` with `Variable` atoms, violating
   `structural_wf`; harmless for `compile`'s contract (no `requires`), and the spec applies the
   front-end lemmas per rule, not to the difference pair.
10. **Successor guard cache**: `CompiledPair::successor` may return the residual unchanged
    (`guard_wf`); the finiteness instance must allow `v = q` (`step_abstracts`).
11. **(S3) is false for the implementation** (§6). (N0) singleton clause / `set` idempotence on a
    single leaf is also unverified.
12. **Minimality across queries** (inc:97-100): matches the code; spec's `same_profile` makes the
    "per query" claim precise for split queries.
13. **Component-local atoms (spec change, approved by the author).** `search::stmt_successor_cases`
    and `_finite_domains` were false as frozen: `model::Primitive` allows cross-component atoms
    `Eq(c, Variable(c'))`. Counterexample: atoms `{Eq(P, Var(A)), Eq(P, Const 5)}`, item
    `(∅, Empty)`, `cases_split = {∅}` (`split_ok`, since `atom_pairs = ∅`), `next = λ_. Empty`;
    the assignment making both atoms true is realizable (`θ.A = 5`, `e.P = 5`), so it is in
    `paper_steps`, but it is not realizable for `θ.A = 0`. Fix: new hypothesis
    `search::atoms_local(atoms)` (every `Eq(c, Variable(c2))` in `atoms` has `c2 = c`), the paper's
    component-locality (bg §3). The implementation enforces it (`search.rs` `atom()` returns `Err`
    otherwise); the implementation layer discharges it from that check.
14. **Numeric renamings avoid the rule's codes (spec change, approved).** `encoding::stmt_numeric_genericity`
    was false: `n_renaming_ok` made `f` fix the rule's codes but not avoid them. Counterexample:
    rule `{Forbid, head.principal = Some(3), tail = All}`, `θ = (7,0,0)`, `w = []`, `f(7) = 3`,
    `f = id` elsewhere: `f` is injective on `{7, 0}` and fixes `{3}`; the original pair is not
    denied (`7 ≠ 3`), the renamed one is. Fix: `n_renaming_ok` gains
    `∀x ∈ values, k ∈ fixed. f(x) = k ⟺ x = k`, mirroring the typed `renaming_preserves`.
15. **Equivalence of `eq_spec` for fresh choices (spec change, approved).** `analyzer::stmt_choice_exists`
    was unprovable for a generic `eq_spec`: with `eq_spec = ≤` on `nat`, `infinite_type` holds,
    but two fresh numbers at one component can never be non-equal in both directions, so no
    choice is admissible. Fix: hypothesis `eq_equivalence::<P/A/R>()` (reflexive, symmetric,
    transitive: the clauses of history-store's key obligations), defined in
    `history_store::typed::verify` next to `native_obligations`, with
    `lemma_native_obligations_eq_equivalence` (native obligations ⟹ equivalence), so the top-level
    condition (Q4) is unchanged.

16. **Finiteness fix (executable change, approved by the author 2026-11-08).** The implemented
    successor had infinitely many reachable states (disproof `/tmp/finite-proof-2/result.tex`,
    confirmation `notes.md`/`confirm.log`: orbit `f_(n+1) = c & (B + f_n)` with constant
    transitions, sizes 24+28n), caused by merging constant leaves of transition *unions* into one
    union-valued leaf (the (S3) failure of §6). Fix: `normalize.rs:2765`
    `TransitionHead::Const(r) =>` -> `TransitionHead::Const(r) if self.intersect =>` (constant leaves
    are merged only in transition intersections; union constants stay separate children). Evidence
    (`/home/zak/work/verus-work2/FinFix/EVIDENCE.md`): the orbit saturates at 2 states; the audit
    harness finds 0 violations of (S0)-(S6) (base: (S3) violated); random campaigns saturate with
    fewer states; both history-semantics Verus configs (947/951) and workspace tests pass. With it,
    §6's status changes from OPEN to: (S0)-(S6) to be mechanized for the implementation and
    `search::finitely_many_items` discharged via `theorem_finite_reachable`.
17. **Verified facade (behavior-preserving restructuring).** `SymbolicLanguage::derive` reads
    positive atoms with an index loop, and `successor` builds its SmallVec key with `new` plus
    `extend_from_slice`; callback APIs and results are unchanged. All eight facade methods now
    have verified contracts, including atom completeness for every `nat` valuation.
18. **Constant-id capacity (author decision during proof completion).** Keep runtime behavior
    and public Rust signatures unchanged. Constructor/query verification has explicit capacity
    preconditions excluding `u32` constant-id overflow; the existing overflow panic is not claimed
    unreachable without those preconditions.
19. **Universe storage.** Private `Rc<[ConstId]>` becomes `Rc<Vec<ConstId>>`; ids and declaration
    order are unchanged.
20. **Register choices.** Equals alternatives keep their compact id list plus one optional
    remainder; final constraints are built only during the product, eliminating intermediate
    enum buffers.
21. **Letter choices.** Compact named ids and prefix/remainder flags replace intermediate option
    buffers without changing class order.
22. **Enumeration.** Explicit products and owning step iteration replace closure/array chains,
    preserving lexicographic order without added constraint clones.
23. **Literal copies and equality.** Verified `copy` uses SmallVec `new` plus `extend_from_slice`;
    manual equality compares ordered literal ids, retaining canonical set-view injectivity.
24. **Table construction.** Explicit copy/shift loops preserve source ordering, earlier-root
    languages, and existing overflow/error paths; successful difference is exactly left minus right.
25. **Remaining native capacities (author decision).** Preserve runtime behavior and Rust
    signatures. Derive product, constraint-id, and fresh-counter size bounds where possible;
    otherwise expose explicit sufficient query/state preconditions for those bounds.
26. **Encoding attempts.** A ghost call count on `FlatEncoder` records each opted-in encode
    attempt. Generic lowering bounds it by head/test traversal size, including error returns;
    typed encoders' runtime and book logic are unchanged.
27. **Counterexample assembly.** Indexed candidate/history construction preserves component and
    history order and fresh-number allocation. History rows are projected directly into one
    preallocated result vector; numerical slot rows and search alphabets are ghost evidence only.
    The native analyzer's 13 tests pass; reconstruction and executable verdict contracts verify
    in focused and complete CI checks; both analyzer configurations verify with 0 errors.
28. **Sufficient query resources.** `query_capacity` (`open(crate)`) requires `count ≤ u32::MAX`
    and `(count + 2)³ ≤ usize::MAX`, where `count` is the existing book size plus 6 plus both
    flattening traversal costs, a conservative bound on the query's vocabulary. It covers constant
    ids and the per-state split/letter products only. An earlier version also bounded constraint
    ids, the queue and fresh counters by the size of the whole constraint family,
    `(n + 2ⁿ)³ ≤ u32::MAX`; that forced `count ≤ 10` and excluded every query with a test atom in
    each tail. Those limits are now runtime errors (item 30).
29. **Query input cloning (implementation counterexample).** `tail_included` constructs rules
    with derived `Head`/`RegexExpr` clones. A well-typed `Copy` principal whose custom `Clone`
    returns `Principal(n + 1)` has coherent equality, hashing and event projections, yet a head
    requiring principal 0 yields a counterexample with principal 1 (`cargo run -p history-analysis
    --features runtime --example clone_probe`, temporary probe removed after execution).
    This clone violates the normal Clone convention, but the current native obligations do not
    exclude it. The author selected borrowed-source flattening: `flatten_rule_parts` reuses the
    existing iterative implementation; `flatten_rule` preserves its API and contract. The query
    now passes original head/tail references and does not invoke their Clone hooks. The corrected
    probe returns principal 0, and all 13 analyzer tests pass. No clone trust boundary is added.
30. **Constraint-id and fresh-value exhaustion are errors (author decision Q12).**
    `ConstraintTable::intern` returns `HistoryError::IdExhausted { domain: "constraint" }` instead
    of panicking when the id does not fit `u32`; counterexample reconstruction allocates fresh
    values with `checked_add` and returns `IdExhausted { domain: "fresh value" }` on overflow.
    Both propagate as `Err`, which carries no claim, like table overflow (Q6). Neither limit is
    reachable before memory is exhausted, and termination depends on neither (item 31).
    `lemma_query_capacity_nonvacuous` proves that `query_capacity` holds on every word size
    whenever `count ≤ 1000`.
31. **Termination of the real search from Lemma 4.4.** The loop in `Search::run` decreases
    `|bound| − next`, where `bound` is one item set fixed before the loop by
    `finiteness::theorem_impl_items_bound`: the items over the states `m_impl` reaches from the
    start state (`theorem_finite_reachable`), with constraints over the start constraint and the
    literals of those states' atoms or the declared domains. Every successor the code computes is
    an `m_impl` step (`lemma_impl_successor_abstracts`, from the derivative and successor
    contracts on the real graph), so the run's archive satisfies `archive_follows`, and
    `lemma_running_items_bound` bounds the queue by the paper's `lemma_trace_nodes_bounded`.
    `m_impl` is a verified over-approximation of the implemented step, not an assumed model of
    it. The previous measure, `|constraint_family| · 2³²` from the `u32` id space, and its
    helper lemmas are removed. All affected configurations verify with 0 errors (semantics
    1575 / 1580 / `public_specs` 19; analyzer 483 / 483), and the native analyzer and semantics
    tests pass.



## 10. Decisions (FROZEN by the author)

Q1 verify the real analyzer (bring `history-analysis` under Verus); Q2 keep the code, state
finiteness of the implementation as a hypothesis until `FinitenessProof-2` settles it; Q3 cover
declared finite domains too (`*_finite_domains` statements are proof targets); Q4 accept
`books::native_obligations` (plus the `FlatEncoder` obligation for `Constants`); Q5 per-case
minimality as implemented; Q6 keep the `Exhausted` short-circuit and `Err` on table overflow;
Q7 accept vacuous meaning on small types; Q8 Figure 2 updated to the implemented rules (done);
Q9 `Constants` codes start at 1 (done: `analyzer.rs:135-150, 590`; analyzer tests, fmt, clippy pass).

Q10 keep constant-id overflow behavior and public signatures; add verified capacity preconditions
to constructor/query contracts (chosen by the author during proof completion).

Q11 keep the remaining native overflow behavior/signatures as well; use verified size
preconditions for product, constraint-id, and fresh-counter limits if not otherwise derivable.
Superseded by Q12 for constraint ids and fresh values.

Q12 report constraint-id and fresh-value exhaustion as `Err` (`IdExhausted`) rather than bound
them by preconditions (§9 item 30). Product and constant-id bounds remain preconditions.

### Original questions

- **Q1 (scope of the exec contract).** `history-analysis` is not a Verus crate. Options: (a) put it
  under Verus and prove the postconditions of §0 on the real code; (b) keep it native and prove the
  layers 0–5 abstractly, with a *checked* trace (e.g. a ghost/debug validator) linking runs to
  `trace_wf`. The spec supports both; (a) is needed for a machine-checked top-level theorem.
- **Q2 ((S3) and implementation finiteness).** Option A: change the implementation so combinator
  unions (`Action::step` `Union(n)` → `collect`, N:4301 and the rebuild paths) no longer merge
  leaves into a union-valued leaf, making (S3) true and the existing finiteness proof applicable
  (a prototype is in `/tmp/perf/variant`, tests pass; its benchmark run was interrupted and is on
  hold). Option B: keep the code; the finiteness layer waits for `FinitenessProof-2`'s proof or
  disproof; until then termination/completeness of Thm 5.5 is claimed only for the model
  normalizer and the implemented analyzer is resource-bounded (always returns, possibly
  `Exhausted`). Which?
- **Q3 (finite domains).** Should the frozen top-level theorem cover declared finite domains
  (`*_finite_domains` statements, beyond the paper), or restrict the claim to unrestricted
  domains and document finite domains as unverified?
- **Q4 (typed vs numeric top layer).** The top layer is stated over the typed DSL semantics
  (`junco_core::verify::dsl`), whose equality is `eq_spec`; typed guarantees elsewhere are
  conditional on `books::native_obligations` (projection and Eq/Hash coherence). **Recommended:
  accept.** The analyzer goes through the same flatten/lower path as the runtime, so the condition
  is the same; the only addition is the `FlatEncoder` obligation for `Constants`.
- **Q5 (minimality wording).** Is "shortest for the same denying rule among candidates with the
  same constant profile" acceptable for `covered`/`at_least_as_strict`, or should the analyzer
  return globally shortest counterexamples (would require running all cases)?
- **Q6 (Exhausted short-circuit, Err on table overflow).** Keep as is (sound, incomplete), or
  continue past `Exhausted` cases and map table overflow to `Exhausted`?
- **Q7 (counterexamples on small types).** Accept that a counterexample over a finite component
  type with too few spare values has vacuous meaning, or require a domain-size side condition?
- **Q8 (paper figure).** Update Fig. `fig:simulation` to the implemented rules, or restrict the
  code to the paper's rules?
- **Q9 (zero codes).** The analyzer's `Constants` issues code 0, violating `FlatEncoder`'s
  nonzero-code contract, which the existing encoding lemmas require. Options: (a) start its codes
  at 1 (a one-line executable change; the analyzer's numeric valuation is the whole candidate,
  so code 0 has no special meaning there), or (b) leave the code and restate the analyzer's
  encoding without the existing lemmas (duplicating them for codes from 0).

## 11. Trust base of this phase

No new `assume`, `admit`, or `assume_specification`. The refinement module's mathematical
definitions remain frozen. Existing trust base (unchanged): `junco-core/src/verify/history_assumptions.rs`
(`assume_specification`s for SmallVec, slices, `Vec::dedup`, …, and the `KernelStore` external
trait specification), `compiled_rule.rs:290` `same_owner`, `observation.rs` and `history-store`
external bodies, and `books::native_obligations` as a hypothesis of typed guarantees.
The analyzer's scoped `BorrowedEncoder` satisfies the `FlatEncoder` contract over its real
constant book. `analyzer_obligations` includes event projection laws and the native Eq/hash
obligations for both constant interning and the internal search/pruning/simulation keys.

The analyzer's new native leaves are `NativeMap<K, V>`, `NativeSet<K>`, and `NativeGroups<K, V>`
in `crates/history-analysis/src/native.rs` (author-approved hashbrown wrappers). Their external
bodies cover only construction, Eq-class lookup, fresh insertion, set insertion, and grouped
append/read. Logical keys are stored Eq representatives, not Rust identity; duplicate Eq keys
retain the existing representative. Contracts are conditional on `key_obligations`, following
`history-store`'s native map pattern. No analyzer, constraint, pruning, simulation, or search
algorithm is a trusted leaf.
The SmallVec antichain key also requires Eq-equivalent keys to have the same ordered regex-id
view. These are explicit native-key hypotheses, not assumptions about an analyzer verdict.
