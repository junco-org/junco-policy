# Checking the mechanized proofs

This repository contains the Junco policy checker (the monitor) and policy analyzer together
with their Verus proofs. This file is the reviewer's entry point: how to re-run the proofs, which
six files fix the meaning of every theorem, where each result of the paper is proved, which
hypotheses the proved statements make, and where the mechanization differs from the paper.

## Toolchain

| Component | Version |
|---|---|
| Verus | release `0.2026.10.04.426d8b0` (`verus-0.2026.10.04.426d8b0-x86-linux.zip`, sha256 `624018662868563a7bec0dd07be5e4dd0c3d61124b4b55105765884bf2d4d1a0`) |
| Z3 | `4.16.0` (`z3-4.16.0-x64-glibc-2.39.zip`, sha256 `7288c49a5bd6dbafd7b0b0d1f65956b91672da24b08f09242919af159be3418e`) |
| Rust | `1.98.1-x86_64-unknown-linux-gnu` with components `rustc-dev` and `llvm-tools` (required by this Verus release) |
| vstd | `0.0.0-2026-10-04-0306`, from crates.io, pinned in `Cargo.lock` |
| Platform | Linux x86-64 (the Verus release asset is built for it) |

## How to run

```sh
# Download the pinned Verus and Z3 into a directory, check their sha256, and verify everything.
scripts/verify-all.sh --download ~/junco-tools

# Or use an installed toolchain: VERUS_DIST (an unpacked Verus release) or verus/cargo-verus on
# PATH, and VERUS_Z3_PATH (or z3 on PATH).
VERUS_DIST=/path/to/verus-x86-linux VERUS_Z3_PATH=/path/to/z3 scripts/verify-all.sh

# Check the toolchain and print the thirteen commands without running them.
scripts/verify-all.sh --list

# Pass arguments to Verus in every command, e.g. to use more cores.
scripts/verify-all.sh -- --num-threads 8
```

`scripts/verify-all.sh` checks the Verus, Z3 and Rust versions, runs `cargo fetch --locked`, and
then runs the same thirteen `cargo verus verify --locked` configurations as the `verify-core`
job of `.github/workflows/ci.yml` (no module filter: every verified function of each package
and of its verified dependencies). It prints a table of verified-function and error counts per
configuration and exits nonzero if any configuration fails. The `rustup` toolchain must be
installed:
`rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu --profile minimal --component rustc-dev --component llvm-tools`.
Verus's memory use grows with the thread count; keep it near the number of cores when memory is
limited (with 16 threads on a 7 GB machine the verifier was killed, `signal: 9, SIGKILL`).

`scripts/trust-scan.sh > TRUST.md` regenerates `TRUST.md`, the inventory of every place where
the proofs assume rather than prove a fact (the counted kinds are listed at its top:
`assume_specification`, `external_body`, external type/trait specifications, `external`,
`admit`, `assume`, unchecked termination, `axiom`, `uninterp`, `derived_eq_claim`,
`unannotated_pub_fn`, and the two verified helper crates). There are no `admit`s or `assume`s.

`scripts/spec-check.sh` tests the `assume_specification`s for the standard library and
`smallvec` (`crates/junco-core/src/verify/history_assumptions.rs`) against the real
implementations with the `verus-spec-check` tool (network access on first use).

## Expected results

| Configuration (`cargo verus verify --locked ...`) | Result |
|---|---|
| `-p history-syntax --no-default-features` | 60 verified, 0 errors |
| `-p history-syntax --features serde,std` | 60 verified, 0 errors |
| `-p junco-core --no-default-features` | 203 verified, 0 errors |
| `-p junco-core --features runtime,std,serde` | 287 verified, 0 errors |
| `-p history-store --no-default-features --features runtime` | 289 verified, 0 errors |
| `-p history-store --features runtime,std` | 289 verified, 0 errors |
| `-p history-semantics --no-default-features --features runtime` | 1619 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache` | 1624 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache --test public_specs` | 19 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache --test reviewer` | 7 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime` | 603 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime,std` | 603 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime,std --test reviewer` | 17 verified, 0 errors |

The counts are from the pinned toolchain (`-- --num-threads N` only changes wall time). The
`--test` rows count the theorems and clients of the test target itself; the library they build
on is verified in the row above them. `cargo test --workspace --features junco-policy/test-util`
passes; the differential suite (`crates/history-analysis/tests/differential.rs`) compares every
analyzer query against brute-force enumeration over small declared domains.

## Reviewer map

Six interface files fix the meaning of every theorem (`docs/verification/INTERFACES.md` has the
per-definition tables and the reading order). Everything else is proof, connected to these by
refinement. Read them against the paper in this order:

| Id | File | Definitions | Read for | Paper |
|---|---|---:|---|---|
| R1 | `crates/history-syntax/src/spec/events.rs` | 14 (+6 `View` impls) | what an event is: `arity`, `event_view`, `well_tagged`, `views_surjective`, `event_laws`; the DSL views `RuleView`, `HeadView`, `RegexView`, `TestView` | `sec:events`, `sec:rules` |
| R2 | `crates/junco-core/src/spec/semantics.rs` | 26 | `head_matches`, `test_sem`, `lang`; over events `rule_evaluation`, `rule_violated`, `policy_denies`, `policy_permits`, `least_violation` | `def:violates`, `def:policy-violates` |
| R3 | `crates/junco-core/src/spec/questions.rs` | 44 | `in_domains`, `domains_wf`, `refines`, `covers`, `never_denies`, `always_denies`, `tails_included`; symbolic counterexamples `CexView`, `InclusionView`, `admissible`, `instantiates`, `cex_has_instance`, `every_instance`, `fresh_capacity`, `capacity_for`; minimality `same_profile`, `shortest`, `shortest_in_case`, `minimal_in_case`; the constant extractors | `def:policy-refinement`, `app:policy-reduction`, `thm:search` |
| R4 | `crates/junco-core/src/spec/hypotheses.rs` | 4 | `hash_coherent` (the trust token), `eq_equivalence`, `key_laws`, `event_obligations` | hypotheses (below) |
| R5 | `crates/history-semantics/src/spec/monitor.rs` | 6 | `ValidatorView`, `check_frame`, `check_step`, `permits_result`, `rollback_step`, `trace_safe` | `thm:matcher` at the level of `Validator` |
| R6 | `crates/history-analysis/src/spec/analyzer.rs` | 21 | `AnalyzerView`, `known_with`, the capacities including `undeclared_capacity`, `rules_of`, `without_rule`, `counterexample_spec`, `covered_spec`, `removal_preserves_decisions`, `redundant_spec`, `at_least_as_strict_spec`, `tail_included_spec`; A5 in prose in the header | A1–A6 |
| P | `crates/history-semantics/src/verify/paper.rs` | one `stmt_*`/`theorem_*` per paper result | the paper index: table of paper label → mechanized statement → proof → file; `theorem_paper_index` proves every row | all |
| T | `crates/history-semantics/tests/reviewer.rs`, `crates/history-analysis/tests/reviewer.rs` | 7 and 17 verified items | the end-to-end statements over public items only (below) | `thm:matcher`, A1–A6, S9 |

The theorems a reviewer reads:

- `crates/history-semantics/tests/reviewer.rs`: `theorem_monitor_check` (the three cases of
  `check_step` spelled out with `rule_violated`: grant ⇔ no rule violated, denial names the
  first violated rule by zero-based source-order index and mode, errors are never invariant failures), `theorem_monitor_permits`,
  `theorem_trace_safe` (every state of a run of `check`/`rollback` from a fresh validator is
  `trace_safe`, by induction over the run), `theorem_analyzer_to_monitor` (if `P ⊑ Q` on the
  declared domains, a validator over `Q` permits what a validator over `P` grants inside them),
  `theorem_event_obligations_u32_u64`, and the exec clients `monitor_client` /
  `monitor_client_u32_u64` (a `Store`, a builder with one rule, `finish`, one `check`; the result
  satisfies `thm:matcher` and the state is `trace_safe`, from the public contracts only).
- `crates/history-analysis/tests/reviewer.rs`: `stmt_analyzer_a1` … `stmt_analyzer_a6` with
  `theorem_a1_covered_decision`, `theorem_a2_real_counterexamples`, `theorem_a3_refinement`,
  `theorem_a3_redundancy`, `theorem_a4_tail_inclusion`, `theorem_a5_escapes`
  (`theorem_a5_no_invariant_failure`), `theorem_a6_minimality`; `theorem_vacuity_corollaries`
  (`never_denies`/`always_denies` through `at_least_as_strict` with `[]` and
  `[forbid head Univ]`); `theorem_analyzer_to_monitor` (S9, with `at_least_as_strict_spec`);
  `theorem_capacity_u32_u64`; the exec clients `analyzer_client` / `analyzer_client_u32_u64`
  (`Domains::infinite`, `new`, `add_rule`, the four queries, every precondition discharged from
  the previous postconditions).

The `stmt_*` statements of the paper index and the `theorem_*` proofs of the `refinement/`
layer (`crates/history-semantics/src/verify/refinement/`) are the mechanization of Sections 4–5
and Appendices A–C; the executable analyzer (`crates/history-analysis/src/analyzer.rs`) and
monitor (`crates/history-semantics/src/validator.rs`) are verified against R5/R6. Paper notation,
in `crates/history-semantics/src/verify/refinement/`: $\mathcal{L}_\theta(r)$ is `n_lang`
(`encoding`); constraint $\Gamma$, `entails`, `decides`, `paper_split`, `included_under`,
`head_constraint`, `n_covers` are in `inclusion`; `Item`, `witness`, `realizes`, `steps_ok`,
`Case`, `Outcome`/`outcome_ok` in `search`; `dead`, `dominated`, `sim_step`, `sim_sound` in
`pruning`.

## Hypotheses

- **`event_obligations::<E>()` (R4).** Every monitor and analyzer guarantee about the event type
  `E` is conditional on `event_laws::<E>()` (R1: arity in `1..=MAX_ARITY`, stable projections
  tagged with their coordinate, `views_surjective`) and `key_laws::<E::Component>()` (`Eq` agrees
  with `eq_spec`, which is an equivalence, and `hash_coherent`). The frames (`check_frame`,
  `rollback_step`, the view equations of `add_rule`/`tail_included`) are unconditional.
  `junco_core::verify::hypotheses` and `history_syntax::verify::events` prove every conjunct for
  the built-in tuple events `(A, B)`, `(A, B, C)`, `(A, B, C, D)` from the payloads' `eq_spec`,
  except `hash_coherent`.
- **`hash_coherent::<C>()`, the single trust token.** The `external_body` hash containers
  (`NativeMap`/`NativeSet`/`NativeGroups`) behave as maps on `eq_spec` classes only if the key's
  `Hash`/`Eq` are faithful. Nothing discharges this for a user component type: every concrete
  reviewer theorem (`theorem_event_obligations_u32_u64`, `monitor_client_u32_u64`,
  `analyzer_client_u32_u64`, `theorem_capacity_u32_u64`) carries
  `hash_coherent::<Component2<u32, u64>>()` as its only premise. The library's own internal key
  types take it by the five `axiom fn`s in `crates/history-analysis/src/verify/key_axioms.rs`
  (TRUST.md, `axiom`).
- **Root event types.** `LockEvent`, `FlowEvent`, `AgentEvent` in the unverified root crate
  implement `Event` by hand; `event_laws` is a documented hypothesis at each impl (D4), not a
  theorem.
- **Declared domains (R3 `domains_wf`, S9).** A declared coordinate ranges over exactly its
  declared, nonempty, correctly tagged values; an undeclared coordinate over every value of its
  type. Every verdict is stated over pairs `in_domains`; `Domains::with_domain` rejects empty and
  mistagged declarations at runtime. A verdict transfers to the monitor only for requests and
  histories inside the domains (`theorem_analyzer_to_monitor`).
- **Capacity (R3 `fresh_capacity`, `capacity_for`).** A counterexample promises a real instance
  only when each coordinate offers as many fresh values, distinct from the known constants, as
  the counterexample uses (`counterexample_spec`). `junco_core::verify::capacity` discharges
  this for integer coordinates (`lemma_fresh_capacity_u8/u16/u32/u64`: `known[i].len() + k <=
  2^bits`); `theorem_capacity_u32_u64` is the instance for `(u32, u64)`. Every instance is
  always a real failing pair in the domains (`every_instance`), capacity or not.
- **Interning capacities (R6).** `new`, `add_rule` and `tail_included` require
  `constructor_capacity`, `add_rule_capacity`, `query_capacity`: the constants interned so far
  plus the input's fit in `u32`. `known` is fixed by the contracts (`declared_sets(domains)`,
  then `known_with(known, rule_constants(rule))` / `known_with(known, tail_constants(..))` on
  every return).
- **Termination.** `stmt_search_terminates` is conditional on finitely many reachable items,
  discharged for the implementation (`theorem_impl_finitely_many_items`,
  `theorem_impl_items_bound`); no function of `history-analysis` uses
  `exec_allows_no_decreases_clause` (TRUST.md).

## Differences between the paper and the mechanization

1. **One tagged component type, not a product.** An event's components share one Rust type
   `E::Component` tagged with their coordinate (`Component2`, `Component3`, …), so `event_view`
   is a sequence over one type instead of a tuple over $n$ domains. R1's `well_tagged` and
   `views_surjective` make the two readings equivalent: every well-tagged sequence is the view
   of an event. Arity is bounded by `MAX_ARITY` (8).
2. **Named scoped variables.** Rules bind head variables by name and tails refer to them by
   name and coordinate (`head_scoped`, `regex_scoped`, R2), instead of the paper's positional
   $x_i$; `rule_wf` (R2) is the well-formedness every stored rule satisfies.
3. **Equality up to `eq_spec`.** Component equality in every reviewer-facing statement is
   vstd's `PartialEqSpec::eq_spec` (what the type's `PartialEq` computes), never representation
   equality; `key_laws` requires it to be an equivalence respected by `Hash`.
4. **Require rules are covered too.** `rule_violated` (R2) is "fired and the mode disagrees with
   tail membership" (`violated_by`), so coverage, redundancy and refinement are stated uniformly
   over `forbid` and `require` rules; the paper's definitions treat `forbid`.
5. **Declared domains as a runtime assumption.** Declared finite domains (R3) are supported in
   addition to the paper's infinite domains; verdicts hold for pairs inside them (hypotheses
   above). The paper's $\theta$ is bounded by `u64` in the numeric layer (`n_theta_ok`); history
   values are unbounded.
6. **`GRAPH_BYTES` and `Exhausted`.** The paper's search always answers. Each query's search
   may charge at most `MAX_GRAPH_BYTES` of graph; when a charge fails with
   `HistoryError::GraphBudget` (whose contract is `charged + bytes > budget`) the query returns
   `Inclusion::Exhausted`, about which every R6 `*_spec` claims nothing. Every other error,
   including index overflow (`GraphIndex`), propagates as `Err`, never an invariant failure
   (`no_invariant_failure`). When `Exhausted` is returned is prose in R6's header, not a theorem
   (deviation from the handoff's A5 statement: a ghost token threaded from the failing charge
   into `Exhausted` was judged not worth touching the store, the search and the analyzer at
   once).
7. **`RulePolicy` is unverified glue.** The root crate's `RulePolicy::check` (`src/policy/rules.rs`)
   adds a `could_fire` head filter, one `TracePolicy` per distinct event, decide-then-append,
   audit mode and error-to-deny around the verified `TracePolicy`/`History`; `check_step` covers
   each `TracePolicy::decide`, not this composition (TRUST.md, Unverified glue). The AgentDojo
   evaluation path runs it; the RegExLib path uses declared domains and `tail_included`.
8. **Split.** The implementation emits a smaller partition than the paper's $\mathrm{Split}$:
   per compared component, one case per undecided constant plus one case different from all of
   them. The theorems are stated for every case family satisfying `split_ok`
   (`stmt_paper_split_ok` for the paper's).
9. **Simulation rules.** The code's syntactic simulation relation is smaller than Figure
   `fig:simulation`'s; `sim_step`/`test_step` specify the implemented rules and
   `stmt_sim_rules_sound`/`stmt_test_rules_sound` prove them sound.
10. **Minimality** is global for `tail_included` (`shortest`) and per split case for the policy
    queries (`minimal_in_case` over `shortest_in_case`/`same_profile`, R3): every real instance
    of a counterexample has minimum history length among failing pairs whose candidate agrees
    with it on equality with every known constant (A6).
11. **Rule status and the monitor's decision.** `rule_violated`/`policy_denies`/`least_violation`
    (R2) are definitions; the monitor (`Validator::check`, `CompiledPolicy`, `TracePolicy`)
    returns the first violated rule in source order or grants exactly when none is violated
    (`check_step`, R5). `thm:matcher`'s tail-membership steps are `theorem_not_fired`,
    `theorem_rule_decision`, `theorem_similar_tails_same_decision` over the paper-shaped numeric
    model (`pair_lang`); the final case split by the rule's mode is the definition `violated_by`.
12. **Similarity and normalization.** `theorem_symbolic_derivative_correct` and
    `theorem_symbolic_run_correct` are stated for the symbolic derivative before normalization;
    `theorem_similarity_preserves_language` and `theorem_similar_tails_same_decision` lift it;
    the implemented normalizing constructors (`crates/history-semantics/src/normalize.rs`) are
    verified directly against the language of the expression they build.
13. **Reducing refinement.** Proposition `prop:policy` is not mechanized as stated: refinement is
    reduced rule by rule (`stmt_refines_iff_covers`) and the head constraint is split on the
    covering policy's constants with a constrained inclusion per case (`stmt_policy_reduction`,
    `stmt_policy_search_composition`), without appending the candidate event. Vacuity is decided
    through `at_least_as_strict` with `[]` and `[forbid head Univ]`
    (`stmt_vacuity_via_refinement`, `theorem_vacuity_corollaries`).
14. **Successors.** Lemmas `lem:succ` and `lem:uniform` are one statement over successor cases
    `(Γ', α, q')` (`stmt_successor_cases`); a case's residual is specified up to language
    (`successor_ok`); finiteness of residuals is proved separately (`lemma_emitted_steps` for the
    implementation's enumeration).

## Trusted base

Besides Verus (with `vstd`), Z3 and Rust, the proofs trust the items listed in `TRUST.md`
(181 in the five crates at the last regeneration; 17 more in the verified helper crates
`verus-bumpalo` and `hashconsius`): 19 `assume_specification`s for the standard library and
`smallvec` (tested by `scripts/spec-check.sh`); 70 `external_body` items at native boundaries
(the history store's interior-mutable tables and caches, the runtime policies' callback and
diagnostic adapters, allocation-reservation helpers, the hash-map wrappers); external
type/trait specifications for the `Event` trait, `frunk` coproducts, `smallvec` and `lru`; two
`from_iterator` constructors whose termination is not checked; the 5 `axiom fn`s giving
`hash_coherent` to the library's internal key types; 38 `uninterp` spec fns (the native
values' identities, lock invariants and views; those with a meaning are marked); 16
`derived_eq_claim`s (what `derive(PartialEq)` computes, including `Component2/3/4`); and 19
`unannotated_pub_fn`s outside `verus!`. TRUST.md's "Trusted leaves of the search" names the LRU
successor cache and the hash containers; "Unverified glue" names `RulePolicy::check` and the
root event impls (`event_laws` as hypothesis). No analysis algorithm is trusted; typed
guarantees are conditional on `event_obligations::<E>()`, stated as a hypothesis, with
`hash_coherent::<C>()` the only conjunct no proof discharges.
