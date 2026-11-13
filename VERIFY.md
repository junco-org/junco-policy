# Checking the mechanized proofs

This repository contains the Junco policy checker and policy analyzer together with their
Verus proofs. This file explains how to re-run the proofs, where each result of the paper is
proved, which hypotheses the proved statements make, and where the mechanization differs from
the paper.

The specification and proofs of the policy analysis (Sections 4–5 and Appendices A–C of the
paper) are in `crates/history-semantics/src/verify/refinement/`. Each paper result is a
`stmt_*` spec function that states the proposition, proved by a `theorem_*` proof function
with `ensures stmt_*()`. The results of Section 4 on derivatives and the matcher are proof
functions in `crates/history-semantics/src/verify/history_algebra.rs`. The executable
analyzer in `crates/history-analysis/` is verified against these specifications.

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

# Check the toolchain and print the eleven commands without running them.
scripts/verify-all.sh --list

# Pass arguments to Verus in every command, e.g. to use more cores.
scripts/verify-all.sh -- --num-threads 8
```

`scripts/verify-all.sh` checks the Verus, Z3 and Rust versions, runs `cargo fetch --locked`, and
then runs the same eleven `cargo verus verify --locked` configurations as the `verify-core`
job of `.github/workflows/ci.yml` (no module filter: every verified function of each package
and of its verified dependencies). It prints a table of verified-function and error counts per
configuration and exits nonzero if any configuration fails. The `rustup` toolchain must be
installed:
`rustup toolchain install 1.98.1-x86_64-unknown-linux-gnu --profile minimal --component rustc-dev --component llvm-tools`.
On a 2-core machine with 7 GB of memory, a full run with `-- --num-threads 2` takes about
41 minutes. Verus's memory use grows with the thread count: with 16 threads on that machine
the verifier was killed for running out of memory (reported as `signal: 9, SIGKILL`), so keep
the thread count near the number of cores when memory is limited.

`scripts/trust-scan.sh > TRUST.md` regenerates `TRUST.md`, the inventory of every place where
the proofs assume rather than prove a fact: `assume_specification`, `external_body`, external
type/trait specifications, `#[verifier::external]`, `admit`, `assume`, and functions whose
termination is not checked. There are no `admit`s or `assume`s.

`scripts/spec-check.sh` tests the `assume_specification`s for the standard library and
`smallvec` (`crates/junco-core/src/verify/history_assumptions.rs`) against the real
implementations with the `verus-spec-check` tool. It clones that tool's release paired with the
pinned Verus into `spec-check/vendor/` on first use (network access required).

## Expected results

| Configuration (`cargo verus verify --locked ...`) | Result |
|---|---|
| `-p history-syntax --no-default-features` | 55 verified, 0 errors |
| `-p history-syntax --features serde,std` | 55 verified, 0 errors |
| `-p junco-core --no-default-features` | 164 verified, 0 errors |
| `-p junco-core --features runtime,std,serde` | 248 verified, 0 errors |
| `-p history-store --no-default-features --features runtime` | 287 verified, 0 errors |
| `-p history-store --features runtime,std` | 287 verified, 0 errors |
| `-p history-semantics --no-default-features --features runtime` | 1615 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache` | 1620 verified, 0 errors |
| `-p history-semantics --features runtime,std,cache --test public_specs` | 21 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime` | 570 verified, 0 errors |
| `-p history-analysis --no-default-features --features runtime,std` | 570 verified, 0 errors |

These counts are from the pinned toolchain with `-- --num-threads 144 --triggers-mode silent`.
The full gate also passes on the completed model/firing and typed-policy bridge snapshots.
`cargo test --workspace` passes (196 tests across 24 suites). The differential suite includes
444 policy queries and 900 tail queries; separate executable smoke runs cover Alice/Bob,
constant-book growth between queries, duplicate removal, and arities 1 and 8.
The per-case minimality smoke also observes a two-event Alice witness even though Bob has a
one-event witness: all three policy queries are shortest within the returned profile, not
globally across candidate cases.

## Paper results and their mechanized statements

Paths are relative to `crates/history-semantics/src/verify/` unless they start with `crates/`.
Results marked † assume infinite component domains (`n_unrestricted`, see below).

| Paper result | Mechanized statement | File |
|---|---|---|
| Proposition Similarity preserves language (`lem:similarity-language`) | `theorem_similarity_preserves_language` | `history_algebra.rs` |
| Lemma One-step correctness (`lem:sderiv`) | `theorem_symbolic_derivative_correct` | `history_algebra.rs` |
| Theorem Symbolic derivative correctness (`thm:sderiv`) | `theorem_matcher_correct` | `history_algebra.rs` |
| Theorem Matcher correctness (`thm:matcher`) | `theorem_not_fired` (step 1), `theorem_rule_decision` (steps 2–3), `theorem_similar_tails_same_decision` (normalization) | `history_algebra.rs` |
| Lemma Finitely many residuals (`lem:finite-states`) | `stmt_reachable_states_finite` / `theorem_reachable_states_finite`; for the implementation: `theorem_impl_contract`, `theorem_impl_finitely_many_items` | `refinement/finiteness.rs`, `finite_impl.rs` |
| Reductions of refinement, redundancy and vacuity (appendix `app:policy-reduction`) | `stmt_refines_iff_covers`, `stmt_redundant_iff_covered`; `stmt_vacuity_reductions` | `refinement/semantics.rs`; `refinement/inclusion.rs` |
| Proposition Refinement as inclusion (`prop:policy`) | not mechanized as stated; the equivalent rule-by-rule reduction `stmt_policy_reduction` (difference 9 below) | `refinement/inclusion.rs` |
| Lemmas Computing successors (`lem:succ`) and Uniform reachability (`lem:uniform`)† | `stmt_successor_cases` (one statement over successor cases, difference 10 below); for the implementation, `expansion_ok` | `refinement/search.rs`, `refinement/implementation.rs` |
| Theorem Inclusion search correctness (`thm:search`)† | `stmt_search_correct` (soundness, completeness, minimality), `stmt_search_terminates` (termination); for the implementation, `theorem_impl_search_bounded` and `lemma_running_outcome` | `refinement/search.rs`, `refinement/implementation.rs`, `crates/history-analysis/src/verify/search_exec.rs` |
| Equation decomposition (`eq:decomposition`) | `stmt_decomposition` | `refinement/pruning.rs` |
| Lemma Pruning soundness (`lem:prune`) | `stmt_prune_sound`, `stmt_checks_discard` | `refinement/pruning.rs` |
| Lemma Simulation soundness (`lem:simulation`) | `stmt_sim_rules_sound`, `stmt_test_rules_sound` | `refinement/pruning.rs` |
| Executable analyzer (Section 6) | `covered`, `redundant`, and `at_least_as_strict` ensure typed correctness and per-case minimality (`*_ok`); `tail_included` retains `tail_included_ok`; errors exclude internal failures and search terminates by the implemented finite-item bound | `refinement/analyzer.rs`, `refinement/inclusion.rs`; `crates/history-analysis/src/analyzer.rs`, `verify/{verdict,policy_bridge,policy_queries,policy_case_profile,policy_minimality}.rs` |

Each `stmt_X` above is proved by `theorem_X` in the same file. The remaining statements of the
`refinement/` layer are auxiliary: `stmt_genericity` and `stmt_numeric_genericity` (renaming
invariance, used to read counterexamples with fresh values), `stmt_source_regex_local` and
`stmt_front_end_denies` (the typed-to-numeric encoding), `stmt_paper_split_ok` (the paper's
Split satisfies `split_ok`), `stmt_lift_injective` and `stmt_items_from_states` (finiteness),
`stmt_choice_exists` (counterexamples can be instantiated), and the `*_finite_domains`
extensions described below.

## Paper notation and specification names

All names are in `crates/history-semantics/src/verify/refinement/`.

| Paper | Specification | File |
|---|---|---|
| $\mathcal{L}_\theta(r)$ | `n_lang` | `encoding.rs` |
| rule violation, policy violation (`def:violates`, `def:policy-violates`) | `Status`, `rule_status`, `rule_denies`, `policy_denies` | `semantics.rs` |
| constraint $\Gamma$ | `Constraint` (a set of `Literal`s) | `inclusion.rs` |
| $\Gamma' \models \Gamma$ | `entails` | `inclusion.rs` |
| $\Gamma$ decides $x_c = v$ | `decides` | `inclusion.rs` |
| $\mathrm{Split}(\Gamma; \Pi)$ | `paper_split`; what the theorems require of a split: `split_ok` | `inclusion.rs` |
| $r \sqsubseteq_\Gamma s$ | `included_under` | `inclusion.rs` |
| head constraint $\Gamma_h$ | `head_constraint` | `inclusion.rs` |
| $P$ covers $R$ | `n_covers` | `inclusion.rs` |
| item $(\Gamma, q)$ | `Item` | `search.rs` |
| witnesses $W(I)$ | `witness` | `search.rs` |
| $(\theta, e)$ realizes $\alpha$ | `realizes` | `search.rs` |
| successors $\mathrm{succ}(\Gamma, q)$ (`def:successors`) | the items of `paper_steps`; the conclusion of Lemmas `lem:succ` and `lem:uniform`: `steps_ok` | `search.rs` |
| successor case: a successor $(\Gamma', q')$ with its assignment $\alpha$ | `Case { constraint, alpha, next }` | `search.rs` |
| $\theta \vdash I \overset{e}{\leadsto} J$ ($e$ reaches $J$ from $I$ under $\theta$) | `sat_by(theta, c.constraint) && realizes(theta, e, c.alpha)` for a case `c` of `I` with `case_item(c) == J` | `search.rs` |
| search result | `Outcome`, `outcome_ok` | `search.rs` |
| dead item, domination $J \preceq I$ | `dead`, `dominated` | `pruning.rs` |
| syntactic simulation $\sqsubseteq$ | `sim_step` (the rules), `sim_sound` (soundness of a relation) | `pruning.rs` |

## Hypotheses of the proved statements

- **Infinite domains.** `stmt_successor_cases` and `stmt_search_correct` assume
  `n_unrestricted(d)`: no component has a declared finite domain, as the paper assumes. The
  variants `stmt_successor_cases_finite_domains` and `stmt_search_correct_finite_domains` drop
  this hypothesis for declared finite domains, which the paper does not treat.
- **Component-local atoms.** `stmt_successor_cases` assumes `atoms_local(atoms)`: an atom compares
  a component of an event only with the same component of the candidate, as in the paper's
  event model. The analyzer's atoms satisfy it by construction (`atom` in
  `crates/history-analysis/src/search.rs` ensures `atoms_local`).
- **Termination.** `stmt_search_terminates` is conditional on `finitely_many_items`: the search
  is bounded when finitely many items are reachable. For the implementation this is discharged:
  `theorem_impl_finitely_many_items` proves it for the implemented normalizer and successor
  function (via `theorem_impl_contract`) for every case function that follows implemented steps
  (`cases_follow`); the executed search maintains this as the loop invariant `archive_follows`
  (`running` in `crates/history-analysis/src/verify/search_exec.rs`), and
  `theorem_impl_items_bound` gives one finite item set, fixed before the loop, whose size is the
  `decreases` measure of the real search loop (`Search::run` in
  `crates/history-analysis/src/search.rs`); `lemma_running_outcome` gives the same bound for
  every returned outcome.
- **Executable analyzer.** Queries require `analyzer_obligations::<E>()`: stable event projections
  and equality/hashing consistent with their models. Stored-rule queries also require valid
  `RuleId` indices. `add_rule_capacity` and `query_capacity` bound constant-id allocation for
  registration and the borrowed tail query; stored-policy queries add no vocabulary-capacity
  premise. Cartesian-product overflows are checked runtime errors.
- **Nonvacuous counterexamples.** Policy queries additionally require
  `unrestricted_components_infinite`: `infinite_type::<E::Component>()` if any coordinate has no
  declared domain. No infinity premise is needed when all coordinates have declared finite
  domains. `lemma_choice_exists_mixed` and reconstruction establish `cex_has_instance`; a
  counterexample explicitly entails `!covers` or `!refines`, and every admissible instantiation
  witnesses the failure. The standalone `*_correct` predicates retain the earlier vacuous
  meaning on unrestricted types with too few fresh values.

## Differences between the paper and the mechanization

1. **Events and valuations.** Each event type chooses its arity, from 1 to `MAX_ARITY` (8),
   instead of an arbitrary $n$. In the numeric layer the candidate's values are bounded by
   `u64` (`n_theta_ok`); history values are unbounded. Declared finite domains are supported
   in addition to the paper's infinite domains (see Hypotheses).
2. **Split.** The implementation emits a smaller partition than the paper's
   $\mathrm{Split}$: per compared component, one case per undecided constant plus one case
   different from all of them. The theorems are stated for every case family satisfying
   `split_ok`, which includes both (`stmt_paper_split_ok` for the paper's).
3. **Exhaustion and errors.** The paper's search always answers. The mechanized search and the
   implementation may stop with `Exhausted` under a resource budget (the analyzer charges each
   search at most 16 MiB of graph), and the implementation may return an error (`Err`, e.g. on
   an id overflow). `*_correct`, `tail_included_ok`, and `outcome_ok` claim nothing about
   `Exhausted`. Policy queries ensure `no_internal_error`; `tail_included` and `add_rule` ensure
   `no_internal_compile_error`. Invalid-input and resource errors remain possible. The search's
   existing success contract is unchanged; its additional error guarantee is conditional on
   component-local primitives with constant codes fitting `u32`, proved for analyzer inputs.
4. **Simulation rules.** The implemented syntactic simulation has more rules than the paper's
   figure (`fig:simulation`): recursive rules for conjunctions and disjunctions of tests on
   either side, `x ⊑ Star(b)` from `x ⊑ b`, and padding with several `All` factors.
   `sim_step` and `test_step` specify the implemented rules, and `stmt_sim_rules_sound` and
   `stmt_test_rules_sound` prove them sound.
5. **Minimality** is global for `tail_included` (`shortest`) and case-local for policy queries
   (`shortest_in_case`, `same_profile`). `covered`, `redundant`, and `at_least_as_strict` ensure
   `*_ok = *_correct && *_minimal`: every admissible counterexample instance has minimum history
   length among failing pairs with its constant profile. Refinement uses the same denying rule
   for correctness and shortestness. The proof transfers the initial search case's numeric
   length bound through known-code equality reflection; it does not confuse the initial split
   constraint with the stronger reconstructed refutation constraint.
6. **Rule status and policy decisions.** Both are specified. For the analysis, `semantics.rs`
   defines `Status`, `rule_status` (`def:violates`) and `policy_denies` (some rule is violated;
   `def:policy-violates`),
   over which `stmt_refines_iff_covers` and `stmt_redundant_iff_covered` are stated; the numeric
   `n_rule_denies` and `n_policy_denies` (`encoding.rs`, related to the typed ones by
   `stmt_front_end_denies`) are used by `stmt_policy_reduction` and `stmt_vacuity_reductions`.
   For the runtime checker, the verified `Validator`, `CompiledPolicy` and `TracePolicy` return
   the first violated rule in source order, or none exactly when no rule is violated
   (`ordered_result` and `least_violation` in `crates/history-semantics/src/compiled_rule.rs`,
   over `rule_violated` in `crates/junco-core/src/verify/dsl.rs`). The theorems for Matcher
   correctness (`theorem_rule_decision`, `theorem_not_fired`) are stated over the paper-shaped
   numeric model (`pair_lang` in `crates/junco-core/src/verify/history_specs.rs`) and prove the
   tail-membership steps; the final case split from membership to `Violated`/`Satisfied` by the
   rule's mode is a definition (`violated_by`, `rule_violated`), not a separate theorem.
7. **Executable policy queries.** `add_rule` stores validated rules with stable `RuleId` indices,
   retaining verified encodings as the constant book grows. `covered`, `redundant`, and
   `at_least_as_strict` return `Inclusion` and ensure `covered_ok`, `redundant_ok`, and
   `at_least_as_strict_ok`, respectively, including explicit negated properties for
   counterexamples under the stated nonvacuity hypothesis. `tail_included` remains available
   without registration. `never_fires` and `always_fires` remain specification-only and are
   outside this artifact's executable policy-query work.
   `redundant` additionally ensures `policy_removal::redundant_decisions_ok`: `Holds` means
   removing every target id preserves every deny/permit decision. `lemma_removal_iff_covered`
   instantiates `stmt_redundant_iff_covered` after an exact id-filter denial lemma handles
   arbitrary order and duplicate ids. When the target is present, every counterexample instance
   is denied before removal and permitted afterward, explicitly refuting decision preservation.
   If the target is absent, the API keeps its coverage-query meaning; a coverage counterexample
   is not claimed to change an already target-free policy.
8. **Similarity and normalization.** `theorem_symbolic_derivative_correct` and
   `theorem_matcher_correct` are stated for the symbolic derivative before normalization.
   `theorem_similarity_preserves_language` proves that the similarity equations preserve
   languages, and `theorem_similar_tails_same_decision` lifts this to rule decisions. The
   implemented normalizing constructors in `crates/history-semantics/src/normalize.rs`, which
   also apply rewrites that are not similarity equations, are verified directly: each
   constructor's contract states that its result has the language of the expression it builds.
9. **Reducing refinement.** The paper's Proposition `prop:policy` reduces refinement to one
   inclusion between denial expressions, which append the candidate to the history and test it
   with $\pi = x$. The mechanization instead reduces refinement rule by rule
   (`stmt_refines_iff_covers`) and avoids the extra event: for a rule `R`, it splits the head
   constraint $\Gamma_R$ on the head constants of the covering policy and, for each case
   $\Gamma'$, checks the constrained inclusion of `R`'s denial tail in the union of the denial
   tails of the rules whose heads $\Gamma'$ entails (`stmt_policy_reduction`,
   `firing_denials`). `lemma_policy_search_composition` connects this reduction to the proved
   `outcome_ok` search contracts: all cases `Holds` imply coverage; a refuted case supplies every
   uncovered realization and explicit numeric noncoverage, including declared finite domains.
   The executable firing test is exact on split cases, including different heads and both rule
   modes. The typed-policy bridge transports these results to the entry-point contracts.
   This avoids appending a candidate event; Proposition 5.2 itself remains outside scope.
10. **Successors.** The paper defines successors semantically as the items reached by a
    candidate and an event (`def:successors`), computes them with Algorithm `alg:succ`, and
    states Lemmas `lem:succ` and `lem:uniform`. The mechanization states both lemmas as one
    statement over successor cases `(Γ', α, q')`, which also record the atom assignment; the
    search keeps `α` to reconstruct counterexamples. A case's residual is specified up to
    language (`successor_ok`), which suffices for search correctness; finiteness of residuals is
    proved separately. The implementation's enumeration (per-register value options, declared
    finite domains) differs from Algorithm `alg:succ` and is verified to emit cases satisfying
    the same specification (`expansion_ok`).

## Trusted base

Besides Verus (with `vstd`), Z3 and Rust, the proofs trust the items listed in `TRUST.md`:
specifications of standard-library and `smallvec` operations (tested by
`scripts/spec-check.sh`); external bodies at native boundaries (the history store's
interior-mutable tables and caches, callback and diagnostic adapters of the runtime policies,
allocation-reservation helpers, and the analyzer's hash-map wrappers in
`crates/history-analysis/src/native.rs`); external specifications of the `Event` trait and of
`frunk` coproduct and `smallvec`/`lru` types; and two `from_iterator` constructors whose
termination is not checked. The verified helper crates `verus-bumpalo` and `hashconsius`
(arena allocation and hash-consing) are verified together with `history-store` and have their
own trusted items. No analysis algorithm is trusted. Typed guarantees are conditional on the
event type's projection and equality/hashing laws, stated as explicit hypotheses
(`native_obligations`, `key_obligations`, `analyzer_obligations`), not assumed.
