# Verus verification of the policy-refinement analysis

The analyzer exposes stored-rule coverage, redundancy, and refinement queries, alongside
`PolicyAnalyzer::tail_included`. This work is rebased onto `main`'s policy-defined arity
(`1..=8`); `VERIFY.md` records the current contracts, hypotheses, and full verification counts.
The prior search proofs were done on an older base (`feat/inclusion-simulation`) and ported onto `main`; the
exact pre-port state is the local branch `wip/verus-refinement-snapshot` (1315 / 1319 verified,
0 errors, on the old base).

## Where things are

| Path | What |
|---|---|
| `crates/history-semantics/src/verify/refinement/` | The frozen specification: one `stmt_*` spec fn per theorem, plus the proofs done so far (`theorem_*`). Layers: `semantics`, `encoding`, `inclusion`, `search`, `pruning`, `finiteness`, `implementation`, `analyzer`. |
| `crates/history-semantics/src/verify/finite_*.rs` | Finiteness of normalized derivatives (paper Lemma 4.2 and Appendix A): the abstract theorem (`finite_states.rs`) and its link to the implemented normalizer and successor computation. |
| `crates/history-semantics/src/{normalize,symbolic,compile,progress}.rs` | Proof-only annotations for the link, plus one approved executable fix (below). |
| `docs/verification/SPEC.md` | The specification document: top-level statement (§0), each layer (§1–§7), proof plan (§8), paper ↔ code differences (§9), the author's frozen decisions (§10), trust base (§11). |
| `docs/verification/finiteness-notes.md` | Working notes of the finiteness mechanization: design of the machine-typing invariant, lemma inventory, pitfalls. |

`SPEC.md` and the notes were written on the author's machine: absolute paths (`/tmp/...`,
`/home/...`) and agent names in them are historical. In `SPEC.md` §10, Q2 was resolved by
option A: the executable fix below is applied (§9 entry 16).

## Executable change

One behavior change, approved and covered by the workspace tests: in `normalize.rs`, the
transition collector merges constant leaves only for intersections
(`TransitionHead::Const(r) if self.intersect => …`). Merging union-valued leaves inside unions
broke finiteness: there is an explicit infinite orbit `f_{n+1} = c & (B + f_n)` without it.
With the fix that orbit saturates after two states. The other non-proof changes
(simulation rules in `history-analysis/src/simulation.rs`, `Constants` codes starting at 1 in
`analyzer.rs`, README wording) implement decisions Q8 and Q9 of `SPEC.md` §10.

## Status

Baseline for the approved proof-completion plan (Verus 0.2026.10.04.426d8b0, Z3 4.16.0,
Rust 1.98.1; all nine CI commands launched with `-- --num-threads 16`):

| Check | Result |
|---|---|
| `history-syntax`, minimal and `serde,std` | passed; cached results, counts not emitted |
| `junco-core`, minimal / `runtime,std,serde` | 163 / 241 verified, 0 errors |
| `history-store`, `runtime` / `runtime,std` | 284 / 284 verified, 0 errors |
| `history-semantics`, `runtime` / `runtime,std,cache` | 1431 / 1436 verified, 0 errors |
| `history-semantics --features runtime,std,cache --test public_specs` | 19 verified, 0 errors |
| `cargo test --locked -p history-analysis` | 13 passed |
| `cargo test --locked -p history-semantics` | passed; 0 tests with default features |
| `cargo test --locked -p history-semantics --features runtime,std,cache` | 42 passed |
| Trust scan of analyzer, semantics `verify/`, and facade | no matches |

The baseline exercised the first nine CI verification commands below; C1 adds the two analyzer
configurations. They may be launched in parallel; Cargo can serialize compilation through the
shared target-directory lock.

On the old base (branch `wip/verus-refinement-snapshot`, pushed alongside) everything verified
as well: 1315 / 1319 functions, history-store 186. During the port, `RegexId::set` (whose body
differs on `main`) needed `#[verifier::spinoff_prover]` and `#[verifier::rlimit(80)]` (84 s in
the `cache` configuration); `derivative_step`, `interpret` and `verify::refinement::inclusion`
needed proof repairs for `main`'s versions of that code. No statement changed.

All 23 frozen `stmt_*` statements now have focused, verified `theorem_*` proofs:

| Layer | Proved | Open |
|---|---|---|
| semantics | `refines_iff_covers`, `redundant_iff_covered`, `genericity` | — |
| encoding | `source_regex_local`, `front_end_denies`, `numeric_genericity` | — |
| inclusion | `paper_split_ok`, `policy_reduction`, `vacuity_reductions` | — |
| search | `successor_cases`, `successor_cases_finite_domains`, `search_correct`, `search_correct_finite_domains`, `search_terminates` | — |
| pruning | `decomposition`, `prune_sound`, `sim_rules_sound`, `test_rules_sound`, `checks_discard` | — |
| finiteness | `lift_injective`, `reachable_states_finite`, `items_from_states` | — |
| analyzer | `choice_exists` | — |

Beyond the statements, the finiteness layer proves that the implemented normalizer satisfies the
abstract contract (`theorem_impl_contract`) and that the implementation has finitely many
reachable items (`theorem_impl_finitely_many_items`) given `cases_follow(m_impl(), cases_of)`,
discharged by the analyzer's retained expansion archive and `theorem_impl_search_bounded`.

All C1–C6 slices and all eleven unfiltered CI verification commands pass with the pinned toolchain.

| Final CI configuration | Result |
|---|---|
| `history-syntax --no-default-features` | cached pass; counts not emitted |
| `history-syntax --features serde,std` | cached pass; counts not emitted |
| `junco-core --no-default-features` | 166 verified, 0 errors |
| `junco-core --features runtime,std,serde` | 247 verified, 0 errors |
| `history-store --no-default-features --features runtime` | 285 verified, 0 errors |
| `history-store --features runtime,std` | 285 verified, 0 errors |
| `history-semantics --no-default-features --features runtime` | 1575 verified, 0 errors |
| `history-semantics --features runtime,std,cache` | 1580 verified, 0 errors |
| `history-semantics --features runtime,std,cache --test public_specs` | 19 verified, 0 errors |
| `history-analysis --no-default-features --features runtime` | 483 verified, 0 errors |
| `history-analysis --no-default-features --features runtime,std` | 483 verified, 0 errors |

Final native checks: analyzer 13 tests passed; enabled-runtime semantics 42 passed; default
semantics test command and `cargo check --locked --workspace --all-targets` passed. The C2
successor-enumeration, value-changing Clone, and validated-vector allocation-reuse probes passed
and were removed. All 23 statement/theorem ensures links are present. The 191 original refinement
spec bodies are mathematically unchanged; three have proof-only trigger annotations adjusted.

C5 combined acceptance: real `search/run/expand` plus search helpers 117 verified, 0 errors;
the complete implementation boundedness theorem module 1 verified, 0 errors. Cases are retained
in ghost evidence independently of successor-cache eviction.

Focused completion: search 27 verified, 0 errors; facade and its ghost module 17 verified,
0 errors, with related store/derivative/atom/successor functions checked separately. The search's
reusable correctness helpers require complete successor cases only for expanded trace nodes;
this permits retained ghost expansion evidence without assuming that the successor LRU never evicts.
Pruning focused acceptance: 13 verified, 0 errors with the default pinned solver; its accepted
draft was removed. Only the padding quantifier's SMT trigger changed; its mathematical body
and all statements are unchanged.
Encoding focused acceptance: 13 verified, 0 errors with the default pinned solver; both accepted
draft files were removed. Recursive mention quantifiers now trigger on closed parent/index
helpers instead of recursive calls; their mathematical bodies and statements are unchanged.
C1 acceptance: analyzer `runtime` and `runtime,std` each 0 verified, 0 errors (native-leaf stage);
bare analyzer tests 13 passed, and workspace/all-targets compatibility passed.
No analyzer algorithm is a trusted leaf; the temporary encoder scaffold was removed by C4.
C2 acceptance: constraint and ghost-view modules 136 verified, 0 errors; all 13 analyzer tests
passed. The throwaway successor smoke proved the two refinements and their exact 2 + 3 letter
class sets, with no classes at the other components, then was removed. Split/letter products
and constraint interning expose explicit size preconditions for the search caller to discharge.
C3 acceptance: tables and table ghost helpers 19 verified, 0 errors; all 13 analyzer tests passed.
Exact source-copy/difference semantics and earlier-root language preservation include errors.
C4 acceptance: frontend 39 verified, 0 errors; analyzer tests 13 passed. Related core metadata:
compile 10, flatten 12, typed 21 verified, all 0 errors.
C6 acceptance: analyzer (including `tail_included` and `decide`) 25 verified, 0 errors; typed
numeric bridge 34, verdict helpers 16, reconstruction helpers 13, native reconstruction 4 and
components 1 verified, all 0 errors. Borrowed-source flattener scope repair: 2 verified, 0 errors.
The value-changing Clone probe now preserves the requested principal, and all 13 analyzer tests
pass. Full integration is covered by the final matrix above.

## Trust

The only new trusted bodies are the author-approved hashbrown wrappers in
`history-analysis/src/native.rs`: `NativeMap`, `NativeSet`, and `NativeGroups`. No new `assume`,
`admit`, or `assume_specification` is introduced. Native-key Eq/hash and ordered-key view
correspondence are explicit hypotheses of `analyzer_obligations`; see `SPEC.md` §11.
The real search consumes `theorem_impl_search_bounded`; `finitely_many_items` is no longer an
undischarged implementation hypothesis. Typed guarantees retain projection/Eq obligations;
`query_capacity` bounds the query's vocabulary so constant ids fit `u32`. Event types choose
one through eight coordinates. Split and letter products check multiplication at each coordinate;
overflow returns `GraphLimit`, which the analyzer reports as `Exhausted`, rather than requiring
a product-capacity precondition. Constraint-id and fresh-value exhaustion remain runtime `Err`s
(`IdExhausted`); see `SPEC.md` §9 item 30. The assumed std and smallvec specifications in junco-core's
`history_assumptions.rs` are tested against the real implementations by
`scripts/spec-check.sh` (`spec-check/`, verus-spec-check; also a CI job).

## Implementation links

- `history-analysis/src/analyzer.rs`: `covered`, `redundant`, and `at_least_as_strict` ensure
  their typed `*_correct` predicates, with every admissible counterexample instance witnessing
  failure and explicit `!covers`/`!refines` under the unrestricted-component infinity premise.
  `tail_included` retains `tail_included_ok`; all four queries exclude internal errors.
- `history-analysis/src/verify/{policy_source,policy_bridge,policy_queries}.rs`: canonical
  numeric rules, whole-policy typed/numeric transport, and executable query composition.
- `history-analysis/src/verify/policy_firing.rs`: exact head firing on split cases.
- `history-semantics/src/verify/refinement/inclusion.rs`:
  `lemma_policy_search_composition` composes split-policy reduction with `outcome_ok`.
- `history-analysis/src/verify/search_exec.rs`: actual result proof consumes the implementation bound.
- `history-analysis/src/search.rs` (`Search::run`): the loop's `decreases` is the item bound of
  `finiteness::theorem_impl_items_bound` (Lemma 4.4 for `m_impl`), via `lemma_running_items_bound`;
  see `SPEC.md` §9 item 31.
- `history-semantics/src/verify/refinement/implementation.rs`: `theorem_impl_search_bounded`.
- `history-analysis/src/verify/reconstruction.rs` and `typed_numeric.rs`: every admissible
  counterexample instantiation and globally shortest history, without a u64 bound on history values.
- `junco-core/src/flatten.rs`: borrowed-source lowering avoids Clone-dependent query semantics;
  the original `flatten_rule` entry point retains its API and verified contract.

## Toolchain and commands

- Verus 0.2026.10.04 (commit `426d8b01e7ff`, same as CI), Rust toolchain `1.98.1-x86_64-unknown-linux-gnu`
  (`RUSTUP_TOOLCHAIN`), Z3 4.16.0 (`VERUS_Z3_PATH`).
- Full verification, as in CI (`.github/workflows/ci.yml`):
  ```sh
  cargo verus verify --locked -p history-syntax --no-default-features
  cargo verus verify --locked -p history-syntax --features serde,std
  cargo verus verify --locked -p junco-core --no-default-features
  cargo verus verify --locked -p junco-core --features runtime,std,serde
  cargo verus verify --locked -p history-store --no-default-features --features runtime
  cargo verus verify --locked -p history-store --features runtime,std
  cargo verus verify --locked -p history-semantics --no-default-features --features runtime
  cargo verus verify --locked -p history-semantics --features runtime,std,cache
  cargo verus verify --locked -p history-semantics --features runtime,std,cache --test public_specs
  cargo verus verify --locked -p history-analysis --no-default-features --features runtime
  cargo verus verify --locked -p history-analysis --no-default-features --features runtime,std
  ```
  Append `-- --num-threads N` to use more cores (default 1). On the author's 2-core machine each
  `history-semantics` configuration took about 4.5 minutes with 2 threads.
- Assumed specifications against std and smallvec: `scripts/spec-check.sh` (fetches the
  verus-spec-check release paired with the pinned Verus into `spec-check/vendor/`).
- Focused verification of one module or function (`cargo verus verify` refuses partial runs):
  ```sh
  rm -rf target/verus-partial/debug/.fingerprint/history-semantics-*
  cargo verus focus --locked -p history-semantics --no-default-features --features runtime -- \
      --verify-only-module verify::refinement::search [--verify-function theorem_x] --triggers-mode silent
  ```
- Tests: `cargo test --locked -p history-analysis` and `-p history-semantics`.

## Conventions the proofs so far followed

- No executable-behavior change without the author's approval; spec, proof and ghost code only.
- Never change a `stmt_*` statement or a definition it depends on. If one looks false, record a
  counterexample and raise it.
- SMT trigger/unfolding annotations may be repaired without changing any mathematical body.
- No new trust (see above).
- New proof files go under `verify/refinement/` (or `verify/finite_*`) and are registered in the
  corresponding `mod.rs`.

## Verus pitfalls met so far

- vstd `Set` is always finite and `Set::new` returns `Option`; use `ISet` with `finite()` and
  `Set::new_from_iset`.
- Triggers cannot contain `seq![..]`/`set![..]` literals or boolean operators.
- Never put a trigger on a recursive call inside a recursive spec body (fuel mismatch); use a
  least-fixpoint form or index triggers such as `#![trigger cs[i]]`.
- `#[trigger]` inside closure-call arguments is ignored; use `#![trigger vs[i]]`.
- Large open spec functions in exec contexts blew the rlimit; make them opaque and reveal in
  lemmas (see `finite_steps.rs`).

## Paper ↔ code names for the finiteness conditions

The paper's Appendix A now names the conditions; the code and `SPEC.md` still use the numbers.

| Code / SPEC | Paper |
|---|---|
| (N0) | Parts, Fixed |
| (N1), (N2), (N3) | UnionForm, InterForm, NotForm |
| (N4), (N4′) | CatForm, Regroup |
| (N5) | FiniteTests |
| (S0) | SuccEval |
| (S1) | SuccBase |
| (S2)–(S6) | SuccUnion, SuccInter, SuccNot, SuccStar, SuccList |
| (C1)–(C4) | Finite, Closed, OpClosed, ListClosed |
| `C(q)` | Bound(q) |

On 2026-11-08 the paper's SuccUnion, SuccStar and SuccList were stated in stronger forms (the
sets inside `Cl_+` rather than their closures, the products of a union as the union of the
operands' products), which the appendix's justification proves. Compare them with (S2), (S5)
and (S6) as mechanized before claiming that the mechanization matches the paper.

Other differences between the mechanization and the paper's Appendix A: the successor
equations are not separate lemmas but follow from one bound per constructor kind (the largest
relations the equations allow); collapsing equal branches and pruning are covered only through
those bounds; and the set normalizer is a relation (`Model.nset` in `finite_states.rs`) where the
paper has a function. Evidence for the executable fix is in `finiteness-fix-evidence.md`.
