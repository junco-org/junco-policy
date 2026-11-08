# Verus verification of the policy-refinement analysis: handoff

This branch (`handoff/verus-proofs`, based on `main`) carries the machine-checked part of the
paper's policy-inclusion analysis that exists so far, plus everything needed to continue it.
The work was done on an older base (`feat/inclusion-simulation`) and ported onto `main`; the
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
| `docs/verification/drafts/` | Unverified drafts for slices 2 and 4 (see below). Not compiled. |

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

State at handoff (2026-11-08, after porting onto `main`, `-- --num-threads 2`):

| Check | Result |
|---|---|
| `history-semantics --features runtime,std,cache` | 1436 verified, 0 errors |
| `history-semantics --no-default-features --features runtime` | 1431 verified, 0 errors |
| `history-store --features runtime,std` | 284 verified, 0 errors |
| `history-store --no-default-features --features runtime` | 0 errors (cargo reused a cached result) |
| `cargo test -p history-analysis` | 13 passed |
| `junco-core`, `history-syntax` | not re-verified: byte-identical to `main` |
| `cargo test -p history-semantics`, fmt, clippy | not run |

Run the full CI list (below) first. The eight CI verify commands are independent and can run in
parallel on a machine with enough memory.

On the old base (branch `wip/verus-refinement-snapshot`, pushed alongside) everything verified
as well: 1315 / 1319 functions, history-store 186. During the port, `RegexId::set` (whose body
differs on `main`) needed `#[verifier::spinoff_prover]` and `#[verifier::rlimit(80)]` (84 s in
the `cache` configuration); `derivative_step`, `interpret` and `verify::refinement::inclusion`
needed proof repairs for `main`'s versions of that code. No statement changed.

Statements of the spec (`stmt_*`, 23 in total):

| Layer | Proved | Open |
|---|---|---|
| semantics | `refines_iff_covers`, `redundant_iff_covered`, `genericity` | — |
| encoding | — | `source_regex_local`, `front_end_denies`, `numeric_genericity` (drafts exist) |
| inclusion | `paper_split_ok`, `policy_reduction`, `vacuity_reductions` | — |
| search | — | `successor_cases`, `successor_cases_finite_domains`, `search_correct`, `search_correct_finite_domains`, `search_terminates` |
| pruning | — | `decomposition`, `prune_sound`, `sim_rules_sound`, `test_rules_sound`, `checks_discard` (partial draft) |
| finiteness | `lift_injective`, `reachable_states_finite`, `items_from_states` | — |
| analyzer | `choice_exists` | — |

Beyond the statements, the finiteness layer proves that the implemented normalizer satisfies the
abstract contract (`theorem_impl_contract`) and that the implementation has finitely many
reachable items (`theorem_impl_finitely_many_items`) given `cases_follow(m_impl(), cases_of)`,
which slice 6 discharges from the analyzer's search via `lemma_impl_successor_abstracts`.

Not started: bringing `history-analysis` under Verus (decision Q1), the implementation link, and
the exec postconditions of `SPEC.md` §0.

## Trust

No new `assume`, `admit`, `external_body`, `assume_specification` or `#[verifier::external]`.
Open hypotheses:
- `search::finitely_many_items` in `stmt_search_terminates` (statement unchanged; discharged for
  the implementation as described above once `cases_follow` is proved);
- typed guarantees are conditional on `books::native_obligations` (and `eq_equivalence`, implied
  by them) and on the `FlatEncoder` obligation for the analyzer's `Constants` (decision Q4).

## Remaining work

| # | Slice | Depends on | Notes |
|---|---|---|---|
| 2 | Encoding (3 statements) | — | `drafts/encoding.rs.draft` drafts all three theorems; last focused run had 3 compile errors, fixed, not re-run. See `drafts/encoding-notes.md`. Old base: re-check against `main`'s `junco-core` encoding lemmas. |
| 3 | Search (5 statements, paper Lemma 5.3 / Theorem 5.5) | finiteness (done) for termination | Correctness can proceed independently. |
| 4 | Pruning (5 statements) | — | `drafts/pruning.rs.draft`: helper lemmas (`lemma_union_ops_lang`, `lemma_inter_ops_lang`, `lemma_decomposition`, …), never compiled. |
| 5 | `history-analysis` under Verus | — | Largest and least predictable. |
| 6 | Implementation link + §0 postconditions; `cases_follow(m_impl(), cases_of)` | 2–5 | |
| 7 | Finite-domain variants (`*_finite_domains`) | 2–4 | Partly inside slice 3. |

Slices 2, 3, 4 and 5 touch disjoint files and can run in parallel.

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
  ```
  Append `-- --num-threads N` to use more cores (default 1). On the author's 2-core machine each
  `history-semantics` configuration took about 4.5 minutes with 2 threads.
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
