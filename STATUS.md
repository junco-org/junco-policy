# STATUS — [attempt B] Reviewer-readable mechanization

Integration branch: `refactor-reviewer-surface-b` (from `origin/handoff/reviewer-surface-b` @ `46621e4`).
Plan: `local://reviewer-surface-b-plan.md` (integration owner's copy). Deleted in the last commit before the PR.

## Wave / tracks

| Track | State | Branch | Notes |
|---|---|---|---|
| 0 | done | integration | 0.0–0.4 and M4 done at `b18250c`; M5 deferred to Track T; timing table below |
| G | merged `036ddad` | `track/g-b` | singleton axiom gone; dead `mem::replace` spec gone; `Arc`/`&T` identity documented (no coincidence possible for the compared singleton types); trust-scan kinds `uninterp`/`derived_eq_claim`/`unannotated_pub_fn` + helper crates; D2 benches without `test-util` (CI test step now `--features junco-policy/test-util`; bench numbers moved because counters are compiled out) |
| E | merged `6d42297` | `track/e-b` | `verify/paper.rs` index (14 statements), `stmt_/theorem_` convention, named finiteness conditions, `expansion_ok`/`covered_with_ok`/`n_unrestricted` deleted; needs two one-token edits at B's merge (`::<C>` → `::<E>` in `stmt_app_policy_reduction`/`theorem_paper_index`) |
| C | gate FAILED on `history-semantics --no-default-features --features runtime` (1 error; the std configuration passes); reproducing on the rebased branch | `track/c-b` | `GraphLimit` → `GraphBudget { limit }` + `GraphIndex`; `charge`/`projected` ensure `charged + bytes > budget` on `GraphBudget`; `search`'s budget error is by construction (single constructor), not a spec; `TransitionAction::step` rlimit 30 → 40 |
| D | merged `cc53150` | `track/d-b` | `Validator` `View`/closed `wf`, R5 contracts on `check`/`permits`/`rollback`/`finish`, `trace_safe` lemmas, `policy_permits` in `CompiledPolicy`/`TracePolicy`, `TraceRule::clone` source equality (external_body claim, TRUST note), arity-3 `requires`; `public_specs` 19 (two statements moved by F) |
| A | reported `ba3c1cf`, merge pending (after C) | `track/a-b` | `PartialEqSpecImpl` for `Component2/3/4`; `event_laws` witnesses; `junco_core::verify::hypotheses` lemmas (`hash_coherent::<C>()` the only premise); internal-key `*_obligations()` discharged by the five axioms; `analyzer_obligations == event_obligations` |
| F-prep | reported `4792853`, merge pending (after A) | `track/f-b` | closed `wf`, ghost `declared`/`known` set by contract, verified `Domains::{infinite,with_domain}` with `DomainError`, R6 capacities in `requires`, `RuleId` owner tags + `UnknownId`, vacuity via refinement; `never_fires_ok`/`always_fires_ok` deletion left to B (file deleted on B) |
| B | running | `track/{a,b,c,d,f}-b` from `0f71984` | wave 1; B absorbed the verdict half of `refinement/analyzer.rs`, `policy_removal.rs`, `verify/{policy_minimality,policy_case_profile,policy_queries}.rs`, the four query `ensures` and `impl View for PolicyAnalyzer` (F keeps `new`/`with_domain`/capacities/RuleId ownership/vacuity/opaque `wf`); F adds ghost `declared`/`known` fields set by contract |
| F | not started | `track/f-b` | wave 2 |
| T | not started | `track/t-b` | wave 3 |

## Last gate results

Each gate: the five full-feature `cargo verus verify` configurations of `scripts/verify-all.sh --list` plus `--test public_specs`, concurrently through the personal runner (6 jobs x 42 threads); then `cargo fmt --check`, `cargo clippy --locked --no-deps --all-targets -D warnings`, `cargo test --locked` for the six packages.

| step | head | syntax | core | store | semantics | public_specs | analysis | fmt/clippy/test | wall |
|---|---|---:|---:|---:|---:|---:|---:|---|---:|
| PR #10 merge | `3e30f33` | cached | cached | cached | 1620/0 | 21/0 | 570/0 | ok / ok / 196 pass | 138 s |
| M1 rename | `a484553` | cached | 248/0 | 287/0 | 1620/0 | 21/0 | 570/0 | ok / ok / 196 pass | 167 s |
| M2 R1 move | `32a418b` | 55/0 | 248/0 | 287/0 | 1620/0 | 21/0 | 570/0 | ok / ok / 196 pass | 171 s |
| M3 R2 move | `595708e` | cached | 249/0 | 287/0 | 1620/0 | 21/0 | 570/0 | ok / ok / 196 pass | 166 s |
| 0.4 R1–R6 | `b981486` | 55/0 | 249/0 | 287/0 | 1620/0 | 21/0 | 571/0 | ok / ok / 196 pass | 172 s |
| M4 R4 cutover | `b18250c` | 55/0 | 249/0 | 287/0 | 1620/0 | 21/0 | 571/0 | ok / ok / 196 pass | 170 s |
| no-default configs on `0f71984` (INBOX request) | `0f71984` | FAIL (vstd `std_specs::hash` needs `std`) ×5 | | | | | | | 271 s |
| G merge | `036ddad` | 55/0 ×2 | 170/0, 254/0 | 287/0 ×2 | 1615/0, 1620/0 | 21/0 | 571/0 ×2 | ok / ok / 194 pass | 218 s |
| E merge | `6d42297` | cached | 254/0 | 287/0 ×2 | 1632/0, 1637/0 | 21/0 | 571/0 ×2 | ok / ok / 194 pass | 218 s |
| D merge | `cc53150` | cached | 170/0, 254/0 | 287/0 ×2 | 1635/0, 1640/0 | 19/0 | 571/0 ×2 | ok / ok / 194 pass | 218 s |
| INBOX fix, all eleven | `d0f700d` | 55/0, 55/0 | 170/0, 254/0 | 287/0, 287/0 | 1615/0, 1620/0 | 21/0 | 571/0, 570/1 (rlimit in `normalize_pieces`, fixed by `rlimit(20)`: 571/0 on re-run) | ok / ok / 196 pass | 308 s |

M3 needed two proof repairs after the first gate: `lemma_trace_decision_result` (the Deny clause now states `least_violation` directly) and a broadcast lemma `junco_core::verify::dsl::lemma_rule_views_index` (`rule_views(rules)[i] == rules[i]@`) that `public_specs` uses.

PR #10 merge gate @ `3e30f33` (2026-11-13): full-feature configs of all five crates + `public_specs`, run concurrently via the personal runner (6 jobs x 42 threads): history-syntax/junco-core/history-store cached (unchanged by the merge), `history-semantics --features runtime,std,cache` 1620 verified / 0 errors, `--test public_specs` 21 / 0, `history-analysis --no-default-features --features runtime,std` 570 / 0; wall 138 s. `cargo fmt --check`, `cargo clippy -D warnings`, `cargo test` for the six packages: pass.

PR #10 commit integrated: `52118c4`.

## Blockers

(none)

## Decisions deviated from the plan

- 2026-11-13 A5 (`Exhausted`): `Exhausted` is vacuous in every R6 `*_spec`; A5 is prose in R6's header (`Exhausted` only on `Err(GraphBudget)` from `charge`, whose contract is `charged + bytes > budget` after Track C). This differs from the handoff's target A5 as a statement. Not adopting the unforgeable-token form: it needs a ghost token constructed only by the store's failing charge, threaded through `search` into `Exhausted`, touching Tracks C, F and the store at once; if the maintainer wants it, it is a follow-up after wave 2 (Track F's wave-2 brief forbids ghost numbers chosen by the implementation).

- 2026-11-13 M5 (hygiene renames `lang → numeric_lang` in `junco_core::verify::history_specs`, `flat::verify::lang → flat_lang`, `error.rs → errors.rs`) is **deferred to Track T** (wave 3). The numeric `lang` has ~700 call sites, 450 of them in `normalize.rs`, `history_algebra.rs`, `symbolic.rs`, which Tracks B and F edit heavily in waves 1–2; renaming first would force every track branch through conflicts. Track T does the three renames when no other track is open. Nothing else depends on the order.
- 2026-11-13 M4 adds the eight `axiom fn`s (vstd `obeys_key_model` for `Component2/3/4`, `RegexId`, `TestId`, pairs, `SmallVec<[RegexId; 4]>`, `Constraint`) as Verus `broadcast axiom fn`s rather than `external_body` proof fns, and `scripts/trust-scan.sh` gains an `axiom` kind so TRUST.md lists them (8 in the total). `search_obligations`/`memo_obligations`/`parts_key_obligations` stay as hypotheses of the analyzer contract until Track F discharges them with the axioms.
- 2026-11-13 R3 `domains_wf` and R6 `analyzer_wf` do not state `Set::finite`: the pinned vstd's `Set` is finite by construction (`ISet` is the infinite one).

- 2026-11-13: branch name `refactor/reviewer-surface-b` is impossible: a branch `refactor` exists locally and on origin (ref hierarchy clash, same reason attempt A is `refactor-reviewer-surface`). Integration branch is `refactor-reviewer-surface-b`; track branches `track/<x>-b` as planned. PR opens from `refactor-reviewer-surface-b`.
- 2026-11-13: handoff head moved `c263ff8 → 46621e4` before branching; the branch starts from `46621e4`.

## Inbox acknowledgements

- 2026-11-13 "Surface review of `b18250c`" (read via the poller at 2026-11-13, after wave 1 had started from `0f71984`): (1) the five no-default configurations were run on `0f71984` (results in the gate table below; `junco-core --no-default-features` and everything above it failed to compile: `vstd::std_specs::hash` needs vstd's `std`). Fix on the integration branch: R4 `hash_coherent` is a single `uninterp` spec fn (no link to `obeys_key_model`: nothing in the verified crates uses vstd's hash-map specs, the `NativeMap` wrappers are `external_body`, so a link would be a trusted item with no use); the internal key axioms ensure `hash_coherent::<K>()` directly. (2) `AnalyzerView::known` is fixed by contract: R6 states `new ⇒ known == declared_sets(domains)`, `add_rule ⇒ known_with(before.known, rule_constants(rule))`, `tail_included ⇒ known_with(before.known, tail_constants(head, left, right))`, other queries unchanged; `known_grows` deleted; Track F ensures them. (3) `pattern_constant`, `test_constants`, `regex_constants`, `head_constants`, `rule_constants` (and the `*_constant_at`/`*_forest` helpers) now live in R3; Track B deletes the old ones in `refinement/semantics.rs`. (4) `Exhausted` recorded under deviations below. The three running tracks that touch these files (A, B, F) received the exact patch (`/tmp/r2/inbox-fix.patch`) and apply it on their branches.
- 2026-11-13 "No primitive or component-type key axioms" (same read): the three `Component2/3/4` axioms added by M4 (`history-syntax/src/verify/key_axioms.rs`) are deleted; Track A's brief is amended (no primitive lemmas discharging `hash_coherent`; witnesses take `hash_coherent::<C>()` as their only premise); the five internal key-type axioms stay; `INTERFACES.md`'s earlier contingency text is replaced. TRUST.md axiom count: 5.

- 2026-11-13 "Abandon the changes to `scripts/verify-all.sh`" (INBOX, read 2026-11-13T03:25Z via the poller): acknowledged. I **had** changed the script (commit `732ed0c`, `--jobs/--target-root/--only` plus `scripts/surface-diff.sh`, pushed to `refactor-reviewer-surface-b`); no track branch existed yet. Dropped by resetting the integration branch to the handoff head `9b8a5b5` (force-push) and redoing the PR #10 merge on top; `scripts/verify-all.sh` is byte-identical to `main`. Gates now run the `--list` commands directly through a personal runner outside the repo (`/home/eioannidis/git/junco-gate.sh`: per-configuration persistent `CARGO_TARGET_DIR`, nproc/jobs threads); the surface diff is likewise a personal script (`/home/eioannidis/git/junco-surface-diff.sh`). Consequence for Track G/D2: adding a `test-util` configuration to `configs` is no longer allowed, so D2 uses the handoff's preferred form (drop `test-util` from benchmark dev-dependencies, root-feature-gate the tests that need it, re-run the two benchmarks). Track T registers only the two reviewer test targets.

- 2026-11-13 "Track G additions (dead std spec; `arc_identity` fidelity)" (INBOX, read 2026-11-13 before branching): both items added to Track G's brief (delete the dead `core::mem::replace` `assume_specification` after a use search; determine how the pinned Verus models `Arc<T>`/`&T` in spec, prove or document the identity invariant at the wrappers, report in STATUS.md before any change if distinct `Arc`s can coincide). `scripts/spec-check.sh` runs at G's merge gate because `history_assumptions.rs` changes.
- 2026-11-13 handoff `72a86fa` "eliminate the singleton_invariants axiom (Track G)": added to Track G's brief as its first item (fold `singleton_valid` into `numeric_store_wf`, delete the axiom and its calls, lower `numeric_store_wf` visibility). Tension noted: the handoff's Priority 2 now reads "no `external_body` proof function remains", while decision 4 (and this plan) adds the hash-model axioms for `Component2/3/4` and the five internal key types; they are the only new proof axioms and are listed in TRUST.md's "proof axioms" section with justifications. Contingency unchanged: if the maintainer objects, the two bundle theorems take `hash_coherent::<Component3<…>>()` as an explicit hypothesis and the axioms are dropped.

## Slowest-proof assignments

`cargo verus verify … -- --num-threads 32 --time-expanded` at `0f71984` (Verus reports the top-3 modules per phase, not per-function times):

| crate | wall (verification) | smt-run total (32 threads) | slowest modules (smt-run) | owner |
|---|---:|---:|---|---|
| history-semantics (runtime,std,cache) | 84.5 s | 262 s | `normalize` 84.0 s; `symbolic` 80.0 s; `normalize::verify` 36.3 s (air: `normalize::verify` 18.7 s) | not edited by any wave-1 track (B/F touch `refinement/*`, `verify/*`); Track T's `numeric_lang` rename touches them textually only |
| history-store (runtime,std) | 10.1 s | 10.8 s | `graph` 7.9 s; `store` 1.5 s; `typed` 1.4 s | G (`store.rs`), C (`graph.rs`) |
| history-analysis (runtime,std) | 32.3 s | 61.5 s | `search` 24.1 s; `verify::search_exec` 15.6 s; `analyzer` 4.1 s | F (`analyzer.rs`), C (`search.rs` error contract), A (`search_exec` obligations) |
