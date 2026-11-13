# Verified policy queries: progress at handoff

Working notes for continuing `docs/verification/HANDOFF-inclusion-e2e.md` (the specification).
Delete this directory before opening the PR.

Branch `verify/policy-analyzer-e2e`, created from `handoff/verus-proofs` (`a2c1255`).

## State of the branch

The integration branch is linear in milestones (`git log --first-parent`):

| Commit | Content | Verification |
|---|---|---|
| `c02c647` | M0: interfaces (below) | integrator's `verify-all`: every configuration 0 errors except the last (`history-analysis --features runtime,std`), which the run did not reach before its timeout; worker branches containing M0 verify in that configuration |
| `c57e61c` | M0b: `redundant_correct` also states `removable` | in the worker branches below |
| `9399251` | merge of `wip/core` (contains `wip/model`, `wip/nie`, `wip/search` up to `924b40f`, `wip/bridge` up to `dd18b49`, `wip/typed`) | per worker branch, see below |
| `ef0664f` | merge of `wip/search` `51acf13` (deletes two unused lemmas) | worker: `history-analysis` 501/0 in both configurations |
| `de650f9` | merge of `wip/bridge` `1ad6a55` (uses `inclusion::lemma_split_ok_mono`) | worker: `history-analysis` 519/0 in both configurations |
| `af08332` | merge of `wip/min` `cfd95b5` (minimality lemmas) | worker: `history-analysis` 505/0 in both configurations |
| `9d5995d` | **WIP, never run through Verus**: helper lemmas for the entry points in `verify/verdict.rs` | none |

**The consolidated tree has not been verified as a whole.** Each piece was verified on its
worker branch against the M0 interfaces. File ownership was disjoint and the merges were
conflict-free. First step: verify both `history-analysis` configurations, then run the full
`scripts/verify-all.sh`.

Per-branch verification reported by the workers:

| Branch | Commits | Reported |
|---|---|---|
| `wip/model` | `bfa5ef7` | `refinement` modules 32 verified, 0 errors; full-crate runs not completed |
| `wip/nie` | `3bff938` | `history-store` 287/0; `history-semantics --features runtime,std,cache` 1580/0; `public_specs` and the `runtime`-only configuration not completed |
| `wip/search` | `197f183`, `924b40f`, `51acf13` | `history-analysis` 501/0 in both configurations |
| `wip/bridge` | `2f15a8b`, `dd18b49`, `1ad6a55` | `history-analysis` 519/0 in both configurations |
| `wip/core` | `e81e46e`, `4e01cce`, `aab21bf` | committed after the worker's Verus runs, as the worker protocol requires; counts not recorded |
| `wip/typed` | `3f406bb` | `history-analysis --features runtime` 539/0; `runtime,std` not completed |
| `wip/min` | `b141930`, `cfd95b5` | `history-analysis` 505/0 in both configurations |

## Interfaces fixed in M0 (and spec changes so far)

history-semantics `crates/history-semantics/src/verify/refinement/`:

- `analyzer.rs`: `covered_ok = covered_correct && covered_minimal`, likewise for `redundant_*`
  and `at_least_as_strict_*`. Compared with the old `*_ok`, each `*_correct` adds an explicit
  negation under `unrestricted_infinite(d)` (components without a declared domain have infinite
  types): `!covers`, `!refines`, and for `redundant` `!removable`. New: `unrestricted_infinite`,
  `others(policy, rule)` (`policy.filter(|id| id != rule)`), `fresh_unrestricted(d, cex)`,
  `stmt_choice_exists_declared` (proved by `theorem_choice_exists_declared`), and (M0b)
  `removable(a, rule, policy)`, which `redundant_correct` states for `Holds` and refutes for a
  counterexample when `policy.contains(rule)`.
- `policy.rs` (new): **R1 composition** `stmt_policy_outcomes`, proved by
  `theorem_policy_outcomes` / `lemma_policy_outcomes`, with `case_cex_uncovered`,
  `realizations_uncovered`, `no_uncovered_shorter`.
- `inclusion.rs`: `lemma_case_denies` (the counterexample-transfer argument, factored out of
  `lemma_policy_reduction`, whose statement is unchanged) and `lemma_split_ok_mono`.

history-analysis:

- Rule store (`analyzer.rs`): `pub struct RuleId(pub(crate) usize)`, `AnalyzedRule<E> { constants,
  mode, tail, source: Ghost<(Rule<E>, FlatRule<ComponentValue<E>>)> }`, `PolicyAnalyzer.rules`. The
  view's `rules` reads the store; `analyzer_state_wf` includes `rules_wf` (`stored_rule_wf` per
  rule: flattened, lowered against the book, `structural_wf`, head pins). Stored encodings stay
  valid as the book grows (`lemma_rules_extend`). `lemma_declared_wf` requires an empty store.
- `Tables::difference` now gives the difference pair the head `[Bind; 3]` instead of `[Any; 3]`.
  This is an executable change. Heads play no part in a tail's language, and with the new head a
  table with component-local variables is `structural_wf` (`table::lemma_bind_structural`),
  which `compile`'s no-internal-error clause needs.
- `verify/policy.rs` (interfaces): `template_regex` (a stored template as a regex),
  `numeric_rule`, `stored_numeric`, `numeric_policy(a, ids)`, `ids_valid`, `policy_atoms`,
  `difference_of`, `query_ready` (what `decide` requires), `decided` (what it ensures),
  `policy_capacity` ($(k+2)^3 \le$ `usize::MAX` for $k$ book entries), `rule_capacity`.
- `search_exec::primitives_safe`.

Contract additions (ensures only, existing clauses unchanged):

- `Constraint::entails`: `result == (register_entails(..principal..) && ..action.. && ..resource..)` (exact).
- `CanonicalStore::with_budget`, `CompiledPair::compile`, `SymbolicLanguage::{compile, nullable,
  read_regex, read_test, derive, successor}`: no internal error under valid ids, `structural_wf`
  templates and budgets that are multiples of 16 (`wip/nie` `3bff938`; exact clauses in that commit).
- `Tables::*`, `ConstraintTable::intern`: unconditional `no_internal_error`. `search`:
  `primitives_safe(regex_primitives(root)) ==> no_internal_error(result)`. Inner search, prune and
  simulation functions carry matching clauses (`wip/search`). The internal lemma
  `lemma_vocabulary_frame` gains `requires a.start@ == b.start@`.
- `encode`, `counterexample`: `no_internal_error`.
- `decide(&self, constraint, difference, Ghost(left), Ghost(right))`: requires
  `policy::query_ready`, ensures `policy::decided` and `no_internal_error(result)` (R2).
- `tail_included`: gains `no_internal_compile_error(result)`, `final(self)@.rules ==
  old(self)@.rules`; `tail_included_ok` unchanged.
- `add_rule(&mut self, &Rule<E>) -> Result<RuleId, CompileError>`: requires
  `analyzer_obligations`, `analyzer_state_wf`, `rule_capacity`; ensures `analyzer_state_wf`,
  `no_internal_compile_error`, and on `Ok(id)`: `final(self)@.rules == old(self)@.rules.push(rule@)
  && id@ == old(self)@.rules.len() && rule_wf(rule@)`.

No trusted items have been added (`admit`, `assume`, `external_body`, `#[verifier::external]`).

## Proved lemmas available for the entry points

- `verify/firing.rs` (R3, Bridge): `lemma_template_regex`/`lemma_template_test` (F1: a template's
  regex has the template's `source_regex` language); `lemma_policy_split` (F2: the cases of
  `split(&base, &Operands::of(policy_atoms), universes)` satisfy `split_ok` on
  `head_pairs(numeric_policy)`, each case is satisfiable with known codes); `lemma_split_capacity`
  (`policy_capacity ==> split_capacity`, call before `split`); `lemma_exact_firing` (F3:
  `Constraint::head` then `entails` == semantic entailment of the rule's head constraint);
  `head_result`, `case_set`, `lemma_stored_head`.
- `verify/verdict.rs` (Core): `lemma_decided_instance`, `lemma_decided_shortest`,
  `lemma_decided_fresh`, `lemma_source_primitives_safe`; WIP (unverified, `9d5995d`):
  `lemma_firing_language`, `lemma_denial_language`, `lemma_policy_resources`.
- `verify/policy_bridge.rs` (R4, Typed): `lemma_stored_denies` (B1, typed = numeric denial of
  a stored rule), `lemma_policy_denies` (B2), `lemma_covers_from_numeric` (B3),
  `lemma_covered_unsat` (B4: unsatisfiable head constraint ⇒ `covered_correct(.., Holds)`),
  `lemma_covered_holds` (every case included ⇒ `covered_correct(.., Holds)`),
  `lemma_covered_cex` (a case's decided counterexample ⇒ `covered_correct(.., Counterexample)`),
  `lemma_strict_holds`, `lemma_strict_cex`, `lemma_redundant_correct`.
- `verify/minimality.rs` (R6, Min): `lemma_profile_case`, `lemma_covered_minimal` (with
  hypothesis `denials_agree`, to be discharged by B1/B2), `lemma_redundant_minimal`,
  `lemma_strict_minimal`.

## Remaining work

1. **Verify the consolidated tree** and fix `9d5995d`.
2. **M4 entry points** in `analyzer.rs` (one owner for `analyzer.rs` and `verify/verdict.rs`).
   Algorithm: `git show e2aa01e:crates/history-analysis/src/analyzer.rs` l.300-530, without
   `stats`, returning `Result<Inclusion<E>, HistoryError>`.

   ```rust
   pub fn covered(&self, rule: RuleId, by: &[RuleId]) -> (result: Result<Inclusion<E>, HistoryError>)
       requires analyzer_obligations::<E>(), analyzer_state_wf(*self), policy_capacity(*self),
           rule@ < self@.rules.len(), ids_valid(*self, rule_ids(by@)),
       ensures no_internal_error(result),
           result matches Ok(v) ==> analyzer::covered_correct(self@, rule@, rule_ids(by@), v@),
   ```

   - `Constraint::head(analyzed.constants, &self.universes)`: `None` ⇒ `Ok(Holds)` by `lemma_covered_unsat`.
   - Atoms of `by`'s head constants in the order of `policy_atoms` (`x_k = κ_k`, `x_k = v` per
     head constant), `Operands::of`, `lemma_split_capacity`, `split`, `lemma_policy_split`.
   - Per case `i` (loop with `decreases`): fresh `Tables`; denial of the rule (`append` the stored
     tail; for `require`, `push(Complement(root))`); for each `j`, if
     `Constraint::head(by_j.constants)` is `Some(hc)` and `case.entails(&hc)` (exact by
     `lemma_exact_firing`) push the denial of `by_j`; `push(Union(matching))`; `difference`;
     `decide(case, difference, Ghost(denial(R)), Ghost(firing_denials(d, P, constraint_of(case@))))`.
     The `matching` invariant follows `P.take(j).filter(pred)`; the union's language is
     `lemma_firing_language`. `query_ready`: `structural_wf` by `table::lemma_structural_local`,
     `lemma_append_local`, `lemma_bind_structural`; codes as in `tail_included`
     (`lemma_append_payload`, ...); `difference_of` from the tables' language ensures, F1 and
     `lemma_denial_language`; resources by `lemma_policy_resources`. Earlier nodes keep their
     language as the tables grow (`frame`).
   - Holds in every case ⇒ `lemma_covered_holds` (keep `included_under` for cases `< i` as an
     invariant). Counterexample ⇒ `lemma_covered_cex`. Exhausted ⇒ return it.
   - `redundant(rule, policy)`: filter `policy` by `id.0 != rule.0` (invariant
     `rule_ids(others@) == analyzer::others(rule_ids(policy@.take(i)), rule@)`), `covered`,
     `lemma_redundant_correct`; ensures `redundant_correct(self@, rule@, rule_ids(policy@), v@)`.
   - `at_least_as_strict(stricter, than)`: per rule of `than`, `covered(than[j], stricter)`; first
     non-`Holds` ⇒ `lemma_strict_cex`; invariant: every earlier rule of `than` is covered; all
     `Holds` ⇒ `lemma_strict_holds`. Ensures `at_least_as_strict_correct(self@, rule_ids(stricter@), rule_ids(than@), v@)`.
3. **R7 tests**: `differential_policy.rs` (this directory, untested draft, never compiled)
   extends `crates/history-analysis/tests/differential.rs`. Append it and add `Counterexample`
   to the `history_analysis` import. It contains `policy_queries_agree_with_brute_force` (random
   policies; `covered`, `redundant` vs brute force and the runtime `TracePolicy`;
   `at_least_as_strict`; per-case minimality checked on a finer partition) and the paper's
   Alice/Bob regression `covered_refutes_for_agents_other_than_alice` (`inclusion.tex`
   l.129-142). `src/tests.rs` already has `add_rule` unit tests (from `wip/core`):
   `cargo test -p history-analysis --lib` passes on `324aa18` (13 tests). The workspace tests and
   `tests/differential.rs` were not run on the consolidated tree.
4. **M5**: add `*_minimal` to the three entry points' `ensures` (making `*_ok` hold):
   `lemma_covered_minimal` (discharge `denials_agree` with `lemma_stored_denies` /
   `lemma_policy_denies`), `lemma_redundant_minimal`, `lemma_strict_minimal`. Optional: ship
   without it if it is not ready.
5. **Docs**: `VERIFY.md` (results-table row "Executable analyzer" → the three entry points and
   their `*_correct` (`*_ok` if M5 lands) plus `no_internal_error`; row `prop:policy` → add
   `stmt_policy_outcomes` in `refinement/policy.rs`; list `stmt_choice_exists_declared` among the
   auxiliary statements; Hypotheses "Executable analyzer" → `policy_capacity`, `rule_capacity`,
   valid rule ids, `unrestricted_infinite` for the explicit negations; difference 3 → `Err` is
   never `Invariant`; difference 5 → minimality status; replace difference 7 "Only
   `tail_included` is executable" by "vacuity has no entry point of its own"; difference 9 →
   `covered` decides one inclusion per case; expected verified-function counts). Regenerate
   `TRUST.md` with `scripts/trust-scan.sh > TRUST.md`. Update the header comment of
   `refinement/analyzer.rs`, which lists the intended `ensures`.
6. Full `scripts/verify-all.sh` (0 errors everywhere), `cargo test --workspace`, clippy as in
   CI, push, PR against `main`.

## Verification notes

- Toolchain: `scripts/verify-all.sh --download <dir> -- --num-threads <cores>` once. Later runs
  without `--download` need `VERUS_DIST=<dir>/verus-dist` and
  `VERUS_Z3_PATH=<dir>/z3/z3-4.16.0-x64-glibc-2.39/bin/z3`; without them the script exits
  immediately. Rust `1.98.1-x86_64-unknown-linux-gnu` with `rustc-dev` and `llvm-tools`.
- A full `verify-all` takes about 25 minutes at 16 threads on an idle 20-core machine. Under load
  it exceeded an hour, so give it a long timeout.
- Single crate:
  `PATH=<dir>/verus-dist/verus-x86-linux:$PATH VERUS_Z3_PATH=... RUSTUP_TOOLCHAIN=1.98.1-x86_64-unknown-linux-gnu`,
  then `cargo verus focus --locked -p history-analysis --no-default-features --features runtime -- --num-threads N --verify-module verify::policy_bridge [--verify-function F]`.
  `focus` skips verifying dependencies. Configurations are the ones listed in `.github/workflows/ci.yml`.
- When a full run follows a module-filtered run of the same crate, cargo treats the crate as
  built and prints no `verification results` line. Touch a source file to force a run.
- Recursive spec functions: use `reveal_with_fuel(f, 2)` plus small unfolding lemmas (as
  `language::lemma_lang_intersect` does); a `forall` inside an unfolded body is not usable directly.
- All files are LF. The Validator CI job's `cargo fmt` failure on `benches/agentdojo/camel.rs`
  is pre-existing.
