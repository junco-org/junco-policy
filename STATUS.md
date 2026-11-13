# STATUS — [attempt B] Reviewer-readable mechanization

Integration branch: `refactor-reviewer-surface-b` (from `origin/handoff/reviewer-surface-b` @ `46621e4`).
Plan: `local://reviewer-surface-b-plan.md` (integration owner's copy). Deleted in the last commit before the PR.

## Wave / tracks

| Track | State | Branch | Notes |
|---|---|---|---|
| 0 | in progress | integration | 0.0 done; 0.1 withdrawn by INBOX (script unchanged); 0.2 PR #10 merged at `3e30f33` (gate passed); M1 in progress |
| A, B, B2, C, D, E, G, F-prep | not started | `track/<x>-b` | wave 1 |
| F | not started | `track/f-b` | wave 2 |
| T | not started | `track/t-b` | wave 3 |

## Last gate results

PR #10 merge gate @ `3e30f33` (2026-11-13): full-feature configs of all five crates + `public_specs`, run concurrently via the personal runner (6 jobs x 42 threads): history-syntax/junco-core/history-store cached (unchanged by the merge), `history-semantics --features runtime,std,cache` 1620 verified / 0 errors, `--test public_specs` 21 / 0, `history-analysis --no-default-features --features runtime,std` 570 / 0; wall 138 s. `cargo fmt --check`, `cargo clippy -D warnings`, `cargo test` for the six packages: pass.

PR #10 commit integrated: `52118c4`.

## Blockers

(none)

## Decisions deviated from the plan

- 2026-11-13: branch name `refactor/reviewer-surface-b` is impossible: a branch `refactor` exists locally and on origin (ref hierarchy clash, same reason attempt A is `refactor-reviewer-surface`). Integration branch is `refactor-reviewer-surface-b`; track branches `track/<x>-b` as planned. PR opens from `refactor-reviewer-surface-b`.
- 2026-11-13: handoff head moved `c263ff8 → 46621e4` before branching; the branch starts from `46621e4`.

## Inbox acknowledgements

- 2026-11-13 "Abandon the changes to `scripts/verify-all.sh`" (INBOX, read 2026-11-13T03:25Z via the poller): acknowledged. I **had** changed the script (commit `732ed0c`, `--jobs/--target-root/--only` plus `scripts/surface-diff.sh`, pushed to `refactor-reviewer-surface-b`); no track branch existed yet. Dropped by resetting the integration branch to the handoff head `9b8a5b5` (force-push) and redoing the PR #10 merge on top; `scripts/verify-all.sh` is byte-identical to `main`. Gates now run the `--list` commands directly through a personal runner outside the repo (`/home/eioannidis/git/junco-gate.sh`: per-configuration persistent `CARGO_TARGET_DIR`, nproc/jobs threads); the surface diff is likewise a personal script (`/home/eioannidis/git/junco-surface-diff.sh`). Consequence for Track G/D2: adding a `test-util` configuration to `configs` is no longer allowed, so D2 uses the handoff's preferred form (drop `test-util` from benchmark dev-dependencies, root-feature-gate the tests that need it, re-run the two benchmarks). Track T registers only the two reviewer test targets.

- 2026-11-13 "Track G additions (dead std spec; `arc_identity` fidelity)" (INBOX, read 2026-11-13 before branching): both items added to Track G's brief (delete the dead `core::mem::replace` `assume_specification` after a use search; determine how the pinned Verus models `Arc<T>`/`&T` in spec, prove or document the identity invariant at the wrappers, report in STATUS.md before any change if distinct `Arc`s can coincide). `scripts/spec-check.sh` runs at G's merge gate because `history_assumptions.rs` changes.
- 2026-11-13 handoff `72a86fa` "eliminate the singleton_invariants axiom (Track G)": added to Track G's brief as its first item (fold `singleton_valid` into `numeric_store_wf`, delete the axiom and its calls, lower `numeric_store_wf` visibility). Tension noted: the handoff's Priority 2 now reads "no `external_body` proof function remains", while decision 4 (and this plan) adds the hash-model axioms for `Component2/3/4` and the five internal key types; they are the only new proof axioms and are listed in TRUST.md's "proof axioms" section with justifications. Contingency unchanged: if the maintainer objects, the two bundle theorems take `hash_coherent::<Component3<…>>()` as an explicit hypothesis and the axioms are dropped.

## Slowest-proof assignments

(after Track 0's `--time-expanded` run)
