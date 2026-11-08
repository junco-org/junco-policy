# Finiteness fix, candidate A — evidence (VerifyCoordinator2, 2026-11-08)

Diff (against /home/zak/junco-policy-inclusion): /home/zak/work/verus-work2/FinFix/candidate-A.diff
```
--- crates/history-semantics/src/normalize.rs
+++ crates/history-semantics/src/normalize.rs
@@ -2765 +2765 @@
-                                            TransitionHead::Const(r) => {
+                                            TransitionHead::Const(r) if self.intersect => {
```
Effect: `TransitionMode::collect` merges constant leaves into one leaf only for transition
intersections; in transition unions a `Const` child falls through to the existing `_` arm (kept as a
separate child). Affects every union `collect` (symbolic.rs union derivative and the step driver's
`Action::Union`). The alternative /tmp/perf/variant.diff (adds a `merge` flag, disables merging only
for `Action::Union`) is 9 hunks / 2 files; candidate A is 1 line and passes the same checks.

Copies: FinFix (finite-proof-2 copy + fix + scratch probe), FinBase (same, without fix),
FinMain (main tree + fix). Scratch probe `fix_orbit_saturation` in FinFix/.../finite_probe.rs.

## (a) disproof orbit
- fix: A -> A+B -> A+B; BFS over all atom valuations saturates: 2 states, 2 levels.
- base: unsaturated at CAP=300 (301 states, 300 levels).

## (b) successor equations (audit harness, graph_tests.rs tmp_seq_check / tmp_closure_check)
| run | base | fix |
|---|---|---|
| seq_check RICH=1 (TRIALS=200,CAP=400) | S3 3/628 violated | 0 violations S0–S6 |
| seq_check RICH=1 CX=5 | S3 200/800 violated | 0 |
| seq_check RICH=1 CX=6, CX=7 | — | 0 |
| seq_check RICH=1 DEPTH=7 TRIALS=2000 CAP=800 SEED=23/7/101 (release) | (variant run: 0) | 0 / 0 / 0 (S3 checked 14719/13688/13160) |
| closure_check RICH=1 (default, CX=5,6,7, CX=2) | 0 | 0 |
| closure_check RICH=1 SAMEFIELD DEPTH=6 TRIALS=1500 CAP=800 | | 0 violations, 1 capped |
| closure_check RICH=1 DEPTH=7 TRIALS=1500 CAP=800 | | 0 violations, 9 capped |

## random saturation campaigns (finite_probe, release; rank/provenance assertions on)
| campaign | base roots sat/capped, total states, edges | fix |
|---|---|---|
| TRIALS=3000 DEPTH=7 SEED=23 CAP=5000 | 2997/3, 65,587, 340,631 | 2999/1, 38,931, 218,950 |
| SAMEFIELD TRIALS=3000 SEED=101 | 2999/1, 53,682, 339,019 | 2999/1, 35,579, 207,649 |
| STICKY TRIALS=1000 DEPTH=6 SEED=79 | 1000/0, 10,312, 55,163 | 1000/0, 8,126, 40,492 |
Max orbit: base 12,085 (trial 1736, capped) vs fix 7,210 (trial 1187, capped; base had 6,267 there at cap).
Zero assertion violations in all runs.

## (c) main tree + fix (FinMain)
- cargo verus verify -p history-semantics --no-default-features --features runtime: 947 verified, 0 errors
  (deps: junco-core 1908, history-store 233, ... all 0 errors)
- cargo verus verify -p history-semantics --features runtime,std,cache: 951 verified, 0 errors
- cargo test --locked --workspace: all test results ok, 0 failed.

## Performance notes (no timing)
- States: fewer reachable states overall (−41%, −34%, −21% in the three campaigns); one capped root
  explores more states before the cap.
- Transitions: a union transition now keeps k separate Const children instead of one merged Const
  leaf, so union transition nodes can be larger (k children instead of 1), and later intersections
  distribute over those children instead of a single leaf. Interpretation still builds the union
  regex for the selected branch, so the produced states are unions as before. Total successor
  evaluations (edges) fell in all three campaigns.
