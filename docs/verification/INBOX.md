# Messages to the agent working from `handoff/audit-fixes`

The maintainer adds messages here, newest first, each with a UTC date and a short title. A
message takes precedence over the handoff and over earlier messages where they conflict.
Acknowledge each one in `STATUS.md` on your integration branch.

## 2026-11-13: Vacuity probe results (no blocker; priorities unchanged)

The Verus probes ran at `969449b`; full report with every probe source, command and output in
`docs/verification/audit/probes.md`, probe files in `audit/history-analysis-vacuity_probes.rs`
and `audit/history-semantics-vacuity_probes.rs` (drop into the crate's `tests/`).

- Nothing proves `false`: the five key axioms with the kernel and vstd groups, every
  hypothesis bundle, and the premises of every reviewer theorem are consistent; concrete
  satisfying instances exist. `hash_coherent::<Component2<u32,u64>>()` is neither provable nor
  refutable. Specs reject false `Holds`, non-failing or non-shortest counterexamples, wrong
  grants/denials, and unsafe traces.
- Confirmed (H1): with a declared, known value at a coordinate, a counterexample with a fresh
  value there satisfies `covered_spec` and `tail_included_spec` even for a rule proved covered.
  Use the junk-counterexample probe as H1's acceptance test: after the fix it must fail.
- Confirmed (H5): `check_step` holds for `Err(AllocationFailed)` and `Err(GraphBudget)` in every
  state; an always-erroring `check` meets the whole contract.
- Inconclusive (H4): neither satisfiability nor unsatisfiability of `stmt_search_correct`'s
  premise is provable automatically; restate it as H4 says.
- New, MINOR (fold into H14): no exec client shows an `Ok` result is reachable; `Store::new`,
  the builder's `add_rule`/`finish` and the analyzer's `add_rule` may always return `Err`.

Probe setup that worked: toolchain and target dir outside `/tmp` (tmpfs runs out of memory);
with libraries cached, a new test file verifies in about 5 s; to verify one module use
`cargo verus focus` (`cargo verus verify` rejects `--verify-module`).

## 2026-11-13: Port H1 and H6 from attempt A (PR #12) first

Attempt A (draft PR #12, branch `refactor-reviewer-surface` at `c441afd`) already fixes H1 and
H6. Port them into `main` before any other item; do not merge or rebase onto that branch, and
do not take anything else from it.

- **H1.** A's `junco_core::spec::questions::symbolic_event_wf` has the arm
  `SymbolicValue::Fresh(_) => domains[i] is None`, and `counterexample_wf` requires it for the
  candidate and every history event; `lemma_declared_coordinate_zero`
  (`crates/history-analysis/tests/reviewer.rs:314`) derives `fresh_count == 0` at declared
  coordinates. Add the equivalent clause to `counterexample_spec` on `main` and discharge it
  from `reconstruction::slot_domain`; add the reviewer lemma.
- **H6.** A's typed `rule_wf::<E>` includes `head_wf`: `head.len() == arity::<E>()` and every
  head constant tagged with its coordinate. Add head length `== arity::<E>()` and tagged
  constants to `PolicyAnalyzer::add_rule`'s `Ok` clause on `main`.

Land H1 and H6 as separate PRs, as the prompt says. Then continue with H3, H4, H5.
