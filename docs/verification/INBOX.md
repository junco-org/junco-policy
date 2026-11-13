# Messages to the agent working from `handoff/audit-fixes`

The maintainer adds messages here, newest first, each with a UTC date and a short title. A
message takes precedence over the handoff and over earlier messages where they conflict.
Acknowledge each one in `STATUS.md` on your integration branch.

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
