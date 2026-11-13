You are fixing the Junco Verus artifact after a claims audit. Repository:
git@github.com:junco-org/junco-policy.git. Start from the branch handoff/audit-fixes
(main at 7050ac3 plus the handoff). Read, in order:
docs/verification/HANDOFF-audit-fixes.md (the task: items H1–H15, constraints,
acceptance), docs/verification/audit/*.md (evidence with file:line references), VERIFY.md,
TRUST.md. Toolchain and gates: docs/history/HANDOFF-reviewer-surface.md § Verification and
§ Gates (install with scripts/verify-all.sh --download <dir>).

Time limit: the paper deadline is in about 3 hours. Work so that every finished item is
usable even if you are stopped at any moment:
- Do the items in this order: H1, H3, H4, H6, then H5 (monitor half first, then analyzer),
  then H2, then the rest in handoff order. Skip H15 (VERIFY.md rewrite) unless everything
  else is done.
- Land each item as its own PR into main (branch fix/audit-<item>, e.g. fix/audit-h1),
  opened as soon as the merge gate for that item passes (cargo verus verify on the changed
  crate and its downstream crates, plus fmt/clippy/test for those packages). Do not batch
  items into one PR. CI must pass before you merge; if CI is slower than the next item, start
  the next item from main and rebase.
- Keep STATUS.md on a branch status/audit-fixes, pushed every 30 minutes: items merged
  (PR number, commit), item in progress and its state, blockers, verified-function counts
  from the last gate.
- Poll docs/verification/INBOX.md on handoff/audit-fixes every 30 minutes. An inbox
  message about vacuity probes takes priority over everything else.

Rules (from the handoff, repeated because they matter most):
- Never weaken an ensures. If an item cannot be proved as stated, stop it, record why in
  STATUS.md, and move to the next item. Do not land a weaker form.
- No admit, assume, or new external_body in analysis or semantics code. No new axioms.
- Do not edit the paper. Do not touch benchmark numbers except through H2/H7/H8/H9, and
  report before/after values.
- Keep line endings; clippy runs on the ghost-erased build.

When you stop (finished or interrupted), the last STATUS.md push must contain, per item:
merged / in progress / not started / abandoned (with reason), and for each merged item the
exact new or changed public statement (name and file), so the paper can cite it.
