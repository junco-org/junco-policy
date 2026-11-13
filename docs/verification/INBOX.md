# Messages to the agent working from `handoff/reviewer-surface-b`

The maintainer adds messages here, newest first, each with a UTC date and a short title. A
message takes precedence over the handoff and over earlier messages where they conflict.
Acknowledge each one in `STATUS.md` on your integration branch.

## 2026-11-13: Track G additions (dead std spec; `arc_identity` fidelity)

1. **Delete the dead `assume_specification` for `core::mem::replace`**
   (`junco-core/src/verify/history_assumptions.rs`). Its only use is in the unverified,
   `test-util`-only `CanonicalStore::replace_graph_byte_pressure` (`history-store/src/graph.rs`),
   so no verified code depends on it. Confirm that with a search before deleting; `TRUST.md` loses
   one item.

2. **Check that `arc_identity` cannot identify distinct `Arc`s.** The identity wrappers
   (`share_store`, `borrow_store`, `share_numeric_owner`, `borrow_numeric_owner`,
   `same_numeric_reference`, `CompiledRule::same_owner`) state their contracts with
   `arc_identity`/`reference_identity` (`junco-core/src/verify/history_assumptions.rs`), which are
   uninterpreted functions of the `Arc`/reference *value*. If Verus models `Arc<T>` by its contents,
   two distinct `Arc`s with equal contents would have equal spec values and therefore equal
   `arc_identity`, while `Arc::ptr_eq` at runtime says they differ, so an `external_body`
   postcondition such as `same_numeric_reference`'s would be false for the running code.
   - Determine how the pinned Verus models `Arc<T>` and `&T` in spec code.
   - If distinct stores (and every other type whose identity is compared) always differ in their
     spec value, e.g. through ghost identity fields, prove or document that invariant at the
     wrappers and note it in `TRUST.md`.
   - If they can coincide, report it in `STATUS.md` before changing anything: it would make the
     store-ownership guarantees (`WrongHistoryOwner`, `WrongCheckpointOwner`, cross-store proofs)
     rest on a false trusted contract.
