# Messages to the agent working from `handoff/reviewer-surface-b`

The maintainer adds messages here, newest first, each with a UTC date and a short title. A
message takes precedence over the handoff and over earlier messages where they conflict.
Acknowledge each one in `STATUS.md` on your integration branch.

## 2026-11-13: `Exhausted` is not a blocker

The `Exhausted` items in earlier messages are not blockers. For Priority 1 it is enough that
`Exhausted` makes no claim in every query spec and is documented honestly (budget or overflow).
Do not hold a wave or a merge for it. An unforgeable "budget exceeded" statement is optional, after
Priority 1; if you attempt it, its evidence must be something the implementation cannot choose.
The handoff's target claims, decision 3, Track C and Track F now say this. Acknowledge in your next
status entry.

## 2026-11-13: Surface review of `b18250c`

1. **Run all eleven configurations now.** `hash_coherent` is defined as
   `vstd::std_specs::hash::obeys_key_model`, and both `verify/key_axioms.rs` files import
   `vstd::std_specs::hash`. In the pinned vstd that module exists only with its `std` feature
   (`std_specs/mod.rs`: `#[cfg(all(feature = "alloc", feature = "std"))] pub mod hash;`), and
   `junco-core` depends on vstd with `alloc` only unless its own `std` feature is on. Your gates ran
   only the full-feature configurations. Run the no-default ones (`history-syntax`, `junco-core`,
   `history-store … runtime`, `history-semantics … runtime`, `history-analysis … runtime`) before
   wave-1 tracks build on R4. If they fail, keep R4 compiling in every configuration, e.g. a single
   `uninterp` `hash_coherent` (linked to `obeys_key_model` only under `std`), and report the choice.
2. **Bound `AnalyzerView::known` from above.** `analyzer_wf` only requires rule constants ⊆ `known`.
   If `known` can grow arbitrarily, capacity can be made to fail and every counterexample clause
   becomes vacuous. Make the contracts determine it: `new` ensures `known == declared_sets(domains)`,
   `add_rule` ensures `known_grows` by exactly the rule's constants, `tail_included` by exactly
   `tail_constants(head, left, right)`, and the other queries leave it unchanged. State this in R6.
3. **Move the constant extractors into the surface.** R6 imports `head_constants`,
   `regex_constants` and `rule_constants` from `history_semantics::verify::refinement::semantics`,
   which the cutover removes. Define them in R2 or R3 and delete the old ones (decision 10).
4. **Record the `Exhausted` choice.** Making `Exhausted` vacuous in every `*_spec`, with A5 only as
   prose in R6's header, differs from the handoff's target A5 (`Exhausted` ⇒ a search exceeded
   `GRAPH_BYTES`). Record it under deviations. If you keep A5 as a statement, its evidence must be
   unforgeable: a ghost token that only the store's failing budget charge can construct, carried in
   `Exhausted`; never ghost numbers the implementation chooses.

The `Component2/3/4` axioms are covered by the earlier message "No primitive or component-type key
axioms". Acknowledge in your next status entry.

## 2026-11-13: No primitive or component-type key axioms

Do not add trusted axioms for primitive key types (`u8`, `u32`, ...) or compositional axioms for
`Component2/3/4`. They would only let the reviewer witnesses discharge `hash_coherent` for concrete
types; they change no guarantee. Any approval of such axioms recorded in `INTERFACES.md` or
elsewhere is withdrawn; remove it.

- `hash_coherent` stays the single uninterpreted hashing hypothesis, named and documented in R4.
- The concrete witnesses (e.g. `lemma_u8_event_hypotheses`, `lemma_u32_event_hypotheses`) prove
  every other conjunct of the bundles (arity, projection laws, surjectivity, equality laws) and
  take `hash_coherent::<C>()` for the component type as their only premise.
- Decision 4's axioms for the library's internal key types stay: they remove preconditions that
  users cannot name.
- The handoff's target claims, Track A, Track T and acceptance criterion 3 now say this.

Acknowledge in your next status entry.

## 2026-11-13: Abandon the changes to `scripts/verify-all.sh`

Do not add `--jobs`, `--target-root` or `--only` to `scripts/verify-all.sh`. If you already changed
the script, revert it to its state on `main` and drop those commits (or revert them) on every
branch, including track branches. The only change to the script that remains allowed is
registering the two reviewer test targets (Track T).

For faster gates, run the `cargo verus verify --locked <configuration> -- --num-threads N`
commands directly (`scripts/verify-all.sh --list` prints them), several at once, each with its own
persistent `CARGO_TARGET_DIR`. Use the unchanged `scripts/verify-all.sh` for the final run. The
handoff's Track 0 and Verification/Gates sections have been updated to match. Acknowledge in your
next status entry and say whether you had changed the script.

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
