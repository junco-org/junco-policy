# Messages to the agent working from `handoff/reviewer-surface`

The maintainer adds messages here, newest first, each with a UTC date and a short title. A
message takes precedence over the handoff and over earlier messages where they conflict.
Acknowledge each one in `STATUS.md` on your integration branch.

## 2026-11-13: Internal-key axioms may assert only `hash_coherent`

The internal-key introductions added in the atomic merge assert more than the hashing law:
the four `external_body` proof functions in `junco-core/src/spec/hypotheses.rs`
(`internal_keys`) and the `assume_specification` on the no-op `native_constraint_key_laws()` in
`history-analysis/src/constraint.rs` each ensure all of `key_laws::<K>()` (`obeys_eq_spec`, the
equivalence laws and `hash_coherent`), and `lemma_parts_key_laws` also asserts that `eq_spec`
implies view equality for `SmallVec<[RegexId; 4]>`.

- The only trusted fact allowed for an internal key type is `hash_coherent::<K>()`. Narrow each
  introduction to exactly that, one per internal key type.
- Remove every other assumed conjunct. Prove `obeys_eq_spec`, the equivalence laws and the
  `SmallVec` view-equality fact from the types' definitions and existing specifications instead.
  If one of them cannot be proved, report which and why in your next status entry instead of
  assuming it.
- Acknowledge in your next status entry.

## 2026-11-13: `Exhausted` is not a blocker

The `Exhausted` items in earlier messages are not blockers. For Priority 1 it is enough that
`Exhausted` makes no claim in every query spec and is documented honestly (budget or overflow).
Do not hold a wave or a merge for it. An unforgeable "budget exceeded" statement is optional, after
Priority 1; if you attempt it, its evidence must be something the implementation cannot choose.
The handoff's target claims, decision 3, Track C and Track F now say this. Acknowledge in your next
status entry.

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

## 2026-11-13: Surface review — fix before Wave 1 builds on R6

1. **Bound `Counterexample::known`.** As written, an implementation can return a counterexample whose
   `known` covers the carrier, making `every_instance` vacuous and capacity false, so every
   counterexample clause is satisfied without proof. Add to `counterexample_wf` (or each query spec)
   that `cex.known[i]` is a subset of the analyzer's knowable constants at coordinate `i`: the
   constants of the registered rules (for `tail_included`, of the head and both tails) plus the
   declared domain values. Define that set once in R3/R6.
2. **Make `Exhausted` evidence unforgeable.** `charged`/`requested` are unconstrained, so any
   implementation may return `Exhausted` with large numbers. Replace them with a ghost token that only
   the store's failing budget charge can construct (private constructor, records the store's budget
   equal to `GRAPH_BYTES`), carried in `Exhausted` and checked by `escapes`. If that is
   disproportionate, drop the fields and state that `Exhausted` makes no claim; do not keep evidence the
   implementation can choose.
3. **Drop the `Event::coordinate_cardinality` hook.** The S1 regression expectation is relaxed: for an
   undeclared finite-enum coordinate whose real events are covered, the analyzer must return `Holds` or a
   counterexample whose capacity fails at that coordinate, never a capacity-satisfying refutation. No
   new trait method.
4. Update `INTERFACES.md` accordingly and acknowledge in your next status entry.

## 2026-11-13: Keep completed `verify-all.sh` work

This amends "Abandon the changes to `scripts/verify-all.sh`" below. You do not have to abandon work
you have already completed: keep the `verify-all.sh` changes you already made and verified
(`5f0523d`, "Add parallel filterable Verus configuration gates"), and keep using them for gates.
Do not extend the script further beyond registering the two reviewer test targets. Before the final
PR, confirm once that the default invocation, with no new options, still runs the same eleven
configurations sequentially as on `main`, so CI is unchanged.

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
