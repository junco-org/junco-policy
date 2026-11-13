# Public reviewer interfaces

The current reviewer guide is [VERIFY.md](../../VERIFY.md); this inventory is navigation,
not a transition plan. Historical handoffs and the audit plan are in [docs/history](../history/).

- **R1:** [events](../../crates/history-syntax/src/spec/events.rs): structural views,
  arity, real-event projections, correct coordinate tags, projection laws and surjectivity.
- **R2:** [semantics](../../crates/junco-core/src/spec/semantics.rs): scoped head/test/tail
  semantics, whole-history language, rule/policy denial, least violation and well-formedness.
- **R3:** [questions](../../crates/junco-core/src/spec/questions.rs): declared domains,
  coverage/refinement/redundancy/vacuity/tail inclusion, bounded known contexts, tag-correct
  symbolic witnesses and real-event instances, coordinate capacity and profile minima.
- **R4:** [hypotheses](../../crates/junco-core/src/spec/hypotheses.rs): equality laws,
  the single uninterpreted `hash_coherent`, monitor/analyzer bundles and concrete tuple lemmas.
- **R5:** [monitor](../../crates/history-semantics/src/spec/monitor.rs):
  `ValidatorView { rules, history }`, opaque `wf` with public consequences, ordered decisions,
  atomic check/read-only permits, frames, rollback, registration and committed-prefix safety.
- **R6:** [analyzer](../../crates/history-analysis/src/spec/analyzer.rs):
  `AnalyzerView { domains, rules }`, opaque `wf` with `lemma_wf`, semantic vocabulary and ids,
  result revealing lemmas, frames, escapes and four public query contracts.
- **P:** [paper index](../../crates/history-semantics/src/verify/paper.rs): thirteen checked
  statement/proof pairs, including explicit qualifications on policy reduction and simulation.
- **T:** public [monitor](../../crates/history-semantics/tests/reviewer.rs) and
  [analyzer](../../crates/history-analysis/tests/reviewer.rs) clients.

Codebooks, native owner state, allocation availability, numeric encodings and writable graphs
are not semantic state fields. Native owner checks supplement semantic index validity.
`Counterexample.known` is erased semantic output bounded by all registered-rule literals plus
declared domains; borrowed tail queries use their head and both tails plus domains. Historical
interned values do not enlarge that allowed context. Capacity counts distinct used fresh names
per coordinate and is not a query precondition. Every real instance witnesses failure;
existence/refutation is capacity-qualified. Holds soundness does not need capacity.

`QueryResult::Exhausted` is a unit variant and makes no claim. No forgeable byte fields or
provenance tokens are introduced. Errors exclude invariant failures, not resource/input errors.
Declared domains restrict analyzer-to-monitor transfer to in-domain candidates and histories.
Redundancy removes all occurrences of the target id, preserves arbitrary order/duplicates,
and retains coverage meaning for an absent target. Policy minima are within the returned
constant profile; strictness uses the same selected Q rule for failure and minimum.

Monitor hypotheses do not need surjectivity; analyzer hypotheses add it. Concrete
`lemma_u8_event_hypotheses` and `lemma_u32_event_hypotheses` discharge every other law assuming
only component `hash_coherent`. Primitive/component-compositional axioms are not permitted;
the five exact internal hashing introductions may assert **only `hash_coherent`**.
Equality laws and `obeys_eq_spec` are verified separately, not asserted by those introductions.
The ordered-parts key is the library-owned, SmallVec-backed `observation::PartsKey`, with verified
equality/view reflection over borrowed slices. The pinned SmallVec model alone could not prove
that reflection; no replacement equality/view axiom is added. [TRUST.md](../../TRUST.md) enumerates
the five hashing-only introductions. The complete thirteen-configuration gate passes this boundary.
No Event cardinality hook is used. An undeclared finite coordinate can produce Holds or a
counterexample whose capacity fails there, never a capacity-satisfying real refutation of a
true property. See VERIFY for counting methodology, paper differences and restricted Arc identity.
