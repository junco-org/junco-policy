//! Store-bound owned DSL compilation and retained numeric decisions.

use super::Store;
use crate::error::{CompileError, HistoryError};
use crate::event::Event;
use crate::flat::FlatPair;
#[cfg(verus_keep_ghost)]
use crate::flatten::ComponentValue;
use crate::flatten::flatten_rule;
use crate::history::{History, StoredHistory};
use crate::limits::{Limits, Unmetered};
use crate::observation::ObservationWorld;
use crate::runtime::RuleRuntime;
use crate::syntax::{Rule, RuleMode};
use alloc::sync::Arc;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::verify as books;
#[cfg(verus_keep_ghost)]
use crate::history::verify as raw;
#[cfg(verus_keep_ghost)]
use crate::verify::{encoding, flatten as source, typed_decision as decision};
#[cfg(verus_keep_ghost)]
use verify::*;

#[cfg(verus_keep_ghost)]
verus! {
broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
/// The result retains a structural witness, not an assumed language equivalence.
pub(crate) open spec fn compiled_source<E: Event>(
    rule: Rule<E>, mode: RuleMode, numeric: FlatPair<u64>,
    maps: encoding::Codebook<ComponentValue<E>>, eq: encoding::Equality<ComponentValue<E>>,
    domain: encoding::Domain<ComponentValue<E>>,
) -> bool {
    mode == rule.mode && exists|flat: crate::flat::FlatRule<ComponentValue<E>>|
        source::flattened::<E>(rule, flat)
            && encoding::lowering(flat.source, numeric, maps, eq)
            && encoding::constants_in_domain(flat.source, domain)
}
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    pub tracked struct ObservedHistory {
        pub(crate) snapshot: raw::Snapshot,
        pub(crate) registration: books::HistoryRegistration,
    }

    pub open(crate) spec fn source_rule<E: Event>(compiled: CompiledRule<E>) -> Rule<E> {
        compiled.source@
    }

    pub open(crate) spec fn observation_matches(registry: vstd::resource::Loc, key: (usize, u64),
        events: Seq<crate::verify::history_specs::EventView>, observation: ObservedHistory) -> bool {
        observation.registration.id() == registry && observation.registration.key() == key.0
            && observation.registration.value() == observation.snapshot.id()
            && observation.snapshot.value().revision == key.1 as nat
            && observation.snapshot.value().events == events
    }

    pub open(crate) spec fn observations_wf(registry: vstd::resource::Loc,
        snapshots: crate::runtime::verify::HistorySnapshots,
        observations: Map<(usize, u64), ObservedHistory>) -> bool {
        snapshots.dom() == observations.dom()
            && forall|key: (usize, u64)| observations.contains_key(key) ==>
                observation_matches(registry, key, snapshots[key], observations[key])
    }

    pub(crate) proof fn lemma_observations_insert(registry: vstd::resource::Loc,
        snapshots: crate::runtime::verify::HistorySnapshots, observations: Map<(usize, u64), ObservedHistory>,
        key: (usize, u64), events: Seq<crate::verify::history_specs::EventView>, observation: ObservedHistory)
        requires observations_wf(registry, snapshots, observations),
            observation_matches(registry, key, events, observation),
        ensures observations_wf(registry, snapshots.insert(key, events), observations.insert(key, observation)),
    {
        assert forall|k: (usize, u64)| observations.insert(key, observation).contains_key(k) implies
            observation_matches(registry, k, snapshots.insert(key, events)[k], observations.insert(key, observation)[k]) by {
            if k != key {
                assert(observations.contains_key(k));
                assert(observation_matches(registry, k, snapshots[k], observations[k]));
            }
        }
    }

    pub open(crate) spec fn compiled_wf<E: Event>(compiled: CompiledRule<E>) -> bool {
        books::store_wf(*compiled.store)
            && crate::flat::verify::structural_wf(compiled.template)
            && decision::runtime_represents(compiled.template, compiled.runtime)
            && observations_wf(books::registry_id(&compiled.store),
                compiled.runtime.snapshots@, compiled.observations@)
            && (books::native_obligations::<E>() ==> books::maps_wf::<E>(compiled.maps@)
                && books::snapshot_published::<E>(books::registry_id(&compiled.store), compiled.maps@)
                && compiled_source::<E>(compiled.source@, compiled.mode, compiled.template,
                    compiled.maps@, source::component_equality::<E>(), books::domain::<E>()))
    }

    pub open(crate) spec fn constructed<E: Event>(compiled: CompiledRule<E>, rule: Rule<E>, store: Arc<Store<E>>) -> bool {
        compiled_wf(compiled) && compiled.source@ == rule && compiled.store == store
            && compiled.runtime.cursors@ == Seq::<crate::runtime::HistoryCursor>::empty()
            && compiled.runtime.snapshots@ == Map::<(usize, u64), Seq<crate::verify::history_specs::EventView>>::empty()
    }

    pub(crate) proof fn lemma_constructed_decision<E: Event>(compiled: CompiledRule<E>, rule: Rule<E>,
        store: Arc<Store<E>>, history: History<E>)
        requires constructed(compiled, rule, store), raw::history_wf(history),
        ensures decision_requires(compiled, history),
    {}

    pub open(crate) spec fn decision_requires<E: Event>(compiled: CompiledRule<E>, history: History<E>) -> bool {
        compiled_wf(compiled) && raw::history_wf(history)
    }

    /// Persistent observations agree with the history's body-maintained transition ledger.
    pub(crate) proof fn lemma_history_compatible(registry: vstd::resource::Loc,
        history: usize, stored: StoredHistory, snapshots: crate::runtime::verify::HistorySnapshots,
        tracked observations: &Map<(usize, u64), ObservedHistory>,
        tracked registration: &books::HistoryRegistration, tracked lifecycle: &raw::Lifecycle)
        requires observations_wf(registry, snapshots, *observations), lifecycle.wf(),
            registration.id() == registry, registration.key() == history,
            registration.value() == lifecycle.id(), lifecycle.state() == stored@,
        ensures crate::runtime::verify::snapshot_compatible(snapshots,
            history, stored.revision, crate::kernel::verify::events_view(stored.events@)),
    {
        crate::history::lemma_stored_history_view(stored);
        let key = (history, stored.revision);
        if snapshots.contains_key(key) {
            assert(observations.contains_key(key));
            assert(observation_matches(registry, key, snapshots[key], observations[key]));
            let tracked observation = observations.tracked_borrow(key);
            books::registrations_agree(&observation.registration, registration);
            assert(observation.snapshot.id() == lifecycle.id());
            lifecycle.validate(&observation.snapshot);
            assert(observation.snapshot.value().revision == stored.revision as nat);
            assert(observation.snapshot.value().events.is_prefix_of(
                crate::kernel::verify::events_view(stored.events@)));
        }
    }

    pub open(crate) spec fn dsl_result<E: Event>(rule: Rule<E>, history: History<E>, candidate: E,
        result: Result<Option<bool>, HistoryError>) -> bool {
        result matches Ok(answer) ==> match answer {
            None => !crate::verify::dsl::head_matches(rule.head@, books::projection(candidate)),
            Some(accepted) => crate::verify::dsl::head_matches(rule.head@, books::projection(candidate))
                && accepted == crate::verify::dsl::lang(rule.tail@, rule.head@,
                    books::projection(candidate), raw::raw_word(history)),
        }
    }

    pub open(crate) spec fn decision_result<E: Event>(before: CompiledRule<E>, after: CompiledRule<E>,
        history: History<E>, candidate: E, result: Result<Option<bool>, HistoryError>) -> bool {
        compiled_wf(after) && after.template == before.template && after.mode == before.mode
            && after.store == before.store && after.source@ == before.source@ && after.maps@ == before.maps@
            && (result is Err ==> after.runtime.cursors@ == before.runtime.cursors@)
            && (books::native_obligations::<E>() ==> dsl_result(before.source@, history, candidate, result))
    }

    pub open(crate) spec fn numeric_result(template: FlatPair<u64>, request: crate::store::Event,
        stored: StoredHistory, result: Result<Option<bool>, HistoryError>) -> bool {
        result matches Ok(answer) ==> match answer {
            None => crate::compile::verify::head_rejects(template, request),
            Some(accepted) => exists|bindings: crate::runtime::Bindings|
                crate::compile::verify::bindings_match(template, request, bindings)
                    && crate::verify::history_specs::event_wf(bindings@)
                    && accepted == crate::compile::verify::source_regex(template, template.root as nat,
                        bindings@, crate::kernel::verify::events_view(stored.events@)),
        }
    }

    pub(crate) proof fn lemma_typed_result<E: Event>(compiled: CompiledRule<E>, history: History<E>, candidate: E,
        request: crate::store::Event, maps: books::ComponentMaps<E>, result: Result<Option<bool>, HistoryError>)
        requires compiled_wf(compiled), raw::history_wf(history), books::native_obligations::<E>(),
            books::maps_wf::<E>(maps), books::maps_extend::<E>(compiled.maps@, maps),
            books::maps_extend::<E>(history.maps@, maps), books::event_encoded::<E>(maps, candidate, request),
            numeric_result(compiled.template, request, history.numeric, result),
        ensures dsl_result(compiled.source@, history, candidate, result),
    {
        let flat = choose|flat: crate::flat::FlatRule<ComponentValue<E>>|
            source::flattened::<E>(compiled.source@, flat)
                && encoding::lowering(flat.source, compiled.template, compiled.maps@, source::component_equality::<E>())
                && encoding::constants_in_domain(flat.source, books::domain::<E>());
        let numeric_word = history.numeric.events@.map(|i: int, event: crate::store::Event| books::numeric_values(event));
        assert forall|i: int| 0 <= i < history.events@.len() implies
            books::event_encoded::<E>(maps, history.events@[i], history.numeric.events@[i]) by {
            books::lemma_event_extension::<E>(history.maps@, maps, history.events@[i], history.numeric.events@[i]);
        }
        assert(encoding::word_encoded(maps, source::component_equality::<E>(), books::domain::<E>(),
            source::word_values::<E>(raw::raw_word(history)), numeric_word));
        assert(crate::compile::verify::word_representation(numeric_word,
            crate::kernel::verify::events_view(history.numeric.events@)));
        encoding::lemma_dsl_later_maps_preservation::<E>(compiled.source@, flat, compiled.template,
            compiled.maps@, maps, books::domain::<E>(), books::projection(candidate), raw::raw_word(history),
            books::numeric_values(request), numeric_word);
        crate::compile::verify::lemma_flat_head(compiled.template, books::numeric_values(request), request@);
        if let Ok(answer) = result {
            match answer {
                None => crate::compile::verify::lemma_head_rejects(compiled.template, request),
                Some(accepted) => {
                    let bindings = choose|bindings: crate::runtime::Bindings|
                        crate::compile::verify::bindings_match(compiled.template, request, bindings)
                            && crate::verify::history_specs::event_wf(bindings@)
                            && accepted == crate::compile::verify::source_regex(compiled.template,
                                compiled.template.root as nat, bindings@,
                                crate::kernel::verify::events_view(history.numeric.events@));
                    crate::compile::verify::lemma_bindings_match(compiled.template, request, bindings);
                    crate::compile::verify::lemma_flat_regex(compiled.template, compiled.template.root as nat,
                        books::numeric_values(request), request@, numeric_word,
                        crate::kernel::verify::events_view(history.numeric.events@), bindings@);
                },
            }
        }
    }
    }
}

// Arc identity is a native ownership leaf; it supplies no encoding or language theorem.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures result ==> *left == *right)]
fn same_owner<E: Event>(left: &Arc<Store<E>>, right: &Arc<Store<E>>) -> bool {
    Arc::ptr_eq(left, right)
}

verus! {
pub(crate) type LoweredRule<E> = (RuleMode, FlatPair<u64>, Ghost<super::ComponentMaps<E>>);

/// Flatten before locking; publish one finite snapshot after encoding constants.
pub(crate) fn lower_rule<E: Event, L: Limits>(
    store: &Store<E>, rule: &Rule<E>, limits: &mut L, world: &mut ObservationWorld,
) -> (result: Result<LoweredRule<E>, CompileError>)
    requires books::store_wf(*store),
    ensures result matches Ok((mode, numeric, maps)) ==> mode == rule.mode
        && crate::flat::verify::structural_wf(numeric)
        && books::snapshot_published::<E>(books::registry_id(store), maps@)
        && (books::native_obligations::<E>() ==> books::maps_wf::<E>(maps@)
            && compiled_source::<E>(*rule, mode, numeric, maps@,
                source::component_equality::<E>(), books::domain::<E>())),
{
    let flat = flatten_rule(rule, limits, world)?;
    proof_decl! { let ghost flattened = flat; }
    proof! {
        if books::native_obligations::<E>() { books::lemma_empty_maps_wf::<E>(); }
    }
    let (result, maps) = store.lower_with_snapshot(&flat.source, limits, world,
        verus_exec_expr! { Ghost(books::empty_maps::<E>()) });
    let numeric = result?;
    proof! {
        if books::native_obligations::<E>() {
            assert(source::flattened::<E>(*rule, flattened));
            assert(compiled_source::<E>(*rule, flat.mode, numeric, maps@,
                source::component_equality::<E>(), books::domain::<E>()));
        }
    }
    Ok((flat.mode, numeric, maps))
}
}

/// A rule owns one graph generation; all histories and constants share its store.
#[verus_verify]
pub struct CompiledRule<E: Event> {
    pub(crate) template: FlatPair<u64>,
    pub(crate) mode: RuleMode,
    pub(crate) store: Arc<Store<E>>,
    pub(crate) runtime: RuleRuntime,
    #[cfg(verus_keep_ghost)]
    pub(crate) source: Ghost<Rule<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) maps: Ghost<books::ComponentMaps<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) observations: Tracked<Map<(usize, u64), ObservedHistory>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<E: Event> CompiledRule<E> {
    pub closed spec fn mode_spec(&self) -> RuleMode { self.mode }
}
}

#[verus_verify]
impl<E: Event> CompiledRule<E> {
    /// Consume the source on every outcome using its iterative disposal path.
    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store))]
    pub fn new(store: Arc<Store<E>>, rule: Rule<E>) -> Result<Self, CompileError> {
        Self::new_with_limits(store, rule, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store))]
    pub(crate) fn new_with_limits<L: Limits>(
        store: Arc<Store<E>>,
        rule: Rule<E>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, CompileError> {
        Self::construct(store, rule, cfg!(feature = "cache"), limits, world)
    }

    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store))]
    fn construct<L: Limits>(
        store: Arc<Store<E>>,
        rule: Rule<E>,
        precompile: bool,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, CompileError> {
        proof_decl! { let ghost source = rule; }
        // No `?` may bypass disposal of the caller's recursive owned source.
        let lowered = lower_rule(&store, &rule, limits, world);
        rule.dispose();
        let (mode, template, _maps) = lowered?;
        let runtime = RuleRuntime::new(&template, precompile, limits, world)?;
        proof! { reveal(crate::runtime::verify::constructor_result); }
        proof_decl! { let tracked observations = Map::<(usize, u64), ObservedHistory>::tracked_empty(); }
        Ok(Self {
            template,
            mode,
            store,
            runtime,
            #[cfg(verus_keep_ghost)]
            source: verus_exec_expr! { Ghost(source) },
            #[cfg(verus_keep_ghost)]
            maps: _maps,
            #[cfg(verus_keep_ghost)]
            observations: verus_exec_expr! { Tracked(observations) },
        })
    }

    #[verus_spec(result => ensures result == self.mode_spec())]
    pub const fn mode(&self) -> RuleMode {
        proof! { reveal(CompiledRule::mode_spec); }
        self.mode
    }

    /// `None` is only a head mismatch; operational errors never become verdicts.
    #[verus_spec(result => requires decision_requires(*old(self), *history),
        ensures decision_result(*old(self), *final(self), *history, *candidate, result))]
    pub fn accepts_history(
        &mut self,
        history: &History<E>,
        candidate: &E,
    ) -> Result<Option<bool>, HistoryError> {
        self.accepts_history_with_limits(history, candidate, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires decision_requires(*old(self), *history),
        ensures decision_result(*old(self), *final(self), *history, *candidate, result))]
    pub(crate) fn accepts_history_with_limits<L: Limits>(
        &mut self,
        history: &History<E>,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        // Check before projections, codebook publication, or any residual lookup.
        if !same_owner(&self.store, history.store()) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        proof! {
            crate::history::lemma_stored_history_view(history.numeric);
            let ghost registry = books::registry_id(&self.store);
            lemma_history_compatible(registry, history.id, history.numeric,
                self.runtime.snapshots@, self.observations.borrow(), history.registration.borrow(), history.lifecycle.borrow());
            let key = (history.id, history.numeric.revision);
            let events = crate::kernel::verify::events_view(history.numeric.events@);
            reveal(crate::runtime::verify::runtime_wf);
            crate::runtime::verify::lemma_cursor_cache_observe(self.runtime.pair,
                self.runtime.cursors@, self.runtime.snapshots@, history.id, history.numeric.revision, events);
            let tracked observation = ObservedHistory {
                snapshot: history.lifecycle.borrow().observe(),
                registration: history.registration.borrow().duplicate(),
            };
            lemma_observations_insert(registry, self.runtime.snapshots@, self.observations@, key, events, observation);
            self.observations.borrow_mut().tracked_insert(key, observation);
            *self.runtime.snapshots = self.runtime.snapshots@.insert(key, events);
            assert(compiled_wf(*self));
        }
        let (encoded, _maps) = self.store.encode_event_with_snapshot(
            candidate,
            verus_exec_expr! { Ghost(self.maps@) },
            verus_exec_expr! { Ghost(history.maps@) },
        );
        let request = encoded?;
        proof_decl! { let ghost observed = self.runtime.snapshots@; }
        let first = decide_template(
            &mut self.runtime,
            &self.template,
            history.id,
            &request,
            &history.numeric,
            limits,
            world,
        );
        proof! {
            let key = (history.id, history.numeric.revision);
            let events = crate::kernel::verify::events_view(history.numeric.events@);
            assert(observed.insert(key, events) =~= observed);
            assert(self.runtime.snapshots@ == observed);
            assert(compiled_wf(*self));
        }
        let result = match first {
            Err(HistoryError::GraphLimit { .. }) => {
                // A failed replacement must not discard the old committed cursor cache.
                let mut replacement =
                    RuleRuntime::new(&self.template, cfg!(feature = "cache"), limits, world)?;
                proof! { reveal(crate::runtime::verify::constructor_result); }
                proof_decl! { let tracked mut replacement_observations = Map::<(usize, u64), ObservedHistory>::tracked_empty(); }
                proof! {
                    crate::history::lemma_stored_history_view(history.numeric);
                    let tracked observation = ObservedHistory {
                        snapshot: history.lifecycle.borrow().observe(),
                        registration: history.registration.borrow().duplicate(),
                    };
                    let key = (history.id, history.numeric.revision);
                    let events = crate::kernel::verify::events_view(history.numeric.events@);
                    lemma_observations_insert(books::registry_id(&self.store), replacement.snapshots@,
                        replacement_observations, key, events, observation);
                    replacement_observations.tracked_insert(key, observation);
                    *replacement.snapshots = replacement.snapshots@.insert(key, events);
                    assert(decision::runtime_represents(self.template, replacement));
                }
                proof_decl! { let ghost new_snapshots = replacement.snapshots@; }
                let answer = decide_template(
                    &mut replacement,
                    &self.template,
                    history.id,
                    &request,
                    &history.numeric,
                    limits,
                    world,
                )?;
                proof! {
                    let key = (history.id, history.numeric.revision);
                    let events = crate::kernel::verify::events_view(history.numeric.events@);
                    assert(new_snapshots.insert(key, events) =~= new_snapshots);
                    assert(replacement.snapshots@ == new_snapshots);
                    assert(observations_wf(books::registry_id(&self.store),
                        replacement.snapshots@, replacement_observations));
                }
                self.runtime = replacement;
                proof! {
                    *self.observations = replacement_observations;
                    assert(compiled_wf(*self));
                }
                Ok(answer)
            }
            other => other,
        };
        proof! {
            if books::native_obligations::<E>() {
                lemma_typed_result(entry, *history, *candidate, request, _maps@, result);
            }
        }
        result
    }
}

/// Bind the candidate and evaluate against the retained graph generation.
#[verus_verify]
#[verus_spec(result =>
    requires decision::runtime_represents(*template, *old(runtime)),
        crate::flat::verify::structural_wf(*template),
        crate::runtime::verify::snapshot_compatible(old(runtime).snapshots@, history,
            stored.revision, crate::kernel::verify::events_view(stored.events@)),
    ensures decision::runtime_represents(*template, *final(runtime)),
        crate::progress::verify::pair_frame(old(runtime).pair, final(runtime).pair),
        result is Err ==> final(runtime).cursors@ == old(runtime).cursors@,
        final(runtime).snapshots@ == old(runtime).snapshots@
            || final(runtime).snapshots@ == old(runtime).snapshots@.insert((history, stored.revision),
                crate::kernel::verify::events_view(stored.events@)),
        numeric_result(*template, *request, *stored, result),
)]
pub(crate) fn decide_template<L: Limits>(
    runtime: &mut RuleRuntime,
    template: &FlatPair<u64>,
    history: usize,
    request: &crate::store::Event,
    stored: &StoredHistory,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Option<bool>, HistoryError> {
    proof_decl! { let ghost entry = *runtime; }
    let bindings = match template.bindings(request) {
        Some(bindings) => bindings,
        None => return Ok(None),
    };
    proof! {
        crate::compile::verify::lemma_bindings_match(*template, *request, bindings);
        reveal(crate::runtime::verify::resume_requires);
        reveal(crate::runtime::verify::runtime_wf);
    }
    let result = decide_numeric(runtime, history, &bindings, stored, limits, world);
    proof! {
        decision::lemma_runtime_frame(*template, entry, *runtime);
    }
    match result {
        Err(error) => Err(error),
        Ok(answer) => {
            proof! {
                assert(exists|witness: crate::runtime::Bindings|
                    crate::compile::verify::bindings_match(*template, *request, witness)
                        && crate::verify::history_specs::event_wf(witness@)
                        && answer == crate::compile::verify::source_regex(*template,
                            template.root as nat, witness@,
                            crate::kernel::verify::events_view(stored.events@))) by {
                    assert(crate::compile::verify::bindings_match(*template, *request, bindings));
                }
            }
            Ok(Some(answer))
        }
    }
}

/// One full-prefix batch makes answer/publication failures atomic for the whole call.
#[verus_verify]
#[verus_spec(result =>
    requires crate::runtime::verify::runtime_wf(*old(runtime)),
        crate::runtime::verify::snapshot_compatible(old(runtime).snapshots@, history, stored.revision,
            crate::kernel::verify::events_view(stored.events@)),
        crate::verify::history_specs::event_wf(bindings@),
    ensures crate::runtime::verify::runtime_wf(*final(runtime)),
        crate::progress::verify::pair_frame(old(runtime).pair, final(runtime).pair),
        result is Err ==> final(runtime).cursors@ == old(runtime).cursors@,
        final(runtime).snapshots@ == old(runtime).snapshots@.insert((history, stored.revision),
            crate::kernel::verify::events_view(stored.events@)),
        result matches Ok(answer) ==> answer == crate::kernel::verify::regex_lang(
            old(runtime).pair.store.graph(), bindings@, old(runtime).pair.root@,
            crate::kernel::verify::events_view(stored.events@)),
)]
pub(crate) fn decide_numeric<L: Limits>(
    runtime: &mut RuleRuntime,
    history: usize,
    bindings: &crate::runtime::Bindings,
    stored: &StoredHistory,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<bool, HistoryError> {
    proof! {
        crate::history::lemma_stored_history_view(*stored);
        reveal(crate::runtime::verify::runtime_wf);
        reveal(crate::runtime::verify::resume_requires);
        reveal(crate::runtime::verify::resume_ensures);
        reveal(crate::runtime::verify::advance_requires);
        reveal(crate::runtime::verify::advance_ensures);
    }
    proof_decl! { let ghost initial_snapshots = runtime.snapshots@; }
    let target = stored.len();
    let mut cursor = runtime.resume_cursor(history, bindings, stored, target);
    proof! {
        assert(runtime.snapshots@ == initial_snapshots.insert((history, stored.revision),
            crate::kernel::verify::events_view(stored.events@)));
    }
    proof_decl! { let ghost start = cursor; }
    let result = runtime.advance_cursor(
        &mut cursor,
        history,
        bindings,
        stored,
        target,
        usize::MAX,
        limits,
        world,
    );
    proof! {
        let key = (history, stored.revision);
        let events = crate::kernel::verify::events_view(stored.events@);
        assert(runtime.snapshots@ == initial_snapshots.insert(key, events).insert(key, events));
        assert(initial_snapshots.insert(key, events).insert(key, events) =~= initial_snapshots.insert(key, events));
        crate::verify::history_specs::lemma_selected_end(
            start.consumed as nat, target as nat, usize::MAX as nat);
        assert(crate::kernel::verify::events_view(stored.events@).take(target as int)
            =~= crate::kernel::verify::events_view(stored.events@));
    }
    match result {
        Err(error) => Err(error),
        Ok(Some(answer)) => Ok(answer),
        Ok(None) => {
            proof! { assert(false); }
            Err(HistoryError::invariant(
                "complete history batch returned no answer",
            ))
        }
    }
}

#[cfg(any(test, feature = "test-util"))]
impl<E: Event> CompiledRule<E> {
    /// Construct the same runtime without optional precompilation for work probes.
    pub fn new_lazy(store: Arc<Store<E>>, rule: Rule<E>) -> Result<Self, CompileError> {
        Self::construct(store, rule, false, &mut Unmetered, &mut ObservationWorld)
    }

    pub fn work_counters(&self) -> &crate::runtime::WorkCounters {
        self.runtime.work_counters()
    }

    pub fn reset_work_counters(&mut self) {
        self.runtime.reset_work_counters();
    }

    pub fn work_events(&self) -> usize {
        self.runtime.work_events()
    }

    pub fn reset_work_events(&mut self) {
        self.runtime.reset_work_events();
    }

    pub fn clear_cursors(&mut self) {
        self.runtime.clear_cursors();
    }

    pub fn cursor_positions(
        &self,
    ) -> alloc::vec::Vec<(usize, crate::runtime::Bindings, u64, usize)> {
        self.runtime.cursor_positions()
    }

    pub fn replace_graph_byte_pressure(&mut self, bytes: usize) -> usize {
        self.runtime.replace_graph_byte_pressure(bytes)
    }

    pub fn set_answer_checkpoint_failure(&mut self, fail: bool) {
        self.runtime.set_answer_checkpoint_failure(fail);
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;
    use crate::limits::LimitError;
    use crate::syntax::{AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, TestExpr};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Probe(u8, u8, u8);

    impl Event for Probe {
        type Principal = u8;
        type Action = u8;
        type Resource = u8;
        fn principal(self) -> u8 {
            self.0
        }
        fn action(self) -> u8 {
            self.1
        }
        fn resource(self) -> u8 {
            self.2
        }
    }

    fn head() -> Head<Probe> {
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(2),
            ComponentPattern::variable("resource"),
        )
    }

    fn reads() -> Rule<Probe> {
        Rule::new(
            RuleMode::Require,
            head(),
            RegexExpr::star(RegexExpr::test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(1)),
            ))),
        )
    }

    #[test]
    fn consuming_constructor_disposes_deep_success_and_unbound_failure() {
        let store = Arc::new(Store::new().unwrap());
        let mut valid = RegexExpr::epsilon();
        let mut invalid = RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("missing")),
        ));
        for _ in 0..4096 {
            valid = RegexExpr::star(valid);
            invalid = RegexExpr::star(invalid);
        }
        let mut compiled = CompiledRule::new(
            Arc::clone(&store),
            Rule::new(RuleMode::Require, head(), valid),
        )
        .unwrap();
        let history = History::new(Arc::clone(&store)).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Probe(1, 2, 1)),
            Ok(Some(true))
        );
        assert!(matches!(CompiledRule::new(store,
            Rule::new(RuleMode::Require, head(), invalid)),
            Err(CompileError::UnboundVariable { name }) if name == "missing"));
    }

    struct FailPublication;
    impl Limits for FailPublication {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Err(LimitError::MemoryLimitExceeded { usage: 2, limit: 1 })
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
    }

    #[test]
    fn answer_and_publication_errors_preserve_committed_cursors_and_history() {
        let store = Arc::new(Store::new().unwrap());
        let mut history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let mut compiled = CompiledRule::new_lazy(store, reads()).unwrap();
        let candidate = Probe(1, 2, 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        history.push(Probe(1, 1, 1)).unwrap();
        let revision = history.numeric.revision();
        let raw = history.as_slice().to_vec();
        let numeric = history.numeric.events.clone();

        compiled.set_answer_checkpoint_failure(true);
        assert!(matches!(
            compiled.accepts_history(&history, &candidate),
            Err(HistoryError::Limit(_))
        ));
        compiled.set_answer_checkpoint_failure(false);
        assert_eq!(compiled.cursor_positions(), prior);
        assert!(matches!(
            compiled.accepts_history_with_limits(
                &history,
                &candidate,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(history.as_slice(), raw);
        assert_eq!(history.numeric.events, numeric);
        assert_eq!(history.numeric.revision(), revision);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
    }

    #[test]
    fn failed_graph_replacement_keeps_old_generation_cache() {
        let store = Arc::new(Store::new().unwrap());
        let mut history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let read = || {
            RegexExpr::test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(1)),
            ))
        };
        let rule = Rule::new(
            RuleMode::Require,
            head(),
            RegexExpr::concat([read(), RegexExpr::star(read())]),
        );
        let mut compiled = CompiledRule::new_lazy(store, rule).unwrap();
        let candidate = Probe(1, 2, 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        history.push(Probe(1, 1, 1)).unwrap();
        let pressure = compiled.replace_graph_byte_pressure(crate::limits::MAX_GRAPH_BYTES + 1);
        let request = compiled.store.encode_event(&candidate).unwrap();
        assert!(matches!(
            decide_template(
                &mut compiled.runtime,
                &compiled.template,
                history.id,
                &request,
                &history.numeric,
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::GraphLimit { .. })
        ));
        assert!(matches!(
            compiled.accepts_history_with_limits(
                &history,
                &candidate,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(
            compiled.replace_graph_byte_pressure(pressure),
            crate::limits::MAX_GRAPH_BYTES + 1
        );
        compiled.replace_graph_byte_pressure(crate::limits::MAX_GRAPH_BYTES + 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        assert_eq!(compiled.work_events(), 2);
        compiled.reset_work_events();
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        assert_eq!(compiled.work_events(), 0);
    }

    #[test]
    fn candidate_allocation_failure_keeps_prior_cursors_and_history() {
        let store = Arc::new(Store::new().unwrap());
        let history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let mut compiled = CompiledRule::new(store, reads()).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Probe(1, 2, 1)),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        let failure = crate::observation::fail_reservations_after(0);
        assert_eq!(
            compiled.accepts_history(&history, &Probe(2, 2, 1)),
            Err(HistoryError::AllocationFailed)
        );
        drop(failure);
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(history.as_slice(), [Probe(1, 1, 1)]);
        assert_eq!(history.numeric.len(), 1);
        assert_eq!(history.numeric.revision(), 0);
        assert_eq!(
            compiled.accepts_history(&history, &Probe(2, 2, 1)),
            Ok(Some(true))
        );
    }

    #[test]
    fn foreign_owner_is_rejected_before_even_head_mismatch_projections() {
        use core::sync::atomic::{AtomicUsize, Ordering};
        static PROJECTIONS: AtomicUsize = AtomicUsize::new(0);
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct Counted(Probe);
        impl Event for Counted {
            type Principal = u8;
            type Action = u8;
            type Resource = u8;
            fn principal(self) -> u8 {
                PROJECTIONS.fetch_add(1, Ordering::SeqCst);
                self.0.0
            }
            fn action(self) -> u8 {
                PROJECTIONS.fetch_add(1, Ordering::SeqCst);
                self.0.1
            }
            fn resource(self) -> u8 {
                PROJECTIONS.fetch_add(1, Ordering::SeqCst);
                self.0.2
            }
        }
        let store = Arc::new(Store::new().unwrap());
        let foreign = Arc::new(Store::new().unwrap());
        let rule = Rule::<Counted>::new(
            RuleMode::Require,
            Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(2),
                ComponentPattern::variable("resource"),
            ),
            RegexExpr::epsilon(),
        );
        let mut compiled = CompiledRule::new(store, rule).unwrap();
        let history = History::new(foreign).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Counted(Probe(1, 3, 1))),
            Err(HistoryError::WrongHistoryOwner)
        );
        assert_eq!(PROJECTIONS.load(Ordering::SeqCst), 0);
        assert!(compiled.cursor_positions().is_empty());
    }
}
