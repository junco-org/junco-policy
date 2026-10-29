//! Constant encoding preserves portable DAG topology; graph compilation is separate.

use crate::error::HistoryError;
use crate::event::Event;
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::flatten::ComponentValue;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::syntax::Component;
#[cfg(verus_keep_ghost)]
use crate::verify::encoding::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Component-specific constant encoding. Hashes are lookup aids, never identities.
///
/// Native implementations opt in to the ghost contract only after establishing
/// their equality/hash correspondence and finite-map implementation obligations.
pub trait FlatEncoder<C>: Sized {
    spec fn equality() -> Equality<C>;
    spec fn domain() -> Domain<C>;
    spec fn maps(&self) -> Codebook<C>;
    spec fn obeys_encoding_spec(&self) -> bool;

    // Keep the original books valid when a nested mutable encoder borrow ends.
    #[verifier::prophetic]
    spec fn restoration(&self) -> (Codebook<C>, bool);

    fn encode(&mut self, field: Component, value: &C) -> (result: Result<u64, HistoryError>)
        ensures final(self).restoration() == old(self).restoration(),
            old(self).obeys_encoding_spec()
            && maps_wf(old(self).maps(), Self::equality(), Self::domain()) ==> {
            final(self).obeys_encoding_spec()
            && maps_wf(final(self).maps(), Self::equality(), Self::domain())
            && extends(old(self).maps(), final(self).maps(), Self::equality())
            && match result {
                Ok(id) => Self::domain()(field, *value)
                    && encoded(final(self).maps(), Self::equality(), field, *value, id),
                Err(_) => true,
            }
        };
}

pub open spec fn encoder_wf<C, M: FlatEncoder<C>>(encoder: M) -> bool {
    encoder.obeys_encoding_spec() && maps_wf(encoder.maps(), M::equality(), M::domain())
}

/// Validate a typed constant's coordinate before touching a component codebook.
pub fn validate_component<E: Event>(field: Component, value: &ComponentValue<E>)
    -> (result: Result<(), HistoryError>)
    ensures result.is_ok() == match (field, *value) {
        (Component::Principal, ComponentValue::Principal(_))
        | (Component::Action, ComponentValue::Action(_))
        | (Component::Resource, ComponentValue::Resource(_)) => true,
        _ => false,
    },
    result matches Err(error) ==> match error {
        HistoryError::InvalidPolicy { path, message } => path@ == "$"@
            && message == "constant belongs to another component",
        _ => false,
    },
{
    match (field, value) {
        (Component::Principal, ComponentValue::Principal(_))
        | (Component::Action, ComponentValue::Action(_))
        | (Component::Resource, ComponentValue::Resource(_)) => Ok(()),
        _ => Err(HistoryError::invalid_policy("$", "constant belongs to another component")),
    }
}

fn invalid_source() -> (error: HistoryError)
    ensures match error {
        HistoryError::InvalidPolicy { path, message } => path@ == "$"@
            && message == "invalid portable history source",
        _ => false,
    },
{
    HistoryError::invalid_policy("$", "invalid portable history source")
}

fn copy_ids<L: Limits>(source: &[u32], limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<Vec<u32>, HistoryError>)
    ensures result matches Ok(ids) ==> ids@ == source@,
{
    let mut ids = Vec::new();
    match world.try_reserve_vec_exact(&mut ids, source.len()) {
        Ok(()) => {}, Err(_) => return Err(HistoryError::AllocationFailed),
    }
    let mut index = 0;
    while index < source.len()
        invariant index <= source@.len(), ids@ == source@.take(index as int),
        decreases source@.len() - index,
    {
        limits.checkpoint()?;
        ids.push(source[index]);
        index += 1;
    }
    Ok(ids)
}

fn encode_head<C, M: FlatEncoder<C>>(source: &FlatHead<C>, field: Component, encoder: &mut M)
    -> (result: Result<FlatHead<u64>, HistoryError>)
    ensures result matches Ok(head) ==> head_shape(*source, head),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(head) ==> head_encoded(*source, head, field, final(encoder).maps(), M::equality())
                && head_in_domain(*source, field, M::domain())),
{
    match source {
        FlatHead::Any => Ok(FlatHead::Any),
        FlatHead::Bind => Ok(FlatHead::Bind),
        FlatHead::Constant(value) => Ok(FlatHead::Constant(encoder.encode(field, value)?)),
    }
}

fn encode_test<C, M: FlatEncoder<C>, L: Limits>(source: &FlatTest<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatTest<u64>, HistoryError>)
    ensures result matches Ok(test) ==> test_shape(*source, test),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(test) ==> test_encoded(*source, test, final(encoder).maps(), M::equality())
                && test_in_domain(*source, M::domain())),
{
    match source {
        FlatTest::Bool(value) => Ok(FlatTest::Bool(*value)),
        FlatTest::Atom { field, term, positive } => {
            let term = match term {
                FlatTerm::Constant(value) => FlatTerm::Constant(encoder.encode(*field, value)?),
                FlatTerm::Variable(variable) => FlatTerm::Variable(*variable),
            };
            Ok(FlatTest::Atom { field: *field, term, positive: *positive })
        },
        FlatTest::And(children) => Ok(FlatTest::And(copy_ids(children, limits, world)?)),
        FlatTest::Or(children) => Ok(FlatTest::Or(copy_ids(children, limits, world)?)),
    }
}

fn copy_regex<L: Limits>(source: &FlatRegex, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRegex, HistoryError>)
    ensures result matches Ok(regex) ==> regex_same(*source, regex),
{
    Ok(match source {
        FlatRegex::Empty => FlatRegex::Empty,
        FlatRegex::All => FlatRegex::All,
        FlatRegex::Epsilon => FlatRegex::Epsilon,
        FlatRegex::Test(id) => FlatRegex::Test(*id),
        FlatRegex::Concat(ids) => FlatRegex::Concat(copy_ids(ids, limits, world)?),
        FlatRegex::Union(ids) => FlatRegex::Union(copy_ids(ids, limits, world)?),
        FlatRegex::Intersect(ids) => FlatRegex::Intersect(copy_ids(ids, limits, world)?),
        FlatRegex::Star(id) => FlatRegex::Star(*id),
        FlatRegex::Complement(id) => FlatRegex::Complement(*id),
    })
}

/// Validate before interning, then encode each stored constant exactly once.
/// Repeated edges, unreachable nodes, and non-last roots remain untouched.
pub fn lower_flat<C, M: FlatEncoder<C>, L: Limits>(source: &FlatPair<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatPair<u64>, HistoryError>)
    ensures result matches Ok(target) ==> topology(*source, target)
            && crate::flat::verify::structural_wf(target),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(target) ==> lowering(*source, target, final(encoder).maps(), M::equality())
                && constants_in_domain(*source, M::domain())),
{
    if source.validate().is_err() { return Err(invalid_source()); }
    let ghost initial_maps = encoder.maps();
    let ghost verified = encoder_wf::<C, M>(*encoder);
    let principal = encode_head(&source.head[0], Component::Principal, encoder)?;
    let ghost principal_maps = encoder.maps();
    let action = encode_head(&source.head[1], Component::Action, encoder)?;
    let ghost action_maps = encoder.maps();
    let resource = encode_head(&source.head[2], Component::Resource, encoder)?;
    proof {
        if verified {
            lemma_extends_transitive(initial_maps, principal_maps, action_maps, M::equality());
            lemma_extends_transitive(principal_maps, action_maps, encoder.maps(), M::equality());
            lemma_extends_transitive(initial_maps, action_maps, encoder.maps(), M::equality());
            lemma_head_extends(source.head@[0], principal, Component::Principal, principal_maps, encoder.maps(), M::equality());
            lemma_head_extends(source.head@[1], action, Component::Action, action_maps, encoder.maps(), M::equality());
        }
    }
    let mut builder = FlatBuilder::new([principal, action, resource]);
    let mut index = 0;
    while index < source.tests.len()
        invariant index <= source.tests@.len(), builder.wf(),
            encoder.restoration() == old(encoder).restoration(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            builder.tests_view().len() == index, builder.regexes_view().len() == 0,
            (forall|i: int| 0 <= i < 3 ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < index ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && (forall|i: int| 0 <= i < 3 ==> head_in_domain(source.head@[i], field_at(i), M::domain()))
                && (forall|i: int| 0 <= i < index ==> test_in_domain(source.tests@[i], M::domain()))
                && (forall|i: int| 0 <= i < 3 ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < index ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.tests@.len() - index,
    {
        limits.checkpoint()?;
        let ghost before = encoder.maps();
        let node = encode_test(&source.tests[index], encoder, limits, world)?;
        proof {
            if verified {
                lemma_extends_transitive(initial_maps, before, encoder.maps(), M::equality());
                assert forall|i: int| 0 <= i < 3 implies head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()) by {
                    lemma_head_extends(source.head@[i], builder.head_view()[i], field_at(i), before, encoder.maps(), M::equality());
                }
                assert forall|i: int| 0 <= i < index implies test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality()) by {
                    lemma_test_extends(source.tests@[i], builder.tests_view()[i], before, encoder.maps(), M::equality());
                }
            }
        }
        builder.test(node, limits, world)?;
        index += 1;
    }
    index = 0;
    while index < source.regexes.len()
        invariant index <= source.regexes@.len(), builder.wf(),
            encoder.restoration() == old(encoder).restoration(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            regex_tables_same(source.regexes@.take(index as int), builder.regexes_view()),
            builder.tests_view().len() == source.tests@.len(),
            (forall|i: int| 0 <= i < 3 ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < source.tests@.len() ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && constants_in_domain(*source, M::domain())
                && (forall|i: int| 0 <= i < 3 ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < source.tests@.len() ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.regexes@.len() - index,
    {
        limits.checkpoint()?;
        let node = copy_regex(&source.regexes[index], limits, world)?;
        builder.regex(node, limits, world)?;
        index += 1;
    }
    builder.finish(source.root)
}

}

#[cfg(feature = "runtime")]
mod numeric {
    use super::*;
    use crate::graph::{ArenaStorage, CanonicalStore, RuntimeKernel, allocation};
    #[cfg(verus_keep_ghost)]
    use crate::kernel::verify as model;
    use crate::kernel::*;
    #[cfg(verus_keep_ghost)]
    use crate::normalize::verify as norm;
    use crate::progress::CompiledPair;
    use crate::store::Event as NumericEvent;
    #[cfg(verus_keep_ghost)]
    use crate::verify::history_assumptions::{KernelStoreSpec, StorageSpec};
    #[cfg(verus_keep_ghost)]
    use crate::verify::history_specs as language;
    #[cfg(verus_keep_ghost)]
    use verify::*;

    #[verus_verify]
    #[verus_spec(result => ensures result@ == term_view(*term))]
    fn numeric_term(term: &FlatTerm<u64>) -> Term {
        match term {
            FlatTerm::Constant(value) => Term::Constant(*value),
            FlatTerm::Variable(field) => Term::Variable(*field),
        }
    }

    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn bindings_match(template: FlatPair<u64>, request: NumericEvent, bindings: Bindings) -> bool {
            language::head_match(head_view(template), request@, bindings@)
        }

        pub closed spec fn head_rejects(template: FlatPair<u64>, request: NumericEvent) -> bool {
            !exists|theta: language::Subst| language::head_match(head_view(template), request@, theta)
        }

        pub(crate) proof fn lemma_bindings_match(template: FlatPair<u64>, request: NumericEvent, bindings: Bindings)
            ensures bindings_match(template, request, bindings)
                == language::head_match(head_view(template), request@, bindings@),
        { reveal(bindings_match); }

        pub(crate) proof fn lemma_head_rejects(template: FlatPair<u64>, request: NumericEvent)
            ensures head_rejects(template, request)
                == !exists|theta: language::Subst| language::head_match(head_view(template), request@, theta),
        { reveal(head_rejects); }
    }

    impl FlatHead<u64> {
        #[allow(
            clippy::missing_const_for_fn,
            reason = "Keep the existing operation and its Verus contract unchanged"
        )]
        #[verus_verify]
        #[verus_spec(result => ensures match result {
        Some(binding) => language::head_field_match(self@, value as nat, binding as nat),
        None => !exists|binding: nat| language::head_field_match(self@, value as nat, binding),
    })]
        fn bind(&self, value: u64) -> Option<u64> {
            match self {
                FlatHead::Any => Some(0),
                FlatHead::Constant(expected) if value == *expected => Some(0),
                FlatHead::Constant(_) => None,
                FlatHead::Bind => Some(value),
            }
        }
    }

    #[verus_verify]
    impl FlatPair<u64> {
        #[verus_verify]
        #[verus_spec(result => ensures match result {
            Some(bindings) => bindings_match(*self, *request, bindings),
            None => head_rejects(*self, *request),
        })]
        pub fn bindings(&self, request: &NumericEvent) -> Option<Bindings> {
            proof! { reveal(bindings_match); reveal(head_rejects); }
            let p = self.head[0].bind(request.principal.get())?;
            let a = self.head[1].bind(request.action.get())?;
            let r = self.head[2].bind(request.resource.get())?;
            Some(Bindings([p, a, r]))
        }

        #[allow(
            clippy::option_if_let_else,
            reason = "Explicit matches preserve the Verus proof structure"
        )]
        #[verus_verify]
        #[verus_spec(result => ensures result matches Ok(value)
        ==> (id as nat) < values@.len() && value == values@[id as int])]
        fn lookup<T: Copy>(values: &[T], id: u32) -> KernelResult<T> {
            let index = match usize::try_from(id) {
                Ok(index) => index,
                Err(_) => return Err(HistoryError::invariant("source node index overflow")),
            };
            proof! { assert(index as nat == id as nat); }
            match values.get(index) {
                Some(value) => Ok(*value),
                None => Err(HistoryError::invariant("invalid source node reference")),
            }
        }

        #[verus_verify]
        #[verus_spec(result => ensures result matches Ok(found) ==> {
        found@.len() == ids@.len()
        && forall|i: int| 0 <= i < ids@.len()
            ==> #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int]
    })]
        fn references<T: Copy>(
            values: &[T],
            ids: &[u32],
            world: &mut ObservationWorld,
        ) -> KernelResult<Vec<T>> {
            let mut found = Vec::new();
            allocation(world.try_reserve_vec_exact(&mut found, ids.len()))?;
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= ids@.len(), found@.len() == index,
                forall|i: int| 0 <= i < index
                    ==> #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int],
            decreases ids@.len() - index,
        ))]
            while index < ids.len() {
                let id = match ids.get(index) {
                    Some(id) => *id,
                    None => return Err(HistoryError::invariant("missing source reference")),
                };
                proof! { assert(id == ids@[index as int]); }
                let value = Self::lookup(values, id)?;
                proof_decl! { let ghost previous = found@; }
                found.push(value);
                proof! {
                    assert(index < usize::MAX);
                    assert forall|i: int| 0 <= i <= index implies
                        #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int] by {
                        if i < index {
                            assert(found@[i] == previous[i]);
                        } else {
                            assert(i == index);
                            assert(found@[i] == value);
                        }
                    }
                }
                index = index.saturating_add(1);
            }
            Ok(found)
        }
        /// Build a fresh graph from immutable numeric source, including after exhaustion.
        #[allow(
            clippy::shadow_unrelated,
            reason = "Separate lowering loops retain their proof-local index bindings"
        )]
        #[verus_verify]
        #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
        #[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
        #[verus_spec(result => ensures result matches Ok(pair) ==> {
        crate::progress::verify::pair_wf(pair)
        && forall|theta: language::Subst, word: Seq<language::EventView>| language::event_wf(theta)
            ==> model::regex_lang(pair.store.graph(), theta, pair.root@, word)
                == source_regex(*self, self.root as nat, theta, word)
    })]
        pub(crate) fn compile<L: Limits>(
            &self,
            limits: &mut L,
            world: &mut ObservationWorld,
        ) -> KernelResult<CompiledPair> {
            limits.checkpoint().map_err(HistoryError::from)?;
            let mut store = CanonicalStore::new(ArenaStorage::new()?, world)?;
            let mut tests = Vec::new();
            let mut regexes = Vec::new();
            allocation(world.try_reserve_vec_exact(&mut tests, self.tests.len()))?;
            allocation(world.try_reserve_vec_exact(&mut regexes, self.regexes.len()))?;
            {
                let mut kernel = RuntimeKernel {
                    store: &mut store,
                    limits,
                    world,
                };
                proof_decl! { let ghost restoration = kernel.restoration(); }
                let mut index = 0;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant index <= self.tests@.len(), tests@.len() == index,
                    kernel.valid_store(), model::graph_wf(kernel.graph()),
                    kernel.restoration() == restoration,
                    test_maps(kernel.graph(), *self, tests@),
                    regex_maps(kernel.graph(), *self, regexes@), regexes@.len() == 0,
                decreases self.tests@.len() - index,
            ))]
                while index < self.tests.len() {
                    kernel.checkpoint()?;
                    let test = match self.tests.get(index) {
                        Some(test) => test,
                        None => return Err(HistoryError::invariant("missing numeric test node")),
                    };
                    proof_decl! { let ghost before = kernel.graph(); }
                    proof_decl! { let ghost mut selected_ids = Seq::<TestId>::empty(); }
                    proof! { assert(*test == self.tests@[index as int]); }
                    let id = match test {
                        FlatTest::Bool(value) => {
                            if *value {
                                kernel.constants().test_true
                            } else {
                                kernel.constants().test_false
                            }
                        }
                        FlatTest::Atom {
                            field,
                            term,
                            positive,
                        } => kernel.intern_test(TestView::Atom {
                            primitive: Primitive::Eq {
                                field: *field,
                                term: numeric_term(term),
                            },
                            positive: *positive,
                        })?,
                        FlatTest::And(children) => {
                            let selected = Self::references(&tests, children, kernel.world)?;
                            proof! {
                                selected_ids = selected@;
                                selected_tests_valid(kernel.graph(), *self, tests@, children@, selected@);
                            }
                            TestId::connective(&mut kernel, &selected, true)?
                        }
                        FlatTest::Or(children) => {
                            let selected = Self::references(&tests, children, kernel.world)?;
                            proof! {
                                selected_ids = selected@;
                                selected_tests_valid(kernel.graph(), *self, tests@, children@, selected@);
                            }
                            TestId::connective(&mut kernel, &selected, false)?
                        }
                    };
                    proof! {
                        maps_extend(before, kernel.graph(), *self, tests@, regexes@);
                        assert(test_correct(kernel.graph(), *self, index as nat, id)) by {
                            reveal_with_fuel(source_test, 1);
                            model::lemma_graph_wf_elim(kernel.graph());
                            assert forall|theta: language::Subst, event: language::EventView|
                                language::event_wf(theta) implies
                                norm::test_truth(kernel.graph(), theta, id@, event)
                                    == source_test(*self, index as nat, theta, event) by {
                                match test {
                                    FlatTest::Bool(_) | FlatTest::Atom { .. } => {
                                        norm::test_lemma_truth(kernel.graph(), theta, id@, event);
                                    }
                                    FlatTest::And(children) => {
                                        test_connective_transfer(kernel.graph(), *self, tests@,
                                            children@, selected_ids, theta, event, true);
                                    }
                                    FlatTest::Or(children) => {
                                        test_connective_transfer(kernel.graph(), *self, tests@,
                                            children@, selected_ids, theta, event, false);
                                    }
                                }
                            }
                        }
                        test_push(kernel.graph(), *self, tests@, id);
                    }
                    tests.push(id);
                    index = index.saturating_add(1);
                }
                let mut index = 0;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant index <= self.regexes@.len(), regexes@.len() == index,
                    kernel.valid_store(), model::graph_wf(kernel.graph()),
                    kernel.restoration() == restoration,
                    test_maps(kernel.graph(), *self, tests@), tests@.len() == self.tests@.len(),
                    regex_maps(kernel.graph(), *self, regexes@),
                decreases self.regexes@.len() - index,
            ))]
                while index < self.regexes.len() {
                    kernel.checkpoint()?;
                    let regex = match self.regexes.get(index) {
                        Some(regex) => regex,
                        None => return Err(HistoryError::invariant("missing numeric regex node")),
                    };
                    proof_decl! { let ghost before = kernel.graph(); }
                    proof_decl! { let ghost mut selected_ids = Seq::<RegexId>::empty(); }
                    proof! { assert(*regex == self.regexes@[index as int]); }
                    let id = match regex {
                        FlatRegex::Empty => kernel.constants().empty,
                        FlatRegex::All => kernel.constants().all,
                        FlatRegex::Epsilon => kernel.constants().epsilon,
                        FlatRegex::Test(test) => {
                            RegexId::from_test(&mut kernel, Self::lookup(&tests, *test)?)?
                        }
                        FlatRegex::Concat(children) => {
                            let selected = Self::references(&regexes, children, kernel.world)?;
                            proof! {
                                selected_ids = selected@;
                                selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                            }
                            RegexId::concat(&mut kernel, &selected)?
                        }
                        FlatRegex::Union(children) => {
                            let selected = Self::references(&regexes, children, kernel.world)?;
                            proof! {
                                selected_ids = selected@;
                                selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                            }
                            RegexId::set(&mut kernel, &selected, false)?
                        }
                        FlatRegex::Intersect(children) => {
                            let selected = Self::references(&regexes, children, kernel.world)?;
                            proof! {
                                selected_ids = selected@;
                                selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                            }
                            RegexId::set(&mut kernel, &selected, true)?
                        }
                        FlatRegex::Star(child) => {
                            Self::lookup(&regexes, *child)?.star(&mut kernel)?
                        }
                        FlatRegex::Complement(child) => {
                            Self::lookup(&regexes, *child)?.not(&mut kernel)?
                        }
                    };
                    proof! {
                        maps_extend(before, kernel.graph(), *self, tests@, regexes@);
                        assert(regex_correct(kernel.graph(), *self, index as nat, id)) by {
                            reveal_with_fuel(source_regex, 1);
                            norm::regex_constants(kernel.graph());
                            assert forall|theta: language::Subst, word: Seq<language::EventView>|
                                language::event_wf(theta) implies
                                model::regex_lang(kernel.graph(), theta, id@, word)
                                    == source_regex(*self, index as nat, theta, word) by {
                                match regex {
                                    FlatRegex::Test(test) => {
                                        assert((*test as nat) < tests@.len());
                                        assert(test_correct(kernel.graph(), *self, *test as nat,
                                            tests@[*test as int]));
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Concat(children) => {
                                        assert(selected_ids =~= Seq::new(children@.len(),
                                            |i: int| regexes@[children@[i] as int]));
                                        regex_concat_transfer(kernel.graph(), *self, regexes@, children@,
                                            index as nat, theta, word);
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Star(child) => {
                                        regex_star_transfer(kernel.graph(), *self, regexes@,
                                            *child as nat, theta, word);
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Union(children) => {
                                        regex_set_transfer(kernel.graph(), *self, regexes@,
                                            children@, selected_ids, theta, word, false);
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Intersect(children) => {
                                        regex_set_transfer(kernel.graph(), *self, regexes@,
                                            children@, selected_ids, theta, word, true);
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Complement(child) => {
                                        assert((*child as nat) < regexes@.len());
                                        assert(regex_correct(kernel.graph(), *self, *child as nat,
                                            regexes@[*child as int]));
                                        assert(self.regexes@[index as int] == FlatRegex::Complement(*child));
                                        assert(source_regex(*self, index as nat, theta, word)
                                            == ((*child as nat) < index && !source_regex(*self, *child as nat, theta, word)));
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == !model::regex_lang(kernel.graph(), theta, regexes@[*child as int]@, word));
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                    FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => {
                                        assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                            == source_regex(*self, index as nat, theta, word));
                                    }
                                }
                            }
                        }
                        regex_push(kernel.graph(), *self, regexes@, id);
                    }
                    regexes.push(id);
                    index = index.saturating_add(1);
                }
                proof! {
                    assert(kernel.valid_store());
                    assert(model::graph_wf(kernel.graph()));
                    assert(regex_maps(kernel.graph(), *self, regexes@));
                }
            }
            proof! {
                assert(store.valid_store());
                assert(model::graph_wf(store.graph()));
                assert(regex_maps(store.graph(), *self, regexes@));
            }
            let root = Self::lookup(&regexes, self.root)?;
            limits.checkpoint().map_err(HistoryError::from)?;
            proof! {
                assert(model::graph_wf(store.graph()));
                assert(regex_correct(store.graph(), *self, self.root as nat, root));
            }
            Ok(CompiledPair::new(store, root))
        }
    }

    impl Primitive {
        /// The hot boundary performs only fixed-coordinate u64 equality and a checkpoint.
        // Every binding index addresses one of the three fixed coordinates.
        #[allow(
            clippy::indexing_slicing,
            reason = "Binding indices address the three fixed coordinates"
        )]
        #[allow(
            clippy::shadow_unrelated,
            reason = "Term fields mirror the matched Verus model variants"
        )]
        #[verus_verify]
        #[verus_spec(result => ensures result matches Ok(answer)
        ==> answer == model::primitive_holds(bindings@, self@, event@))]
        pub(crate) fn classify<L: Limits>(
            self,
            event: &NumericEvent,
            bindings: &Bindings,
            limits: &mut L,
            _world: &mut ObservationWorld,
        ) -> KernelResult<bool> {
            limits.checkpoint().map_err(HistoryError::from)?;
            let Primitive::Eq { field, term } = self;
            let left = match field {
                Component::Principal => event.principal.get(),
                Component::Action => event.action.get(),
                Component::Resource => event.resource.get(),
            };
            // Variables read the fixed request substitution, not another history-event coordinate.
            let right = match term {
                Term::Constant(value) => value,
                Term::Variable(field) => match field {
                    Component::Principal => bindings.0[0],
                    Component::Action => bindings.0[1],
                    Component::Resource => bindings.0[2],
                },
            };
            Ok(left == right)
        }
    }

    #[cfg(verus_keep_ghost)]
    pub mod verify {
        use super::*;
        pub use super::{bindings_match, head_rejects};
        pub(crate) use super::{lemma_bindings_match, lemma_head_rejects};
        use crate::verify::history_specs::{EventView, Subst};
        verus! {
        pub open spec fn term_view(term: FlatTerm<u64>) -> model::GTerm {
            match term {
                FlatTerm::Constant(value) => model::GTerm::Constant(value as nat),
                FlatTerm::Variable(field) => model::GTerm::Variable(field),
            }
        }

        impl View for FlatHead<u64> {
            type V = language::HeadField;
            open spec fn view(&self) -> language::HeadField {
                match self {
                    FlatHead::Any => language::HeadField::Any,
                    FlatHead::Constant(value) => language::HeadField::Constant(*value as nat),
                    FlatHead::Bind => language::HeadField::Bind,
                }
            }
        }

        pub open spec fn head_view(template: FlatPair<u64>) -> language::Head {
            language::Head {
                principal: template.head[0]@,
                action: template.head[1]@,
                resource: template.head[2]@,
            }
        }

        /// Independent interpretation of a cold numeric test table. The index guard
        /// makes this total even for malformed templates; executable lookup rejects
        /// those references rather than treating this default as a verdict.
        pub open spec fn source_test(template: FlatPair<u64>, index: nat, theta: Subst, event: EventView) -> bool
            decreases index,
        {
            if index >= template.tests@.len() { false }
            else { match template.tests@[index as int] {
                FlatTest::Bool(value) => value,
                FlatTest::Atom { field, term, positive } =>
                    model::primitive_holds(theta, model::Primitive::Eq(field, term_view(term)), event) == positive,
                FlatTest::And(children) => forall|i: int| 0 <= i < children@.len()
                    ==> children@[i] < index && source_test(template, children@[i] as nat, theta, event),
                FlatTest::Or(children) => exists|i: int| 0 <= i < children@.len()
                    && children@[i] < index && source_test(template, children@[i] as nat, theta, event),
            }}
        }

        /// Independent regex language over the template's postorder nodes.
        pub open spec fn source_regex(template: FlatPair<u64>, index: nat, theta: Subst, word: Seq<EventView>) -> bool
            decreases index,
        {
            if index >= template.regexes@.len() { false }
            else { match template.regexes@[index as int] {
                FlatRegex::Empty => false,
                FlatRegex::All => true,
                FlatRegex::Epsilon => word.len() == 0,
                FlatRegex::Test(test) => word.len() == 1 && source_test(template, test as nat, theta, word[0]),
                FlatRegex::Union(children) => exists|i: int| 0 <= i < children@.len()
                    && children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
                FlatRegex::Intersect(children) => forall|i: int| 0 <= i < children@.len()
                    ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
                FlatRegex::Concat(children) => exists|parts: Seq<Seq<EventView>>|
                    parts.len() == children@.len() && parts.flatten() == word
                    && forall|i: int| 0 <= i < children@.len()
                        ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, parts[i]),
                FlatRegex::Star(child) => child < index && exists|parts: Seq<Seq<EventView>>|
                    parts.flatten() == word && forall|i: int| 0 <= i < parts.len()
                        ==> source_regex(template, child as nat, theta, parts[i]),
                FlatRegex::Complement(child) => child < index && !source_regex(template, child as nat, theta, word),
            }}
        }

        pub(crate) open(crate) spec fn test_correct(g: model::Graph, template: FlatPair<u64>, index: nat, id: TestId) -> bool {
            id@ < g.tests.len() && forall|theta: Subst, event: EventView| language::event_wf(theta)
                ==> norm::test_truth(g, theta, id@, event) == source_test(template, index, theta, event)
        }

        pub(crate) open(crate) spec fn regex_correct(g: model::Graph, template: FlatPair<u64>, index: nat, id: RegexId) -> bool {
            id@ < g.regexes.len() && forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta)
                ==> model::regex_lang(g, theta, id@, word) == source_regex(template, index, theta, word)
        }

        pub(crate) open(crate) spec fn test_maps(g: model::Graph, template: FlatPair<u64>, ids: Seq<TestId>) -> bool {
            ids.len() <= template.tests@.len()
            && forall|i: int| 0 <= i < ids.len() ==> test_correct(g, template, i as nat, ids[i])
        }

        pub(crate) open(crate) spec fn regex_maps(g: model::Graph, template: FlatPair<u64>, ids: Seq<RegexId>) -> bool {
            ids.len() <= template.regexes@.len()
            && forall|i: int| 0 <= i < ids.len() ==> regex_correct(g, template, i as nat, ids[i])
        }

        pub(crate) proof fn maps_extend(before: model::Graph, after: model::Graph,
            template: FlatPair<u64>, tests: Seq<TestId>, regexes: Seq<RegexId>)
            requires model::graph_wf(before), model::graph_extends(before, after),
                test_maps(before, template, tests), regex_maps(before, template, regexes),
            ensures test_maps(after, template, tests), regex_maps(after, template, regexes),
        {
            model::lemma_graph_wf_elim(before);
            model::lemma_lift_stable_under_extends(before, after);
            assert forall|i: int| 0 <= i < tests.len() implies test_correct(after, template, i as nat, tests[i]) by {
                assert(test_correct(before, template, i as nat, tests[i]));
            }
            assert forall|i: int| 0 <= i < regexes.len() implies regex_correct(after, template, i as nat, regexes[i]) by {
                assert(regex_correct(before, template, i as nat, regexes[i]));
            }
        }

        pub(crate) proof fn test_push(g: model::Graph, template: FlatPair<u64>, tests: Seq<TestId>, id: TestId)
            requires test_maps(g, template, tests), tests.len() < template.tests@.len(),
                test_correct(g, template, tests.len(), id),
            ensures test_maps(g, template, tests.push(id)),
        {
            assert forall|i: int| 0 <= i < tests.push(id).len()
                implies test_correct(g, template, i as nat, tests.push(id)[i]) by {
                if i < tests.len() { assert(tests.push(id)[i] == tests[i]); }
                else { assert(i == tests.len()); }
            }
        }

        pub(crate) proof fn regex_push(g: model::Graph, template: FlatPair<u64>, regexes: Seq<RegexId>, id: RegexId)
            requires regex_maps(g, template, regexes), regexes.len() < template.regexes@.len(),
                regex_correct(g, template, regexes.len(), id),
            ensures regex_maps(g, template, regexes.push(id)),
        {
            assert forall|i: int| 0 <= i < regexes.push(id).len()
                implies regex_correct(g, template, i as nat, regexes.push(id)[i]) by {
                if i < regexes.len() { assert(regexes.push(id)[i] == regexes[i]); }
                else { assert(i == regexes.len()); }
            }
        }

        pub(crate) proof fn selected_tests_valid(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<TestId>, children: Seq<u32>, selected: Seq<TestId>)
            requires test_maps(g, template, ids), selected.len() == children.len(),
                forall|i: int| 0 <= i < children.len()
                    ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            ensures norm::test_ids_valid(g, selected),
        {
            assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.tests.len() by {
                assert(children[i] < ids.len());
                assert(test_correct(g, template, children[i] as nat, ids[children[i] as int]));
            }
        }

        pub(crate) proof fn selected_regexes_valid(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>)
            requires regex_maps(g, template, ids), selected.len() == children.len(),
                forall|i: int| 0 <= i < children.len()
                    ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            ensures norm::regex_ids_valid(g, selected),
        {
            assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.regexes.len() by {
                assert(children[i] < ids.len());
                assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
            }
        }

        pub(crate) proof fn test_connective_transfer(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<TestId>, children: Seq<u32>, selected: Seq<TestId>,
            theta: Subst, event: EventView, and: bool)
            requires test_maps(g, template, ids), language::event_wf(theta),
                selected.len() == children.len(),
                forall|i: int| 0 <= i < children.len()
                    ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            ensures norm::test_combo(g, theta, selected, event, and)
                == if and {
                    forall|i: int| 0 <= i < children.len()
                        ==> children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)
                } else {
                    exists|i: int| 0 <= i < children.len()
                        && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)
                },
        {
            reveal(norm::test_combo);
            assert forall|i: int| 0 <= i < children.len() implies
                #[trigger] model::test_holds(theta, model::lift_test(g, selected[i]@), event)
                    == (children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)) by {
                assert(children[i] < ids.len());
                assert(test_correct(g, template, children[i] as nat, ids[children[i] as int]));
            }
            if and {
                if norm::test_combo(g, theta, selected, event, and) {
                    assert forall|i: int| 0 <= i < children.len() implies
                        children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) by {
                        assert(model::test_holds(theta, model::lift_test(g, selected[i]@), event));
                    }
                }
                if forall|i: int| 0 <= i < children.len()
                    ==> children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) {
                    assert forall|i: int| 0 <= i < selected.len() implies
                        model::test_holds(theta, model::lift_test(g, selected[i]@), event) by {
                        assert(children[i] < ids.len() && source_test(template, children[i] as nat, theta, event));
                    }
                }
            } else {
                if norm::test_combo(g, theta, selected, event, and) {
                    let i = choose|i: int| 0 <= i < selected.len()
                        && model::test_holds(theta, model::lift_test(g, selected[i]@), event);
                    assert(children[i] < ids.len() && source_test(template, children[i] as nat, theta, event));
                }
                if exists|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) {
                    let i = choose|i: int| 0 <= i < children.len()
                        && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event);
                    assert(model::test_holds(theta, model::lift_test(g, selected[i]@), event));
                }
            }
        }

        pub(crate) proof fn regex_set_transfer(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>,
            theta: Subst, word: Seq<EventView>, intersect: bool)
            requires regex_maps(g, template, ids), language::event_wf(theta),
                selected.len() == children.len(),
                forall|i: int| 0 <= i < children.len()
                    ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            ensures norm::regex_combo(g, theta, selected, word, intersect)
                == if intersect {
                    forall|i: int| 0 <= i < children.len()
                        ==> children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)
                } else {
                    exists|i: int| 0 <= i < children.len()
                        && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)
                },
        {
            reveal(norm::regex_combo);
            assert forall|i: int| 0 <= i < children.len() implies
                #[trigger] model::regex_lang(g, theta, selected[i]@, word)
                    == (children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)) by {
                assert(children[i] < ids.len());
                assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
            }
            if intersect {
                if norm::regex_combo(g, theta, selected, word, intersect) {
                    assert forall|i: int| 0 <= i < children.len() implies
                        children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) by {
                        assert(model::regex_lang(g, theta, selected[i]@, word));
                    }
                }
                if forall|i: int| 0 <= i < children.len()
                    ==> children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) {
                    assert forall|i: int| 0 <= i < selected.len() implies
                        model::regex_lang(g, theta, selected[i]@, word) by {
                        assert(children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word));
                    }
                }
            } else {
                if norm::regex_combo(g, theta, selected, word, intersect) {
                    let i = choose|i: int| 0 <= i < selected.len()
                        && model::regex_lang(g, theta, selected[i]@, word);
                    assert(children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word));
                }
                if exists|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) {
                    let i = choose|i: int| 0 <= i < children.len()
                        && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word);
                    assert(model::regex_lang(g, theta, selected[i]@, word));
                }
            }
        }

        pub(crate) proof fn regex_concat_transfer(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<RegexId>, children: Seq<u32>, index: nat, theta: Subst, word: Seq<EventView>)
            requires regex_maps(g, template, ids), ids.len() == index, language::event_wf(theta),
                forall|i: int| 0 <= i < children.len() ==> children[i] < ids.len(),
            ensures norm::concat_combo(g, theta,
                Seq::new(children.len(), |i: int| ids[children[i] as int]), word)
                == (exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                    && forall|i: int| 0 <= i < children.len()
                        ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i])),
        {
            let selected = Seq::new(children.len(), |i: int| ids[children[i] as int]);
            let lifted = model::lift_regexes(g, model::regex_ids(selected));
            assert(lifted.len() == children.len());
            assert forall|i: int, piece: Seq<EventView>| 0 <= i < children.len() implies
                language::lang(model::gsem(theta), lifted[i], piece)
                    == source_regex(template, children[i] as nat, theta, piece) by {
                assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
            }
            if norm::concat_combo(g, theta, selected, word) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == lifted.len() && word == parts.flatten()
                    && forall|i: int| 0 <= i < lifted.len()
                        ==> language::lang(model::gsem(theta), lifted[i], parts[i]);
                assert forall|i: int| 0 <= i < children.len() implies children[i] < index
                    && source_regex(template, children[i] as nat, theta, parts[i]) by {}
                assert(exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                    && forall|i: int| 0 <= i < children.len()
                        ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]));
            }
            if exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children.len()
                    ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                    && forall|i: int| 0 <= i < children.len()
                        ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]);
                assert forall|i: int| 0 <= i < lifted.len() implies
                    language::lang(model::gsem(theta), lifted[i], parts[i]) by {}
                assert(norm::concat_combo(g, theta, selected, word));
            }
        }

        pub(crate) proof fn regex_star_transfer(g: model::Graph, template: FlatPair<u64>,
            ids: Seq<RegexId>, child: nat, theta: Subst, word: Seq<EventView>)
            requires regex_maps(g, template, ids), child < ids.len(), language::event_wf(theta),
            ensures language::lang(model::gsem(theta), language::Regex::Star(
                alloc::boxed::Box::new(model::lift_regex(g, ids[child as int]@))), word)
                == (exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                    && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i])),
        {
            let regex = model::lift_regex(g, ids[child as int]@);
            assert(regex_correct(g, template, child, ids[child as int]));
            if language::lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word) {
                let parts = choose|parts: Seq<Seq<EventView>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> language::lang(model::gsem(theta), regex, parts[i]);
                assert forall|i: int| 0 <= i < parts.len() implies source_regex(template, child, theta, parts[i]) by {}
                assert(exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                    && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]));
            }
            if exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == word
                    && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]);
                assert forall|i: int| 0 <= i < parts.len() implies language::lang(model::gsem(theta), regex, parts[i]) by {}
                assert(language::lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word));
            }
        }

        use crate::flat::verify as portable;
        use crate::verify::encoding::{numeric_equality, pointwise, lemma_partition_lift};

        /// Fixed coordinates are a representation, not a second source grammar.
        pub open spec fn event_representation(event: Seq<u64>, numeric: EventView) -> bool {
            event.len() == 3 && numeric.principal == event[0] as nat
                && numeric.action == event[1] as nat && numeric.resource == event[2] as nat
        }

        pub open spec fn event_relation() -> spec_fn(Seq<u64>, EventView) -> bool {
            |event: Seq<u64>, numeric: EventView| event_representation(event, numeric)
        }

        pub open spec fn word_representation(word: Seq<Seq<u64>>, numeric: Seq<EventView>) -> bool {
            pointwise(word, numeric, event_relation())
        }


        /// Portable head matching and the numeric substitution agree coordinate by coordinate.
        pub proof fn lemma_flat_head(template: FlatPair<u64>, candidate: Seq<u64>, request: EventView)
            requires event_representation(candidate, request),
            ensures portable::head_matches(template.head@, candidate, numeric_equality())
                == exists|theta: Subst| language::head_match(head_view(template), request, theta),
        {
            let theta = EventView {
                principal: if template.head@[0] is Bind { request.principal } else { 0 },
                action: if template.head@[1] is Bind { request.action } else { 0 },
                resource: if template.head@[2] is Bind { request.resource } else { 0 },
            };
            assert forall|field: Component| match #[trigger] template.head@[portable::field_index(field)] {
                FlatHead::Constant(value) => (candidate[portable::field_index(field)] == value)
                    == language::head_field_match(template.head@[portable::field_index(field)]@,
                        language::field_value(request, field), language::field_value(theta, field)),
                _ => language::head_field_match(template.head@[portable::field_index(field)]@,
                        language::field_value(request, field), language::field_value(theta, field)),
            } by {
                match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
            }
            if portable::head_matches(template.head@, candidate, numeric_equality()) {
                assert(match template.head@[portable::field_index(Component::Principal)] {
                    FlatHead::Constant(value) => candidate[0] == value, _ => true,
                });
                assert(match template.head@[portable::field_index(Component::Action)] {
                    FlatHead::Constant(value) => candidate[1] == value, _ => true,
                });
                assert(match template.head@[portable::field_index(Component::Resource)] {
                    FlatHead::Constant(value) => candidate[2] == value, _ => true,
                });
                assert(language::head_field_match(template.head@[0]@, request.principal, theta.principal));
                assert(language::head_field_match(template.head@[1]@, request.action, theta.action));
                assert(language::head_field_match(template.head@[2]@, request.resource, theta.resource));
                assert(language::head_match(head_view(template), request, theta));
            }
            if exists|theta: Subst| language::head_match(head_view(template), request, theta) {
                let witness = choose|theta: Subst| language::head_match(head_view(template), request, theta);
                assert forall|field: Component| match #[trigger] template.head@[portable::field_index(field)] {
                    FlatHead::Constant(value) => candidate[portable::field_index(field)] == value,
                    _ => true,
                } by {
                    match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
                }
            }
        }

        pub proof fn lemma_flat_test(template: FlatPair<u64>, id: nat, candidate: Seq<u64>, request: EventView,
            event: Seq<u64>, numeric: EventView, theta: Subst)
            requires portable::structural_wf(template), id < template.tests@.len(),
                event_representation(candidate, request), event_representation(event, numeric),
                language::head_match(head_view(template), request, theta),
            ensures portable::test_sem(template.tests@, id, candidate, event, numeric_equality())
                == source_test(template, id, theta, numeric),
            decreases id,
        {
            reveal_with_fuel(portable::test_sem, 1);
            reveal_with_fuel(source_test, 1);
            assert(portable::test_wf(template.head@, template.tests@[id as int], id));
            match template.tests@[id as int] {
                FlatTest::Atom { field, term, positive } => {
                    assert(language::field_value(numeric, field) == event[portable::field_index(field)] as nat) by {
                        match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
                    }
                    if let FlatTerm::Variable(variable) = term {
                        assert(field == variable);
                        assert(template.head@[portable::field_index(variable)] is Bind);
                        assert(language::field_value(theta, variable) == candidate[portable::field_index(variable)] as nat) by {
                            match variable { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
                        }
                    }
                },
                FlatTest::And(children) | FlatTest::Or(children) => {
                    assert(portable::references_before(children@, id));
                    assert forall|i: int| 0 <= i < children@.len() implies
                        portable::test_sem(template.tests@, children@[i] as nat, candidate, event, numeric_equality())
                            == source_test(template, children@[i] as nat, theta, numeric) by {
                        lemma_flat_test(template, children@[i] as nat, candidate, request, event, numeric, theta);
                    }
                },
                _ => {},
            }
        }

        /// This bridge composes the portable encoding theorem with the actual graph compiler.
        pub proof fn lemma_flat_regex(template: FlatPair<u64>, id: nat, candidate: Seq<u64>, request: EventView,
            word: Seq<Seq<u64>>, numeric: Seq<EventView>, theta: Subst)
            requires portable::structural_wf(template), id < template.regexes@.len(),
                event_representation(candidate, request), word_representation(word, numeric),
                language::head_match(head_view(template), request, theta),
            ensures portable::lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality())
                == source_regex(template, id, theta, numeric),
            decreases id,
        {
            reveal_with_fuel(portable::lang, 1);
            reveal_with_fuel(source_regex, 1);
            assert(portable::regex_wf(template.regexes@[id as int], id, template.tests@.len()));
            assert forall|i: int| 0 <= i < word.len() implies portable::event_wf(word[i]) by {
                assert(event_representation(word[i], numeric[i]));
            }
            match template.regexes@[id as int] {
                FlatRegex::Test(test) => {
                    if word.len() == 1 {
                        lemma_flat_test(template, test as nat, candidate, request, word[0], numeric[0], theta);
                    }
                },
                FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
                    assert(portable::references_before(children@, id));
                    assert forall|i: int| 0 <= i < children@.len() implies
                        portable::lang(template.tests@, template.regexes@, children@[i] as nat, candidate, word, numeric_equality())
                            == source_regex(template, children@[i] as nat, theta, numeric) by {
                        lemma_flat_regex(template, children@[i] as nat, candidate, request, word, numeric, theta);
                    }
                },
                FlatRegex::Concat(children) => {
                    if portable::lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()) {
                        let parts = choose|parts: Seq<Seq<Seq<u64>>>| parts.len() == children@.len() && word == parts.flatten()
                            && (forall|i: int| 0 <= i < parts.len() ==> portable::lang(template.tests@, template.regexes@, children@[i] as nat, candidate, parts[i], numeric_equality()));
                        let reverse = |n: EventView, e: Seq<u64>| event_representation(e, n);
                        assert(pointwise(numeric, word, reverse));
                        lemma_partition_lift(numeric, word, parts, reverse);
                        let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len()
                            && numeric == lifted.flatten()
                            && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], reverse);
                        assert forall|i: int| 0 <= i < parts.len() implies
                            source_regex(template, children@[i] as nat, theta, lifted[i]) by {
                            assert(word_representation(parts[i], lifted[i]));
                            lemma_flat_regex(template, children@[i] as nat, candidate, request, parts[i], lifted[i], theta);
                        }
                        assert(source_regex(template, id, theta, numeric));
                    }
                    if source_regex(template, id, theta, numeric) {
                        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children@.len() && numeric == parts.flatten()
                            && (forall|i: int| 0 <= i < parts.len() ==> source_regex(template, children@[i] as nat, theta, parts[i]));
                        lemma_partition_lift(word, numeric, parts, event_relation());
                        let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                            && word == lifted.flatten()
                            && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], event_relation());
                        assert forall|i: int| 0 <= i < parts.len() implies
                            portable::lang(template.tests@, template.regexes@, children@[i] as nat, candidate, lifted[i], numeric_equality()) by {
                            lemma_flat_regex(template, children@[i] as nat, candidate, request, lifted[i], parts[i], theta);
                        }
                        assert(portable::lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()));
                    }
                },
                FlatRegex::Star(child) => {
                    if portable::lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()) {
                        let parts = choose|parts: Seq<Seq<Seq<u64>>>| word == parts.flatten()
                            && (forall|i: int| 0 <= i < parts.len() ==> portable::lang(template.tests@, template.regexes@, child as nat, candidate, parts[i], numeric_equality()));
                        let reverse = |n: EventView, e: Seq<u64>| event_representation(e, n);
                        assert(pointwise(numeric, word, reverse));
                        lemma_partition_lift(numeric, word, parts, reverse);
                        let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len()
                            && numeric == lifted.flatten()
                            && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], reverse);
                        assert forall|i: int| 0 <= i < parts.len() implies
                            source_regex(template, child as nat, theta, lifted[i]) by {
                            assert(word_representation(parts[i], lifted[i]));
                            lemma_flat_regex(template, child as nat, candidate, request, parts[i], lifted[i], theta);
                        }
                        assert(source_regex(template, id, theta, numeric));
                    }
                    if source_regex(template, id, theta, numeric) {
                        let parts = choose|parts: Seq<Seq<EventView>>| numeric == parts.flatten()
                            && (forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child as nat, theta, parts[i]));
                        lemma_partition_lift(word, numeric, parts, event_relation());
                        let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                            && word == lifted.flatten()
                            && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], event_relation());
                        assert forall|i: int| 0 <= i < parts.len() implies
                            portable::lang(template.tests@, template.regexes@, child as nat, candidate, lifted[i], numeric_equality()) by {
                            lemma_flat_regex(template, child as nat, candidate, request, lifted[i], parts[i], theta);
                        }
                        assert(portable::lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()));
                    }
                },
                FlatRegex::Complement(child) => {
                    lemma_flat_regex(template, child as nat, candidate, request, word, numeric, theta);
                },
                _ => {},
            }
        }
        }
    }
}

#[cfg(all(feature = "runtime", verus_keep_ghost))]
pub use numeric::verify;
