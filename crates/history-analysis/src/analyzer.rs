//! Tail inclusion for every candidate matching a head.

use crate::native::NativeMap;
#[cfg(verus_keep_ghost)]
use crate::verify::frontend::*;
#[cfg(verus_keep_ghost)]
use crate::verify::verdict::*;
#[cfg(verus_keep_ghost)]
use crate::verify::{self as views, search_exec as exec};
use alloc::rc::Rc;
use alloc::vec::Vec;
use history_semantics::SymbolicLanguage;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::{
    analyzer as verdict, implementation, inclusion, search as paper,
};
#[cfg(verus_keep_ghost)]
use history_semantics::{compile_verify as numeric, symbolic_language_verify as facade};
#[cfg(verus_keep_ghost)]
use history_syntax::Rule;
use history_syntax::{Component, Event, Head, RegexExpr, RuleMode};
use junco_core::compile::validate_component;
use junco_core::flat::{FlatHead, FlatPair};
use junco_core::flatten::flatten_rule_parts;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::verify::{encoding as enc, flatten as fl};
use junco_core::{CompileError, ComponentValue, FlatEncoder, HistoryError, lower_flat};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

#[cfg(verus_keep_ghost)]
verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
}

use crate::constraint::{
    COMPONENTS, Class, ConstId, Constraint, Letter, RegisterConstraint, Universes,
};
use crate::search::{SearchOutcome, search};
use crate::tables::Tables;

/// Bytes of runtime graph one search may be charged before it is reported `Exhausted`;
/// the runtime keeps `MAX_GRAPH_BYTES` per rule.
#[verus_verify]
const GRAPH_BYTES: usize = 16 * 1024 * 1024;

/// The values each event component can take.
///
/// By default every component is infinite: it has more values than any analysis mentions, so a
/// counterexample may use a [fresh](Value::Fresh) value for it. Declare the values of a component
/// whose type has only a few, such as an action enum; treated as infinite, it could yield
/// counterexamples that need a value the type does not have.
#[verus_verify]
#[derive(Clone, Debug)]
pub struct Domains<E: Event> {
    pub(crate) principals: Option<Vec<E::Principal>>,
    pub(crate) actions: Option<Vec<E::Action>>,
    pub(crate) resources: Option<Vec<E::Resource>>,
}

impl<E: Event> Domains<E> {
    /// Every component infinite.
    pub fn infinite() -> Self {
        Self {
            principals: None,
            actions: None,
            resources: None,
        }
    }

    /// Declares every principal that events and candidates can have.
    pub fn with_principals(mut self, values: impl IntoIterator<Item = E::Principal>) -> Self {
        self.principals = Some(values.into_iter().collect());
        self
    }

    /// Declares every action that events and candidates can have.
    pub fn with_actions(mut self, values: impl IntoIterator<Item = E::Action>) -> Self {
        self.actions = Some(values.into_iter().collect());
        self
    }

    /// Declares every resource that events and candidates can have.
    pub fn with_resources(mut self, values: impl IntoIterator<Item = E::Resource>) -> Self {
        self.resources = Some(values.into_iter().collect());
        self
    }
}

/// One component value of a counterexample.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Value<T> {
    /// A constant of the analysed rules, or a declared value of a finite component.
    Constant(T),
    /// A value of an infinite component that equals no constant of that component known to the
    /// analyzer. Within one counterexample, equal numbers denote equal values and different
    /// numbers different values.
    Fresh(usize),
}

/// The components of one event of a counterexample.
#[verus_verify]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Components<E: Event> {
    /// The principal.
    pub principal: Value<E::Principal>,
    /// The action.
    pub action: Value<E::Action>,
    /// The resource.
    pub resource: Value<E::Resource>,
}

/// A candidate and a history on which an inclusion fails.
///
/// What failing means depends on the query; each query documents it. No shorter history fails.
#[verus_verify]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample<E: Event> {
    /// Components of the candidate event that rule heads are matched against.
    pub candidate: Components<E>,
    /// Components of the events before the candidate, oldest first.
    pub history: Vec<Components<E>>,
}

/// Outcome of an analysis query.
#[verus_verify]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Inclusion<E: Event> {
    /// The inclusion holds for every candidate.
    Holds,
    /// The inclusion fails; the counterexample witnesses it.
    Counterexample(Counterexample<E>),
    /// A search exceeded its graph budget before deciding.
    Exhausted,
}

/// Constants of the analysed rules and domains, interned with ids per value. Ids start at 1, as
/// the `FlatEncoder` contract requires nonzero codes; the constant with id `i` is `values[i - 1]`.
#[verus_verify]
pub(crate) struct Constants<E: Event> {
    pub(crate) ids: NativeMap<ComponentValue<E>, ConstId>,
    pub(crate) values: Vec<ComponentValue<E>>,
}

verus! {
impl<E: Event> Constants<E> {
    fn try_intern(&mut self, value: ComponentValue<E>) -> (result: Result<ConstId, core::num::TryFromIntError>)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(),
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + 1,
            result matches Ok(id) ==> stored_code(*final(self), value, id),
            result is Err ==> *final(self) == *old(self) && old(self).values@.len() == u32::MAX,
    {
        proof_decl! { let ghost before = *self; }
        if let Some(id) = self.ids.lookup(&value) {
            proof! {
                let i = choose|i: int| 0 <= i < crate::native::representatives(self.ids).len()
                    && crate::native::representatives(self.ids)[i].1 == id
                    && value.eq_spec(&crate::native::representatives(self.ids)[i].0);
                assert(stored_code(*self, value, id));
            }
            return Ok(id);
        }
        proof {
            assert forall|i: int| 0 <= i < before.values@.len() implies !value.eq_spec(&before.values@[i]) by {
                assert(crate::native::representatives(before.ids)[i].0 == before.values@[i]);
            }
        }
        // Counting in u64 keeps a saturated u32 book a checked conversion failure.
        let id = ConstId::try_from(self.values.len() as u64 + 1)?;
        self.values.push(value);
        self.ids.insert_fresh(value, id);
        proof! {
            assert(self.values@ == before.values@.push(value));
            assert(crate::native::representatives(self.ids)
                == before.values@.map(|i: int, v: ComponentValue<E>| (v, (i + 1) as u32)).push((value, id)));
            assert(crate::native::representatives(self.ids)
                =~= self.values@.map(|i: int, v: ComponentValue<E>| (v, (i + 1) as u32)));
            assert forall|i: int, j: int| 0 <= i < j < self.values@.len()
                implies !self.values@[i].eq_spec(&self.values@[j]) by {
                if j == before.values@.len() {
                    assert(!value.eq_spec(&before.values@[i]));
                }
            }
            assert(constants_frame(before, *self));
        }
        Ok(id)
    }

    fn intern(&mut self, value: ComponentValue<E>) -> (result: ConstId)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(), old(self).values@.len() < u32::MAX,
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + 1,
            stored_code(*final(self), value, result),
    {
        self.try_intern(value).expect("constant ids fit in u32")
    }

    /// The universe of a declared finite component, in declaration order without repeats.
    fn universe<T: Copy>(&mut self, values: &[T], wrap: impl Fn(T) -> ComponentValue<E>,
        Ghost(tagged): Ghost<spec_fn(T) -> ComponentValue<E>>) -> (result: Rc<Vec<ConstId>>)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(),
            old(self).values@.len() + values@.len() <= u32::MAX,
            forall|x: T| call_requires(wrap, (x,)),
            forall|x: T, v: ComponentValue<E>| call_ensures(wrap, (x,), v) ==> v == tagged(x),
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + values@.len(),
            universe_encoded(*final(self), (*result)@, values@.map_values(tagged)),
    {
        hide(universe_encoded);
        hide(constants_wf);
        hide(crate::verify::analyzer_obligations);
        proof_decl! { let ghost before = *self; }
        let mut ids = Vec::new();
        let mut i = 0;
        proof { lemma_universe_empty(*self); }
        proof { assert(values@.take(0).map_values(tagged) =~= Seq::<ComponentValue<E>>::empty()); }
        while i < values.len()
            invariant i <= values@.len(), constants_wf(*self), crate::verify::analyzer_obligations::<E>(),
                constants_frame(before, *self), self.values@.len() <= before.values@.len() + i,
                universe_encoded(*self, ids@, values@.take(i as int).map_values(tagged)),
                before.values@.len() + values@.len() <= u32::MAX,
                forall|x: T| call_requires(wrap, (x,)),
                forall|x: T, v: ComponentValue<E>| call_ensures(wrap, (x,), v) ==> v == tagged(x),
            decreases values@.len() - i,
        {
            proof_decl! { let ghost prior = *self; }
            let value = wrap(values[i]);
            let id = self.intern(value);
            proof! { lemma_universe_frame(prior, *self, ids@, values@.take(i as int).map_values(tagged)); }
            let ghost old_ids = ids@;
            let found = contains_id(&ids, id);
            if !found { ids.push(id); } else { proof { assert(ids@.contains(id)); } }
            proof! {
                assert(values@.take(i as int + 1).map_values(tagged)
                    =~= values@.take(i as int).map_values(tagged).push(value));
                lemma_universe_step(*self, old_ids, ids@, values@.take(i as int).map_values(tagged), value, id);
            }
            i += 1;
        }
        proof { assert(values@.take(i as int).map_values(tagged) =~= values@.map_values(tagged)); }
        Rc::new(ids)
    }
}

fn contains_id(ids: &[u32], id: u32) -> (found: bool)
    ensures found == ids@.contains(id),
{
    let mut i = 0;
    while i < ids.len()
        invariant i <= ids@.len(), forall|j: int| 0 <= j < i ==> ids@[j] != id,
        decreases ids@.len() - i,
    {
        if ids[i] == id { return true; }
        i += 1;
    }
    false
}
}

verus! {
/// A scoped adapter is total even when the finite constant-id space is exhausted.
pub(crate) struct BorrowedEncoder<'a, E: Event> {
    pub(crate) constants: &'a mut Constants<E>,
    pub(crate) overflowed: bool,
    // Seeded with the existing book length, then incremented for every encoding attempt.
    pub(crate) calls: Ghost<nat>,
}

impl<'a, E: Event> FlatEncoder<ComponentValue<E>> for BorrowedEncoder<'a, E> {
    open spec fn equality() -> enc::Equality<ComponentValue<E>> { fl::component_equality::<E>() }
    open spec fn domain() -> enc::Domain<ComponentValue<E>> { fl::component_domain::<E>() }
    open(crate) spec fn maps(&self) -> enc::Codebook<ComponentValue<E>> { crate::verify::constant_book(*self.constants) }
    open(crate) spec fn encoding_calls(&self) -> nat { self.calls@ }
    open(crate) spec fn state_wf(&self) -> bool {
        constants_wf(*self.constants) && crate::verify::analyzer_obligations::<E>()
            && self.constants.values@.len() <= self.calls@
            && (self.overflowed ==> u32::MAX < self.calls@)
    }
    open(crate) spec fn obeys_encoding_spec(&self) -> bool {
        constants_wf(*self.constants) && crate::verify::analyzer_obligations::<E>()
    }
    open spec fn errors_are_non_invariant(&self) -> bool { true }
    #[verifier::prophetic]
    open(crate) spec fn restoration(&self) -> (enc::Codebook<ComponentValue<E>>, bool) {
        let future = mut_ref_future(self.constants);
        (crate::verify::constant_book(future), constants_wf(future))
    }

    fn encode(&mut self, field: Component, value: &ComponentValue<E>)
        -> (result: Result<u64, HistoryError>)
    {
        let ghost before = *self.constants;
        self.calls = Ghost(self.calls@ + 1);
        if self.overflowed { return Err(HistoryError::IdExhausted { domain: "constant" }); }
        validate_component(field, value)?;
        let result = match self.constants.try_intern(*value) {
            Ok(id) => Ok(id as u64),
            Err(_) => {
                self.overflowed = true;
                Err(HistoryError::IdExhausted { domain: "constant" })
            },
        };
        proof {
            lemma_constants_maps(*self.constants);
            lemma_constants_extend(before, *self.constants);
            if let Ok(id) = result {
                assert(value_field(*value) == field);
                lemma_stored_encoded(*self.constants, *value, id as u32);
            }
        }
        result
    }
}
}

/// A counterexample component before its constant is resolved.
#[derive(Clone, Copy)]
#[verus_verify]
pub(crate) enum Slot {
    Constant(ConstId),
    Fresh(usize),
}

/// Static analysis of tail inclusion: for every candidate a head matches, whether every history
/// in one tail is in another.
#[verus_verify]
pub struct PolicyAnalyzer<E: Event> {
    pub(crate) constants: Constants<E>,
    pub(crate) universes: Universes,
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {
    /// Creates an analyzer for events whose components take the values of `domains`.
    // Each `match` keeps a Verus closure contract that `Option::map` would not carry.
    #[allow(clippy::manual_map)]
    pub fn new(domains: Domains<E>) -> (result: Self)
        requires crate::verify::analyzer_obligations::<E>(), constructor_capacity(domains),
        ensures constructor_result(result, domains),
    {
        hide(constants_wf);
        hide(crate::verify::analyzer_obligations);
        proof { lemma_constructor_contract::<E>(); }
        let ghost input = domains;
        let mut constants = Constants { ids: NativeMap::new(), values: Vec::new() };
        proof { lemma_empty_constants(constants); }
        let principals = match domains.principals {
            Some(values) => Some(constants.universe(&values,
                verus_exec_expr!(|v: E::Principal| -> (r: ComponentValue<E>) ensures r == ComponentValue::<E>::Principal(v), { ComponentValue::Principal(v) }),
                Ghost(|v: E::Principal| ComponentValue::<E>::Principal(v)))),
            None => None,
        };
        let ghost first = constants;
        let actions = match domains.actions {
            Some(values) => Some(constants.universe(&values,
                verus_exec_expr!(|v: E::Action| -> (r: ComponentValue<E>) ensures r == ComponentValue::<E>::Action(v), { ComponentValue::Action(v) }),
                Ghost(|v: E::Action| ComponentValue::<E>::Action(v)))),
            None => None,
        };
        let ghost second = constants;
        let resources = match domains.resources {
            Some(values) => Some(constants.universe(&values,
                verus_exec_expr!(|v: E::Resource| -> (r: ComponentValue<E>) ensures r == ComponentValue::<E>::Resource(v), { ComponentValue::Resource(v) }),
                Ghost(|v: E::Resource| ComponentValue::<E>::Resource(v)))),
            None => None,
        };
        proof {
            lemma_declared_frame(first, second, principals, input.principals, |v: E::Principal| ComponentValue::<E>::Principal(v));
            lemma_declared_frame(second, constants, principals, input.principals, |v: E::Principal| ComponentValue::<E>::Principal(v));
            lemma_declared_frame(second, constants, actions, input.actions, |v: E::Action| ComponentValue::<E>::Action(v));
        }
        let result = Self { constants, universes: [principals, actions, resources] };
        proof { lemma_declared_wf(result, input); lemma_constructor_domains(result, input); }
        result
    }
}
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {

    /// Whether, for every candidate that `head` matches, every history in `left` is in `right`.
    ///
    /// Both tails may refer to the head's variables. A counterexample is a matching candidate and
    /// a history in `left` but not in `right`.
    #[verus_spec(result => requires views::analyzer_obligations::<E>(),
        analyzer_state_wf(*old(self)), query_capacity(*old(self), *left, *right),
        ensures analyzer_state_wf(*final(self)),
            result matches Ok(v) ==> verdict::tail_included_ok(final(self)@, head@, left@, right@, v@))]
    pub fn tail_included(
        &mut self,
        head: &Head<E>,
        left: &RegexExpr<E>,
        right: &RegexExpr<E>,
    ) -> Result<Inclusion<E>, CompileError> {
        let ghost before = *self;
        proof { lemma_query_capacity(*self, *left, *right); }
        let ghost bound = self.constants.values@.len() + 6 + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@);
        let ghost left_rule = Rule { mode: RuleMode::Forbid, head: *head, tail: *left };
        let ghost right_rule = Rule { mode: RuleMode::Forbid, head: *head, tail: *right };
        let left_flat = flatten_rule_parts(RuleMode::Forbid, head, left, &mut Unmetered, &mut ObservationWorld)?;
        let right_flat = flatten_rule_parts(RuleMode::Forbid, head, right, &mut Unmetered, &mut ObservationWorld)?;
        proof {
            assert(left_rule.head@ == head@ && right_rule.head@ == head@);
            assert(left_rule.tail@ == left@ && right_rule.tail@ == right@);
            assert(left_flat.source.tests@.len() <= fl::regex_cost::<E>(left@));
            assert(right_flat.source.tests@.len() <= fl::regex_cost::<E>(right@));
            assert(encode_capacity(*self, left_flat.source));
        }
        let left_result = self.encode(&left_flat.source);
        proof { lemma_universes_extended(before.constants, self.constants, self.universes); }
        let left_numeric = left_result?;
        let ghost first = *self;
        proof { assert(encode_capacity(*self, right_flat.source)); }
        let right_result = self.encode(&right_flat.source);
        proof { lemma_universes_extended(first.constants, self.constants, self.universes); }
        let right_numeric = right_result?;
        let ghost input = TailInput { left: left_rule, right: right_rule, left_flat, right_flat,
            left_numeric, right_numeric };
        proof {
            enc::lemma_lowering_extends(left_flat.source, left_numeric, views::constant_book(first.constants),
                views::constant_book(self.constants), fl::component_equality::<E>());
            lemma_lowered_payload(self.constants, left_flat.source, left_numeric);
            lemma_lowered_payload(self.constants, right_flat.source, right_numeric);
            assert(tail_input_wf(self.constants, input));
            assert(self.constants.values@.len() <= bound);
        }
        let constants = Self::head_constants(&left_numeric.head);
        let result = match Constraint::head(constants, &self.universes) {
            Some(constraint) => {
                proof { lemma_head_payload(self.constants, left_numeric.head@, constants, constraint); }
                let mut tables = Tables::default();
                let ghost empty = tables@;
                proof {
                    views::table::lemma_structural_dag(left_numeric);
                    views::table::lemma_structural_dag(right_numeric);
                    assert(views::table::dag(tables@));
                    assert(source_codes_wf(self.constants, tables@));
                }
                let left_root = tables.append(&left_numeric)?;
                proof { lemma_append_payload(self.constants, empty, left_numeric, tables@); }
                let ghost first_tables = tables@;
                let right_root = tables.append(&right_numeric)?;
                proof {
                    lemma_append_payload(self.constants, first_tables, right_numeric, tables@);
                    assert forall|theta: junco_core::verify::history_specs::Subst, word: Seq<junco_core::verify::history_specs::EventView>|
                        numeric::source_regex(tables@, left_root as nat, theta, word)
                            == numeric::source_regex(left_numeric, left_numeric.root as nat, theta, word) by {}
                }
                let ghost assembled = tables@;
                let difference = tables.difference(left_root, right_root)?;
                proof {
                    assert(source_codes_wf(self.constants, difference));
                    assert(difference_source(input, difference));
                    assert forall|v: [Set<nat>; 3]| v[0].len() <= self.constants.values@.len()
                        && v[1].len() <= self.constants.values@.len() && v[2].len() <= self.constants.values@.len()
                        implies exec::resource_capacity(v) by {}
                    assert(decision_ready(*self, input, constraint, difference));
                }
                #[cfg(verus_keep_ghost)]
                let decided = self.decide(constraint, difference, Ghost(input))?;
                #[cfg(not(verus_keep_ghost))]
                let decided = self.decide(constraint, difference)?;
                decided
            }
            None => {
                proof { lemma_no_candidates(*self, input); }
                Inclusion::Holds
            }
        };
        Ok(result)
    }
}
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {

    /// The constants that an encoded head pins; variables leave their register free.
    fn head_constants(head: &[FlatHead<u64>; COMPONENTS]) -> (result: [Option<ConstId>; COMPONENTS])
        requires numeric_head_wf(head@),
        ensures crate::verify::head_view(result) == pins(head@),
    {
        let mut result = [None; COMPONENTS];
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant i <= 3, numeric_head_wf(head@),
            forall|j: int| 0 <= j < i ==> crate::verify::option_code(result[j]) == encoding_head_code(head@[j]),
            decreases 3 - i))]
        while i < COMPONENTS {
            result[i] = match head[i] { FlatHead::Constant(v) => Some(v as u32), _ => None };
            i += 1;
        }
        result
    }

    /// `source` with each constant replaced by its constant id.
    fn encode(&mut self, source: &FlatPair<ComponentValue<E>>) -> (result: Result<FlatPair<u64>, HistoryError>)
        requires constants_wf(old(self).constants), crate::verify::analyzer_obligations::<E>(), encode_capacity(*old(self), *source),
        ensures constants_wf(final(self).constants), enc::extends(crate::verify::constant_book(old(self).constants), crate::verify::constant_book(final(self).constants), fl::component_equality::<E>()),
            final(self).universes == old(self).universes,
            final(self).constants.values@.len() <= old(self).constants.values@.len() + 3 + source.tests@.len(),
            result matches Ok(target) ==> enc::lowering(*source, target, crate::verify::constant_book(final(self).constants), fl::component_equality::<E>())
                && junco_core::flat::verify::structural_wf(target) && numeric_head_wf(target.head@),
    {
        let ghost initial_count = self.constants.values@.len();
        proof { assert(initial_count == old(self).constants.values@.len()); }
        proof { lemma_constants_maps(self.constants); }
        let (result, overflowed, Ghost(maps)) = {
            let mut encoder = BorrowedEncoder {
                constants: &mut self.constants, overflowed: false,
                calls: Ghost(initial_count),
            };
            let result = lower_flat(source, &mut encoder, &mut Unmetered, &mut ObservationWorld);
            let ghost maps = encoder.maps();
            proof {
                assert(encoder.calls@ <= initial_count + 3 + source.tests@.len());
                lemma_constant_book_length(*encoder.constants);
                assert(maps[0].len() + maps[1].len() + maps[2].len()
                    <= initial_count + 3 + source.tests@.len());
                assert(!encoder.overflowed);
            }
            let overflowed = encoder.overflowed;
            (result, overflowed, Ghost(maps))
        };
        proof {
            assert(crate::verify::constant_book(self.constants) == maps);
            lemma_constant_book_length(self.constants);
            assert(!overflowed);
        }
        if overflowed {
            let _ = ConstId::try_from(self.constants.values.len() + 1).expect("constant ids fit in u32");
        }
        proof {
            if let Ok(target) = &result { lemma_lowered_head_bound(self.constants, *source, *target); }
        }
        result
    }
}
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {
    /// Decides whether `difference` is empty under `constraint`.
    fn decide(
        &self,
        constraint: Constraint,
        difference: FlatPair<u64>,
        #[cfg(verus_keep_ghost)] Ghost(input): Ghost<TailInput<E>>,
    ) -> (result: Result<Inclusion<E>, HistoryError>)
        requires decision_ready(*self, input, constraint, difference),
        ensures result matches Ok(v) ==> tail_verdict(*self, input, v),
    {
        let mut language = match SymbolicLanguage::compile(&difference, GRAPH_BYTES) {
            Ok(language) => language,
            Err(HistoryError::GraphLimit { .. }) => return Ok(Inclusion::Exhausted),
            Err(error) => return Err(error),
        };
        let ghost original = language;
        let ghost start = paper::Item { constraint: implementation::constraint_of(constraint@),
            state: model::lift_regex(facade::graph(language), facade::root(language)) };
        let ghost vocabulary = exec::root_vocabulary(language, self.universes, constraint@);
        proof {
            lemma_root_payload(*self, language, difference, constraint@);
            lemma_root_fits(*self, language, constraint@, self.constants.values@.len());
            assert(views::constraint_unique::universes_distinct(self.universes));
            assert forall|theta: junco_core::verify::history_specs::Subst, word: Seq<junco_core::verify::history_specs::EventView>|
                junco_core::verify::history_specs::event_wf(theta) implies
                    history_semantics::verify::refinement::encoding::n_lang(theta, start.state, word)
                        == (numeric::source_regex(input.left_numeric, input.left_numeric.root as nat, theta, word)
                            && !numeric::source_regex(input.right_numeric, input.right_numeric.root as nat, theta, word)) by {
                assert(model::regex_lang(facade::graph(language), theta, facade::root(language), word)
                    == numeric::source_regex(difference, difference.root as nat, theta, word));
                reveal(model::regex_lang);
            }
            assert(difference_language(input, start.state));
            assert(tail_ready(*self, input, start.state));
        }
        let outcome = match search(&mut language, &self.universes, constraint) {
            Ok(outcome) => outcome,
            Err(HistoryError::GraphLimit { .. }) => return Ok(Inclusion::Exhausted),
            Err(error) => return Err(error),
        };
        proof {
            lemma_result_outcome(views::ndomains(self.universes), start, exec::outcome_view(outcome));
            lemma_refutation_input(*self, start, outcome, vocabulary);
        }
        match outcome {
            SearchOutcome::Holds => {
                proof { lemma_holds(*self, input, start.state); }
                Ok(Inclusion::Holds)
            }
            SearchOutcome::Refuted(refutation) => {
                #[cfg(verus_keep_ghost)]
                let counterexample = self.counterexample(&refutation.constraint, &refutation.letters, refutation.alphabets)?;
                #[cfg(not(verus_keep_ghost))]
                let counterexample = self.counterexample(&refutation.constraint, &refutation.letters)?;
                proof {
                    reveal(exec::refutation_ready);
                    lemma_counterexample(*self, input, start.state, refutation.constraint,
                        refutation.letters@, refutation.alphabets@, counterexample);
                }
                Ok(Inclusion::Counterexample(counterexample))
            }
        }
    }
}
}

impl<E: Event> PolicyAnalyzer<E> {
    /// Builds a candidate and history from a refuting constraint and letter sequence.
    ///
    /// A register takes the constant the constraint pins it to, the first remaining value of a
    /// finite domain, or a fresh value. A component that a letter leaves unmatched takes a fresh
    /// value, distinct from every other one; a finite component never is unmatched. Fails with
    /// [`HistoryError::IdExhausted`] if the fresh values do not fit `usize`.
    #[verus_verify]
    #[verus_spec(result =>
        requires crate::verify::reconstruction::reconstruction_input(self.constants,
            self.universes, *constraint, letters@, alphabets@),
        ensures result matches Ok(c) ==> crate::verify::reconstruction::reconstructed(self.constants,
            self.universes, *constraint, letters@, alphabets@, c))]
    fn counterexample(
        &self,
        constraint: &Constraint,
        letters: &[Letter],
        #[cfg(verus_keep_ghost)] alphabets: Ghost<Seq<Set<junco_core::kernel::verify::Primitive>>>,
    ) -> Result<Counterexample<E>, HistoryError> {
        #[cfg(verus_keep_ghost)]
        use crate::verify::{
            component_index, component_of, domain_view, lemma_codes, lemma_constraint_possible,
            reconstruction::*, register_possible, register_sat,
        };
        proof! {
            lemma_known_codes(self.constants);
            lemma_constraint_possible(*constraint, self.universes);
        }
        let mut fresh: usize = 0;
        let mut candidate = [Slot::Constant(0); COMPONENTS];
        let mut component: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            component <= 3, fresh <= component,
            reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
            forall|k: int| 0 <= k < component ==> candidate_field_ok(self.constants,
                self.universes, *constraint, k, candidate[k]@),
            forall|k: int| #![trigger candidate[k]@] 0 <= k < component ==> (candidate[k]@ matches
                history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
            forall|k: int| 0 <= k < 3 ==> register_possible(constraint.0[k], self.universes[k]),
            decreases 3 - component,
        ))]
        while component < COMPONENTS {
            proof! {
                lemma_input_field(self.constants, self.universes, *constraint,
                    letters@, alphabets@, component);
            }
            let register = &constraint.0[component];
            let slot = match (register, &self.universes[component]) {
                (RegisterConstraint::Equals(value), _) => Slot::Constant(*value),
                (RegisterConstraint::Differs(_), Some(values)) => {
                    let slice: &[ConstId] = values;
                    proof! { lemma_codes(slice@); }
                    match register.witness(slice) {
                        Some(value) => Slot::Constant(value),
                        None => {
                            proof! {
                                let v = choose|v: nat| crate::verify::codes(slice@).contains(v)
                                    && register_sat(register@, v);
                                let i = choose|i: int| 0 <= i < slice@.len() && slice@[i] as nat == v;
                                assert(false);
                            }
                            panic!("constraints are satisfiable in their universe")
                        }
                    }
                }
                (RegisterConstraint::Differs(_), None) => {
                    let slot = Slot::Fresh(fresh);
                    fresh = match fresh.checked_add(1) {
                        Some(next) => next,
                        None => {
                            return Err(HistoryError::IdExhausted {
                                domain: "fresh value",
                            });
                        }
                    };
                    slot
                }
            };
            proof! {
                let field = component_of(component);
                assert(component_index(field) == component);
                match field { history_syntax::syntax::Component::Principal => {},
                    history_syntax::syntax::Component::Action => {}, history_syntax::syntax::Component::Resource => {} }
                lemma_register_known(self.constants, field, constraint.0[component as int]@);
                assert(candidate_field_ok(self.constants, self.universes, *constraint, component as int, slot@));
            }
            candidate[component] = slot;
            component += 1;
        }
        let candidate_values = self.components(candidate);
        let mut values = Vec::<Components<E>>::with_capacity(letters.len());
        proof_decl! {
            let ghost mut slots_history: Seq<Seq<history_semantics::verify::refinement::implementation::SlotView>>
                = Seq::empty();
        }
        let mut index: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= letters@.len(), values@.len() == index, slots_history.len() == index,
            candidate_values@ == components_of_slots(self.constants, slot_views(candidate)),
            forall|i: int| 0 <= i < index ==> values@[i]@ == components_of_slots(self.constants, slots_history[i]),
            fresh <= 3 * (index + 1),
            reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
            slot_wf(self.constants, slot_views(candidate)),
            forall|k: int| 0 <= k < 3 ==> candidate_field_ok(self.constants,
                self.universes, *constraint, k, candidate[k]@),
            forall|k: int| #![trigger candidate[k]@] 0 <= k < 3 ==> (candidate[k]@ matches
                history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
            forall|i: int| 0 <= i < index ==> slot_wf(self.constants, slots_history[i])
                && forall|k: int| 0 <= k < 3 ==> history_field_matches(slot_views(candidate), letters@[i]@,
                    k, slots_history[i][k]) && slot_domain(slots_history[i][k], domain_view(self.universes[k])),
            forall|i: int, k: int| #![trigger slots_history[i][k]] 0 <= i < index && 0 <= k < 3
                ==> (slots_history[i][k] matches
                    history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
            decreases letters@.len() - index,
        ))]
        while index < letters.len() {
            let letter = &letters[index];
            proof! {
                assert(letter@ == letters@[index as int]@);
                assert(letter_codes_ok(self.constants, crate::verify::ndomains(self.universes),
                    letter@, alphabets@[index as int]));
            }
            let mut slots = [Slot::Constant(0); COMPONENTS];
            let mut component: usize = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                component <= 3, index < letters@.len(), values@.len() == index, slots_history.len() == index,
                fresh <= 3 * (index + 1) + component,
                reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
                letter@ == letters@[index as int]@,
                letter_codes_ok(self.constants, crate::verify::ndomains(self.universes),
                    letter@, alphabets@[index as int]),
                slot_wf(self.constants, slot_views(candidate)),
                forall|k: int| 0 <= k < 3 ==> candidate_field_ok(self.constants,
                    self.universes, *constraint, k, candidate[k]@),
                forall|k: int| #![trigger candidate[k]@] 0 <= k < 3 ==> (candidate[k]@ matches
                    history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                forall|k: int| 0 <= k < component ==> history_field_matches(slot_views(candidate), letter@,
                    k, slots[k]@) && slot_domain(slots[k]@, domain_view(self.universes[k])) && match slots[k]@ {
                        history_semantics::verify::refinement::implementation::SlotView::Code(v) =>
                            code_field(self.constants, component_of(k as usize), v), _ => true },
                forall|i: int| #![trigger slots_history[i]] 0 <= i < index
                    ==> slot_wf(self.constants, slots_history[i]),
                forall|i: int, k: int| #![trigger slots_history[i][k]] 0 <= i < index && 0 <= k < 3
                    ==> (slots_history[i][k] matches
                        history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                forall|k: int| #![trigger slots[k]@] 0 <= k < component ==> (slots[k]@ matches
                    history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                decreases 3 - component,
            ))]
            while component < COMPONENTS {
                let slot = match letter.class(component) {
                    Some(Class::Constant(value)) => Slot::Constant(value),
                    Some(Class::Register) => candidate[component],
                    None => {
                        let slot = Slot::Fresh(fresh);
                        fresh = match fresh.checked_add(1) {
                            Some(next) => next,
                            None => {
                                return Err(HistoryError::IdExhausted {
                                    domain: "fresh value",
                                });
                            }
                        };
                        slot
                    }
                };
                proof! {
                    assert(history_field_matches(slot_views(candidate), letter@, component as int, slot@));
                    lemma_history_field(self.constants, self.universes, slot_views(candidate),
                        letter@, alphabets@[index as int], component, slot@);
                }
                slots[component] = slot;
                component += 1;
            }
            values.push(self.components(slots));
            proof! { slots_history = slots_history.push(slot_views(slots)); }
            index += 1;
        }
        let result = Counterexample {
            candidate: candidate_values,
            history: values,
        };
        proof! {
            assert(constructed(self.constants, self.universes, *constraint, letters@, slot_views(candidate), slots_history));
            assert(result@.history =~= slots_history.map(
                |i: int, row: Seq<history_semantics::verify::refinement::implementation::SlotView>|
                    components_of_slots(self.constants, row)));
            assert(result@ == cex_of_slots(self.constants, slot_views(candidate), slots_history));
            lemma_reconstruction(self.constants, self.universes, *constraint, letters@, alphabets@,
                slot_views(candidate), slots_history);
            assert(reconstructed(self.constants, self.universes, *constraint, letters@, alphabets@, result));
        }
        Ok(result)
    }

    #[verus_verify]
    #[verus_spec(result =>
        requires crate::verify::reconstruction::slot_wf(self.constants,
            crate::verify::reconstruction::slot_views(slots)),
        ensures result@ == crate::verify::reconstruction::components_of_slots(self.constants,
            crate::verify::reconstruction::slot_views(slots)))]
    fn components(&self, slots: [Slot; COMPONENTS]) -> Components<E> {
        let principal = match slots[0] {
            Slot::Fresh(n) => Value::Fresh(n),
            Slot::Constant(id) => match self.constants.values[id as usize - 1] {
                ComponentValue::Principal(v) => Value::Constant(v),
                _ => {
                    proof! { assert(false); }
                    unreachable!("principal constants are principals")
                }
            },
        };
        let action = match slots[1] {
            Slot::Fresh(n) => Value::Fresh(n),
            Slot::Constant(id) => match self.constants.values[id as usize - 1] {
                ComponentValue::Action(v) => Value::Constant(v),
                _ => {
                    proof! { assert(false); }
                    unreachable!("action constants are actions")
                }
            },
        };
        let resource = match slots[2] {
            Slot::Fresh(n) => Value::Fresh(n),
            Slot::Constant(id) => match self.constants.values[id as usize - 1] {
                ComponentValue::Resource(v) => Value::Constant(v),
                _ => {
                    proof! { assert(false); }
                    unreachable!("resource constants are resources")
                }
            },
        };
        Components {
            principal,
            action,
            resource,
        }
    }
}
