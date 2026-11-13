//! Policy coverage, redundancy, refinement, and tail inclusion through constrained search.

use crate::native::NativeMap;
#[cfg(verus_keep_ghost)]
use crate::verify::constraint_wf;
#[cfg(verus_keep_ghost)]
use crate::verify::frontend::*;
#[cfg(verus_keep_ghost)]
use crate::verify::verdict::*;
#[cfg(verus_keep_ghost)]
use crate::verify::{self as views, search_exec as exec};
#[cfg(verus_keep_ghost)]
use crate::verify::{policy_bridge as bridge, policy_firing as firing, policy_queries as queries};
use alloc::rc::Rc;
use alloc::vec::Vec;
use history_semantics::SymbolicLanguage;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::{
    analyzer as verdict, encoding, implementation, inclusion, search as paper, semantics,
};
#[cfg(verus_keep_ghost)]
use history_semantics::{compile_verify as numeric, symbolic_language_verify as facade};
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::{EventSpec, arity};
use history_syntax::{Arity, Component, Event, Head, MAX_ARITY, RegexExpr, Rule, RuleMode};
use junco_core::compile::validate_component;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex};
use junco_core::flatten::flatten_rule_parts;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
#[cfg(verus_keep_ghost)]
use junco_core::verify::{encoding as enc, flatten as fl};
use junco_core::{CompileError, FlatEncoder, HistoryError, lower_flat};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

#[cfg(verus_keep_ghost)]
verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas,
        vstd::seq_lib::lemma_seq_contains_after_push};
}

use crate::constraint::{
    Atom, Class, ConstId, Constraint, Letter, Operand, Operands, RegisterConstraint, Universes,
    split,
};
use crate::search::{SearchOutcome, search};
use crate::tables::Tables;

/// Bytes of runtime graph one search may be charged before it is reported `Exhausted`;
/// the runtime keeps `MAX_GRAPH_BYTES` per rule.
#[verus_verify]
const GRAPH_BYTES: usize = 16 * 1024 * 1024;

verus! {
/// Stable index of a rule in one analyzer. Query ids must belong to that analyzer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleId(pub(crate) usize);

/// Lowered executable rule plus its original front-end provenance.
pub(crate) struct StoredRule<E: Event> {
    #[allow(dead_code)] // Erased front-end provenance also binds the native event type.
    pub original: Ghost<Rule<E>>,
    #[allow(dead_code)]
    pub flat: Ghost<junco_core::flat::FlatRule<E::Component>>,
    pub numeric: FlatPair<u64>,
    pub constants: Vec<Option<ConstId>>,
    pub constraint: Option<Constraint>,
    pub mode: RuleMode,
}

pub(crate) struct NumericDecision<E: Event> {
    pub inclusion: Inclusion<E>,
    #[cfg(verus_keep_ghost)]
    pub outcome: Ghost<paper::Outcome>,
}
}

verus! {
fn excluded(id: RuleId, exclude: Option<RuleId>) -> (result: bool)
    ensures result == excluded_id(id, exclude),
{
    match exclude { Some(other) => id.0 == other.0, None => false }
}
}

/// The values each event component can take.
///
/// By default every component is infinite: it has more values than any analysis mentions, so a
/// counterexample may use a [fresh](Value::Fresh) value for it. Declare the values of a component
/// whose type has only a few, such as an action enum; treated as infinite, it could yield
/// counterexamples that need a value the type does not have.
#[verus_verify]
#[derive(Clone, Debug)]
pub struct Domains<E: Event> {
    pub(crate) components: Vec<Option<Vec<E::Component>>>,
}

impl<E: Event> Domains<E> {
    /// Every component infinite.
    pub fn infinite() -> Self {
        Self {
            components: (0..E::Arity::value()).map(|_| None).collect(),
        }
    }

    /// Declares all values of one coordinate, in declaration order.
    ///
    /// # Panics
    /// Panics if the coordinate is outside this event's arity or a value belongs to another coordinate.
    pub fn with_domain(
        mut self,
        component: Component,
        values: impl IntoIterator<Item = E::Component>,
    ) -> Self {
        let index = component.index();
        assert!(
            index < self.components.len(),
            "domain coordinate is outside event arity"
        );
        self.components[index] = Some(
            values
                .into_iter()
                .map(|value| {
                    assert_eq!(
                        E::coordinate(value),
                        index,
                        "domain value belongs to another coordinate"
                    );
                    value
                })
                .collect(),
        );
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Components<E: Event> {
    /// One value per coordinate, in the event type's coordinate order.
    pub values: Vec<Value<E::Component>>,
}

/// A candidate and a history on which an inclusion fails.
///
/// What failing means depends on the query; each query documents it. Tail-inclusion witnesses
/// have minimum history length; policy-query correctness does not claim global minimality.
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
    pub(crate) ids: Vec<NativeMap<E::Component, ConstId>>,
    pub(crate) values: Vec<E::Component>,
}

verus! {
impl<E: Event> Constants<E> {
    fn try_intern(&mut self, field: Component, value: E::Component) -> (result: Result<ConstId, core::num::TryFromIntError>)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(),
            field.0 < arity::<E>(), E::coordinate_spec(value) == field.0 as nat,
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + 1,
            result matches Ok(id) ==> stored_code(*final(self), value, id),
            result is Err ==> *final(self) == *old(self) && old(self).values@.len() == u32::MAX,
    {
        let ghost before = *self;
        let index = field.index();
        if let Some(id) = self.ids[index].lookup(&value) {
            proof { lemma_constant_lookup(*self, field, value, id); }
            return Ok(id);
        }
        let id = ConstId::try_from(self.values.len() as u64 + 1)?;
        self.values.push(value);
        self.ids[index].insert_fresh(value, id);
        proof { lemma_constants_insert(before, *self, field, value, id); }
        Ok(id)
    }

    fn intern(&mut self, field: Component, value: E::Component) -> (result: ConstId)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(),
            old(self).values@.len() < u32::MAX,
            field.0 < arity::<E>(), E::coordinate_spec(value) == field.0 as nat,
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + 1,
            stored_code(*final(self), value, result),
    {
        self.try_intern(field, value).expect("constant ids fit in u32")
    }

    /// The universe of a declared finite component, in declaration order without repeats.
    fn universe(&mut self, field: Component, values: &[E::Component]) -> (result: Rc<Vec<ConstId>>)
        requires constants_wf(*old(self)), crate::verify::analyzer_obligations::<E>(),
            old(self).values@.len() + values@.len() <= u32::MAX,
            field.0 < arity::<E>(),
            forall|i: int| 0 <= i < values@.len() ==> E::coordinate_spec(values@[i]) == field.0 as nat,
        ensures constants_wf(*final(self)), constants_frame(*old(self), *final(self)),
            final(self).values@.len() <= old(self).values@.len() + values@.len(),
            universe_encoded(*final(self), (*result)@, values@),
    {
        hide(universe_encoded);
        let ghost before = *self;
        let mut ids = Vec::new();
        let mut i = 0;
        proof { lemma_universe_empty(*self); assert(values@.take(0) =~= Seq::<E::Component>::empty()); }
        while i < values.len()
            invariant i <= values@.len(), constants_wf(*self), crate::verify::analyzer_obligations::<E>(),
                field.0 < arity::<E>(),
                forall|j: int| 0 <= j < values@.len() ==> E::coordinate_spec(values@[j]) == field.0 as nat,
                constants_frame(before, *self), self.values@.len() <= before.values@.len() + i,
                universe_encoded(*self, ids@, values@.take(i as int)),
                before.values@.len() + values@.len() <= u32::MAX,
            decreases values@.len() - i,
        {
            let ghost prior = *self;
            let value = values[i];
            let id = self.intern(field, value);
            proof { lemma_universe_frame(prior, *self, ids@, values@.take(i as int)); }
            let ghost old_ids = ids@;
            let found = contains_id(&ids, id);
            if !found { ids.push(id); } else { proof { assert(ids@.contains(id)); } }
            proof {
                assert(values@.take(i as int + 1) =~= values@.take(i as int).push(value));
                lemma_universe_step(*self, old_ids, ids@, values@.take(i as int), value, id);
            }
            i += 1;
        }
        proof { assert(values@.take(i as int) =~= values@); }
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
    #[cfg(verus_keep_ghost)]
    pub(crate) initial_values: Ghost<Seq<E::Component>>,
}

impl<'a, E: Event> FlatEncoder<E::Component> for BorrowedEncoder<'a, E> {
    open spec fn equality() -> enc::Equality<E::Component> { fl::component_equality::<E>() }
    open spec fn domain() -> enc::Domain<E::Component> { fl::component_domain::<E>() }
    open(crate) spec fn maps(&self) -> enc::Codebook<E::Component> { crate::verify::constant_book(*self.constants) }
    open(crate) spec fn encoding_calls(&self) -> nat { self.calls@ }
    open(crate) spec fn state_wf(&self) -> bool {
        constants_wf(*self.constants) && crate::verify::analyzer_obligations::<E>()
            && self.constants.values@.len() <= self.calls@
            && (self.overflowed ==> u32::MAX < self.calls@)
            && self.initial_values@.is_prefix_of(self.constants.values@)
    }
    open(crate) spec fn obeys_encoding_spec(&self) -> bool {
        constants_wf(*self.constants) && crate::verify::analyzer_obligations::<E>()
    }
    open spec fn errors_are_non_invariant(&self) -> bool { true }
    #[verifier::prophetic]
    open(crate) spec fn restoration(&self) -> (enc::Codebook<E::Component>, bool) {
        let future = mut_ref_future(self.constants);
        (crate::verify::constant_book(future), constants_wf(future)
            && self.initial_values@.is_prefix_of(future.values@))
    }

    fn encode(&mut self, field: Component, value: &E::Component)
        -> (result: Result<u64, HistoryError>)
    {
        let ghost before = *self.constants;
        self.calls = Ghost(self.calls@ + 1);
        if self.overflowed { return Err(HistoryError::IdExhausted { domain: "constant" }); }
        validate_component::<E>(field, value)?;
        let result = match self.constants.try_intern(field, *value) {
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
                assert(value_field::<E>(*value) == field);
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

/// Static analysis of stored rules and policies using one inclusion search per candidate case.
/// Rules retain their individual heads and modes, and ids remain stable under store growth.
#[verus_verify]
pub struct PolicyAnalyzer<E: Event> {
    pub(crate) constants: Constants<E>,
    pub(crate) universes: Universes,
    pub(crate) rules: Vec<StoredRule<E>>,
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {
    /// Creates an analyzer for events whose components take the values of `domains`.
    // Each match keeps the declared domain's exact vector view.
    #[allow(clippy::manual_map)]
    pub fn new(domains: Domains<E>) -> (result: Self)
        requires crate::verify::analyzer_obligations::<E>(), domains_wf(domains), constructor_capacity(domains),
        ensures constructor_result(result, domains),
    {
        proof { lemma_constructor_contract::<E>(); }
        let ghost input = domains;
        let arity = E::Arity::value();
        let mut ids = Vec::with_capacity(arity);
        let mut index = 0;
        while index < arity
            invariant index <= arity, arity == history_syntax::event::specs::arity::<E>(),
                1 <= arity <= MAX_ARITY, ids@.len() == index,
                forall|i: int| 0 <= i < index ==> crate::native::representatives(ids@[i]).len() == 0,
            decreases arity - index,
        {
            ids.push(NativeMap::new());
            index += 1;
        }
        let mut constants = Constants { ids, values: Vec::new() };
        proof { lemma_empty_constants(constants); }
        let mut universes = Vec::with_capacity(arity);
        index = 0;
        while index < arity
            invariant index <= arity, arity == history_syntax::event::specs::arity::<E>(),
                1 <= arity <= MAX_ARITY, domains == input, constructor_capacity(input),
                crate::verify::analyzer_obligations::<E>(), domains_wf(input),
                constants_wf(constants), universes@.len() == index,
                constants.values@.len() <= domain_values_count(input.components@.take(index as int)),
                forall|i: int| 0 <= i < index ==>
                    declared_universe(constants, universes@[i], input.components@[i]),
            decreases arity - index,
        {
            let ghost before = constants;
            proof { lemma_domain_count_step(input.components@, index as int); }
            let field = Component::new(index);
            let universe = match &domains.components[index] {
                Some(values) => {
                    proof {
                        lemma_constructor_contract::<E>();
                        assert(domain_values_count(input.components@) <= u32::MAX);
                        assert(input.components@[index as int] == Some(*values));
                        assert(option_len(input.components@[index as int]) == values@.len());
                        assert(constants.values@.len() + values@.len() <= u32::MAX);
                    }
                    Some(constants.universe(field, values))
                },
                None => None,
            };
            proof {
                assert forall|i: int| 0 <= i < index implies
                    declared_universe(constants, universes@[i], input.components@[i]) by {
                    lemma_declared_frame(before, constants, universes@[i], input.components@[i]);
                }
                assert(declared_universe(constants, universe, input.components@[index as int]));
            }
            universes.push(universe);
            index += 1;
        }
        proof { assert(input.components@.take(index as int) =~= input.components@); }
        let result = Self { constants, universes, rules: Vec::new() };
        proof { lemma_declared_wf(result, input); lemma_constructor_domains(result, input); }
        result
    }
}
}

verus! {
impl<E: Event> PolicyAnalyzer<E> {

    /// Validates and stores a rule. Indices remain stable when later rules add constants.
    pub fn add_rule(&mut self, rule: &Rule<E>) -> (result: Result<RuleId, CompileError>)
        requires views::analyzer_obligations::<E>(), analyzer_state_wf(*old(self)),
            add_rule_capacity(*old(self), *rule),
        ensures analyzer_state_wf(*final(self)),
            final(self)@.domains == old(self)@.domains,
            result matches Ok(id) ==> final(self)@.rules == old(self)@.rules.push(encoding::rule_view(*rule))
                && id@ == old(self)@.rules.len()
                && history_semantics::verify::refinement::semantics::rule_wf(encoding::rule_view(*rule)),
            result is Err ==> final(self)@.rules == old(self)@.rules,
            junco_core::verify::history_specs::no_internal_compile_error(result),
    {
        let ghost before = *self;
        let flat = flatten_rule_parts(rule.mode, &rule.head, &rule.tail, &mut Unmetered, &mut ObservationWorld)?;
        proof { assert(encode_capacity(*self, flat.source)); }
        let numeric_result = self.encode(&flat.source);
        proof { lemma_universes_frame(before.constants, self.constants, self.universes); }
        let numeric = numeric_result?;
        let constants = Self::head_constants(&numeric.head);
        let constraint = Constraint::head(&constants, &self.universes);
        proof {
            lemma_lowered_payload(self.constants, flat.source, numeric);
            if let Some(g) = &constraint {
                lemma_head_payload(self.constants, numeric.head@, constants@, *g);
            }
            lemma_universes_frame(before.constants, self.constants, self.universes);
        }
        let id = RuleId(self.rules.len());
        self.rules.push(StoredRule { original: Ghost(*rule), flat: Ghost(flat),
            numeric, constants, constraint, mode: rule.mode });
        proof {
            assert(self@.rules =~= before@.rules.push(encoding::rule_view(*rule)));
        }
        Ok(id)
    }

    /// Whether `by` covers every denial of the stored rule.
    pub fn covered(&self, rule: RuleId, by: &[RuleId]) -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
            rule@ < self@.rules.len(), valid_ids(*self, by@),
            verdict::unrestricted_components_infinite(self@.domains),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(v) ==> verdict::covered_correct(self@, rule@, rule_ids(by@), v@),
            result matches Ok(Inclusion::Counterexample(c)) ==> verdict::cex_has_instance(self@, c@)
                && !semantics::covers(self@.domains, verdict::rules_of(self@, rule_ids(by@)), self@.rules[rule@ as int]),
    {
        self.covered_with(rule, by, None)
    }

    /// Excludes every occurrence of `rule`, without allocating a filtered policy.
    pub fn redundant(&self, rule: RuleId, policy: &[RuleId]) -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
            rule@ < self@.rules.len(), valid_ids(*self, policy@),
            verdict::unrestricted_components_infinite(self@.domains),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(v) ==> verdict::redundant_correct(self@, rule@, rule_ids(policy@), v@),
            result matches Ok(Inclusion::Counterexample(c)) ==> verdict::cex_has_instance(self@, c@)
                && !semantics::covers(self@.domains,
                    verdict::rules_of(self@, verdict::without_rule(rule_ids(policy@), rule@)), self@.rules[rule@ as int]),
    {
        let result = self.covered_with(rule, policy, Some(rule))?;
        proof {
            queries::lemma_selected_ids(*self, policy@, Some(rule));
            assert(queries::selected_rule_ids(policy@, Some(rule)) == verdict::without_rule(rule_ids(policy@), rule@));
            bridge::lemma_redundancy_result(self@, rule@, rule_ids(policy@), result@);
        }
        Ok(result)
    }

    /// Whether `stricter` denies everything denied by `than`.
    pub fn at_least_as_strict(&self, stricter: &[RuleId], than: &[RuleId])
        -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
            valid_ids(*self, stricter@), valid_ids(*self, than@),
            verdict::unrestricted_components_infinite(self@.domains),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(v) ==> verdict::at_least_as_strict_correct(self@, rule_ids(stricter@), rule_ids(than@), v@),
            result matches Ok(Inclusion::Counterexample(c)) ==> verdict::cex_has_instance(self@, c@)
                && !semantics::refines(self@.domains, verdict::rules_of(self@, rule_ids(stricter@)),
                    verdict::rules_of(self@, rule_ids(than@))),
    {
        let mut index = 0;
        while index < than.len()
            invariant index <= than@.len(), analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
                valid_ids(*self, stricter@), valid_ids(*self, than@),
                verdict::unrestricted_components_infinite(self@.domains),
                forall|j: int| 0 <= j < index ==> semantics::covers(self@.domains,
                    verdict::rules_of(self@, rule_ids(stricter@)), self@.rules[than@[j]@ as int]),
            decreases than@.len() - index,
        {
            let inclusion = self.covered(than[index], stricter)?;
            match inclusion {
                Inclusion::Holds => {},
                _ => {
                    proof { bridge::lemma_refinement_result(self@, rule_ids(stricter@), rule_ids(than@), index as int, inclusion@); }
                    return Ok(inclusion);
                },
            }
            index += 1;
        }
        proof { bridge::lemma_refinement_holds(self@, rule_ids(stricter@), rule_ids(than@)); }
        Ok(Inclusion::Holds)
    }

    fn covered_with(&self, rule: RuleId, by: &[RuleId], exclude: Option<RuleId>)
        -> (result: Result<Inclusion<E>, HistoryError>)
        requires analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
            rule.0 < self.rules@.len(), valid_ids(*self, by@),
            verdict::unrestricted_components_infinite(self@.domains),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(v) ==> verdict::covered_correct(self@, rule@, queries::selected_rule_ids(by@, exclude), v@),
            result matches Ok(Inclusion::Counterexample(c)) ==> verdict::cex_has_instance(self@, c@)
                && !semantics::covers(self@.domains, verdict::rules_of(self@, queries::selected_rule_ids(by@, exclude)),
                    self@.rules[rule@ as int]),
    {
        let analyzed = &self.rules[rule.0];
        let ghost policy = queries::numeric_policy(*self, by@, exclude);
        let ghost left = queries::stored_numeric(*analyzed);
        proof {
            queries::lemma_stored_policy(*self, by@, exclude);
            views::table::lemma_structural_dag(analyzed.numeric);
            views::policy_source::lemma_numeric_rule(analyzed.numeric, analyzed.mode);
            assert(left.head =~= pins(analyzed.numeric.head@));
        }
        let constraint = match &analyzed.constraint {
            Some(g) => g,
            None => {
                proof {
                    assert(inclusion::n_covers(views::ndomains(self.universes), policy, left)) by {
                        assert forall|theta: junco_core::verify::history_specs::Subst,
                            word: Seq<junco_core::verify::history_specs::EventView>|
                            encoding::n_theta_ok(views::ndomains(self.universes), theta)
                            && encoding::n_history_in(views::ndomains(self.universes), word)
                            && encoding::n_rule_denies(left, theta, word)
                            implies encoding::n_policy_denies(policy, theta, word) by {
                            inclusion::lemma_rule_denies_iff(left, theta, word);
                        }
                    }
                    queries::lemma_covered_holds(*self, rule, by@, exclude);
                }
                return Ok(Inclusion::Holds);
            },
        };
        let atoms = self.policy_head_atoms(by, exclude);
        let operands = Operands::of(&atoms, self.universes.len());
        proof { views::policy_operands::lemma_policy_operands(*self, by@, exclude, atoms@, operands); }
        let cases = split(constraint, &operands, &self.universes)?;
        let ghost family = views::constraint_views(cases@).map(|v: implementation::ConstraintView| implementation::constraint_of(v));
        proof { firing::lemma_policy_split(*constraint, operands, self.universes, atoms@, cases@, policy); }
        let mut index = 0;
        while index < cases.len()
            invariant index <= cases@.len(), analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
                rule.0 < self.rules@.len(), valid_ids(*self, by@),
                verdict::unrestricted_components_infinite(self@.domains),
                policy == queries::numeric_policy(*self, by@, exclude),
                left == queries::stored_numeric(self.rules@[rule.0 as int]),
                stored_rule_wf(self.constants, self.universes, *analyzed),
                views::shape_wf(*constraint, operands, self.universes),
                constraint_codes_wf(self.constants, constraint@),
                implementation::constraint_of(constraint@) == inclusion::head_constraint(left.head),
                forall|pair: (Component, nat)| inclusion::head_pairs(policy).contains(pair)
                    ==> pair.0.0 < arity::<E>() && operands.register[pair.0.0 as int]
                        && views::codes(operands.constants[pair.0.0 as int].view()).contains(pair.1),
                forall|k: int, v: nat| 0 <= k < arity::<E>()
                    && views::codes(operands.constants[k].view()).contains(v)
                    ==> views::reconstruction::code_field(self.constants, Component(k as u8), v),
                views::constraint_views(cases@) == views::split_views(*constraint, operands, self.universes),
                inclusion::split_ok(views::ndomains(self.universes), inclusion::head_constraint(left.head),
                    inclusion::head_pairs(policy), family),
                family == views::constraint_views(cases@).map(|v: implementation::ConstraintView| implementation::constraint_of(v)),
                forall|j: int| 0 <= j < cases@.len() ==> constraint_wf(cases@[j]),
                forall|j: int| 0 <= j < index ==> inclusion::included_under(views::ndomains(self.universes),
                    implementation::constraint_of(cases@[j]@), inclusion::denial(left),
                    inclusion::firing_denials(views::ndomains(self.universes), policy, implementation::constraint_of(cases@[j]@))),
            decreases cases@.len() - index,
        {
            let case = &cases[index];
            proof {
                assert(cases@.to_set().contains(*case));
                assert(views::constraint_views(cases@).contains(case@));
                assert(family.contains(implementation::constraint_of(case@)));
            }
            #[cfg(verus_keep_ghost)]
            let difference = self.policy_difference(rule, by, exclude, case, constraint, &operands)?;
            #[cfg(not(verus_keep_ghost))]
            let difference = self.policy_difference(rule, by, exclude, case)?;
            let ghost input = NumericInput { left: inclusion::denial(left),
                right: inclusion::firing_denials(views::ndomains(self.universes), policy,
                    implementation::constraint_of(case@)) };
            #[cfg(verus_keep_ghost)]
            let decision = self.decide(case.copy(), difference, Ghost(input))?;
            #[cfg(not(verus_keep_ghost))]
            let decision = self.decide(case.copy(), difference)?;
            proof { queries::lemma_covered_decision(*self, rule, by@, exclude, input, case@, decision); }
            match decision.inclusion {
                Inclusion::Holds => {},
                _ => return Ok(decision.inclusion),
            }
            index += 1;
        }
        proof {
            inclusion::lemma_policy_reduction(views::ndomains(self.universes), policy, left, family);
            queries::lemma_covered_holds(*self, rule, by@, exclude);
        }
        Ok(Inclusion::Holds)
    }

    fn policy_head_atoms(&self, by: &[RuleId], exclude: Option<RuleId>) -> (atoms: Vec<Atom>)
        requires analyzer_state_wf(*self), valid_ids(*self, by@),
        ensures head_atoms_ok(*self, by@, exclude, atoms@),
    {
        let mut atoms = Vec::new();
        let mut component = 0;
        while component < self.universes.len()
            invariant component <= self.universes@.len(), analyzer_state_wf(*self), valid_ids(*self, by@),
                views::atoms_wf(atoms@, arity::<E>()),
                forall|j: int| 0 <= j < atoms@.len() ==> #[trigger] atoms@[j].component < component,
                forall|j: int, k: int| 0 <= j < by@.len() && !excluded_id(by@[j], exclude) && 0 <= k < component
                    ==> match #[trigger] self.rules@[by@[j].0 as int].constants@[k] {
                        Some(v) => atoms@.contains(Atom { component: k as usize, operand: Operand::Constant(v) })
                            && atoms@.contains(Atom { component: k as usize, operand: Operand::Register }), None => true,
                    },
                forall|j: int| 0 <= j < atoms@.len() ==> match #[trigger] atoms@[j].operand {
                    Operand::Constant(v) => views::reconstruction::code_field(self.constants, Component(atoms@[j].component as u8), v as nat),
                    _ => true,
                },
            decreases self.universes@.len() - component,
        {
            let mut registered = false;
            let mut index = 0;
            while index < by.len()
                invariant index <= by@.len(), component < self.universes@.len(),
                    analyzer_state_wf(*self), valid_ids(*self, by@), views::atoms_wf(atoms@, arity::<E>()),
                    registered ==> atoms@.contains(Atom { component, operand: Operand::Register }),
                    forall|j: int| 0 <= j < atoms@.len() ==> #[trigger] atoms@[j].component <= component,
                    forall|j: int, k: int| 0 <= j < by@.len() && !excluded_id(by@[j], exclude)
                        && 0 <= k <= component && (k < component || j < index)
                        ==> match #[trigger] self.rules@[by@[j].0 as int].constants@[k] {
                            Some(v) => atoms@.contains(Atom { component: k as usize, operand: Operand::Constant(v) })
                                && atoms@.contains(Atom { component: k as usize, operand: Operand::Register }), None => true,
                        },
                    forall|j: int| 0 <= j < atoms@.len() ==> match #[trigger] atoms@[j].operand {
                        Operand::Constant(v) => views::reconstruction::code_field(self.constants, Component(atoms@[j].component as u8), v as nat),
                        _ => true,
                    },
                decreases by@.len() - index,
            {
                let id = by[index];
                if !excluded(id, exclude) {
                    let other = &self.rules[id.0];
                    proof {
                        assert(stored_rule_wf(self.constants, self.universes, *other));
                        assert(other.constants@.len() == arity::<E>());
                    }
                    if let Some(value) = other.constants[component] {
                        proof {
                            assert(views::head_view(other.constants@)[component as int]
                                == pins(other.numeric.head@)[component as int]);
                            assert(views::option_code(other.constants@[component as int])
                                == encoding_head_code(other.numeric.head@[component as int]));
                            assert(other.numeric.head@[component as int] == FlatHead::Constant(value as u64));
                            assert(views::reconstruction::code_field(self.constants, Component(component as u8), value as nat));
                        }
                        if !registered {
                            let ghost previous = atoms@;
                            atoms.push(Atom { component, operand: Operand::Register });
                            proof {
                                vstd::seq_lib::lemma_seq_contains_after_push(previous,
                                    Atom { component, operand: Operand::Register },
                                    Atom { component, operand: Operand::Register });
                            }
                            registered = true;
                        }
                        let ghost previous = atoms@;
                        proof { assert(previous.contains(Atom { component, operand: Operand::Register })); }
                        atoms.push(Atom { component, operand: Operand::Constant(value) });
                        proof {
                            vstd::seq_lib::lemma_seq_contains_after_push(previous,
                                Atom { component, operand: Operand::Constant(value) },
                                Atom { component, operand: Operand::Register });
                        }
                    }
                }
                index += 1;
            }
            component += 1;
        }
        atoms
    }

    /// Builds the difference against exactly the heads selected by one decided split case.
    fn policy_difference(&self, rule: RuleId, by: &[RuleId], exclude: Option<RuleId>,
        case: &Constraint,
        #[cfg(verus_keep_ghost)] start: &Constraint,
        #[cfg(verus_keep_ghost)] operands: &Operands) -> (result: Result<FlatPair<u64>, HistoryError>)
        requires analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
            rule.0 < self.rules@.len(), valid_ids(*self, by@),
            views::shape_wf(*start, *operands, self.universes),
            views::split_views(*start, *operands, self.universes).contains(case@),
            constraint_wf(*case), constraint_codes_wf(self.constants, start@),
            inclusion::satisfiable(views::ndomains(self.universes), implementation::constraint_of(case@)),
            forall|pair: (Component, nat)| inclusion::head_pairs(queries::numeric_policy(*self, by@, exclude)).contains(pair)
                ==> pair.0.0 < arity::<E>() && operands.register@[pair.0.0 as int]
                    && views::codes(operands.constants@[pair.0.0 as int].view()).contains(pair.1),
            forall|k: int, v: nat| 0 <= k < operands.constants@.len()
                && views::codes(operands.constants@[k].view()).contains(v)
                ==> views::reconstruction::code_field(self.constants, Component(k as u8), v),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(difference) ==> decision_ready(*self, NumericInput {
                left: inclusion::denial(queries::stored_numeric(self.rules@[rule.0 as int])),
                right: inclusion::firing_denials(views::ndomains(self.universes),
                    queries::numeric_policy(*self, by@, exclude), implementation::constraint_of(case@)),
            }, *case, difference),
    {
        let analyzed = &self.rules[rule.0];
        let ghost left = queries::stored_numeric(*analyzed);
        let mut tables = Tables::new(self.universes.len());
        let ghost empty = tables@;
        proof {
            views::table::lemma_structural_dag(analyzed.numeric);
            views::policy_source::lemma_numeric_rule(analyzed.numeric, analyzed.mode);
        }
        let denial = tables.denial(&analyzed.numeric, analyzed.mode)?;
        proof {
            lemma_append_payload(self.constants, empty, analyzed.numeric, tables@);
            assert forall|theta: junco_core::verify::history_specs::Subst,
                word: Seq<junco_core::verify::history_specs::EventView>|
                junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
                numeric::source_regex(tables@, denial as nat, theta, word)
                    == encoding::n_lang(theta, inclusion::denial(left), word) by {
                inclusion::lemma_denial_lang(left, theta, word);
            }
        }
        let mut matching: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < by.len()
            invariant index <= by@.len(), analyzer_state_wf(*self), views::analyzer_obligations::<E>(),
                valid_ids(*self, by@), rule.0 < self.rules@.len(), views::table::dag(tables@),
                denial < tables.regexes@.len(), source_codes_wf(self.constants, tables@),
                views::shape_wf(*start, *operands, self.universes),
                views::split_views(*start, *operands, self.universes).contains(case@),
                constraint_wf(*case), inclusion::satisfiable(views::ndomains(self.universes), implementation::constraint_of(case@)),
                forall|pair: (Component, nat)| inclusion::head_pairs(queries::numeric_policy(*self, by@, exclude)).contains(pair)
                    ==> pair.0.0 < arity::<E>() && operands.register@[pair.0.0 as int]
                        && views::codes(operands.constants@[pair.0.0 as int].view()).contains(pair.1),
                forall|j: int| 0 <= j < matching@.len() ==> matching@[j] < tables.regexes@.len(),
                covering_prefix(*self, by@, exclude, index as int, *case, tables@, matching@),
                forall|theta: junco_core::verify::history_specs::Subst, word: Seq<junco_core::verify::history_specs::EventView>|
                    junco_core::verify::history_specs::event_wf(theta, theta.len())
                    ==> numeric::source_regex(tables@, denial as nat, theta, word)
                        == encoding::n_lang(theta, inclusion::denial(left), word),
            decreases by@.len() - index,
        {
            let other = by[index];
            let ghost before_tables = tables@;
            let ghost before_roots = matching@;
            let ghost mut added = None::<u32>;
            if !excluded(other, exclude) {
                proof {
                    views::policy_operands::lemma_selected_head_ready(*self, by@, exclude,
                        index as int, *start, *operands, case@);
                }
                let theirs = &self.rules[other.0];
                proof {
                    assert(stored_rule_wf(self.constants, self.universes, *theirs));
                    assert(queries::stored_numeric(*theirs).head =~= pins(theirs.numeric.head@));
                }
                if let Some(head) = &theirs.constraint {
                    proof {
                        firing::lemma_head_firing_exact(views::ndomains(self.universes), case@, head@);
                    }
                    if case.entails(head) {
                        let ghost previous = tables@;
                        proof {
                            views::table::lemma_structural_dag(theirs.numeric);
                            views::policy_source::lemma_numeric_rule(theirs.numeric, theirs.mode);
                        }
                        let root = tables.denial(&theirs.numeric, theirs.mode)?;
                        proof { lemma_append_payload(self.constants, previous, theirs.numeric, tables@); }
                        proof {
                            added = Some(root);
                            assert(queries::stored_numeric(*theirs).head =~= pins(theirs.numeric.head@));
                            assert forall|theta: junco_core::verify::history_specs::Subst,
                                word: Seq<junco_core::verify::history_specs::EventView>|
                                junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
                                numeric::source_regex(tables@, root as nat, theta, word)
                                    == encoding::n_lang(theta, inclusion::denial(queries::stored_numeric(*theirs)), word) by {
                                inclusion::lemma_denial_lang(queries::stored_numeric(*theirs), theta, word);
                            }
                        }
                        matching.push(root);
                    }
                } else {
                    proof { firing::lemma_unsatisfiable_head_does_not_fire(views::ndomains(self.universes),
                        implementation::constraint_of(case@), inclusion::head_constraint(queries::stored_numeric(*theirs).head)); }
                }
            }
            proof {
                lemma_covering_step(*self, by@, exclude, index as int, *case, before_tables,
                    before_roots, tables@, matching@, added);
            }
            index += 1;
        }
        let ghost roots = matching@;
        let ghost before_union = tables@;
        let covering = tables.push(FlatRegex::Union(matching))?;
        proof { views::table::lemma_frame_languages(before_union, tables@); }
        let ghost assembled = tables@;
        proof {
            assert(covering as nat == before_union.regexes@.len());
            assert forall|j: int| 0 <= j < roots.len() implies roots[j] < covering by {}
            match assembled.regexes@[covering as int] {
                FlatRegex::Union(children) => { assert(children@ == roots); },
                _ => { assert(false); },
            }
        }
        let difference = tables.difference(denial, covering)?;
        proof {
            views::policy_operands::lemma_known_split_case_codes(*self, *start, *operands, case@);
            assert forall|theta: junco_core::verify::history_specs::Subst, word: Seq<junco_core::verify::history_specs::EventView>|
                junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
                numeric::source_regex(assembled, covering as nat, theta, word)
                    == encoding::n_lang(theta, inclusion::firing_denials(views::ndomains(self.universes),
                        queries::numeric_policy(*self, by@, exclude), implementation::constraint_of(case@)), word) by {
                queries::lemma_firing_prefix(*self, by@, exclude, *case, theta, word);
                reveal_with_fuel(numeric::source_regex, 1);
                assert forall|j: int| 0 <= j < roots.len() implies
                    numeric::source_regex(assembled, roots[j] as nat, theta, word)
                        == numeric::source_regex(before_union, roots[j] as nat, theta, word) by {}
                let children = match assembled.regexes@[covering as int] {
                    FlatRegex::Union(children) => children,
                    _ => arbitrary(),
                };
                assert(children@ == roots);
                if numeric::source_regex(assembled, covering as nat, theta, word) {
                    let j = choose|j: int| 0 <= j < children@.len() && children@[j] < covering
                        && numeric::source_regex(assembled, children@[j] as nat, theta, word);
                    assert(numeric::source_regex(before_union, roots[j] as nat, theta, word));
                }
                if exists|j: int| 0 <= j < roots.len()
                    && #[trigger] numeric::source_regex(before_union, roots[j] as nat, theta, word) {
                    let j = choose|j: int| 0 <= j < roots.len()
                        && numeric::source_regex(before_union, roots[j] as nat, theta, word);
                    assert(numeric::source_regex(assembled, children@[j] as nat, theta, word));
                    assert(numeric::source_regex(assembled, covering as nat, theta, word));
                }
                assert(numeric::source_regex(assembled, covering as nat, theta, word)
                    == (exists|j: int| 0 <= j < roots.len()
                        && #[trigger] numeric::source_regex(before_union, roots[j] as nat, theta, word)));
            }
        }
        Ok(difference)
    }

    /// Whether, for every candidate that `head` matches, every history in `left` is in `right`.
    ///
    /// Both tails may refer to the head's variables. A counterexample is a matching candidate and
    /// a history in `left` but not in `right`.
    #[verus_spec(result => requires views::analyzer_obligations::<E>(),
        analyzer_state_wf(*old(self)), query_capacity(*old(self), *left, *right),
        ensures analyzer_state_wf(*final(self)),
            junco_core::verify::history_specs::no_internal_compile_error(result),
            result matches Ok(v) ==> verdict::tail_included_ok(final(self)@, head@, left@, right@, v@))]
    pub fn tail_included(
        &mut self,
        head: &Head<E>,
        left: &RegexExpr<E>,
        right: &RegexExpr<E>,
    ) -> Result<Inclusion<E>, CompileError> {
        let ghost before = *self;
        proof { lemma_query_capacity(*self, *left, *right); }
        let ghost bound = self.constants.values@.len() + 2 * arity::<E>() + fl::regex_cost::<E>(left@) + fl::regex_cost::<E>(right@);
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
        proof {
            assert(pins(left_numeric.head@) =~= crate::verify::typed_numeric::template_head(left_numeric));
        }
        let result = match Constraint::head(&constants, &self.universes) {
            Some(constraint) => {
                proof { lemma_head_payload(self.constants, left_numeric.head@, constants@, constraint); }
                let mut tables = Tables::new(self.universes.len());
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
                let ghost numeric_input = NumericInput {
                    left: views::policy_source::source_model(difference, difference.root as nat),
                    right: junco_core::verify::history_specs::Regex::Empty,
                };
                proof {
                    assert(source_codes_wf(self.constants, difference));
                    assert(difference_source(input, difference));
                    views::policy_source::lemma_source_model(difference);
                    assert(numeric_difference(numeric_input, difference));
                    assert(difference_language(input, numeric_input.left));
                    assert(decision_ready(*self, numeric_input, constraint, difference));
                }
                #[cfg(verus_keep_ghost)]
                let decided = self.decide(constraint, difference, Ghost(numeric_input))?;
                #[cfg(not(verus_keep_ghost))]
                let decided = self.decide(constraint, difference)?;
                proof { lemma_tail_decision(*self, input, numeric_input, constraint@, decided); }
                decided.inclusion
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
    fn head_constants(head: &[FlatHead<u64>]) -> (result: Vec<Option<ConstId>>)
        requires numeric_head_wf(head@),
        ensures result@.len() == head@.len(), crate::verify::head_view(result@) == pins(head@),
    {
        let mut result = Vec::with_capacity(head.len());
        let mut i = 0;
        while i < head.len()
            invariant i <= head@.len(), result@.len() == i, numeric_head_wf(head@),
                forall|j: int| 0 <= j < i ==> crate::verify::option_code(result@[j]) == encoding_head_code(head@[j]),
            decreases head@.len() - i,
        {
            result.push(match head[i] { FlatHead::Constant(v) => Some(v as u32), _ => None });
            i += 1;
        }
        result
    }

    /// `source` with each constant replaced by its constant id.
    fn encode(&mut self, source: &FlatPair<E::Component>) -> (result: Result<FlatPair<u64>, HistoryError>)
        requires constants_wf(old(self).constants), crate::verify::analyzer_obligations::<E>(), encode_capacity(*old(self), *source),
        ensures constants_wf(final(self).constants), enc::extends(crate::verify::constant_book(old(self).constants), crate::verify::constant_book(final(self).constants), fl::component_equality::<E>()),
            constants_frame(old(self).constants, final(self).constants),
            final(self).universes == old(self).universes,
            final(self).rules == old(self).rules,
            analyzer_state_wf(*old(self)) ==> analyzer_state_wf(*final(self)),
            junco_core::verify::history_specs::no_internal_error(result),
            final(self).constants.values@.len() <= old(self).constants.values@.len() + source.head@.len() + source.tests@.len(),
            result matches Ok(target) ==> enc::lowering(*source, target, crate::verify::constant_book(final(self).constants), fl::component_equality::<E>())
                && junco_core::flat::verify::structural_wf(target) && numeric_head_wf(target.head@),
    {
        let ghost initial_count = self.constants.values@.len();
        let ghost before = *self;
        proof { assert(initial_count == old(self).constants.values@.len()); }
        proof { lemma_constants_maps(self.constants); }
        let (result, overflowed, Ghost(maps), Ghost(count)) = {
            let mut encoder = BorrowedEncoder {
                constants: &mut self.constants, overflowed: false,
                calls: Ghost(initial_count),
                #[cfg(verus_keep_ghost)]
                initial_values: Ghost(before.constants.values@),
            };
            let result = lower_flat(source, &mut encoder, &mut Unmetered, &mut ObservationWorld);
            let ghost maps = encoder.maps();
            proof {
                assert(encoder.calls@ <= initial_count + source.head@.len() + source.tests@.len());
                assert(encoder.constants.values@.len() <= initial_count + source.head@.len() + source.tests@.len());
                lemma_constant_book_length(*encoder.constants);
                assert(book_entries_count(maps) == encoder.constants.values@.len());
                assert(!encoder.overflowed);
            }
            let ghost count = encoder.constants.values@.len();
            let overflowed = encoder.overflowed;
            (result, overflowed, Ghost(maps), Ghost(count))
        };
        proof {
            assert(crate::verify::constant_book(self.constants) == maps);
            lemma_constant_book_length(self.constants);
            assert(self.constants.values@.len() == count);
            assert(!overflowed);
        }
        if overflowed {
            let _ = ConstId::try_from(self.constants.values.len() + 1).expect("constant ids fit in u32");
        }
        proof {
            if let Ok(target) = &result { lemma_lowered_head_bound(self.constants, *source, *target); }
            if analyzer_state_wf(before) {
            lemma_universes_extended(before.constants, self.constants, self.universes);
                lemma_store_extends(before.constants, self.constants, self.universes, self.rules@);
            }
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
        #[cfg(verus_keep_ghost)] Ghost(input): Ghost<NumericInput>,
    ) -> (result: Result<NumericDecision<E>, HistoryError>)
        requires decision_ready(*self, input, constraint, difference),
        ensures result matches Ok(v) ==> numeric_decision_ok(*self, input, constraint@, v),
            junco_core::verify::history_specs::no_internal_error(result),
    {
        proof {
            assert(numeric::source_dag_wf(difference)) by { reveal(views::table::dag); }
            facade::lemma_aligned_compile_budget(GRAPH_BYTES);
        }
        let mut language = match SymbolicLanguage::compile(&difference, GRAPH_BYTES) {
            Ok(language) => language,
            Err(HistoryError::GraphLimit { .. }) => return Ok(NumericDecision {
                inclusion: Inclusion::Exhausted,
                #[cfg(verus_keep_ghost)]
                outcome: Ghost(paper::Outcome::Exhausted) }),
            Err(error) => return Err(error),
        };
        let ghost original = language;
        let ghost start = paper::Item { constraint: implementation::constraint_of(constraint@),
            state: model::lift_regex(facade::graph(language), facade::root(language)) };
        let ghost vocabulary = exec::root_vocabulary(language, self.universes, constraint@);
        proof {
            lemma_root_payload(*self, language, difference, constraint@);
            assert(views::constraint_unique::universes_distinct(self.universes));
            assert forall|theta: junco_core::verify::history_specs::Subst, word: Seq<junco_core::verify::history_specs::EventView>|
                junco_core::verify::history_specs::event_wf(theta, theta.len()) implies
                    history_semantics::verify::refinement::encoding::n_lang(theta, start.state, word)
                        == (encoding::n_lang(theta, input.left, word)
                            && !encoding::n_lang(theta, input.right, word)) by {
                assert(model::regex_lang(facade::graph(language), theta, facade::root(language), word)
                    == numeric::source_regex(difference, difference.root as nat, theta, word));
                reveal(model::regex_lang);
            }
            assert(paper::initial_ok(start.state, input.left, input.right));
        }
        let outcome = match search(&mut language, &self.universes, constraint) {
            Ok(outcome) => outcome,
            Err(HistoryError::GraphLimit { .. }) => return Ok(NumericDecision {
                inclusion: Inclusion::Exhausted,
                #[cfg(verus_keep_ghost)]
                outcome: Ghost(paper::Outcome::Exhausted) }),
            Err(error) => return Err(error),
        };
        proof {
            lemma_result_outcome(views::ndomains(self.universes), start, exec::outcome_view(outcome));
            lemma_refutation_input(*self, start, outcome, vocabulary);
            lemma_outcome_difference(views::ndomains(self.universes), start,
                input, exec::outcome_view(outcome));
        }
        match outcome {
            SearchOutcome::Holds => {
                Ok(NumericDecision { inclusion: Inclusion::Holds,
                    #[cfg(verus_keep_ghost)]
                    outcome: Ghost(paper::Outcome::Holds) })
            }
            SearchOutcome::Refuted(refutation) => {
                #[cfg(verus_keep_ghost)]
                let counterexample = self.counterexample(&refutation.constraint, &refutation.letters, refutation.alphabets)?;
                #[cfg(not(verus_keep_ghost))]
                let counterexample = self.counterexample(&refutation.constraint, &refutation.letters)?;
                let result = NumericDecision { inclusion: Inclusion::Counterexample(counterexample),
                    #[cfg(verus_keep_ghost)]
                    outcome: Ghost(exec::outcome_view(outcome)) };
                proof {
                    reveal(exec::refutation_ready);
                    lemma_numeric_refutation(*self, input, constraint@, refutation.constraint,
                        refutation.letters@, refutation.alphabets@, result);
                }
                Ok(result)
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
            self.universes, *constraint, letters@, alphabets@, c),
            junco_core::verify::history_specs::no_internal_error(result))]
    fn counterexample(
        &self,
        constraint: &Constraint,
        letters: &[Letter],
        #[cfg(verus_keep_ghost)] alphabets: Ghost<Seq<Set<junco_core::kernel::verify::Primitive>>>,
    ) -> Result<Counterexample<E>, HistoryError> {
        #[cfg(verus_keep_ghost)]
        use crate::verify::{
            component_at, component_index, domain_view, lemma_codes, lemma_constraint_possible,
            reconstruction::*, register_possible, register_sat,
        };
        proof! {
            lemma_known_codes(self.constants);
            lemma_constraint_possible(*constraint, self.universes);
        }
        let arity = self.universes.len();
        let mut fresh: usize = 0;
        let mut candidate = [Slot::Constant(0); MAX_ARITY];
        let mut component: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            arity == self.universes@.len(), arity == history_syntax::event::specs::arity::<E>(),
            1 <= arity <= MAX_ARITY,
            component <= arity, fresh <= component,
            reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
            forall|k: int| 0 <= k < component ==> candidate_field_ok(self.constants,
                self.universes, *constraint, k, candidate[k]@),
            forall|k: int| #![trigger candidate[k]@] 0 <= k < component ==> (candidate[k]@ matches
                history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
            forall|k: int| 0 <= k < arity ==> register_possible(constraint.0[k], self.universes[k]),
            decreases arity - component,
        ))]
        while component < arity {
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
                let field = component_at(component);
                assert(component_index(field) == component);
                lemma_register_known(self.constants, field, constraint.0[component as int]@);
                assert(candidate_field_ok(self.constants, self.universes, *constraint, component as int, slot@));
            }
            candidate[component] = slot;
            component += 1;
        }
        let candidate_values = self.components(&candidate[..arity]);
        let mut values = Vec::<Components<E>>::with_capacity(letters.len());
        proof_decl! {
            let ghost mut slots_history: Seq<Seq<history_semantics::verify::refinement::implementation::SlotView>>
                = Seq::empty();
        }
        let mut index: usize = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            arity == self.universes@.len(), arity == history_syntax::event::specs::arity::<E>(),
            1 <= arity <= MAX_ARITY,
            index <= letters@.len(), values@.len() == index, slots_history.len() == index,
            candidate_values@ == components_of_slots(self.constants, slot_views(candidate@.take(arity as int))),
            forall|i: int| 0 <= i < index ==> values@[i]@ == components_of_slots(self.constants, slots_history[i]),
            fresh <= arity * (index + 1),
            reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
            slot_wf(self.constants, slot_views(candidate@.take(arity as int))),
            forall|k: int| 0 <= k < arity ==> candidate_field_ok(self.constants,
                self.universes, *constraint, k, candidate[k]@),
            forall|k: int| #![trigger candidate[k]@] 0 <= k < arity ==> (candidate[k]@ matches
                history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
            forall|i: int| 0 <= i < index ==> slot_wf(self.constants, slots_history[i])
                && forall|k: int| 0 <= k < arity ==> history_field_matches(slot_views(candidate@.take(arity as int)), letters@[i]@,
                    k, slots_history[i][k]) && slot_domain(slots_history[i][k], domain_view(self.universes[k])),
            forall|i: int, k: int| #![trigger slots_history[i][k]] 0 <= i < index && 0 <= k < arity
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
            let mut slots = [Slot::Constant(0); MAX_ARITY];
            let mut component: usize = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            arity == self.universes@.len(), arity == history_syntax::event::specs::arity::<E>(),
            1 <= arity <= MAX_ARITY,
                component <= arity, index < letters@.len(), values@.len() == index, slots_history.len() == index,
                fresh <= arity * (index + 1) + component,
                reconstruction_input(self.constants, self.universes, *constraint, letters@, alphabets@),
                letter@ == letters@[index as int]@,
                letter_codes_ok(self.constants, crate::verify::ndomains(self.universes),
                    letter@, alphabets@[index as int]),
                slot_wf(self.constants, slot_views(candidate@.take(arity as int))),
                forall|k: int| 0 <= k < arity ==> candidate_field_ok(self.constants,
                    self.universes, *constraint, k, candidate[k]@),
                forall|k: int| #![trigger candidate[k]@] 0 <= k < arity ==> (candidate[k]@ matches
                    history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                forall|k: int| 0 <= k < component ==> history_field_matches(slot_views(candidate@.take(arity as int)), letter@,
                    k, slots[k]@) && slot_domain(slots[k]@, domain_view(self.universes[k])) && match slots[k]@ {
                        history_semantics::verify::refinement::implementation::SlotView::Code(v) =>
                            code_field(self.constants, component_at(k as usize), v), _ => true },
                forall|i: int| #![trigger slots_history[i]] 0 <= i < index
                    ==> slot_wf(self.constants, slots_history[i]),
                forall|i: int, k: int| #![trigger slots_history[i][k]] 0 <= i < index && 0 <= k < arity
                    ==> (slots_history[i][k] matches
                        history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                forall|k: int| #![trigger slots[k]@] 0 <= k < component ==> (slots[k]@ matches
                    history_semantics::verify::refinement::implementation::SlotView::Fresh(n) ==> n < fresh),
                decreases arity - component,
            ))]
            while component < arity {
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
                    assert(history_field_matches(slot_views(candidate@.take(arity as int)), letter@, component as int, slot@));
                    lemma_history_field(self.constants, self.universes, slot_views(candidate@.take(arity as int)),
                        letter@, alphabets@[index as int], component, slot@);
                }
                slots[component] = slot;
                component += 1;
            }
            values.push(self.components(&slots[..arity]));
            proof! {
                slots_history = slots_history.push(slot_views(slots@.take(arity as int)));
                assert(fresh <= arity * (index + 2)) by(nonlinear_arith)
                    requires fresh <= arity * (index + 1) + arity;
            }
            index += 1;
        }
        let result = Counterexample {
            candidate: candidate_values,
            history: values,
        };
        proof! {
            assert(constructed(self.constants, self.universes, *constraint, letters@, slot_views(candidate@.take(arity as int)), slots_history));
            assert(result@.history =~= slots_history.map(
                |i: int, row: Seq<history_semantics::verify::refinement::implementation::SlotView>|
                    components_of_slots(self.constants, row)));
            assert(result@ == cex_of_slots(self.constants, slot_views(candidate@.take(arity as int)), slots_history));
            lemma_reconstruction(self.constants, self.universes, *constraint, letters@, alphabets@,
                slot_views(candidate@.take(arity as int)), slots_history);
            assert(reconstructed(self.constants, self.universes, *constraint, letters@, alphabets@, result));
        }
        Ok(result)
    }

    #[verus_verify]
    #[verus_spec(result =>
        requires crate::verify::reconstruction::slot_wf(self.constants,
            crate::verify::reconstruction::slot_views(slots@)),
        ensures result@ == crate::verify::reconstruction::components_of_slots(self.constants,
            crate::verify::reconstruction::slot_views(slots@)))]
    fn components(&self, slots: &[Slot]) -> Components<E> {
        let mut values: Vec<Value<E::Component>> = Vec::with_capacity(slots.len());
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= slots@.len(), values@.len() == index,
                crate::verify::reconstruction::slot_wf(self.constants,
                    crate::verify::reconstruction::slot_views(slots@)),
                forall|i: int| 0 <= i < index ==> values@[i]@ ==
                    crate::verify::reconstruction::components_of_slots(self.constants,
                        crate::verify::reconstruction::slot_views(slots@))[i],
            decreases slots@.len() - index,
        ))]
        while index < slots.len() {
            let value = match slots[index] {
                Slot::Fresh(n) => Value::Fresh(n),
                Slot::Constant(id) => {
                    proof! {
                        let view = crate::verify::reconstruction::slot_views(slots@);
                        assert(view[index as int] == history_semantics::verify::refinement::implementation::SlotView::Code(id as nat));
                        assert(crate::verify::reconstruction::code_field(self.constants,
                            crate::verify::component_at(index), id as nat));
                    }
                    Value::Constant(self.constants.values[id as usize - 1])
                }
            };
            values.push(value);
            index += 1;
        }
        Components { values }
    }
}
