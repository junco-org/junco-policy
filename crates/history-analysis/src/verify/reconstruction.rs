//! Slot and letter coherence shared by search and counterexample reconstruction.

use super::frontend::{constants_wf, universes_wf, value_field};
use super::{
    component_at, component_index, constraint_wf, domain_view, lemma_constraint_sat, ndomains,
    register_entails, register_sat,
};
use crate::analyzer::{Components, Constants, Counterexample, Inclusion, Slot, Value};
use crate::constraint::{Constraint, Letter, Universes};
use history_semantics::verify::refinement::{analyzer, encoding, implementation};
use history_semantics::verify::refinement::{inclusion, search};
use history_syntax::event::specs::arity;
use history_syntax::{Event, syntax::Component};
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::{self as language};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms,
    vstd::set::group_set_lemmas};

pub(crate) open spec fn code_field<E: Event>(constants: Constants<E>, field: Component,
    code: nat) -> bool
{
    0 < code <= constants.values@.len()
        && value_field::<E>(constants.values@[code as int - 1]) == field
}

pub(crate) open spec fn slot_wf<E: Event>(constants: Constants<E>,
    slots: Seq<implementation::SlotView>) -> bool
{
    1 <= slots.len() <= history_syntax::MAX_ARITY && slots.len() == arity::<E>()
        && forall|i: int| #![trigger slots[i]] 0 <= i < slots.len() ==> match slots[i] {
        implementation::SlotView::Code(v) => code_field(constants, component_at(i as usize), v),
        implementation::SlotView::Fresh(_) => true,
    }
}

pub(crate) open spec fn letter_coherent(final_constraint: implementation::ConstraintView,
    letter: implementation::LetterView, atoms: Set<model::Primitive>) -> bool
{
    &&& 1 <= final_constraint.len() <= history_syntax::MAX_ARITY
    &&& letter.classes.len() == final_constraint.len()
    &&& letter.registers.len() == final_constraint.len()
    &&& forall|p: model::Primitive| #[trigger] atoms.contains(p) ==> match p {
        model::Primitive::Eq(c, model::GTerm::Variable(c2)) => c == c2 && c.0 < final_constraint.len(),
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < final_constraint.len(),
    }
    &&& forall|c: Component| #![trigger implementation::letter_register(letter, c)]
        c.0 < final_constraint.len() ==> match implementation::letter_register(letter, c) {
            implementation::ClassView::Constant(v) => implementation::register_of(
                final_constraint, c) == implementation::RegisterView::Equals(v),
            implementation::ClassView::Register =>
                (atoms.contains(model::Primitive::Eq(c, model::GTerm::Variable(c)))
                    || implementation::letter_class(letter, c)
                        == Some(implementation::ClassView::Register)) ==> {
                    &&& forall|v: nat| #[trigger] atoms.contains(
                        model::Primitive::Eq(c, model::GTerm::Constant(v)))
                        ==> register_entails(implementation::register_of(final_constraint, c),
                            implementation::RegisterView::Differs(Set::empty().insert(v)))
                    &&& implementation::letter_class(letter, c)
                        matches Some(implementation::ClassView::Constant(v))
                        ==> register_entails(implementation::register_of(final_constraint, c),
                            implementation::RegisterView::Differs(Set::empty().insert(v)))
                },
        }
    &&& forall|c: Component| c.0 < final_constraint.len() && #[trigger] implementation::letter_class(letter, c)
        == Some(implementation::ClassView::Register)
        ==> implementation::letter_register(letter, c) == implementation::ClassView::Register
}

pub(crate) open spec fn letter_codes_ok<E: Event>(constants: Constants<E>,
    domains: encoding::NDomains, letter: implementation::LetterView,
    atoms: Set<model::Primitive>) -> bool
{
    &&& domains.len() == arity::<E>()
    &&& letter.classes.len() == domains.len() && letter.registers.len() == domains.len()
    &&& forall|c: Component| #![trigger implementation::letter_class(letter, c)]
        c.0 < domains.len() ==> match implementation::letter_class(letter, c) {
            None => encoding::n_domain(domains, c) is None,
            Some(implementation::ClassView::Register) => true,
            Some(implementation::ClassView::Constant(v)) => code_field(constants, c, v)
                && (encoding::n_domain(domains, c) matches Some(values) ==> values.contains(v)),
        }
    &&& forall|c: Component| c.0 < domains.len() ==> (#[trigger] implementation::letter_register(letter, c)
        matches implementation::ClassView::Constant(v) ==> code_field(constants, c, v))
    &&& forall|p: model::Primitive| #[trigger] atoms.contains(p) ==> match p {
        model::Primitive::Eq(c, model::GTerm::Constant(v)) => code_field(constants, c, v),
        model::Primitive::Eq(_, model::GTerm::Variable(_)) => true,
    }
}

impl View for Slot {
    type V = implementation::SlotView;
    open(crate) spec fn view(&self) -> Self::V {
        match self { Slot::Constant(v) => implementation::SlotView::Code(*v as nat),
            Slot::Fresh(n) => implementation::SlotView::Fresh(*n as nat) }
    }
}

impl<T> View for Value<T> {
    type V = analyzer::ValueView<T>;
    open(crate) spec fn view(&self) -> Self::V {
        match self { Value::Constant(v) => analyzer::ValueView::Constant(*v),
            Value::Fresh(n) => analyzer::ValueView::Fresh(*n as nat) }
    }
}

impl<E: Event> View for Components<E> {
    type V = analyzer::ComponentsView<E::Component>;
    open(crate) spec fn view(&self) -> Self::V {
        self.values@.map(|i: int, v: Value<E::Component>| v@)
    }
}

impl<E: Event> View for Counterexample<E> {
    type V = analyzer::CexView<E::Component>;
    open(crate) spec fn view(&self) -> Self::V {
        analyzer::CexView { candidate: self.candidate@,
            history: self.history@.map(|i: int, c: Components<E>| c@) }
    }
}

impl<E: Event> View for Inclusion<E> {
    type V = analyzer::InclusionView<E::Component>;
    open(crate) spec fn view(&self) -> Self::V {
        match self { Inclusion::Holds => analyzer::InclusionView::Holds,
            Inclusion::Exhausted => analyzer::InclusionView::Exhausted,
            Inclusion::Counterexample(c) => analyzer::InclusionView::Counterexample(c@) }
    }
}

pub(crate) open spec fn slot_views(slots: Seq<Slot>) -> Seq<implementation::SlotView> {
    slots.map(|i: int, slot: Slot| slot@)
}

pub(crate) open spec fn components_of_slots<E: Event>(constants: Constants<E>,
    slots: Seq<implementation::SlotView>) -> analyzer::ComponentsView<E::Component>
{
    slots.map(|i: int, slot: implementation::SlotView| match slot {
        implementation::SlotView::Fresh(n) => analyzer::ValueView::Fresh(n),
        implementation::SlotView::Code(v) => analyzer::ValueView::Constant(constants.values@[v as int - 1]),
    })
}

pub(crate) open spec fn cex_of_slots<E: Event>(constants: Constants<E>,
    candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    -> analyzer::CexView<E::Component>
{
    analyzer::CexView { candidate: components_of_slots(constants, candidate),
        history: history.map(|i: int, slots: Seq<implementation::SlotView>|
            components_of_slots(constants, slots)) }
}

pub(crate) open spec fn used_at(candidate: Seq<implementation::SlotView>,
    history: Seq<Seq<implementation::SlotView>>, field: int) -> ISet<nat>
{
    ISet::new(|n: nat| candidate[field] == implementation::SlotView::Fresh(n)
        || exists|i: int| 0 <= i < history.len()
            && #[trigger] history[i][field] == implementation::SlotView::Fresh(n))
}

pub(crate) open spec fn known_codes<E: Event>(constants: Constants<E>) -> Set<nat> {
    Seq::new(constants.values@.len(), |i: int| (i + 1) as nat).to_set()
}

pub(crate) open spec fn register_codes_ok<E: Event>(constants: Constants<E>, field: Component,
    register: implementation::RegisterView) -> bool
{
    match register {
        implementation::RegisterView::Equals(v) => code_field(constants, field, v),
        implementation::RegisterView::Differs(values) => forall|v: nat|
            #[trigger] values.contains(v) ==> code_field(constants, field, v),
    }
}

pub(crate) open spec fn reconstruction_input<E: Event>(constants: Constants<E>,
    universes: Universes, constraint: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>) -> bool
{
    &&& constants_wf(constants) && universes_wf(constants, universes)
    &&& constraint_wf(constraint)
    &&& constraint.0@.len() == universes@.len()
    &&& inclusion::satisfiable(ndomains(universes), implementation::constraint_of(constraint@))
    &&& alphabets.len() == letters.len()
    &&& forall|c: Component| c.0 < constraint.0@.len() ==> register_codes_ok(constants, c,
        implementation::register_of(constraint@, c))
    &&& forall|i: int| #![trigger letters[i]] 0 <= i < letters.len()
        ==> letter_coherent(constraint@, letters[i]@, alphabets[i])
            && letter_codes_ok(constants, ndomains(universes), letters[i]@, alphabets[i])
}

pub(crate) open spec fn slot_register(slot: implementation::SlotView,
    register: implementation::RegisterView, known: Set<nat>) -> bool
{
    match (slot, register) {
        (implementation::SlotView::Code(v), implementation::RegisterView::Equals(w)) => v == w,
        (implementation::SlotView::Code(v), implementation::RegisterView::Differs(values)) => !values.contains(v),
        (implementation::SlotView::Fresh(_), implementation::RegisterView::Equals(_)) => false,
        (implementation::SlotView::Fresh(_), implementation::RegisterView::Differs(values)) => values.subset_of(known),
    }
}

pub(crate) open spec fn slot_domain(slot: implementation::SlotView,
    domain: Option<Set<nat>>) -> bool
{
    match slot {
        implementation::SlotView::Code(v) => match domain { None => true, Some(values) => values.contains(v) },
        implementation::SlotView::Fresh(_) => domain is None,
    }
}

pub(crate) open spec fn candidate_field_ok<E: Event>(constants: Constants<E>,
    universes: Universes, constraint: Constraint, field: int, slot: implementation::SlotView) -> bool
{
    &&& 0 <= field < arity::<E>() && universes@.len() == arity::<E>() && constraint.0@.len() == arity::<E>()
    &&& slot_register(slot, constraint.0[field]@, known_codes(constants))
    &&& slot_domain(slot, domain_view(universes[field]))
    &&& match slot {
        implementation::SlotView::Code(v) => code_field(constants, component_at(field as usize), v),
        implementation::SlotView::Fresh(n) => n < arity::<E>(),
    }
}

pub(crate) open spec fn history_field_matches(candidate: Seq<implementation::SlotView>,
    letter: implementation::LetterView, field: int, slot: implementation::SlotView) -> bool
{
    0 <= field < candidate.len() && letter.classes.len() == candidate.len()
        && match implementation::letter_class(letter, component_at(field as usize)) {
        Some(implementation::ClassView::Constant(v)) => slot == implementation::SlotView::Code(v),
        Some(implementation::ClassView::Register) => slot == candidate[field],
        None => slot matches implementation::SlotView::Fresh(n)
            && (candidate[field] matches implementation::SlotView::Fresh(m) ==> n != m),
    }
}

pub(crate) open spec fn constructed<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, letters: Seq<Letter>, candidate: Seq<implementation::SlotView>,
    history: Seq<Seq<implementation::SlotView>>) -> bool
{
    &&& slot_wf(constants, candidate)
    &&& forall|k: int| 0 <= k < candidate.len() ==> candidate_field_ok(constants, universes, constraint, k, candidate[k])
    &&& history.len() == letters.len()
    &&& forall|i: int| 0 <= i < history.len() ==> slot_wf(constants, history[i])
        && forall|k: int| 0 <= k < candidate.len() ==> history_field_matches(candidate, letters[i]@, k, history[i][k])
            && slot_domain(history[i][k], domain_view(universes[k]))
}

pub(crate) open spec fn reconstructed<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>,
    result: Counterexample<E>) -> bool
{
    exists|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        constructed(constants, universes, constraint, letters, candidate, history)
        && result@ == cex_of_slots(constants, candidate, history)
        && implementation::reconstruction_ok(ndomains(universes),
            implementation::constraint_of(constraint@),
            super::search_exec::chain_assignments(letters, alphabets), candidate, history,
            known_codes(constants))
}

pub(crate) proof fn lemma_known_codes<E: Event>(constants: Constants<E>)
    ensures forall|v: nat| #[trigger] known_codes(constants).contains(v)
        == (0 < v <= constants.values@.len()),
{
    let seq = Seq::new(constants.values@.len(), |i: int| (i + 1) as nat);
    assert forall|v: nat| #[trigger] known_codes(constants).contains(v)
        == (0 < v <= constants.values@.len()) by {
        if seq.contains(v) {
            let i = choose|i: int| 0 <= i < seq.len() && seq[i] == v;
        } else if 0 < v <= constants.values@.len() {
            assert(seq[v as int - 1] == v);
        }
    }
}

pub(crate) proof fn lemma_slot_register(slot: implementation::SlotView,
    register: implementation::RegisterView, known: Set<nat>, fresh: spec_fn(nat) -> nat)
    requires slot_register(slot, register, known), implementation::fresh_codes_ok(fresh, known),
    ensures register_sat(register, implementation::slot_value(slot, fresh)),
{
    match (slot, register) {
        (implementation::SlotView::Fresh(n), implementation::RegisterView::Differs(values)) => {
            if values.contains(fresh(n)) { assert(known.contains(fresh(n))); }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_slots_field(slots: Seq<implementation::SlotView>,
    field: Component, fresh: spec_fn(nat) -> nat)
    requires field.0 < slots.len(),
    ensures language::field_value(implementation::slots_event(slots, fresh), field)
        == implementation::slot_value(slots[component_index(field) as int], fresh),
{}

pub(crate) proof fn lemma_candidate_slots<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, candidate: Seq<implementation::SlotView>, fresh: spec_fn(nat) -> nat)
    requires candidate.len() == arity::<E>(), 1 <= arity::<E>() <= history_syntax::MAX_ARITY,
        universes@.len() == candidate.len(), constraint.0@.len() == candidate.len(),
        forall|k: int| 0 <= k < candidate.len() ==> candidate_field_ok(constants, universes, constraint, k, candidate[k]),
        implementation::fresh_codes_ok(fresh, known_codes(constants)),
    ensures inclusion::sat_by(implementation::slots_event(candidate, fresh), implementation::constraint_of(constraint@)),
        encoding::n_event_in(ndomains(universes), implementation::slots_event(candidate, fresh)),
{
    let theta = implementation::slots_event(candidate, fresh);
    assert forall|k: int| 0 <= k < candidate.len() implies register_sat(constraint@[k], theta[k]) by {
        lemma_slot_register(candidate[k], constraint.0[k]@, known_codes(constants), fresh);
    }
    lemma_constraint_sat(constraint@, theta);
    assert forall|k: int| #![trigger ndomains(universes)[k]] 0 <= k < universes@.len() implies
        (ndomains(universes)[k] matches Some(values) ==> values.contains(theta[k])) by {
        match candidate[k] {
            implementation::SlotView::Code(_) => {},
            implementation::SlotView::Fresh(_) => {},
        }
    }
}

pub(crate) proof fn lemma_excludes(register: implementation::RegisterView, value: nat, code: nat)
    requires register_sat(register, value),
        register_entails(register, implementation::RegisterView::Differs(Set::empty().insert(code))),
    ensures value != code,
{
    match register { implementation::RegisterView::Equals(_) => {},
        implementation::RegisterView::Differs(_) => {} }
}

pub(crate) proof fn lemma_letter_slots<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, letter: implementation::LetterView, atoms: Set<model::Primitive>,
    candidate: Seq<implementation::SlotView>, row: Seq<implementation::SlotView>,
    fresh: spec_fn(nat) -> nat)
    requires candidate.len() == arity::<E>(), row.len() == candidate.len(),
        universes@.len() == candidate.len(), constraint.0@.len() == candidate.len(),
        forall|k: int| 0 <= k < candidate.len() ==> candidate_field_ok(constants, universes, constraint, k, candidate[k])
            && history_field_matches(candidate, letter, k, row[k]),
        letter_coherent(constraint@, letter, atoms),
        letter_codes_ok(constants, ndomains(universes), letter, atoms),
        implementation::fresh_codes_ok(fresh, known_codes(constants)),
    ensures search::realizes(implementation::slots_event(candidate, fresh),
        implementation::slots_event(row, fresh), implementation::letter_assignment(letter, atoms)),
        encoding::n_event_in(ndomains(universes), implementation::slots_event(row, fresh)),
{
    lemma_known_codes(constants);
    lemma_candidate_slots(constants, universes, constraint, candidate, fresh);
    let theta = implementation::slots_event(candidate, fresh);
    let event = implementation::slots_event(row, fresh);
    lemma_constraint_sat(constraint@, theta);
    assert forall|p: model::Primitive| #[trigger] atoms.contains(p)
        implies implementation::letter_holds(letter, p) == model::primitive_holds(theta, p, event) by {
        let c = match p { model::Primitive::Eq(c, _) => c };
        let k = component_index(c) as int;
        let r = implementation::register_of(constraint@, c);
        lemma_slots_field(candidate, c, fresh);
        lemma_slots_field(row, c, fresh);
        assert(register_sat(r, language::field_value(theta, c)));
        match p {
            model::Primitive::Eq(_, model::GTerm::Constant(v)) => {
                assert(known_codes(constants).contains(v));
                match implementation::letter_class(letter, c) {
                    Some(implementation::ClassView::Constant(w)) => {},
                    Some(implementation::ClassView::Register) => {
                        lemma_excludes(r, language::field_value(theta, c), v);
                    },
                    None => { let n = row[k]->Fresh_0; assert(!known_codes(constants).contains(fresh(n))); },
                }
            },
            model::Primitive::Eq(_, model::GTerm::Variable(c2)) => {
                assert(c2 == c);
                match implementation::letter_class(letter, c) {
                    Some(implementation::ClassView::Register) => {},
                    Some(implementation::ClassView::Constant(v)) => {
                        match implementation::letter_register(letter, c) {
                            implementation::ClassView::Constant(w) => {},
                            implementation::ClassView::Register => {
                                lemma_excludes(r, language::field_value(theta, c), v);
                            },
                        }
                    },
                    None => {
                        let n = row[k]->Fresh_0;
                        match candidate[k] {
                            implementation::SlotView::Code(v) => { assert(known_codes(constants).contains(v)); },
                            implementation::SlotView::Fresh(m) => { assert(m != n); assert(fresh(m) != fresh(n)); },
                        }
                    },
                }
            },
        }
    }
    assert forall|k: int| #![trigger ndomains(universes)[k]] 0 <= k < universes@.len() implies
        (ndomains(universes)[k] matches Some(values) ==> values.contains(event[k])) by {
        let c = component_at(k as usize);
        lemma_slots_field(row, c, fresh);
        assert(encoding::n_domain(ndomains(universes), c) == ndomains(universes)[k]);
        match implementation::letter_class(letter, c) {
            None => {},
            Some(implementation::ClassView::Constant(v)) => {},
            Some(implementation::ClassView::Register) => { lemma_slots_field(candidate, c, fresh); },
        }
    }
}

pub(crate) proof fn lemma_reconstruction<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>,
    candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    requires reconstruction_input(constants, universes, constraint, letters, alphabets),
        constructed(constants, universes, constraint, letters, candidate, history),
    ensures implementation::reconstruction_ok(ndomains(universes),
        implementation::constraint_of(constraint@), super::search_exec::chain_assignments(letters, alphabets),
        candidate, history, known_codes(constants)),
{
    assert forall|fresh: spec_fn(nat) -> nat| #[trigger] implementation::fresh_codes_ok(fresh, known_codes(constants))
        implies {
            let theta = implementation::slots_event(candidate, fresh);
            let u = history.map(|i: int, row: Seq<implementation::SlotView>| implementation::slots_event(row, fresh));
            encoding::n_theta_ok(ndomains(universes), theta) ==> inclusion::sat_by(theta,
                implementation::constraint_of(constraint@))
                && search::follows(ndomains(universes), super::search_exec::chain_assignments(letters, alphabets), theta, u)
        } by {
        lemma_candidate_slots(constants, universes, constraint, candidate, fresh);
        assert forall|i: int| 0 <= i < history.len() implies
            search::realizes(implementation::slots_event(candidate, fresh), implementation::slots_event(history[i], fresh),
                implementation::letter_assignment(letters[i]@, alphabets[i]))
                && encoding::n_event_in(ndomains(universes), implementation::slots_event(history[i], fresh)) by {
            lemma_letter_slots(constants, universes, constraint, letters[i]@, alphabets[i], candidate, history[i], fresh);
        }
    }
}

pub(crate) proof fn lemma_used_at<E: Event>(constants: Constants<E>,
    candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    requires slot_wf(constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> slot_wf(constants, history[i]),
    ensures forall|k: int| 0 <= k < candidate.len() ==> used_at(candidate, history, k)
        == analyzer::fresh_used(cex_of_slots(constants, candidate, history), k),
{
    let cex = cex_of_slots(constants, candidate, history);
    assert forall|k: int| 0 <= k < candidate.len() implies used_at(candidate, history, k)
        == analyzer::fresh_used(cex, k) by {
        assert forall|n: nat| used_at(candidate, history, k).contains(n)
            == analyzer::fresh_used(cex, k).contains(n) by {
            assert((cex.candidate[k] == analyzer::ValueView::Fresh(n))
                == (candidate[k] == implementation::SlotView::Fresh(n)));
            assert forall|i: int| 0 <= i < history.len() implies
                (cex.history[i][k] == analyzer::ValueView::Fresh(n))
                    == (history[i][k] == implementation::SlotView::Fresh(n)) by {
                assert(cex.history[i] == components_of_slots(constants, history[i]));
            }
        }
        assert(used_at(candidate, history, k) =~= analyzer::fresh_used(cex, k));
    }
}

pub(crate) proof fn lemma_code_payload<E: Event>(constants: Constants<E>, field: Component, code: nat)
    requires constants_wf(constants), code_field(constants, field, code),
    ensures code <= u32::MAX,
        super::constant_book(constants)[junco_core::flat::verify::field_index(field)].contains(
            (constants.values@[code as int - 1], code as u64)),
        known_codes(constants).contains(code),
{
    lemma_known_codes(constants);
    super::frontend::lemma_field_book(constants, field);
    let entries = super::frontend::entries::<E>(constants.values@);
    let predicate = |entry: (E::Component, u64)| value_field::<E>(entry.0) == field;
    entries.lemma_filter_contains(predicate, code as int - 1);
    assert(entries[code as int - 1] == (constants.values@[code as int - 1], code as u64));
}

pub(crate) proof fn lemma_register_known<E: Event>(constants: Constants<E>, field: Component,
    register: implementation::RegisterView)
    requires register_codes_ok(constants, field, register),
    ensures match register {
        implementation::RegisterView::Equals(v) => known_codes(constants).contains(v),
        implementation::RegisterView::Differs(values) => values.subset_of(known_codes(constants)),
    },
{
    lemma_known_codes(constants);
    match register {
        implementation::RegisterView::Equals(v) => {},
        implementation::RegisterView::Differs(values) => {
            assert forall|v: nat| #[trigger] values.contains(v)
                implies known_codes(constants).contains(v) by {};
        },
    }
}

pub(crate) proof fn lemma_field_views(constraint: Constraint, universes: Universes, field: usize)
    requires field < constraint.0@.len(), field < universes@.len(), field < history_syntax::MAX_ARITY,
    ensures implementation::register_of(constraint@, component_at(field)) == constraint.0[field as int]@,
        encoding::n_domain(ndomains(universes), component_at(field)) == domain_view(universes[field as int]),
        component_index(component_at(field)) == field,
{}

pub(crate) proof fn lemma_input_field<E: Event>(constants: Constants<E>, universes: Universes,
    constraint: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, field: usize)
    requires reconstruction_input(constants, universes, constraint, letters, alphabets), field < arity::<E>(),
    ensures register_codes_ok(constants, component_at(field), constraint.0[field as int]@),
        super::register_possible(constraint.0[field as int], universes[field as int]),
        encoding::n_domain(ndomains(universes), component_at(field)) == domain_view(universes[field as int]),
{
    lemma_field_views(constraint, universes, field);
    super::lemma_constraint_possible(constraint, universes);
    assert(register_codes_ok(constants, component_at(field),
        implementation::register_of(constraint@, component_at(field))));
}

pub(crate) proof fn lemma_history_field<E: Event>(constants: Constants<E>, universes: Universes,
    candidate: Seq<implementation::SlotView>, letter: implementation::LetterView,
    atoms: Set<model::Primitive>, field: usize, slot: implementation::SlotView)
    requires field < arity::<E>(), slot_wf(constants, candidate), universes@.len() == arity::<E>(),
        slot_domain(candidate[field as int], domain_view(universes[field as int])),
        letter_codes_ok(constants, ndomains(universes), letter, atoms),
        history_field_matches(candidate, letter, field as int, slot),
    ensures slot_domain(slot, domain_view(universes[field as int])),
        slot matches implementation::SlotView::Code(v) ==> code_field(constants, component_at(field), v),
{
    assert(encoding::n_domain(ndomains(universes), component_at(field))
        == domain_view(universes[field as int]));
    match implementation::letter_class(letter, component_at(field)) {
        None => {}, Some(implementation::ClassView::Constant(v)) => {},
        Some(implementation::ClassView::Register) => {},
    }
}
}
