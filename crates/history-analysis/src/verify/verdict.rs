//! Numeric decision certificates, reconstruction provenance, and the tail-inclusion client.

use super::frontend::*;
use super::reconstruction::code_field;
use super::search_exec::{self as exec, root_vocabulary};
use super::*;
use super::{reconstruction as slots, typed_numeric as typed};
use crate::analyzer::{Constants, PolicyAnalyzer};
use crate::analyzer::{Counterexample, Inclusion, NumericDecision};
use crate::spec::analyzer;
use history_semantics::{
    SymbolicLanguage, compile_verify as numeric, symbolic_language_verify as facade,
    symbolic_verify as symbolic,
};
use history_syntax::Rule;
use history_syntax::spec::events::{arity, event_view};
use junco_core::flat::FlatRule;
use junco_core::flat::{FlatHead, FlatPair, FlatTerm, FlatTest};
use junco_core::spec::{questions, semantics as tdsl};
use junco_core::verify::{encoding as enc, flatten as fl};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas,
    crate::verify::frontend::domain_view::lemma_analyzer_view,
    crate::verify::frontend::domain_view::lemma_rule_id_view};

pub(crate) open spec fn test_fields_bounded<C>(test: FlatTest<C>, arity: nat) -> bool {
    match test {
        FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } =>
            field.0 < arity && variable.0 < arity,
        FlatTest::Atom { field, .. } => field.0 < arity,
        _ => true,
    }
}

/// Numeric table heads may be all `Any`; only field bounds, not binder declarations, are needed.
pub(crate) open spec fn source_fields_bounded<C>(source: FlatPair<C>) -> bool {
    1 <= source.head@.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < source.tests@.len() ==>
            test_fields_bounded(#[trigger] source.tests@[i], source.head@.len())
}

pub(crate) proof fn lemma_source_fields_bounded(source: FlatPair<u64>)
    requires source_fields_bounded(source),
    ensures search::atoms_bounded(numeric::source_primitives(source), source.head@.len()),
{
    assert forall|p: model::Primitive| numeric::source_primitives(source).contains(p) implies match p {
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < source.head@.len(),
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < source.head@.len() && v.0 < source.head@.len(),
    } by {
        numeric::lemma_source_primitive_prefix(source, source.tests@.len(), p);
        let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len() && match source.tests@[i] {
            FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, numeric::term_view(term)),
            _ => false,
        };
        assert(test_fields_bounded(source.tests@[i], source.head@.len()));
        match source.tests@[i] {
            FlatTest::Atom { term: FlatTerm::Constant(_), .. } => {},
            FlatTest::Atom { term: FlatTerm::Variable(_), .. } => {},
            _ => {},
        }
    }
}

pub(crate) open spec fn source_codes_wf<E: Event>(c: Constants<E>, source: FlatPair<u64>) -> bool {
    &&& source.head@.len() == arity::<E>()
    &&& source_fields_bounded(source)
    &&& forall|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
        ==> match source.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
            _ => true,
        }
}

pub(crate) open spec fn head_codes_wf<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>) -> bool {
    head.len() == arity::<E>() && forall|i: int| #![trigger head[i]] 0 <= i < head.len() ==> match head[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat),
        _ => true,
    }
}

pub(crate) open spec fn constraint_codes_wf<E: Event>(c: Constants<E>, g: implementation::ConstraintView) -> bool {
    g.len() == arity::<E>() && forall|field: Component, v: nat| field.0 < g.len()
        && #[trigger] register_codes(implementation::register_of(g, field)).contains(v)
            ==> code_field(c, field, v)
}

pub(crate) open spec fn constraint_codes_known<E: Event>(c: Constants<E>, g: implementation::ConstraintView,
    known: Seq<Set<E::Component>>) -> bool {
    known.len() == arity::<E>() && forall|k: int, v: nat| 0 <= k < g.len()
        && register_codes(g[k]).contains(v)
        ==> typed::known_value::<E>(known, k, c.values@[v as int - 1])
}

pub(crate) proof fn lemma_encoded_payload<E: Event>(c: Constants<E>, field: Component,
    value: E::Component, id: u64)
    requires constants_wf(c), enc::encoded(constant_book(c), fl::component_equality::<E>(), field, value, id),
    ensures code_field(c, field, id as nat),
{
    lemma_field_book(c, field);
    let f = junco_core::flat::verify::field_index(field);
    let i = choose|i: int| 0 <= i < constant_book(c)[f].len()
        && constant_book(c)[f][i].1 == id
        && fl::component_equality::<E>()(field, value, constant_book(c)[f][i].0);
    lemma_field_entry_source::<E>(c.values@, field, i);
    let j = choose|j: int| 0 <= j < c.values@.len()
        && field_entries::<E>(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
    assert(id as nat == j + 1);
    assert(value_field::<E>(c.values@[j]) == field);
}

/// Interning may choose an equal representative; it does not change the query's known class.
pub(crate) proof fn lemma_encoded_known<E: Event>(c: Constants<E>, field: Component,
    value: E::Component, id: u64, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        enc::encoded(constant_book(c), fl::component_equality::<E>(), field, value, id),
        typed::known_value::<E>(known, field.0 as int, value),
    ensures code_field(c, field, id as nat),
        typed::known_value::<E>(known, field.0 as int, c.values@[id as int - 1]),
{
    lemma_encoded_payload(c, field, value, id);
    lemma_field_book(c, field);
    let k = field.0 as int;
    let i = choose|i: int| 0 <= i < constant_book(c)[k].len()
        && constant_book(c)[k][i].1 == id && fl::component_equality::<E>()(field, value, constant_book(c)[k][i].0);
    lemma_field_entry_source::<E>(c.values@, field, i);
    let j = choose|j: int| 0 <= j < c.values@.len()
        && field_entries::<E>(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
    assert(j == id as int - 1);
    let constant = choose|constant: E::Component| known[k].contains(constant) && value.eq_spec(&constant);
    questions::lemma_native_eq_symmetric(value, c.values@[j]);
    questions::lemma_native_eq_transitive(c.values@[j], value, constant);
    assert(typed::known_value::<E>(known, k, c.values@[j]));
}

pub(crate) open spec fn head_codes_known<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>,
    known: Seq<Set<E::Component>>) -> bool {
    known.len() == arity::<E>() && head.len() == arity::<E>()
        && forall|k: int, code: u64| 0 <= k < head.len() && head[k] == FlatHead::Constant(code)
            ==> typed::known_value::<E>(known, k, c.values@[code as int - 1])
}

/// Every numeric head pin represents an actual source-head literal.
pub(crate) proof fn lemma_lowered_head_known<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, target: FlatPair<u64>, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        fl::flattened(rule, flat), enc::lowering(flat.source, target, constant_book(c), fl::component_equality::<E>()),
        known.len() == arity::<E>(),
        forall|k: int| 0 <= k < arity::<E>() ==> questions::rule_constants(rule@)[k].subset_of(known[k]),
    ensures head_codes_known(c, target.head@, known),
{
    fl::lemma_flattened_constants(rule, flat);
    assert forall|k: int, code: u64| 0 <= k < target.head@.len() && target.head@[k] == FlatHead::Constant(code)
        implies typed::known_value::<E>(known, k, c.values@[code as int - 1]) by {
        assert(enc::topology(flat.source, target));
        assert(k < flat.source.head@.len());
        assert(enc::head_shape(flat.source.head@[k], target.head@[k]));
        assert(flat.source.head@[k] is Constant);
        assert(enc::head_encoded(flat.source.head@[k], target.head@[k], enc::field_at(k),
            constant_book(c), fl::component_equality::<E>()));
        assert(enc::head_encoded(flat.source.head@[k], target.head@[k], Component(k as u8),
            constant_book(c), fl::component_equality::<E>()));
        assert(flat.source.head@[k] is Constant);
        let value = match flat.source.head@[k] { FlatHead::Constant(value) => value, _ => arbitrary() };
        assert(known[k].contains(value));
        questions::lemma_native_eq_reflexive(value);
        assert(typed::known_value::<E>(known, k, value));
        lemma_encoded_known(c, Component(k as u8), value, code, known);
    }
}

/// Declared numeric universe members are equal to members of the retained caller domain.
pub(crate) proof fn lemma_universes_known<E: Event>(a: PolicyAnalyzer<E>, known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        known.len() == arity::<E>(),
        forall|k: int| #![trigger a@.domains[k]] 0 <= k < arity::<E>() ==> (a@.domains[k] matches Some(values) ==> values.subset_of(known[k])),
    ensures forall|k: int, code: nat| 0 <= k < arity::<E>()
        && (domain_view(a.universes[k]) matches Some(values) && values.contains(code))
        ==> #[trigger] typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
{
    lemma_analyzer_semantic_wf(a);
    assert forall|k: int, code: nat| #![trigger typed::known_value::<E>(known, k, a.constants.values@[code as int - 1])]
        0 <= k < arity::<E>()
        && (domain_view(a.universes[k]) matches Some(values) && values.contains(code))
        implies typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
        lemma_declared_coordinate(a, k);
        let ids = a.universes[k]->Some_0;
        lemma_codes((*ids)@);
        let j = choose|j: int| 0 <= j < (*ids)@.len() && (*ids)@[j] as nat == code;
        let value = a.constants.values@[code as int - 1];
        questions::lemma_native_eq_reflexive(value);
        assert(selected_values(a.constants, a.universes[k])->Some_0.contains(value));
        assert(domain_member(selected_values(a.constants, a.universes[k]), value));
        assert(domain_member(a@.domains[k], value));
        assert(exists|constant: E::Component| a@.domains[k]->Some_0.contains(constant) && value.eq_spec(&constant));
        let constant = choose|constant: E::Component| a@.domains[k]->Some_0.contains(constant) && value.eq_spec(&constant);
        assert(known[k].contains(constant));
    }
}

pub(crate) open spec fn primitives_known<E: Event>(c: Constants<E>, known: Seq<Set<E::Component>>,
    atoms: Set<model::Primitive>) -> bool {
    known.len() == arity::<E>() && forall|field: Component, code: nat|
        #[trigger] atoms.contains(model::Primitive::Eq(field, model::GTerm::Constant(code)))
        ==> code_field(c, field, code) && typed::known_value::<E>(known, field.0 as int, c.values@[code as int - 1])
}

pub(crate) proof fn lemma_primitives_known_subset<E: Event>(c: Constants<E>, known: Seq<Set<E::Component>>,
    before: Set<model::Primitive>, after: Set<model::Primitive>)
    requires primitives_known(c, known, before), after.subset_of(before),
    ensures primitives_known(c, known, after),
{}

pub(crate) proof fn lemma_reachable_known_frame<E: Event>(c: Constants<E>, before: FlatPair<u64>,
    after: FlatPair<u64>, root: nat, known: Seq<Set<E::Component>>)
    requires table::dag(before), table::frame(before, after), root < before.regexes@.len(),
        primitives_known(c, known, numeric::reachable_regex_primitives(before, root)),
    ensures primitives_known(c, known, numeric::reachable_regex_primitives(after, root)),
{
    super::policy_source::lemma_regex_primitives_frame(before, after, root);
    lemma_primitives_known_subset(c, known, numeric::reachable_regex_primitives(before, root),
        numeric::reachable_regex_primitives(after, root));
}

/// Source containment and actual lowering justify the support of the compiled numeric root.
pub(crate) proof fn lemma_rule_primitives_known<E: Event>(c: Constants<E>, rule: Rule<E>,
    flat: FlatRule<E::Component>, target: FlatPair<u64>, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        fl::flattened(rule, flat), enc::lowering(flat.source, target, constant_book(c), fl::component_equality::<E>()),
        known.len() == arity::<E>(),
        forall|k: int| 0 <= k < arity::<E>() ==> questions::rule_constants(rule@)[k].subset_of(known[k]),
    ensures primitives_known(c, known, numeric::reachable_regex_primitives(target, target.root as nat)),
{
    fl::lemma_regex_constants_bounded::<E>(flat.source.tests@, flat.source.regexes@, flat.source.root as nat,
        rule.tail@, rule.head@, known);
    lemma_reachable_regex_known(c, flat.source, target, flat.source.root as nat, known);
}

pub(crate) proof fn lemma_union_primitives_known<E: Event>(c: Constants<E>, pair: FlatPair<u64>,
    root: nat, children: Seq<u32>, known: Seq<Set<E::Component>>)
    requires root < pair.regexes@.len(), known.len() == arity::<E>(),
        match pair.regexes@[root as int] { junco_core::flat::FlatRegex::Union(ids) => ids@ == children, _ => false },
        forall|i: int| 0 <= i < children.len() ==> children[i] < root
            && primitives_known(c, known, numeric::reachable_regex_primitives(pair, children[i] as nat)),
    ensures primitives_known(c, known, numeric::reachable_regex_primitives(pair, root)),
{
    reveal_with_fuel(numeric::reachable_regex_primitives, 1);
    assert forall|field: Component, code: nat|
        numeric::reachable_regex_primitives(pair, root).contains(model::Primitive::Eq(field, model::GTerm::Constant(code)))
        implies code_field(c, field, code) && typed::known_value::<E>(known, field.0 as int, c.values@[code as int - 1]) by {
        let p = model::Primitive::Eq(field, model::GTerm::Constant(code));
        numeric::lemma_reachable_regex_prefix_member(pair, root, children.len(), children, p);
        let i = choose|i: int| 0 <= i < children.len() && children[i] < root
            && numeric::reachable_regex_primitives(pair, children[i] as nat).contains(p);
    }
}

proof fn lemma_reachable_test_prefix_known<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>, id: nat, n: nat, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        id < source.tests@.len(), known.len() == arity::<E>(),
        fl::test_constants_bounded(source.tests@, id, known),
    ensures primitives_known(c, known, numeric::reachable_test_prefix(target, id, n)),
    decreases id, 0nat, n,
{
    reveal_with_fuel(numeric::reachable_test_prefix, 1);
    reveal_with_fuel(fl::test_constants_bounded, 2);
    match target.tests@[id as int] {
        FlatTest::And(children) | FlatTest::Or(children) => {
            if 0 < n <= children@.len() {
                lemma_reachable_test_prefix_known(c, source, target, id, (n - 1) as nat, known);
                let child = children@[n - 1] as nat;
                assert(enc::test_encoded(source.tests@[id as int], target.tests@[id as int],
                    constant_book(c), fl::component_equality::<E>()));
                match source.tests@[id as int] {
                    FlatTest::And(ids) | FlatTest::Or(ids) => assert(ids@ == children@),
                    _ => {},
                }
                assert(fl::test_constants_bounded(source.tests@, child, known));
                if child < id { lemma_reachable_test_known(c, source, target, child, known); }
            }
        },
        _ => {},
    }
}

/// Only reachable source literals, not unrelated flat-table entries, justify a numeric atom.
pub(crate) proof fn lemma_reachable_test_known<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>, id: nat, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        id < source.tests@.len(), known.len() == arity::<E>(),
        fl::test_constants_bounded(source.tests@, id, known),
    ensures primitives_known(c, known, numeric::reachable_test_primitives(target, id)),
    decreases id, 1nat, 0nat,
{
    reveal_with_fuel(numeric::reachable_test_primitives, 1);
    reveal_with_fuel(fl::test_constants_bounded, 1);
    match (source.tests@[id as int], target.tests@[id as int]) {
        (FlatTest::Atom { field, term: FlatTerm::Constant(value), .. },
            FlatTest::Atom { term: FlatTerm::Constant(code), .. }) => {
            questions::lemma_native_eq_reflexive(value);
            assert(typed::known_value::<E>(known, field.0 as int, value));
            lemma_encoded_known(c, field, value, code, known);
        },
        (_, FlatTest::And(children)) | (_, FlatTest::Or(children)) => {
            lemma_reachable_test_prefix_known(c, source, target, id, children@.len(), known);
        },
        _ => {},
    }
}

proof fn lemma_reachable_regex_prefix_known<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>, id: nat, n: nat, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        id < source.regexes@.len(), known.len() == arity::<E>(),
        fl::regex_constants_bounded(source.tests@, source.regexes@, id, known),
    ensures primitives_known(c, known, numeric::reachable_regex_prefix(target, id, n)),
    decreases id, 0nat, n,
{
    reveal_with_fuel(numeric::reachable_regex_prefix, 1);
    reveal_with_fuel(fl::regex_constants_bounded, 2);
    match target.regexes@[id as int] {
        junco_core::flat::FlatRegex::Union(children) | junco_core::flat::FlatRegex::Concat(children)
            | junco_core::flat::FlatRegex::Intersect(children) => {
            if 0 < n <= children@.len() {
                lemma_reachable_regex_prefix_known(c, source, target, id, (n - 1) as nat, known);
                let child = children@[n - 1] as nat;
                assert(enc::regex_same(source.regexes@[id as int], target.regexes@[id as int]));
                match source.regexes@[id as int] {
                    junco_core::flat::FlatRegex::Union(ids)
                    | junco_core::flat::FlatRegex::Concat(ids)
                    | junco_core::flat::FlatRegex::Intersect(ids) => assert(ids@ == children@),
                    _ => {},
                }
                assert(fl::regex_constants_bounded(source.tests@, source.regexes@, child, known));
                if child < id { lemma_reachable_regex_known(c, source, target, child, known); }
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_reachable_regex_known<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>, id: nat, known: Seq<Set<E::Component>>)
    requires constants_wf(c), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        id < source.regexes@.len(), known.len() == arity::<E>(),
        fl::regex_constants_bounded(source.tests@, source.regexes@, id, known),
    ensures primitives_known(c, known, numeric::reachable_regex_primitives(target, id)),
    decreases id, 1nat, 0nat,
{
    reveal_with_fuel(numeric::reachable_regex_primitives, 1);
    reveal_with_fuel(fl::regex_constants_bounded, 1);
    match target.regexes@[id as int] {
        junco_core::flat::FlatRegex::Test(test) => lemma_reachable_test_known(c, source, target, test as nat, known),
        junco_core::flat::FlatRegex::Union(children) | junco_core::flat::FlatRegex::Concat(children)
            | junco_core::flat::FlatRegex::Intersect(children) =>
                lemma_reachable_regex_prefix_known(c, source, target, id, children@.len(), known),
        junco_core::flat::FlatRegex::Star(child) | junco_core::flat::FlatRegex::Complement(child) => {
            if child < id { lemma_reachable_regex_known(c, source, target, child as nat, known); }
        },
        _ => {},
    }
}

/// The actual search vocabulary adds only current root atoms, case pins, and declared values.
pub(crate) proof fn lemma_root_vocabulary_known<E: Event>(a: PolicyAnalyzer<E>, l: SymbolicLanguage,
    g: implementation::ConstraintView, known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), g.len() == arity::<E>(),
        primitives_known(a.constants, known, symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))),
        constraint_codes_known(a.constants, g, known),
        forall|k: int, code: nat| 0 <= k < arity::<E>()
            && (domain_view(a.universes[k]) matches Some(values) && values.contains(code))
            ==> #[trigger] typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
    ensures forall|k: int, code: nat| 0 <= k < arity::<E>() && root_vocabulary(l, a.universes, g)[k].contains(code)
        ==> typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
{
    let atoms = symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)));
    assert forall|k: int, code: nat| 0 <= k < arity::<E>() && root_vocabulary(l, a.universes, g)[k].contains(code)
        implies typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
        let field = component_at(k as usize);
        facade::lemma_primitive_codes_contains(atoms, field, code);
        if facade::primitive_codes(atoms, field).contains(code) {
            assert(atoms.contains(model::Primitive::Eq(field, model::GTerm::Constant(code))));
            assert(primitives_known(a.constants, known, atoms));
            assert(field.0 as int == k);
            assert(code_field(a.constants, field, code));
            assert(typed::known_value::<E>(known, field.0 as int, a.constants.values@[code as int - 1]));
            assert(typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]));
        } else if register_codes(g[k]).contains(code) {
            assert(constraint_codes_known(a.constants, g, known));
            assert(typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]));
        } else {
            assert(exec::domain_values(a.universes[k]).contains(code));
            assert(domain_view(a.universes[k]) matches Some(values) && values.contains(code));
        }
    }
}

pub(crate) proof fn lemma_lowered_payload<E: Event>(c: Constants<E>, source: FlatPair<E::Component>,
    target: FlatPair<u64>)
    requires constants_wf(c), enc::lowering(source, target, constant_book(c), fl::component_equality::<E>()),
        source.head@.len() == arity::<E>(), junco_core::flat::verify::structural_wf(source),
    ensures source_codes_wf(c, target), head_codes_wf(c, target.head@), source_fields_bounded(target),
{
    assert forall|i: int| #![trigger target.tests@[i]] 0 <= i < target.tests@.len()
        implies match target.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
            FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
            _ => true,
        } by {
        if let FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } = target.tests@[i] {
            let value = match source.tests@[i] {
                FlatTest::Atom { term: FlatTerm::Constant(value), .. } => value,
                _ => arbitrary(),
            };
            lemma_encoded_payload(c, field, value, v);
        } else {
            assert(junco_core::flat::verify::test_wf(source.head@, source.tests@[i], i as nat));
            match (source.tests@[i], target.tests@[i]) {
                (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {},
                _ => {},
            }
    }
    }
    assert forall|i: int| #![trigger target.head@[i]] 0 <= i < target.head@.len() implies match target.head@[i] {
        FlatHead::Constant(v) => code_field(c, enc::field_at(i), v as nat), _ => true,
    } by {
        if let FlatHead::Constant(v) = target.head@[i] {
            let value = match source.head@[i] { FlatHead::Constant(value) => value, _ => arbitrary() };
            lemma_encoded_payload(c, enc::field_at(i), value, v);
        }
    }
    assert forall|i: int| 0 <= i < target.tests@.len() implies
        test_fields_bounded(target.tests@[i], target.head@.len()) by {
        assert(junco_core::flat::verify::test_wf(source.head@, source.tests@[i], i as nat));
        match (source.tests@[i], target.tests@[i]) {
            (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {},
            _ => {},
        }
    }
}

pub(crate) proof fn lemma_append_payload<E: Event>(c: Constants<E>, before: FlatPair<u64>,
    source: FlatPair<u64>, after: FlatPair<u64>)
    requires source_codes_wf(c, before), source_codes_wf(c, source), table::frame(before, after),
        table::tests_copied(source, after, before.tests@.len(), source.tests@.len()),
        after.tests@.len() == before.tests@.len() + source.tests@.len(),
        source_fields_bounded(before), source_fields_bounded(source),
        after.head@.len() == before.head@.len(), after.head@.len() == source.head@.len(),
    ensures source_codes_wf(c, after), source_fields_bounded(after),
{
    assert forall|i: int| #![trigger after.tests@[i]] 0 <= i < after.tests@.len() implies
        test_fields_bounded(after.tests@[i], after.head@.len())
            && match after.tests@[i] {
                FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => code_field(c, field, v as nat),
                FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } => field == variable,
                _ => true,
            } by {
        if i < before.tests@.len() { assert(after.tests@[i] == before.tests@[i]); }
        else {
            let j = i - before.tests@.len();
            assert(table::test_shift(source.tests@[j], after.tests@[i], before.tests@.len()));
            match (source.tests@[j], after.tests@[i]) {
                (FlatTest::Atom { .. }, FlatTest::Atom { .. }) => {}, _ => {},
            }
        }
    }
}

pub(crate) proof fn lemma_root_payload<E: Event>(a: PolicyAnalyzer<E>, l: SymbolicLanguage,
    source: FlatPair<u64>, g: implementation::ConstraintView)
    requires source_codes_wf(a.constants, source), universes_wf(a.constants, a.universes),
        constants_wf(a.constants),
        constraint_codes_wf(a.constants, g),
        source_fields_bounded(source), source.head@.len() == a.universes@.len(),
        symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))
            .subset_of(numeric::source_primitives(source)),
    ensures g.len() == a.universes@.len(),
        root_vocabulary(l, a.universes, g).len() == arity::<E>(),
        search::atoms_bounded(symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l))), a.universes@.len()),
        facade::primitives_search_safe(symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)))),
        forall|field: Component, v: nat|
            field.0 < a.universes@.len() && root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
                ==> code_field(a.constants, field, v),
{
    let ps = symbolic::regex_primitives(model::lift_regex(facade::graph(l), facade::root(l)));
    facade::lemma_primitive_codes_mono(ps, numeric::source_primitives(source));
    lemma_source_fields_bounded(source);
    assert forall|p: model::Primitive| ps.contains(p) implies match p {
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < a.universes@.len(),
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < a.universes@.len() && v.0 < a.universes@.len(),
    } by { assert(numeric::source_primitives(source).contains(p)); }
    assert forall|p: model::Primitive| ps.contains(p) implies match p {
        model::Primitive::Eq(_, model::GTerm::Constant(v)) => v <= u32::MAX,
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c == v,
    } by {
        numeric::lemma_source_primitive_prefix(source, source.tests@.len(), p);
        let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
            && match source.tests@[i] {
                FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, numeric::term_view(term)),
                _ => false,
            };
        match source.tests@[i] {
            FlatTest::Atom { field, term: FlatTerm::Constant(v), .. } => {
                assert(code_field(a.constants, field, v as nat));
            },
            FlatTest::Atom { field, term: FlatTerm::Variable(v), .. } => { assert(field == v); },
            _ => {},
        }
    }
    assert forall|field: Component, v: nat|
        field.0 < a.universes@.len() && root_vocabulary(l, a.universes, g)[component_index(field) as int].contains(v)
        implies code_field(a.constants, field, v) by {
        let k = component_index(field) as int;
        if facade::primitive_codes(ps, field).contains(v) {
            numeric::lemma_source_code_member(source, field, v);
            let i = choose|i: int| #![trigger source.tests@[i]] 0 <= i < source.tests@.len()
                && match source.tests@[i] {
                    FlatTest::Atom { field: f, term: FlatTerm::Constant(code), .. } => f == field && code as nat == v,
                    _ => false,
                };
            match source.tests@[i] {
                FlatTest::Atom { field: f, term: FlatTerm::Constant(code), .. } => {
                    assert(code_field(a.constants, f, code as nat));
                    assert(code_field(a.constants, field, v));
                },
                _ => {},
            }
        } else if exec::domain_values(a.universes[k]).contains(v) {
            if let Some(ids) = a.universes[k] {
                let id = choose|id: u32| (*ids)@.to_set().contains(id) && id as nat == v;
                let j = choose|j: int| 0 <= j < (*ids)@.len() && (*ids)@[j] == id;
                assert(value_field::<E>(a.constants.values@[id as int - 1]) == field);
                assert(0 < id <= a.constants.values@.len());
                assert(code_field(a.constants, field, v));
            }
        } else {
            assert(register_codes(implementation::register_of(g, field)).contains(v));
            assert(code_field(a.constants, field, v));
        }
    }
}

}

verus! {
pub(crate) struct TailInput<E: Event> {
    pub left: Rule<E>,
    pub right: Rule<E>,
    pub left_flat: FlatRule<E::Component>,
    pub right_flat: FlatRule<E::Component>,
    pub left_numeric: FlatPair<u64>,
    pub right_numeric: FlatPair<u64>,
}

pub(crate) open spec fn tail_input_wf<E: Event>(c: Constants<E>, i: TailInput<E>) -> bool {
    &&& i.left.head@ == i.right.head@
    &&& i.left.head@.len() == arity::<E>()
    &&& fl::flattened(i.left, i.left_flat) && fl::flattened(i.right, i.right_flat)
    &&& enc::constants_in_domain(i.left_flat.source, fl::component_domain::<E>())
    &&& enc::constants_in_domain(i.right_flat.source, fl::component_domain::<E>())
    &&& enc::lowering(i.left_flat.source, i.left_numeric, constant_book(c), fl::component_equality::<E>())
    &&& enc::lowering(i.right_flat.source, i.right_numeric, constant_book(c), fl::component_equality::<E>())
}

pub(crate) proof fn lemma_tail_sources_wf<E: Event>(c: Constants<E>, i: TailInput<E>)
    requires tail_input_wf(c, i),
    ensures tdsl::rule_wf::<E>(i.left), tdsl::rule_wf::<E>(i.right),
        tdsl::head_tails_wf::<E>(i.left.head@, i.left.tail@, i.right.tail@),
{
    fl::lemma_flattened_rule_wf::<E>(i.left, i.left_flat);
    fl::lemma_flattened_rule_wf::<E>(i.right, i.right_flat);
}

pub(crate) open spec fn difference_source<E: Event>(i: TailInput<E>, p: FlatPair<u64>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| numeric::source_regex(p, p.root as nat, theta, w)
        == (numeric::source_regex(i.left_numeric, i.left_numeric.root as nat, theta, w)
            && !numeric::source_regex(i.right_numeric, i.right_numeric.root as nat, theta, w))
}

pub(crate) open spec fn difference_language<E: Event>(i: TailInput<E>, q: language::Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==> encoding::n_lang(theta, q, w)
        == (numeric::source_regex(i.left_numeric, i.left_numeric.root as nat, theta, w)
            && !numeric::source_regex(i.right_numeric, i.right_numeric.root as nat, theta, w))
}

pub(crate) open spec fn tail_ready<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>) -> bool {
    analyzer_state_wf(a) && junco_core::spec::hypotheses::analyzer_hypotheses::<E>() && tail_input_wf(a.constants, i) && difference_language(i, q)
}

pub(crate) open spec fn tail_failure<E: Event>(i: TailInput<E>) -> spec_fn(E, Seq<E>) -> bool {
    |c: E, h: Seq<E>| tdsl::head_matches(i.left.head@, c)
        && tdsl::lang(i.left.tail@, i.left.head@, c, h)
        && !tdsl::lang(i.right.tail@, i.right.head@, c, h)
}


pub(crate) proof fn lemma_numeric_head_sat(h: encoding::NHead, theta: Subst)
    requires h.len() == theta.len(), h.len() <= history_syntax::MAX_ARITY,
    ensures inclusion::sat_by(theta, inclusion::head_constraint(h)) == encoding::n_head_matches(h, theta),
{
    inclusion::lemma_head_sat(h, theta);
}

pub(crate) proof fn lemma_empty_language(theta: Subst, w: Seq<EventView>)
    ensures !encoding::n_lang(theta, language::Regex::<model::Test>::Empty, w),
{ reveal_with_fuel(language::numeric_lang, 1); }

pub(crate) proof fn lemma_result_outcome(d: encoding::NDomains, start: search::Item, outcome: search::Outcome)
    requires exec::search_result(d, start, outcome),
    ensures search::outcome_ok(d, start.constraint, start.state, language::Regex::Empty, outcome),
{
    reveal(exec::search_result);
    assert(search::initial_ok(start.state, start.state, language::Regex::Empty)) by {
        assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len())
            implies encoding::n_lang(theta, start.state, w)
                == (encoding::n_lang(theta, start.state, w) && !encoding::n_lang(theta, language::Regex::Empty, w)) by {
            lemma_empty_language(theta, w);
        }
    }
}

proof fn lemma_embed_failure<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    c: E, h: Seq<E>) -> (coding: typed::NatCoding<E>)
    requires tail_ready(a, i, q), questions::in_domains(a@.domains, c, h), tail_failure(i)(c, h),
    ensures inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
        q, language::Regex::Empty, typed::numeric_event::<E>(coding, event_view(c)),
        typed::numeric_history::<E>(coding, typed::projected_history(h))),
        typed::numeric_history::<E>(coding, typed::projected_history(h)).len() == h.len(),
{
    let coding = typed::lemma_pair_embedding(a.constants, event_view(c), typed::projected_history(h));
    assert forall|j: int| 0 <= j < h.len()
        implies typed::covered_event::<E>(coding, event_view(h[j])) by {
        assert(typed::projected_history(h)[j] == event_view(h[j]));
        assert(typed::covered_event::<E>(coding, typed::projected_history(h)[j]));
    }
    typed::lemma_analyzer_domain_embedding(a, coding, c, h);
    typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
        i.left_numeric, i.right_numeric, a.constants, coding, c, h);
    lemma_numeric_head_sat(typed::template_head(i.left_numeric), typed::numeric_event::<E>(coding, event_view(c)));
    lemma_empty_language(typed::numeric_event::<E>(coding, event_view(c)),
        typed::numeric_history::<E>(coding, typed::projected_history(h)));
    coding
}

pub(crate) proof fn lemma_holds<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>)
    requires tail_ready(a, i, q), inclusion::included_under(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty),
    ensures analyzer::tail_included_spec(a@, a@, i.left.head@, i.left.tail@, i.right.tail@, analyzer::QueryResult::Holds),
{
    lemma_tail_sources_wf(a.constants, i);
    assert forall|c: E, h: Seq<E>| questions::in_domains(a@.domains, c, h)
        implies !tail_failure(i)(c, h) by {
        if tail_failure(i)(c, h) { let coding = lemma_embed_failure(a, i, q, c, h); }
    }
}

pub(crate) proof fn lemma_shortest<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>, n: nat)
    requires tail_ready(a, i, q), inclusion::no_cex_shorter(ndomains(a.universes),
        inclusion::head_constraint(typed::template_head(i.left_numeric)), q, language::Regex::Empty, n),
    ensures questions::shortest(a@.domains, n, tail_failure(i)),
{
    assert forall|c: E, h: Seq<E>| questions::in_domains(a@.domains, c, h) && h.len() < n
        implies !tail_failure(i)(c, h) by {
        if tail_failure(i)(c, h) { let coding = lemma_embed_failure(a, i, q, c, h); }
    }
}

pub(crate) proof fn lemma_no_candidates<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(), tail_input_wf(a.constants, i),
        !inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))),
    ensures analyzer::tail_included_spec(a@, a@, i.left.head@, i.left.tail@, i.right.tail@, analyzer::QueryResult::Holds),
{
    lemma_tail_sources_wf(a.constants, i);
    assert forall|c: E, h: Seq<E>| questions::in_domains(a@.domains, c, h)
        implies !tail_failure(i)(c, h) by {
        if tail_failure(i)(c, h) {
            let coding = typed::lemma_pair_embedding(a.constants, event_view(c), typed::projected_history(h));
            assert forall|j: int| 0 <= j < h.len()
                implies typed::covered_event::<E>(coding, event_view(h[j])) by {
                assert(typed::projected_history(h)[j] == event_view(h[j]));
                assert(typed::covered_event::<E>(coding, typed::projected_history(h)[j]));
            }
            typed::lemma_analyzer_domain_embedding(a, coding, c, h);
            typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
                i.left_numeric, i.right_numeric, a.constants, coding, c, h);
            let theta = typed::numeric_event::<E>(coding, event_view(c));
            lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
            assert(inclusion::satisfiable(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric))));
        }
    }
}

pub(crate) proof fn lemma_counterexample<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>, q: language::Regex<model::Test>,
    g: Constraint, letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>, result: Counterexample<E>)
    requires tail_ready(a, i, q), slots::reconstructed(a.constants, a.universes, g, letters, alphabets, result),
        result@.known == questions::tail_knowable_constants::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@),
        search::outcome_ok(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)), q,
            language::Regex::Empty, search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets))),
    ensures analyzer::tail_included_spec(a@, a@, i.left.head@, i.left.tail@, i.right.tail@,
        analyzer::QueryResult::Counterexample(result@)),
{
    lemma_tail_sources_wf(a.constants, i);
    questions::lemma_tail_knowable_rules::<E>(a@.domains, i.left, i.right);
    let (candidate, history) = choose|candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>|
        #[trigger] slots::constructed(a.constants, a.universes, g, letters, candidate, history)
            && result@ == slots::cex_of_slots(a.constants, candidate, history, result@.known)
            && implementation::reconstruction_ok(ndomains(a.universes), implementation::constraint_of(g@),
                exec::chain_assignments(letters, alphabets), candidate, history, slots::known_codes(a.constants));
    slots::lemma_counterexample_wf(a, g, letters, candidate, history, result@.known);
    assert forall|c: E, h: Seq<E>| questions::instance(a@.domains, result@, c, h)
        implies tail_failure(i)(c, h) by {
        let coding = typed::lemma_slot_embedding(a, candidate, history, c, h, result@.known);
        typed::lemma_fixes_known_subset(a.constants, coding, result@.known, questions::rule_constants(i.left@));
        typed::lemma_fixes_known_subset(a.constants, coding, result@.known, questions::rule_constants(i.right@));
        let theta = typed::numeric_event::<E>(coding, event_view(c));
        let w = typed::numeric_history::<E>(coding, typed::projected_history(h));
        assert(slots::candidate_field_ok(a.constants, a.universes, g, 0, candidate[0]));
        slots::lemma_candidate_slots(a.constants, a.universes, g, candidate, typed::numeric_fresh::<E>(a.constants));
        assert(inclusion::sat_by(theta, implementation::constraint_of(g@)));
        assert(search::follows(ndomains(a.universes), exec::chain_assignments(letters, alphabets), theta, w));
        assert(inclusion::inclusion_cex(ndomains(a.universes), inclusion::head_constraint(typed::template_head(i.left_numeric)),
            q, language::Regex::Empty, theta, w));
        lemma_numeric_head_sat(typed::template_head(i.left_numeric), theta);
        typed::lemma_source_failure(i.left, i.right, i.left_flat, i.right_flat,
            i.left_numeric, i.right_numeric, a.constants, coding, c, h);
    }
    assert(questions::every_instance(a@.domains, result@, tail_failure(i)));
    lemma_shortest(a, i, q, exec::chain_assignments(letters, alphabets).len());
    assert(result@.history.len() == exec::chain_assignments(letters, alphabets).len());
    assert forall|c: E, h: Seq<E>| questions::in_domains(a@.domains, c, h)
        && h.len() < result@.history.len() && tdsl::head_matches(i.left.head@, c)
        && tdsl::lang(i.left.tail@, i.left.head@, c, h)
        implies tdsl::lang(i.right.tail@, i.right.head@, c, h) by {
        assert(!tail_failure(i)(c, h));
    }
    assert(questions::known_within(result@, result@.known));
    if questions::counterexample_capacity::<E>(a@.domains, result@) {
        questions::lemma_counterexample_has_instance::<E>(a@.domains, result@);
        let (c, h) = choose|c: E, h: Seq<E>| questions::instance(a@.domains, result@, c, h);
        assert(!questions::tails_included::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@));
    }
}
}

verus! {
/// The numeric languages compared by a search. They need not share a head or a mode.
pub(crate) struct NumericInput {
    pub left: language::Regex<model::Test>,
    pub right: language::Regex<model::Test>,
}


pub(crate) open spec fn numeric_difference(i: NumericInput, p: FlatPair<u64>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
        numeric::source_regex(p, p.root as nat, theta, w)
            == (encoding::n_lang(theta, i.left, w) && !encoding::n_lang(theta, i.right, w))
}

pub(crate) open spec fn numeric_decision_ok<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput,
    g: implementation::ConstraintView, result: NumericDecision<E>, known: Seq<Set<E::Component>>) -> bool {
    &&& constraint_codes_known(a.constants, g, known)
    &&& search::outcome_ok(ndomains(a.universes), implementation::constraint_of(g),
        i.left, i.right, result.outcome@)
    &&& match result.inclusion {
        Inclusion::Holds => result.outcome@ == search::Outcome::Holds,
        Inclusion::Exhausted => result.outcome@ == search::Outcome::Exhausted,
        Inclusion::Counterexample(c) => c@.known == known && exists|refutation: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            result.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                exec::chain_assignments(letters, alphabets))
            && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c),
    }
}

pub(crate) proof fn lemma_numeric_refutation<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput,
    start: implementation::ConstraintView, g: Constraint, letters: Seq<Letter>,
    alphabets: Seq<Set<model::Primitive>>, decision: NumericDecision<E>, known: Seq<Set<E::Component>>)
    requires search::outcome_ok(ndomains(a.universes), implementation::constraint_of(start),
            i.left, i.right, decision.outcome@),
        constraint_codes_known(a.constants, start, known),
        decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g@), exec::chain_assignments(letters, alphabets)),
        decision.inclusion matches Inclusion::Counterexample(c)
            && slots::reconstructed(a.constants, a.universes, g, letters, alphabets, c) && c@.known == known,
    ensures numeric_decision_ok(a, i, start, decision, known),
{
    slots::lemma_inclusion_view(decision.inclusion);
    if let Inclusion::Counterexample(c) = decision.inclusion {
        assert(exists|g1: Constraint, ls: Seq<Letter>, atoms: Seq<Set<model::Primitive>>|
            decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(g1@), exec::chain_assignments(ls, atoms))
            && slots::reconstructed(a.constants, a.universes, g1, ls, atoms, c)) by {
            assert(slots::reconstructed(a.constants, a.universes, g, letters, alphabets, c));
        }
    }
}

pub(crate) proof fn lemma_outcome_difference(d: encoding::NDomains, start: search::Item,
    i: NumericInput, outcome: search::Outcome)
    requires search::initial_ok(start.state, i.left, i.right),
        exec::search_result(d, start, outcome),
    ensures search::outcome_ok(d, start.constraint, i.left, i.right, outcome),
{
    reveal(exec::search_result);
}

pub(crate) proof fn lemma_tail_decision<E: Event>(a: PolicyAnalyzer<E>, i: TailInput<E>,
    n: NumericInput, g: implementation::ConstraintView, decision: NumericDecision<E>)
    requires tail_ready(a, i, n.left), n.right == language::Regex::Empty,
        implementation::constraint_of(g) == inclusion::head_constraint(typed::template_head(i.left_numeric)),
        numeric_decision_ok(a, n, g, decision,
            questions::tail_knowable_constants::<E>(a@.domains, i.left.head@, i.left.tail@, i.right.tail@)),
    ensures analyzer::tail_included_spec(a@, a@, i.left.head@, i.left.tail@, i.right.tail@, decision.inclusion@),
{
    slots::lemma_inclusion_view(decision.inclusion);
    match decision.inclusion {
        Inclusion::Holds => lemma_holds(a, i, n.left),
        Inclusion::Exhausted => { lemma_tail_sources_wf(a.constants, i); },
        Inclusion::Counterexample(c) => {
            let (refutation, letters, alphabets) = choose|refutation: Constraint, letters: Seq<Letter>,
                alphabets: Seq<Set<model::Primitive>>|
                decision.outcome@ == search::Outcome::Refuted(implementation::constraint_of(refutation@),
                    exec::chain_assignments(letters, alphabets))
                && slots::reconstructed(a.constants, a.universes, refutation, letters, alphabets, c);
            lemma_counterexample(a, i, n.left, refutation, letters, alphabets, c);
        },
    }
}
}

verus! {
pub(crate) open spec fn decision_ready<E: Event>(a: PolicyAnalyzer<E>, i: NumericInput, g: Constraint,
    difference: FlatPair<u64>, known: Seq<Set<E::Component>>) -> bool {
    &&& analyzer_state_wf(a) && junco_core::spec::hypotheses::analyzer_hypotheses::<E>()
    &&& source_codes_wf(a.constants, difference) && numeric_difference(i, difference)
    &&& constraint_wf(g) && constraint_codes_wf(a.constants, g@)
    &&& slots::context_wf::<E>(known) && constraint_codes_known(a.constants, g@, known)
    &&& primitives_known(a.constants, known, numeric::reachable_regex_primitives(difference, difference.root as nat))
    &&& source_fields_bounded(difference)
    &&& difference.head@.len() == arity::<E>()
    &&& g@.len() == a.universes@.len() && difference.head@.len() == a.universes@.len()
    &&& table::dag(difference) && difference.root < difference.regexes@.len()
    &&& inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(g@))
}

pub(crate) proof fn lemma_universes_extended<E: Event>(before: Constants<E>, after: Constants<E>, u: Universes)
    requires junco_core::spec::hypotheses::analyzer_hypotheses::<E>(), constants_wf(before), constants_wf(after), universes_wf(before, u),
        enc::extends(constant_book(before), constant_book(after), fl::component_equality::<E>()),
    ensures universes_wf(after, u),
{
    assert forall|k: int| #![trigger u[k]] 0 <= k < u@.len() implies match u[k] {
        None => true,
        Some(ids) => (*ids)@.no_duplicates() && forall|j: int| 0 <= j < (*ids)@.len()
            ==> code_field(after, enc::field_at(k), (*ids)@[j] as nat),
    } by {
        if let Some(ids) = u[k] {
            assert forall|j: int| 0 <= j < (*ids)@.len()
                implies code_field(after, enc::field_at(k), (*ids)@[j] as nat) by {
                let id = (*ids)@[j];
                let value = before.values@[id as int - 1];
                typed::lemma_native_equivalence::<E>();
                questions::lemma_native_eq_reflexive(value);
                assert(stored_code(before, value, id));
                lemma_stored_encoded(before, value, id);
                lemma_encoded_payload(after, enc::field_at(k), value, id as u64);
            }
        }
    }
}

pub(crate) proof fn lemma_head_payload<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>,
    constants: Seq<Option<u32>>, g: Constraint)
    requires head_codes_wf(c, head), head_view(constants) == pins(head),
        g.0@.len() == constants.len(), constants.len() == head.len(),
        forall|i: int| 0 <= i < constants.len() ==> g.0[i]@ == match constants[i] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        },
    ensures constraint_codes_wf(c, g@),
{
    assert forall|field: Component, v: nat| field.0 < g.0@.len() && register_codes(implementation::register_of(g@, field)).contains(v)
        implies code_field(c, field, v) by {
        let k = component_index(field) as int;
        assert(0 <= k < constants.len());
        assert(head_view(constants)[k] == option_code(constants[k]));
        assert(pins(head)[k] == encoding_head_code(head[k]));
        assert(head_view(constants)[k] == pins(head)[k]);
        assert(option_code(constants[k]) == encoding_head_code(head[k]));
        match constants[k] {
            Some(code) => { assert(head[k] == FlatHead::Constant(code as u64)); },
            None => { assert(!register_codes(implementation::register_of(g@, field)).contains(v)); },
        }
    }
}

pub(crate) proof fn lemma_head_constraint_known<E: Event>(c: Constants<E>, head: Seq<FlatHead<u64>>,
    constants: Seq<Option<u32>>, g: Constraint, known: Seq<Set<E::Component>>)
    requires head_codes_known(c, head, known), head_view(constants) == pins(head),
        g.0@.len() == constants.len(), constants.len() == head.len(),
        forall|i: int| 0 <= i < constants.len() ==> g.0[i]@ == match constants[i] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        },
    ensures constraint_codes_known(c, g@, known),
{
    assert forall|k: int, code: nat| 0 <= k < g@.len() && register_codes(g@[k]).contains(code)
        implies typed::known_value::<E>(known, k, c.values@[code as int - 1]) by {
        assert(head_view(constants)[k] == pins(head)[k]);
        match constants[k] {
            Some(v) => {
                assert(head[k] == FlatHead::Constant(v as u64));
                assert(code == v as nat);
            },
            None => { assert(!register_codes(g@[k]).contains(code)); },
        }
    }
}

pub(crate) proof fn lemma_refutation_input<E: Event>(a: PolicyAnalyzer<E>, start: search::Item,
    outcome: crate::search::SearchOutcome, vocabulary: Seq<Set<nat>>)
    requires analyzer_state_wf(a), exec::search_result(ndomains(a.universes), start, exec::outcome_view(outcome)),
        exec::refutation_ready(outcome, a.universes, vocabulary),
        forall|field: Component, v: nat| field.0 < vocabulary.len() && vocabulary[component_index(field) as int].contains(v)
            ==> code_field(a.constants, field, v),
    ensures match outcome {
        crate::search::SearchOutcome::Holds => true,
        crate::search::SearchOutcome::Refuted(r) => slots::reconstruction_input(a.constants, a.universes,
            r.constraint, r.letters@, r.alphabets@),
    },
{
    reveal(exec::refutation_ready);
    lemma_result_outcome(ndomains(a.universes), start, exec::outcome_view(outcome));
    if let crate::search::SearchOutcome::Refuted(r) = outcome {
        assert(vocabulary.len() == a.universes@.len());
        assert(vocabulary.len() == arity::<E>());
        assert(r.constraint@.len() == vocabulary.len());
        assert forall|field: Component| field.0 < r.constraint.0@.len() implies slots::register_codes_ok(a.constants, field,
            implementation::register_of(r.constraint@, field)) by {
            assert forall|v: nat| register_codes(implementation::register_of(r.constraint@, field)).contains(v)
                implies code_field(a.constants, field, v) by {}
            match implementation::register_of(r.constraint@, field) {
                implementation::RegisterView::Equals(_) => {}, implementation::RegisterView::Differs(_) => {},
            }
        }
        assert forall|j: int| 0 <= j < r.letters@.len() implies
            slots::letter_codes_ok(a.constants, ndomains(a.universes), r.letters@[j]@, r.alphabets@[j]) by {
            exec::lemma_letter_payload(a.constants, vocabulary, a.universes, r.letters@[j]@, r.alphabets@[j]);
        }
        assert(inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(r.constraint@)));
    }
}

/// Search carries the actual root vocabulary into every refutation constraint and letter.
pub(crate) proof fn lemma_refutation_known<E: Event>(a: PolicyAnalyzer<E>,
    outcome: crate::search::SearchOutcome, vocabulary: Seq<Set<nat>>, known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), exec::refutation_ready(outcome, a.universes, vocabulary),
        slots::context_wf::<E>(known), vocabulary.len() == arity::<E>(),
        forall|k: int, code: nat| 0 <= k < arity::<E>() && vocabulary[k].contains(code)
            ==> typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
        forall|k: int, code: nat| 0 <= k < arity::<E>()
            && (domain_view(a.universes[k]) matches Some(values) && values.contains(code))
            ==> #[trigger] typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
    ensures outcome matches crate::search::SearchOutcome::Refuted(r)
        ==> slots::reconstruction_known(a.constants, a.universes, r.constraint, r.letters@, known),
{
    reveal(exec::refutation_ready);
    if let crate::search::SearchOutcome::Refuted(r) = outcome {
        assert forall|k: int, code: nat| 0 <= k < arity::<E>() && register_codes(r.constraint@[k]).contains(code)
            implies typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
            assert(vocabulary[k].contains(code));
        }
        assert forall|j: int, k: int, code: nat| 0 <= j < r.letters@.len() && 0 <= k < arity::<E>()
            && r.letters@[j]@.classes[k] == Some(implementation::ClassView::Constant(code))
            implies typed::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
            let field = component_at(k as usize);
            assert(implementation::letter_class(r.letters@[j]@, field) == Some(implementation::ClassView::Constant(code)));
            assert(vocabulary[k].contains(code));
        }
    }
}
}

verus! {
pub(crate) open spec fn excluded_id(id: crate::analyzer::RuleId, exclude: Option<crate::analyzer::RuleId>) -> bool {
    match exclude { Some(other) => id.0 == other.0, None => false }
}

pub(crate) open spec fn head_atoms_ok<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, atoms: Seq<crate::constraint::Atom>) -> bool {
    &&& atoms_wf(atoms, arity::<E>())
    &&& forall|j: int, k: int| 0 <= j < ids.len() && !excluded_id(ids[j], exclude) && 0 <= k < arity::<E>()
        ==> match #[trigger] a.rules@[ids[j].0 as int].constants@[k] {
            Some(v) => atoms.contains(crate::constraint::Atom { component: k as usize,
                operand: crate::constraint::Operand::Constant(v) })
                && atoms.contains(crate::constraint::Atom { component: k as usize,
                    operand: crate::constraint::Operand::Register }), None => true,
        }
    &&& forall|j: int| 0 <= j < atoms.len() ==> match #[trigger] atoms[j].operand {
        crate::constraint::Operand::Constant(v) => code_field(a.constants, Component(atoms[j].component as u8), v as nat),
        _ => true,
    }
    &&& forall|j: int, code: u32| 0 <= j < atoms.len()
        && atoms[j].operand == crate::constraint::Operand::Constant(code)
        ==> exists|r: int| 0 <= r < a.rules@.len()
            && a.rules@[r].constants@[atoms[j].component as int] == Some(code)
}

pub(crate) open spec fn firing_prefix<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, n: int, g: Constraint, theta: Subst, word: Seq<EventView>) -> bool {
    exists|j: int| 0 <= j < n && !excluded_id(ids[j], exclude)
        && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
            inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int]).head))
        && #[trigger] encoding::n_lang(theta,
            inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int])), word)
}

/// Meaning of the union roots already accumulated by the borrowed-policy loop.
pub(crate) open spec fn covering_prefix<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<crate::analyzer::RuleId>,
    exclude: Option<crate::analyzer::RuleId>, n: int, g: Constraint, p: FlatPair<u64>, roots: Seq<u32>) -> bool {
    forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
        ((exists|j: int| 0 <= j < roots.len() && #[trigger] numeric::source_regex(p, roots[j] as nat, theta, word))
        == #[trigger] firing_prefix(a, ids, exclude, n, g, theta, word))
}

pub(crate) proof fn lemma_covering_step<E: Event>(a: PolicyAnalyzer<E>,
    ids: Seq<crate::analyzer::RuleId>, exclude: Option<crate::analyzer::RuleId>, index: int, g: Constraint,
    before: FlatPair<u64>, roots: Seq<u32>, after: FlatPair<u64>, next: Seq<u32>, added: Option<u32>)
    requires 0 <= index < ids.len(), covering_prefix(a, ids, exclude, index, g, before, roots),
        forall|j: int, theta: Subst, w: Seq<EventView>| 0 <= j < roots.len()
            ==> numeric::source_regex(before, roots[j] as nat, theta, w)
                == numeric::source_regex(after, roots[j] as nat, theta, w),
        match added {
            Some(root) => !excluded_id(ids[index], exclude)
                && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                    inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]).head))
                && next == roots.push(root)
                && forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) ==>
                    numeric::source_regex(after, root as nat, theta, w)
                        == encoding::n_lang(theta, inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int])), w),
            None => next == roots && (excluded_id(ids[index], exclude)
                || !inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                    inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]).head))),
        },
    ensures covering_prefix(a, ids, exclude, index + 1, g, after, next),
{
    assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) implies
        ((exists|j: int| 0 <= j < next.len() && #[trigger] numeric::source_regex(after, next[j] as nat, theta, w))
            == #[trigger] firing_prefix(a, ids, exclude, index + 1, g, theta, w)) by {
        let r = super::policy_queries::stored_numeric(a.rules@[ids[index].0 as int]);
        let fires = !excluded_id(ids[index], exclude)
            && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@), inclusion::head_constraint(r.head));
        assert(firing_prefix(a, ids, exclude, index + 1, g, theta, w)
            == (firing_prefix(a, ids, exclude, index, g, theta, w)
                || (fires && encoding::n_lang(theta, inclusion::denial(r), w)))) by {
            if firing_prefix(a, ids, exclude, index + 1, g, theta, w) {
                let j = choose|j: int| 0 <= j < index + 1 && !excluded_id(ids[j], exclude)
                    && inclusion::entails(ndomains(a.universes), implementation::constraint_of(g@),
                        inclusion::head_constraint(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int]).head))
                    && encoding::n_lang(theta, inclusion::denial(super::policy_queries::stored_numeric(a.rules@[ids[j].0 as int])), w);
                if j < index { assert(firing_prefix(a, ids, exclude, index, g, theta, w)); }
            }
        }
        if exists|j: int| 0 <= j < next.len() && #[trigger] numeric::source_regex(after, next[j] as nat, theta, w) {
            let j = choose|j: int| 0 <= j < next.len() && numeric::source_regex(after, next[j] as nat, theta, w);
            if j < roots.len() {
                assert(numeric::source_regex(before, roots[j] as nat, theta, w));
                assert(firing_prefix(a, ids, exclude, index, g, theta, w));
            } else {
                assert(added is Some && j == roots.len());
            }
        }
        if firing_prefix(a, ids, exclude, index, g, theta, w) {
            let j = choose|j: int| 0 <= j < roots.len() && numeric::source_regex(before, roots[j] as nat, theta, w);
            assert(numeric::source_regex(after, next[j] as nat, theta, w));
        }
        if fires && encoding::n_lang(theta, inclusion::denial(r), w) {
            assert(added is Some);
            assert(numeric::source_regex(after, next[roots.len() as int] as nat, theta, w));
        }
    }
}
}
