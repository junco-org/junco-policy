//! Typed Eq-class embeddings into Nat and the analyzer's source-language bridge.
//!
//! Real constant books retain their u64 representation. These finite, per-field ghost codings
//! extend equality classes into Nat: the candidate is seeded before history classes, so only
//! its codes need the runtime's u64 bound. Histories remain mathematically unbounded.

use crate::analyzer::{Constants, PolicyAnalyzer};
use crate::verify::{self as views, frontend::*};
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::{analyzer, encoding, implementation, semantics};
use history_syntax::{Component, Event, Rule};
use junco_core::ComponentValue;
use junco_core::flat::verify as portable;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatRule, FlatTerm, FlatTest};
use junco_core::verify::history_specs::{self as language, EventView, Subst};
use junco_core::verify::{dsl as tdsl, encoding as enc, flatten as fl};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};

pub open spec fn equivalence<T>(eq: spec_fn(T, T) -> bool) -> bool {
    &&& forall|a: T| #![trigger eq(a, a)] eq(a, a)
    &&& forall|a: T, b: T| #![trigger eq(a, b)] eq(a, b) == eq(b, a)
    &&& forall|a: T, b: T, c: T| #![trigger eq(a, b), eq(b, c)]
        eq(a, b) && eq(b, c) ==> eq(a, c)
}

pub open spec fn coding_wf<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool) -> bool {
    &&& forall|i: int| 0 <= i < entries.len() ==> entries[i].1 > 0
    &&& forall|i: int, j: int| #![trigger entries[i], entries[j]]
        0 <= i < entries.len() && 0 <= j < entries.len()
            ==> (eq(entries[i].0, entries[j].0) == (entries[i].1 == entries[j].1))
}

pub open spec fn lookup_code<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool, value: T) -> nat
    decreases entries.len(),
{
    if entries.len() == 0 { 0 }
    else if eq(entries.last().0, value) { entries.last().1 }
    else { lookup_code(entries.drop_last(), eq, value) }
}

pub proof fn lemma_lookup_code<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool,
    value: T, index: int)
    requires equivalence(eq), coding_wf(entries, eq), 0 <= index < entries.len(),
        eq(entries[index].0, value),
    ensures lookup_code(entries, eq, value) == entries[index].1,
    decreases entries.len(),
{
    reveal_with_fuel(lookup_code, 1);
    if eq(entries.last().0, value) {
        assert(eq(value, entries[index].0));
        assert(eq(entries.last().0, entries[index].0));
        assert(entries.last() == entries[entries.len() - 1]);
    } else {
        assert(index < entries.len() - 1);
        let rest = entries.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies rest[i].1 > 0 by {
            assert(rest[i] == entries[i]);
        }
        assert forall|i: int, j: int| #![trigger rest[i], rest[j]]
            0 <= i < rest.len() && 0 <= j < rest.len()
            implies eq(rest[i].0, rest[j].0) == (rest[i].1 == rest[j].1) by {
            assert(rest[i] == entries[i]);
            assert(rest[j] == entries[j]);
        }
        lemma_lookup_code(rest, eq, value, index);
    }
}

pub proof fn lemma_coding_reflects_eq<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool,
    a: T, b: T, i: int, j: int)
    requires equivalence(eq), coding_wf(entries, eq),
        0 <= i < entries.len(), 0 <= j < entries.len(),
        eq(entries[i].0, a), eq(entries[j].0, b),
    ensures eq(a, b) == (lookup_code(entries, eq, a) == lookup_code(entries, eq, b)),
{
    lemma_lookup_code(entries, eq, a, i);
    lemma_lookup_code(entries, eq, b, j);
    if eq(a, b) {
        assert(eq(a, entries[j].0));
        assert(eq(entries[i].0, entries[j].0));
    } else if entries[i].1 == entries[j].1 {
        assert(eq(entries[i].0, entries[j].0));
        assert(eq(a, entries[j].0));
        assert(eq(a, b));
    }
}

pub open spec fn has_code<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool, value: T) -> bool {
    exists|i: int| #![trigger entries[i]] 0 <= i < entries.len() && eq(entries[i].0, value)
}

pub open spec fn max_code<T>(entries: Seq<(T, nat)>) -> nat
    decreases entries.len(),
{
    if entries.len() == 0 { 0 } else {
        let previous = max_code(entries.drop_last());
        if previous < entries.last().1 { entries.last().1 } else { previous }
    }
}

pub proof fn lemma_max_code<T>(entries: Seq<(T, nat)>)
    ensures forall|i: int| 0 <= i < entries.len() ==> entries[i].1 <= max_code(entries),
    decreases entries.len(),
{
    if entries.len() > 0 {
        let rest = entries.drop_last();
        lemma_max_code(rest);
        assert forall|i: int| 0 <= i < entries.len()
            implies entries[i].1 <= max_code(entries) by {
            if i < rest.len() { assert(entries[i] == rest[i]); }
            else { assert(entries[i] == entries.last()); }
        }
    }
}

pub open spec fn new_code<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool, value: T) -> nat {
    if has_code(entries, eq, value) { lookup_code(entries, eq, value) }
    else { max_code(entries) + 1 }
}

pub proof fn lemma_push_coding<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool, value: T)
    requires equivalence(eq), coding_wf(entries, eq),
    ensures coding_wf(entries.push((value, new_code(entries, eq, value))), eq),
{
    let code = new_code(entries, eq, value);
    let next = entries.push((value, code));
    if has_code(entries, eq, value) {
        let index = choose|i: int| 0 <= i < entries.len() && eq(entries[i].0, value);
        lemma_lookup_code(entries, eq, value, index);
        assert(code > 0);
        assert forall|j: int| 0 <= j < entries.len()
            implies eq(entries[j].0, value) == (entries[j].1 == code) by {
            lemma_coding_reflects_eq(entries, eq, entries[j].0, value, j, index);
            lemma_lookup_code(entries, eq, entries[j].0, j);
        }
    } else {
        lemma_max_code(entries);
        assert(code > 0);
        assert forall|j: int| 0 <= j < entries.len()
            implies eq(entries[j].0, value) == (entries[j].1 == code) by {}
    }
    assert forall|i: int| 0 <= i < next.len() implies next[i].1 > 0 by {
        if i < entries.len() { assert(next[i] == entries[i]); }
    }
    assert forall|i: int, j: int| #![trigger next[i], next[j]]
        0 <= i < next.len() && 0 <= j < next.len()
        implies eq(next[i].0, next[j].0) == (next[i].1 == next[j].1) by {
        if i < entries.len() && j < entries.len() {
            assert(next[i] == entries[i]);
            assert(next[j] == entries[j]);
        } else if i < entries.len() {
            assert(next[i] == entries[i]);
            assert(next[j] == (value, code));
        } else if j < entries.len() {
            assert(next[j] == entries[j]);
            assert(next[i] == (value, code));
            assert(eq(value, entries[j].0) == eq(entries[j].0, value));
        }
    }
}

pub open spec fn extend_codes<T>(entries: Seq<(T, nat)>, values: Seq<T>, eq: spec_fn(T, T) -> bool)
    -> Seq<(T, nat)>
    decreases values.len(),
{
    if values.len() == 0 { entries } else {
        let before = extend_codes(entries, values.drop_last(), eq);
        before.push((values.last(), new_code(before, eq, values.last())))
    }
}

pub proof fn lemma_extend_codes<T>(entries: Seq<(T, nat)>, values: Seq<T>, eq: spec_fn(T, T) -> bool)
    requires equivalence(eq), coding_wf(entries, eq),
    ensures coding_wf(extend_codes(entries, values, eq), eq),
        extend_codes(entries, values, eq).len() == entries.len() + values.len(),
        forall|i: int| 0 <= i < entries.len() ==> extend_codes(entries, values, eq)[i] == entries[i],
        forall|i: int| 0 <= i < values.len() ==> has_code(extend_codes(entries, values, eq), eq, values[i]),
    decreases values.len(),
{
    if values.len() > 0 {
        let rest = values.drop_last();
        lemma_extend_codes(entries, rest, eq);
        let before = extend_codes(entries, rest, eq);
        lemma_push_coding(before, eq, values.last());
        let result = extend_codes(entries, values, eq);
        assert(result == before.push((values.last(), new_code(before, eq, values.last()))));
        assert forall|i: int| 0 <= i < entries.len() implies result[i] == entries[i] by {
            assert(result[i] == before[i]);
        }
        assert forall|i: int| 0 <= i < values.len() implies has_code(result, eq, values[i]) by {
            if i < rest.len() {
                assert(values[i] == rest[i]);
                let index = choose|j: int| 0 <= j < before.len() && eq(before[j].0, values[i]);
                assert(result[index] == before[index]);
            } else {
                assert(values[i] == values.last());
                assert(result[result.len() - 1].0 == values.last());
                assert(eq(values.last(), values.last()));
            }
        }
    }
}

pub proof fn lemma_max_code_bound<T>(entries: Seq<(T, nat)>, bound: nat)
    requires forall|i: int| 0 <= i < entries.len() ==> entries[i].1 <= bound,
    ensures max_code(entries) <= bound,
    decreases entries.len(),
{
    if entries.len() > 0 {
        let rest = entries.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies rest[i].1 <= bound by {
            assert(rest[i] == entries[i]);
        }
        lemma_max_code_bound(rest, bound);
    }
}

pub proof fn lemma_seed_code_bound<T>(entries: Seq<(T, nat)>, eq: spec_fn(T, T) -> bool, value: T)
    requires equivalence(eq), coding_wf(entries, eq),
    ensures 0 < new_code(entries, eq, value) <= max_code(entries) + 1,
        lookup_code(entries.push((value, new_code(entries, eq, value))), eq, value)
            == new_code(entries, eq, value),
{
    if has_code(entries, eq, value) {
        let index = choose|i: int| 0 <= i < entries.len() && eq(entries[i].0, value);
        lemma_lookup_code(entries, eq, value, index);
        lemma_max_code(entries);
    }
    lemma_push_coding(entries, eq, value);
    let result = entries.push((value, new_code(entries, eq, value)));
    lemma_lookup_code(result, eq, value, entries.len() as int);
}

pub proof fn lemma_prefix_coding_stable<T>(before: Seq<(T, nat)>, after: Seq<(T, nat)>,
    eq: spec_fn(T, T) -> bool, value: T, index: int)
    requires equivalence(eq), coding_wf(before, eq), coding_wf(after, eq),
        before.len() <= after.len(),
        forall|i: int| 0 <= i < before.len() ==> after[i] == before[i],
        0 <= index < before.len(), eq(before[index].0, value),
    ensures lookup_code(after, eq, value) == lookup_code(before, eq, value),
{
    lemma_lookup_code(before, eq, value, index);
    lemma_lookup_code(after, eq, value, index);
}

pub proof fn lemma_fresh_coding<T>(known: Seq<(T, nat)>, numbers: Seq<nat>,
    eq: spec_fn(T, T) -> bool, fresh: spec_fn(nat) -> T, bound: nat)
    requires equivalence(eq), coding_wf(known, eq),
        forall|i: int| 0 <= i < known.len() ==> known[i].1 <= bound,
        forall|i: int, j: int| #![trigger numbers[i], known[j]]
            0 <= i < numbers.len() && 0 <= j < known.len()
                ==> !eq(fresh(numbers[i]), known[j].0),
        forall|i: int, j: int| #![trigger numbers[i], numbers[j]]
            0 <= i < numbers.len() && 0 <= j < numbers.len() && numbers[i] != numbers[j]
                ==> !eq(fresh(numbers[i]), fresh(numbers[j])),
    ensures coding_wf(known + numbers.map(|i: int, n: nat| (fresh(n), bound + n + 1)), eq),
{
    let added = numbers.map(|i: int, n: nat| (fresh(n), bound + n + 1));
    let result = known + added;
    assert forall|i: int| 0 <= i < result.len() implies result[i].1 > 0 by {
        if i < known.len() { assert(result[i] == known[i]); }
        else {
            assert(result[i] == added[i - known.len()]);
            assert(added[i - known.len()] == (fresh(numbers[i - known.len()]),
                bound + numbers[i - known.len()] + 1));
        }
    }
    assert forall|i: int, j: int| #![trigger result[i], result[j]]
        0 <= i < result.len() && 0 <= j < result.len()
        implies eq(result[i].0, result[j].0) == (result[i].1 == result[j].1) by {
        if i < known.len() && j < known.len() {
            assert(result[i] == known[i]);
            assert(result[j] == known[j]);
        } else if i < known.len() {
            let n = numbers[j - known.len()];
            assert(result[i] == known[i]);
            assert(result[j] == (fresh(n), bound + n + 1));
            assert(!eq(fresh(n), known[i].0));
            assert(!eq(known[i].0, fresh(n)));
        } else if j < known.len() {
            let n = numbers[i - known.len()];
            assert(result[j] == known[j]);
            assert(result[i] == (fresh(n), bound + n + 1));
            assert(!eq(fresh(n), known[j].0));
        } else {
            let n = numbers[i - known.len()];
            let m = numbers[j - known.len()];
            assert(result[i] == (fresh(n), bound + n + 1));
            assert(result[j] == (fresh(m), bound + m + 1));
            if n == m { assert(eq(fresh(n), fresh(m))); }
            else { assert(!eq(fresh(n), fresh(m))); }
        }
    }
}
}

verus! {

pub(crate) type NatCoding<E> = Seq<Seq<(ComponentValue<E>, nat)>>;

pub(crate) open spec fn native_eq<E: Event>() -> spec_fn(ComponentValue<E>, ComponentValue<E>) -> bool {
    |a: ComponentValue<E>, b: ComponentValue<E>| a.eq_spec(&b)
}

pub(crate) proof fn lemma_native_equivalence<E: Event>()
    requires views::analyzer_obligations::<E>(),
    ensures equivalence(native_eq::<E>()),
{}

pub(crate) open spec fn known_seed<E: Event>(c: Constants<E>, k: int) -> Seq<(ComponentValue<E>, nat)> {
    views::constant_book(c)[k].map(|i: int, p: (ComponentValue<E>, u64)| (p.0, p.1 as nat))
}

pub(crate) open spec fn fixes_book<E: Event>(c: Constants<E>, coding: NatCoding<E>) -> bool {
    coding.len() == 3 && forall|k: int| #![trigger coding[k]] 0 <= k < 3 ==> {
        &&& coding_wf(coding[k], native_eq::<E>())
        &&& forall|i: int| 0 <= i < known_seed(c, k).len() ==> coding[k][i] == known_seed(c, k)[i]
        &&& known_seed(c, k).len() <= coding[k].len()
    }
}

pub(crate) open spec fn covered_event<E: Event>(coding: NatCoding<E>, event: tdsl::EventView<E::Principal, E::Action, E::Resource>) -> bool {
    coding.len() == 3 && forall|k: int| #![trigger coding[k]] 0 <= k < 3
        ==> has_code(coding[k], native_eq::<E>(), fl::event_values::<E>(event)[k])
}

pub(crate) open spec fn code_value<E: Event>(coding: NatCoding<E>, field: Component, value: ComponentValue<E>) -> nat {
    lookup_code(coding[portable::field_index(field)], native_eq::<E>(), value)
}

pub(crate) open spec fn numeric_event<E: Event>(coding: NatCoding<E>, event: tdsl::EventView<E::Principal, E::Action, E::Resource>) -> EventView {
    EventView {
        principal: code_value(coding, Component::Principal, ComponentValue::<E>::Principal(event.principal)),
        action: code_value(coding, Component::Action, ComponentValue::<E>::Action(event.action)),
        resource: code_value(coding, Component::Resource, ComponentValue::<E>::Resource(event.resource)),
    }
}

pub(crate) open spec fn numeric_history<E: Event>(coding: NatCoding<E>, history: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>) -> Seq<EventView> {
    history.map(|i: int, e: tdsl::EventView<E::Principal, E::Action, E::Resource>| numeric_event(coding, e))
}

pub(crate) proof fn lemma_numeric_field<E: Event>(coding: NatCoding<E>, event: tdsl::EventView<E::Principal, E::Action, E::Resource>, field: Component)
    ensures language::field_value(numeric_event(coding, event), field)
        == code_value(coding, field, fl::event_values::<E>(event)[portable::field_index(field)]),
{ match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} } }

proof fn lemma_known_seed<E: Event>(c: Constants<E>, k: int)
    requires constants_wf(c), views::analyzer_obligations::<E>(), 0 <= k < 3,
    ensures coding_wf(known_seed(c, k), native_eq::<E>()),
        forall|i: int| 0 <= i < known_seed(c, k).len() ==> known_seed(c, k)[i].1 <= c.values@.len(),
{
    lemma_constants_maps(c);
    let field = enc::field_at(k);
    assert(portable::field_index(field) == k);
    lemma_field_book(c, field);
    assert forall|i: int| 0 <= i < known_seed(c, k).len() implies known_seed(c, k)[i].1 > 0
        && known_seed(c, k)[i].1 <= c.values@.len() by {
        lemma_field_entry_source(c.values@, field, i);
        let j = choose|j: int| 0 <= j < c.values@.len()
            && field_entries(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
        assert(known_seed(c, k)[i].1 == (j + 1) as nat);
    }
    assert forall|i: int, j: int| #![trigger known_seed(c, k)[i], known_seed(c, k)[j]]
        0 <= i < known_seed(c, k).len() && 0 <= j < known_seed(c, k).len()
        implies (native_eq::<E>()(known_seed(c, k)[i].0, known_seed(c, k)[j].0)
            == (known_seed(c, k)[i].1 == known_seed(c, k)[j].1)) by {
        let a = views::constant_book(c)[k][i].0;
        let b = views::constant_book(c)[k][j].0;
        match (field, a, b) {
            (Component::Principal, ComponentValue::Principal(_), ComponentValue::Principal(_)) => {},
            (Component::Action, ComponentValue::Action(_), ComponentValue::Action(_)) => {},
            (Component::Resource, ComponentValue::Resource(_), ComponentValue::Resource(_)) => {},
            _ => {},
        }
    }
}

pub(crate) proof fn lemma_pair_embedding<E: Event>(c: Constants<E>, candidate: tdsl::EventView<E::Principal, E::Action, E::Resource>, history: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>) -> (coding: NatCoding<E>)
    requires constants_wf(c), views::analyzer_obligations::<E>(),
    ensures fixes_book(c, coding), covered_event(coding, candidate),
        language::event_wf(numeric_event(coding, candidate)),
        forall|i: int| 0 <= i < history.len() ==> covered_event(coding, history[i]),
        numeric_history(coding, history).len() == history.len(),
{
    lemma_native_equivalence::<E>();
    let eq = native_eq::<E>();
    let result = Seq::new(3, |k: int| {
        let seed = known_seed(c, k);
        let v = fl::event_values::<E>(candidate)[k];
        extend_codes(seed.push((v, new_code(seed, eq, v))),
            history.map(|i: int, e: tdsl::EventView<E::Principal, E::Action, E::Resource>| fl::event_values::<E>(e)[k]), eq)
    });
    assert forall|k: int| #![trigger result[k]] 0 <= k < 3 implies {
        &&& coding_wf(result[k], eq)
        &&& known_seed(c, k).len() <= result[k].len()
        &&& forall|i: int| 0 <= i < known_seed(c, k).len() ==> result[k][i] == known_seed(c, k)[i]
        &&& has_code(result[k], eq, fl::event_values::<E>(candidate)[k])
        &&& lookup_code(result[k], eq, fl::event_values::<E>(candidate)[k]) <= u32::MAX + 1
        &&& forall|i: int| 0 <= i < history.len() ==> has_code(result[k], eq, fl::event_values::<E>(history[i])[k])
    } by {
        let seed = known_seed(c, k);
        let v = fl::event_values::<E>(candidate)[k];
        lemma_known_seed(c, k);
        lemma_max_code_bound(seed, u32::MAX as nat);
        lemma_seed_code_bound(seed, eq, v);
        let before = seed.push((v, new_code(seed, eq, v)));
        let vs = history.map(|i: int, e: tdsl::EventView<E::Principal, E::Action, E::Resource>| fl::event_values::<E>(e)[k]);
        lemma_push_coding(seed, eq, v);
        lemma_extend_codes(before, vs, eq);
        assert(result[k] == extend_codes(before, vs, eq));
        assert(result[k][seed.len() as int].0 == v);
        assert(eq(v, v));
        assert(has_code(result[k], eq, v));
        assert forall|i: int| 0 <= i < seed.len() implies result[k][i] == seed[i] by {
            assert(result[k][i] == before[i]);
        }
        assert forall|i: int| 0 <= i < history.len()
            implies has_code(result[k], eq, fl::event_values::<E>(history[i])[k]) by {
            assert(vs[i] == fl::event_values::<E>(history[i])[k]);
            assert(has_code(result[k], eq, vs[i]));
        }
        lemma_prefix_coding_stable(before, result[k], eq, v, seed.len() as int);
    }
    lemma_numeric_field(result, candidate, Component::Principal);
    lemma_numeric_field(result, candidate, Component::Action);
    lemma_numeric_field(result, candidate, Component::Resource);
    assert forall|i: int| 0 <= i < history.len() implies covered_event(result, history[i]) by {}
    result
}

pub(crate) proof fn lemma_fixed_code<E: Event>(c: Constants<E>, coding: NatCoding<E>, field: Component, value: ComponentValue<E>, id: u64)
    requires views::analyzer_obligations::<E>(), fixes_book(c, coding),
        enc::encoded(views::constant_book(c), fl::component_equality::<E>(), field, value, id),
        fl::component_domain::<E>()(field, value),
        enc::maps_wf(views::constant_book(c), fl::component_equality::<E>(), fl::component_domain::<E>()),
    ensures has_code(coding[portable::field_index(field)], native_eq::<E>(), value),
        code_value(coding, field, value) == id as nat,
{
    lemma_native_equivalence::<E>();
    let k = portable::field_index(field);
    let i = choose|i: int| 0 <= i < views::constant_book(c)[k].len()
        && views::constant_book(c)[k][i].1 == id
        && fl::component_equality::<E>()(field, value, views::constant_book(c)[k][i].0);
    let rep = views::constant_book(c)[k][i].0;
    match (field, value, rep) {
        (Component::Principal, ComponentValue::Principal(_), ComponentValue::Principal(_)) => {},
        (Component::Action, ComponentValue::Action(_), ComponentValue::Action(_)) => {},
        (Component::Resource, ComponentValue::Resource(_), ComponentValue::Resource(_)) => {},
        _ => {},
    }
    assert(native_eq::<E>()(coding[k][i].0, value));
    lemma_lookup_code(coding[k], native_eq::<E>(), value, i);
}

pub(crate) open spec fn flat_event_encoded<E: Event>(coding: NatCoding<E>, event: Seq<ComponentValue<E>>, n: EventView) -> bool {
    coding.len() == 3 && event.len() == 3 && forall|k: int| #![trigger event[k]] 0 <= k < 3 ==> {
        &&& fl::component_domain::<E>()(enc::field_at(k), event[k])
        &&& has_code(coding[k], native_eq::<E>(), event[k])
        &&& language::field_value(n, enc::field_at(k)) == lookup_code(coding[k], native_eq::<E>(), event[k])
    }
}

proof fn lemma_flat_encoded_field<E: Event>(coding: NatCoding<E>, event: Seq<ComponentValue<E>>, n: EventView, field: Component)
    requires flat_event_encoded(coding, event, n),
    ensures fl::component_domain::<E>()(field, event[portable::field_index(field)]),
        has_code(coding[portable::field_index(field)], native_eq::<E>(), event[portable::field_index(field)]),
        language::field_value(n, field) == code_value(coding, field, event[portable::field_index(field)]),
{
    match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
}

pub(crate) proof fn lemma_typed_event_encoded<E: Event>(coding: NatCoding<E>, event: tdsl::EventView<E::Principal, E::Action, E::Resource>)
    requires covered_event(coding, event),
    ensures flat_event_encoded(coding, fl::event_values::<E>(event), numeric_event(coding, event)),
{
    assert forall|k: int| #![trigger coding[k]] 0 <= k < 3 implies {
        &&& fl::component_domain::<E>()(enc::field_at(k), fl::event_values::<E>(event)[k])
        &&& has_code(coding[k], native_eq::<E>(), fl::event_values::<E>(event)[k])
        &&& language::field_value(numeric_event(coding, event), enc::field_at(k))
            == lookup_code(coding[k], native_eq::<E>(), fl::event_values::<E>(event)[k])
    } by { lemma_numeric_field(coding, event, enc::field_at(k)); if k == 0 {} else if k == 1 {} else {} }
}

proof fn lemma_reflect_component<E: Event>(coding: NatCoding<E>, field: Component, a: ComponentValue<E>, b: ComponentValue<E>)
    requires views::analyzer_obligations::<E>(), coding.len() == 3,
        coding_wf(coding[portable::field_index(field)], native_eq::<E>()),
        fl::component_domain::<E>()(field, a), fl::component_domain::<E>()(field, b),
        has_code(coding[portable::field_index(field)], native_eq::<E>(), a),
        has_code(coding[portable::field_index(field)], native_eq::<E>(), b),
    ensures fl::component_equality::<E>()(field, a, b) == (code_value(coding, field, a) == code_value(coding, field, b)),
        native_eq::<E>()(a, b) == (code_value(coding, field, a) == code_value(coding, field, b)),
{
    lemma_native_equivalence::<E>();
    let es = coding[portable::field_index(field)];
    let eq = native_eq::<E>();
    let i = choose|i: int| 0 <= i < es.len() && eq(es[i].0, a);
    let j = choose|j: int| 0 <= j < es.len() && eq(es[j].0, b);
    lemma_coding_reflects_eq(es, eq, a, b, i, j);
    match (field, a, b) {
        (Component::Principal, ComponentValue::Principal(_), ComponentValue::Principal(_)) => {},
        (Component::Action, ComponentValue::Action(_), ComponentValue::Action(_)) => {},
        (Component::Resource, ComponentValue::Resource(_), ComponentValue::Resource(_)) => {},
        _ => {},
    }
}

proof fn lemma_flat_source_test<E: Event>(source: FlatPair<ComponentValue<E>>, target: FlatPair<u64>, id: nat,
    c: Constants<E>, coding: NatCoding<E>, request: Seq<ComponentValue<E>>, theta: Subst,
    event: Seq<ComponentValue<E>>, n: EventView)
    requires portable::structural_wf(source), id < source.tests@.len(),
        enc::lowering(source, target, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book(c, coding),
        flat_event_encoded(coding, request, theta), flat_event_encoded(coding, event, n),
    ensures portable::test_sem(source.tests@, id, request, event, fl::component_equality::<E>())
        == numeric::source_test(target, id, theta, n),
    decreases id,
{
    reveal_with_fuel(portable::test_sem, 1);
    reveal_with_fuel(numeric::source_test, 1);
    lemma_constants_maps(c);
    assert(portable::test_wf(source.head@, source.tests@[id as int], id));
    match (source.tests@[id as int], target.tests@[id as int]) {
        (FlatTest::Atom { field, term: FlatTerm::Constant(value), positive },
            FlatTest::Atom { term: FlatTerm::Constant(code), .. }) => {
            lemma_fixed_code(c, coding, field, value, code);
            let k = portable::field_index(field);
            assert(enc::field_at(k) == field);
            lemma_flat_encoded_field(coding, event, n, field);
            lemma_reflect_component(coding, field, event[k], value);
        },
        (FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. }, _) => {
            assert(field == variable);
            let k = portable::field_index(field);
            assert(enc::field_at(k) == field);
            lemma_flat_encoded_field(coding, event, n, field);
            lemma_flat_encoded_field(coding, request, theta, field);
            lemma_reflect_component(coding, field, event[k], request[k]);
        },
        (FlatTest::And(children), _) | (FlatTest::Or(children), _) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                portable::test_sem(source.tests@, children@[i] as nat, request, event, fl::component_equality::<E>())
                    == numeric::source_test(target, children@[i] as nat, theta, n) by {
                lemma_flat_source_test(source, target, children@[i] as nat, c, coding, request, theta, event, n);
            }
        },
        _ => {},
    }
}

proof fn lemma_flat_source_regex<E: Event>(source: FlatPair<ComponentValue<E>>, target: FlatPair<u64>, id: nat,
    c: Constants<E>, coding: NatCoding<E>, request: Seq<ComponentValue<E>>, theta: Subst,
    word: Seq<Seq<ComponentValue<E>>>, w: Seq<EventView>)
    requires portable::structural_wf(source), id < source.regexes@.len(),
        enc::lowering(source, target, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book(c, coding),
        flat_event_encoded(coding, request, theta),
        enc::pointwise(word, w, |e: Seq<ComponentValue<E>>, n: EventView| flat_event_encoded(coding, e, n)),
    ensures portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>())
        == numeric::source_regex(target, id, theta, w),
    decreases id,
{
    reveal_with_fuel(portable::lang, 1);
    reveal_with_fuel(numeric::source_regex, 1);
    assert(portable::regex_wf(source.regexes@[id as int], id, source.tests@.len()));
    assert(enc::regex_same(source.regexes@[id as int], target.regexes@[id as int]));
    let rel = |e: Seq<ComponentValue<E>>, n: EventView| flat_event_encoded(coding, e, n);
    let rev = |n: EventView, e: Seq<ComponentValue<E>>| flat_event_encoded(coding, e, n);
    assert forall|i: int| 0 <= i < word.len() implies portable::event_wf(word[i]) by {}
    match source.regexes@[id as int] {
        FlatRegex::Test(test) => {
            if word.len() == 1 { lemma_flat_source_test(source, target, test as nat, c, coding, request, theta, word[0], w[0]); }
        },
        FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, word, fl::component_equality::<E>())
                    == numeric::source_regex(target, children@[i] as nat, theta, w) by {
                lemma_flat_source_regex(source, target, children@[i] as nat, c, coding, request, theta, word, w);
            }
        },
        FlatRegex::Complement(child) => { lemma_flat_source_regex(source, target, child as nat, c, coding, request, theta, word, w); },
        FlatRegex::Concat(children) => {
            if portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<ComponentValue<E>>>>| parts.len() == children@.len() && word == parts.flatten()
                    && forall|i: int| 0 <= i < children@.len() ==> portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, parts[i], fl::component_equality::<E>());
                assert(enc::pointwise(w, word, rev));
                enc::lemma_partition_lift(w, word, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && w == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < children@.len() implies children@[i] < id
                    && numeric::source_regex(target, children@[i] as nat, theta, lifted[i]) by {
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_flat_source_regex(source, target, children@[i] as nat, c, coding, request, theta, parts[i], lifted[i]);
                }
            }
            if numeric::source_regex(target, id, theta, w) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children@.len() && w == parts.flatten()
                    && forall|i: int| 0 <= i < children@.len() ==> children@[i] < id && numeric::source_regex(target, children@[i] as nat, theta, parts[i]);
                enc::lemma_partition_lift(word, w, parts, rel);
                let lifted = choose|lifted: Seq<Seq<Seq<ComponentValue<E>>>>| lifted.len() == parts.len() && word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < children@.len() implies
                    portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, lifted[i], fl::component_equality::<E>()) by {
                    lemma_flat_source_regex(source, target, children@[i] as nat, c, coding, request, theta, lifted[i], parts[i]);
                }
            }
        },
        FlatRegex::Star(child) => {
            if portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<ComponentValue<E>>>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> portable::lang(source.tests@, source.regexes@, child as nat, request, parts[i], fl::component_equality::<E>());
                assert(enc::pointwise(w, word, rev));
                enc::lemma_partition_lift(w, word, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| w == lifted.flatten() && lifted.len() == parts.len()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < parts.len() implies numeric::source_regex(target, child as nat, theta, lifted[i]) by {
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_flat_source_regex(source, target, child as nat, c, coding, request, theta, parts[i], lifted[i]);
                }
            }
            if numeric::source_regex(target, id, theta, w) {
                let parts = choose|parts: Seq<Seq<EventView>>| w == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> numeric::source_regex(target, child as nat, theta, parts[i]);
                enc::lemma_partition_lift(word, w, parts, rel);
                let lifted = choose|lifted: Seq<Seq<Seq<ComponentValue<E>>>>| word == lifted.flatten() && lifted.len() == parts.len()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < parts.len() implies
                    portable::lang(source.tests@, source.regexes@, child as nat, request, lifted[i], fl::component_equality::<E>()) by {
                    lemma_flat_source_regex(source, target, child as nat, c, coding, request, theta, lifted[i], parts[i]);
                }
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_source_language<E: Event>(rule: Rule<E>, flat: FlatRule<ComponentValue<E>>, template: FlatPair<u64>,
    c: Constants<E>, coding: NatCoding<E>, candidate: tdsl::EventView<E::Principal, E::Action, E::Resource>, history: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires fl::flattened(rule, flat), enc::lowering(flat.source, template, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(flat.source, fl::component_domain::<E>()), constants_wf(c), views::analyzer_obligations::<E>(),
        fixes_book(c, coding), covered_event(coding, candidate),
        forall|i: int| 0 <= i < history.len() ==> covered_event(coding, history[i]),
    ensures tdsl::lang(rule.tail@, rule.head@, candidate, history)
        == numeric::source_regex(template, template.root as nat, numeric_event(coding, candidate), numeric_history(coding, history)),
        tdsl::head_matches(rule.head@, candidate) == encoding::n_head_matches(template_head(template), numeric_event(coding, candidate)),
{
    fl::flattening_preserves_semantics(rule, flat, candidate, history);
    lemma_typed_event_encoded(coding, candidate);
    let word = fl::word_values::<E>(history);
    let w = numeric_history(coding, history);
    assert forall|i: int| 0 <= i < history.len() implies flat_event_encoded(coding, word[i], w[i]) by {
        lemma_typed_event_encoded(coding, history[i]);
    }
    lemma_flat_source_regex(flat.source, template, flat.source.root as nat, c, coding, fl::event_values::<E>(candidate), numeric_event(coding, candidate), word, w);
    lemma_constants_maps(c);
    assert forall|field: Component| match #[trigger] flat.source.head@[portable::field_index(field)] {
        FlatHead::Constant(v) => fl::component_equality::<E>()(field, fl::event_values::<E>(candidate)[portable::field_index(field)], v)
            == (language::field_value(numeric_event(coding, candidate), field) == encoding::n_head_field(template_head(template), field)->Some_0),
        _ => true,
    } by {
        let k = portable::field_index(field);
        assert(enc::field_at(k) == field);
        if let FlatHead::Constant(v) = flat.source.head@[k] {
            let id = match template.head@[k] { FlatHead::Constant(id) => id, _ => arbitrary() };
            lemma_fixed_code(c, coding, field, v, id);
            lemma_reflect_component(coding, field, fl::event_values::<E>(candidate)[k], v);
            lemma_numeric_field(coding, candidate, field);
        }
        match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
    }
}

pub(crate) open spec fn template_head(template: FlatPair<u64>) -> encoding::NHead {
    encoding::NHead { principal: encoding::head_code(template.head@[0]), action: encoding::head_code(template.head@[1]), resource: encoding::head_code(template.head@[2]) }
}

proof fn lemma_tagged_domain<E: Event, T: PartialEq>(c: Constants<E>, u: crate::constraint::Universe,
    domain: Option<Set<T>>, tag: spec_fn(T) -> ComponentValue<E>, project: spec_fn(ComponentValue<E>) -> T,
    coding: NatCoding<E>, field: Component, value: T)
    requires constants_wf(c), views::analyzer_obligations::<E>(), fixes_book(c, coding),
        tagged_codes(c, u, domain, tag),
        forall|x: T, y: T| #[trigger] tag(x).eq_spec(&tag(y)) == x.eq_spec(&y),
        forall|x: T| #[trigger] fl::component_domain::<E>()(field, tag(x)),
        forall|v: ComponentValue<E>| #[trigger] value_field(v) == field ==> tag(project(v)) == v,
        has_code(coding[portable::field_index(field)], native_eq::<E>(), tag(value)),
        u matches Some(ids) ==> forall|j: int| #![trigger (*ids)@[j]] 0 <= j < (*ids)@.len()
            ==> 0 < (*ids)@[j] <= c.values@.len() && value_field(c.values@[(*ids)@[j] as int - 1]) == field,
    ensures semantics::in_domain(domain, value) == match views::domain_view(u) {
        None => true, Some(ids) => ids.contains(code_value(coding, field, tag(value))) },
{
    lemma_constants_maps(c);
    lemma_native_equivalence::<E>();
    if let (Some(raw), Some(vs)) = (u, domain) {
        views::lemma_codes((*raw)@);
        if semantics::in_domain(domain, value) {
            let rep = choose|rep: T| vs.contains(rep) && value.eq_spec(&rep);
            let i = choose|i: int| 0 <= i < (*raw)@.len() && c.values@[(*raw)@[i] as int - 1] == tag(rep);
            let id = (*raw)@[i];
            assert(stored_code(c, tag(rep), id));
            assert(value_field(tag(rep)) == field);
            lemma_stored_encoded(c, tag(rep), id);
            lemma_fixed_code(c, coding, field, tag(rep), id as u64);
            lemma_reflect_component(coding, field, tag(value), tag(rep));
            assert(views::codes((*raw)@).contains(id as nat));
        }
        if views::codes((*raw)@).contains(code_value(coding, field, tag(value))) {
            let i = choose|i: int| 0 <= i < (*raw)@.len() && (*raw)@[i] as nat == code_value(coding, field, tag(value));
            let id = (*raw)@[i];
            let rep = project(c.values@[id as int - 1]);
            assert(tag(rep) == c.values@[id as int - 1]);
            assert(vs.contains(rep));
            lemma_stored_encoded(c, tag(rep), id);
            lemma_fixed_code(c, coding, field, tag(rep), id as u64);
            lemma_reflect_component(coding, field, tag(value), tag(rep));
            assert(value.eq_spec(&rep));
            assert(semantics::in_domain(domain, value));
        }
    }
    else { assert(u is None && domain is None); }
}

proof fn lemma_tagged_selected<E: Event, T>(c: Constants<E>, u: crate::constraint::Universe,
    tag: spec_fn(T) -> ComponentValue<E>, project: spec_fn(ComponentValue<E>) -> T,
    pred: spec_fn(ComponentValue<E>) -> bool)
    requires forall|x: T| #[trigger] project(tag(x)) == x && pred(tag(x)),
        forall|v: ComponentValue<E>| #[trigger] pred(v) ==> tag(project(v)) == v,
        u matches Some(ids) ==> forall|i: int| #![trigger (*ids)@[i]] 0 <= i < (*ids)@.len()
            ==> 0 < (*ids)@[i] <= c.values@.len(),
    ensures tagged_codes(c, u, match selected_values(c, u) { None => None,
        Some(vs) => Some(vs.filter(pred).map(project)) }, tag),
{
    if let Some(ids) = u {
        let selected = (*ids)@.to_set().map(|id: u32| c.values@[id as int - 1]);
        assert forall|x: T| #[trigger] selected.filter(pred).map(project).contains(x)
            implies exists|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == tag(x) by {
            let v = choose|v: ComponentValue<E>| selected.filter(pred).contains(v) && project(v) == x;
            let id = choose|id: u32| (*ids)@.to_set().contains(id) && c.values@[id as int - 1] == v;
            let i = choose|i: int| 0 <= i < (*ids)@.len() && (*ids)@[i] == id;
            assert(tag(x) == v);
        }
        assert forall|x: T| (exists|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == tag(x))
            implies #[trigger] selected.filter(pred).map(project).contains(x) by {
            let i = choose|i: int| 0 <= i < (*ids)@.len() && c.values@[(*ids)@[i] as int - 1] == tag(x);
            assert((*ids)@.to_set().contains((*ids)@[i]));
            assert(selected.contains(tag(x)));
            assert(project(tag(x)) == x);
            assert(pred(tag(x)));
            vstd::set::lemma_set_filter(selected, pred, tag(x));
            assert(selected.filter(pred).contains(tag(x)));
        }
    }
}

pub(crate) proof fn lemma_domain_event<E: Event>(a: PolicyAnalyzer<E>, coding: NatCoding<E>, event: tdsl::EventView<E::Principal, E::Action, E::Resource>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), fixes_book(a.constants, coding), covered_event(coding, event),
    ensures semantics::event_in(a@.domains, event) == encoding::n_event_in(views::ndomains(a.universes), numeric_event(coding, event)),
{
    let c = a.constants;
    assert forall|v: ComponentValue<E>| #[trigger] value_field(v) == Component::Principal
        implies ComponentValue::<E>::Principal(principal_of::<E>(v)) == v by { match v { ComponentValue::Principal(_) => {}, _ => {} } }
    assert forall|v: ComponentValue<E>| #[trigger] value_field(v) == Component::Action
        implies ComponentValue::<E>::Action(action_of::<E>(v)) == v by { match v { ComponentValue::Action(_) => {}, _ => {} } }
    assert forall|v: ComponentValue<E>| #[trigger] value_field(v) == Component::Resource
        implies ComponentValue::<E>::Resource(resource_of::<E>(v)) == v by { match v { ComponentValue::Resource(_) => {}, _ => {} } }
    lemma_tagged_selected(c, a.universes[0], |x: E::Principal| ComponentValue::<E>::Principal(x), |v: ComponentValue<E>| principal_of::<E>(v), |v: ComponentValue<E>| v is Principal);
    lemma_tagged_selected(c, a.universes[1], |x: E::Action| ComponentValue::<E>::Action(x), |v: ComponentValue<E>| action_of::<E>(v), |v: ComponentValue<E>| v is Action);
    lemma_tagged_selected(c, a.universes[2], |x: E::Resource| ComponentValue::<E>::Resource(x), |v: ComponentValue<E>| resource_of::<E>(v), |v: ComponentValue<E>| v is Resource);
    lemma_tagged_domain(c, a.universes[0], a@.domains.principal, |x: E::Principal| ComponentValue::<E>::Principal(x), |v: ComponentValue<E>| principal_of::<E>(v), coding, Component::Principal, event.principal);
    lemma_tagged_domain(c, a.universes[1], a@.domains.action, |x: E::Action| ComponentValue::<E>::Action(x), |v: ComponentValue<E>| action_of::<E>(v), coding, Component::Action, event.action);
    lemma_tagged_domain(c, a.universes[2], a@.domains.resource, |x: E::Resource| ComponentValue::<E>::Resource(x), |v: ComponentValue<E>| resource_of::<E>(v), coding, Component::Resource, event.resource);
    let nd = views::ndomains(a.universes);
    let n = numeric_event(coding, event);
    if semantics::event_in(a@.domains, event) {
        assert forall|field: Component| #[trigger] encoding::n_domain(nd, field) is Some
            implies encoding::n_domain(nd, field)->Some_0.contains(language::field_value(n, field)) by {
            match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
        assert(encoding::n_event_in(nd, n));
    }
    if encoding::n_event_in(nd, n) {
        assert(match encoding::n_domain(nd, Component::Principal) { None => true, Some(vs) => vs.contains(n.principal) });
        assert(match encoding::n_domain(nd, Component::Action) { None => true, Some(vs) => vs.contains(n.action) });
        assert(match encoding::n_domain(nd, Component::Resource) { None => true, Some(vs) => vs.contains(n.resource) });
        assert(semantics::in_domain(a@.domains.principal, event.principal));
        assert(semantics::in_domain(a@.domains.action, event.action));
        assert(semantics::in_domain(a@.domains.resource, event.resource));
        assert(semantics::event_in(a@.domains, event));
    }
    assert forall|field: Component| match #[trigger] encoding::n_domain(views::ndomains(a.universes), field) {
        None => true, Some(vs) => vs.contains(language::field_value(numeric_event(coding, event), field))
    } == match field {
        Component::Principal => semantics::in_domain(a@.domains.principal, event.principal),
        Component::Action => semantics::in_domain(a@.domains.action, event.action),
        Component::Resource => semantics::in_domain(a@.domains.resource, event.resource),
    } by { match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} } }
}

pub(crate) proof fn lemma_analyzer_domain_embedding<E: Event>(a: PolicyAnalyzer<E>, coding: NatCoding<E>, candidate: tdsl::EventView<E::Principal, E::Action, E::Resource>, history: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), fixes_book(a.constants, coding),
        covered_event(coding, candidate), language::event_wf(numeric_event(coding, candidate)),
        forall|i: int| 0 <= i < history.len() ==> covered_event(coding, history[i]),
        semantics::event_in(a@.domains, candidate), semantics::history_in(a@.domains, history),
    ensures encoding::n_theta_ok(views::ndomains(a.universes), numeric_event(coding, candidate)),
        encoding::n_history_in(views::ndomains(a.universes), numeric_history(coding, history)),
{
    lemma_domain_event(a, coding, candidate);
    assert forall|i: int| 0 <= i < history.len() implies encoding::n_event_in(views::ndomains(a.universes), numeric_history(coding, history)[i]) by {
        lemma_domain_event(a, coding, history[i]);
    }
}

pub(crate) open spec fn numeric_fresh<E: Event>(c: Constants<E>) -> spec_fn(nat) -> nat {
    |n: nat| c.values@.len() + n + 1
}

pub(crate) proof fn lemma_numeric_fresh<E: Event>(c: Constants<E>)
    ensures implementation::fresh_codes_ok(numeric_fresh(c), views::reconstruction::known_codes(c)),
{
    assert forall|n: nat| !#[trigger] views::reconstruction::known_codes(c).contains(numeric_fresh(c)(n)) by {
        let s = Seq::new(c.values@.len(), |i: int| (i + 1) as nat);
        if s.to_set().contains(numeric_fresh(c)(n)) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == numeric_fresh(c)(n);
        }
    }
}

pub(crate) open spec fn field_slots(candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>, k: int) -> Seq<implementation::SlotView> {
    seq![candidate[k]] + history.map(|i: int, row: Seq<implementation::SlotView>| row[k])
}

pub(crate) open spec fn fresh_numbers(slots: Seq<implementation::SlotView>) -> Seq<nat>
    decreases slots.len(),
{
    if slots.len() == 0 { Seq::empty() } else {
        let rest = fresh_numbers(slots.drop_last());
        match slots.last() { implementation::SlotView::Fresh(n) => rest.push(n), _ => rest }
    }
}

proof fn lemma_fresh_numbers(slots: Seq<implementation::SlotView>)
    ensures forall|n: nat| #[trigger] fresh_numbers(slots).contains(n)
        == (exists|i: int| 0 <= i < slots.len() && slots[i] == implementation::SlotView::Fresh(n)),
    decreases slots.len(),
{
    reveal_with_fuel(fresh_numbers, 1);
    if slots.len() > 0 {
        let rest = slots.drop_last();
        lemma_fresh_numbers(rest);
        match slots.last() {
            implementation::SlotView::Fresh(m) => { assert(fresh_numbers(slots) == fresh_numbers(rest).push(m)); },
            implementation::SlotView::Code(_) => { assert(fresh_numbers(slots) == fresh_numbers(rest)); },
        }
        assert forall|n: nat| #[trigger] fresh_numbers(slots).contains(n)
            == (exists|i: int| 0 <= i < slots.len() && slots[i] == implementation::SlotView::Fresh(n)) by {
            if exists|i: int| 0 <= i < slots.len() && slots[i] == implementation::SlotView::Fresh(n) {
                let i = choose|i: int| 0 <= i < slots.len() && slots[i] == implementation::SlotView::Fresh(n);
                if i < rest.len() {
                    assert(rest[i] == implementation::SlotView::Fresh(n));
                    assert(fresh_numbers(rest).contains(n));
                    match slots.last() {
                        implementation::SlotView::Fresh(m) => {
                            vstd::seq_lib::lemma_seq_contains_after_push(fresh_numbers(rest), m, n);
                        },
                        implementation::SlotView::Code(_) => {},
                    }
                } else {
                    assert(slots.last() == implementation::SlotView::Fresh(n));
                    vstd::seq_lib::lemma_seq_contains_after_push(fresh_numbers(rest), n, n);
                }
                assert(fresh_numbers(slots).contains(n));
            }
            if fresh_numbers(slots).contains(n) {
                if fresh_numbers(rest).contains(n) {
                    let i = choose|i: int| 0 <= i < rest.len() && rest[i] == implementation::SlotView::Fresh(n);
                    assert(slots[i] == implementation::SlotView::Fresh(n));
                } else { assert(slots[slots.len() - 1] == implementation::SlotView::Fresh(n)); }
                assert(exists|i: int| 0 <= i < slots.len() && slots[i] == implementation::SlotView::Fresh(n));
            }
        }
    }
}

pub(crate) open spec fn tagged_fresh<E: Event>(f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>, k: int, n: nat) -> ComponentValue<E> {
    if k == 0 { ComponentValue::Principal((f.principal)(n)) }
    else if k == 1 { ComponentValue::Action((f.action)(n)) }
    else { ComponentValue::Resource((f.resource)(n)) }
}

proof fn lemma_fresh_admissible<E: Event>(a: PolicyAnalyzer<E>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>,
    f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>, k: int)
    requires constants_wf(a.constants), views::analyzer_obligations::<E>(), 0 <= k < 3,
        views::reconstruction::slot_wf(a.constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> views::reconstruction::slot_wf(a.constants, history[i]),
        analyzer::admissible(a@, views::reconstruction::cex_of_slots(a.constants, candidate, history), f),
    ensures coding_wf(known_seed(a.constants, k) + fresh_numbers(field_slots(candidate, history, k)).map(
        |i: int, n: nat| (tagged_fresh::<E>(f, k, n), numeric_fresh(a.constants)(n))), native_eq::<E>()),
{
    let c = a.constants;
    let numbers = fresh_numbers(field_slots(candidate, history, k));
    lemma_fresh_numbers(field_slots(candidate, history, k));
    views::reconstruction::lemma_used_at(c, candidate, history);
    lemma_known_seed(c, k);
    lemma_native_equivalence::<E>();
    assert forall|i: int| 0 <= i < numbers.len() implies views::reconstruction::used_at(candidate, history, k).contains(numbers[i]) by {
        assert(numbers.contains(numbers[i]));
        assert(field_slots(candidate, history, k).len() == history.len() + 1);
        let j = choose|j: int| 0 <= j < field_slots(candidate, history, k).len()
            && field_slots(candidate, history, k)[j] == implementation::SlotView::Fresh(numbers[i]);
        if j > 0 {
            assert(field_slots(candidate, history, k)[j] == history[j - 1][k]);
            assert(history[j - 1][k] == implementation::SlotView::Fresh(numbers[i]));
        } else { assert(candidate[k] == implementation::SlotView::Fresh(numbers[i])); }
    }
    assert forall|i: int, j: int| #![trigger numbers[i], known_seed(c, k)[j]]
        0 <= i < numbers.len() && 0 <= j < known_seed(c, k).len()
        implies !native_eq::<E>()(tagged_fresh::<E>(f, k, numbers[i]), known_seed(c, k)[j].0) by {
        let field = enc::field_at(k);
        lemma_field_book(c, field);
        lemma_field_entry_source(c.values@, field, j);
        let rep = known_seed(c, k)[j].0;
        assert(c.values@.to_set().contains(rep));
        if k == 0 {
            vstd::set::lemma_set_filter(c.values@.to_set(), |v: ComponentValue<E>| v is Principal, rep);
            assert(a@.known_principals.contains(principal_of::<E>(rep)));
        } else if k == 1 {
            vstd::set::lemma_set_filter(c.values@.to_set(), |v: ComponentValue<E>| v is Action, rep);
            assert(a@.known_actions.contains(action_of::<E>(rep)));
        } else {
            vstd::set::lemma_set_filter(c.values@.to_set(), |v: ComponentValue<E>| v is Resource, rep);
            assert(a@.known_resources.contains(resource_of::<E>(rep)));
        }
        match rep { ComponentValue::Principal(_) => {}, ComponentValue::Action(_) => {}, ComponentValue::Resource(_) => {} }
    }
    assert forall|i: int, j: int| #![trigger numbers[i], numbers[j]]
        0 <= i < numbers.len() && 0 <= j < numbers.len() && numbers[i] != numbers[j]
        implies !native_eq::<E>()(tagged_fresh::<E>(f, k, numbers[i]), tagged_fresh::<E>(f, k, numbers[j])) by {
        if k == 0 {} else if k == 1 {} else {}
    }
    lemma_fresh_coding(known_seed(c, k), numbers, native_eq::<E>(), |n: nat| tagged_fresh::<E>(f, k, n), c.values@.len());
}

proof fn lemma_slot_event<E: Event>(c: Constants<E>, coding: NatCoding<E>, slots: Seq<implementation::SlotView>,
    f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), fixes_book(c, coding), views::reconstruction::slot_wf(c, slots),
        forall|k: int| #![trigger slots[k]] 0 <= k < 3 ==> (slots[k] matches implementation::SlotView::Fresh(n)
            ==> fresh_numbers(field_slots(candidate, history, k)).contains(n)),
        forall|k: int| #![trigger coding[k]] 0 <= k < 3 ==> coding[k] == known_seed(c, k)
            + fresh_numbers(field_slots(candidate, history, k)).map(|i: int, n: nat| (tagged_fresh::<E>(f, k, n), numeric_fresh(c)(n))),
    ensures covered_event(coding, analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f)),
        numeric_event(coding, analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f))
            == implementation::slots_event(slots, numeric_fresh(c)),
{
    lemma_constants_maps(c);
    lemma_native_equivalence::<E>();
    let event = analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f);
    assert forall|k: int| #![trigger coding[k]] 0 <= k < 3 implies has_code(coding[k], native_eq::<E>(), fl::event_values::<E>(event)[k])
        && language::field_value(numeric_event(coding, event), enc::field_at(k)) == implementation::slot_value(slots[k], numeric_fresh(c)) by {
        lemma_numeric_field(coding, event, enc::field_at(k));
        if k == 0 {} else if k == 1 {} else {}
        match slots[k] {
            implementation::SlotView::Code(v) => {
                let value = c.values@[v as int - 1];
                assert(value_field(value) == enc::field_at(k));
                match value { ComponentValue::Principal(_) => {}, ComponentValue::Action(_) => {}, ComponentValue::Resource(_) => {} }
                assert(fl::event_values::<E>(event)[k] == value);
                lemma_stored_encoded(c, value, v as u32);
                lemma_fixed_code(c, coding, enc::field_at(k), value, v as u64);
            },
            implementation::SlotView::Fresh(n) => {
                let ns = fresh_numbers(field_slots(candidate, history, k));
                let i = choose|i: int| 0 <= i < ns.len() && ns[i] == n;
                let j = known_seed(c, k).len() as int + i;
                assert(coding[k][j] == (tagged_fresh::<E>(f, k, n), numeric_fresh(c)(n)));
                assert(fl::event_values::<E>(event)[k] == tagged_fresh::<E>(f, k, n));
                lemma_lookup_code(coding[k], native_eq::<E>(), fl::event_values::<E>(event)[k], j);
            },
        }
    }
}

pub(crate) proof fn lemma_slot_embedding<E: Event>(a: PolicyAnalyzer<E>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>,
    f: analyzer::FreshChoice<E::Principal, E::Action, E::Resource>) -> (coding: NatCoding<E>)
    requires constants_wf(a.constants), views::analyzer_obligations::<E>(), views::reconstruction::slot_wf(a.constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> views::reconstruction::slot_wf(a.constants, history[i]),
        forall|k: int| #![trigger candidate[k]] 0 <= k < 3 ==> (candidate[k] matches implementation::SlotView::Fresh(n) ==> n < 3),
        analyzer::admissible(a@, views::reconstruction::cex_of_slots(a.constants, candidate, history), f),
    ensures fixes_book(a.constants, coding),
        covered_event(coding, analyzer::event_of(views::reconstruction::cex_of_slots(a.constants, candidate, history).candidate, f)),
        numeric_event(coding, analyzer::event_of(views::reconstruction::cex_of_slots(a.constants, candidate, history).candidate, f))
            == implementation::slots_event(candidate, numeric_fresh(a.constants)),
        language::event_wf(implementation::slots_event(candidate, numeric_fresh(a.constants))),
        forall|i: int| 0 <= i < history.len() ==> covered_event(coding, analyzer::history_of(views::reconstruction::cex_of_slots(a.constants, candidate, history), f)[i]),
        numeric_history(coding, analyzer::history_of(views::reconstruction::cex_of_slots(a.constants, candidate, history), f))
            == history.map(|i: int, slots: Seq<implementation::SlotView>| implementation::slots_event(slots, numeric_fresh(a.constants))),
        implementation::fresh_codes_ok(numeric_fresh(a.constants), views::reconstruction::known_codes(a.constants)),
{
    let c = a.constants;
    let result = Seq::new(3, |k: int| known_seed(c, k) + fresh_numbers(field_slots(candidate, history, k)).map(
        |i: int, n: nat| (tagged_fresh::<E>(f, k, n), numeric_fresh(c)(n))));
    assert forall|k: int| #![trigger result[k]] 0 <= k < 3 implies coding_wf(result[k], native_eq::<E>())
        && known_seed(c, k).len() <= result[k].len()
        && forall|j: int| 0 <= j < known_seed(c, k).len() ==> result[k][j] == known_seed(c, k)[j] by {
        lemma_fresh_admissible(a, candidate, history, f, k);
        lemma_fresh_numbers(field_slots(candidate, history, k));
    }
    assert forall|k: int, n: nat| #![trigger fresh_numbers(field_slots(candidate, history, k)).contains(n)]
        0 <= k < 3 implies fresh_numbers(field_slots(candidate, history, k)).contains(n)
            == views::reconstruction::used_at(candidate, history, k).contains(n) by {
        lemma_fresh_numbers(field_slots(candidate, history, k));
        if views::reconstruction::used_at(candidate, history, k).contains(n) {
            if candidate[k] == implementation::SlotView::Fresh(n) {
                assert(field_slots(candidate, history, k)[0] == implementation::SlotView::Fresh(n));
            } else {
                let i = choose|i: int| 0 <= i < history.len() && history[i][k] == implementation::SlotView::Fresh(n);
                assert(field_slots(candidate, history, k)[i + 1] == implementation::SlotView::Fresh(n));
            }
        }
        if fresh_numbers(field_slots(candidate, history, k)).contains(n) {
            let i = choose|i: int| 0 <= i < field_slots(candidate, history, k).len()
                && field_slots(candidate, history, k)[i] == implementation::SlotView::Fresh(n);
            if i > 0 { assert(history[i - 1][k] == implementation::SlotView::Fresh(n)); }
        }
    }
    lemma_slot_event(c, result, candidate, f, candidate, history);
    assert forall|i: int| 0 <= i < history.len() implies covered_event(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f)[i])
        && numeric_event(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f)[i])
            == implementation::slots_event(history[i], numeric_fresh(c)) by {
        lemma_slot_event(c, result, history[i], f, candidate, history);
    }
    assert(numeric_history(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f))
        =~= history.map(|i: int, slots: Seq<implementation::SlotView>| implementation::slots_event(slots, numeric_fresh(c))));
    assert forall|k: int| 0 <= k < 3 implies implementation::slot_value(candidate[k], numeric_fresh(c)) <= u64::MAX by {
        match candidate[k] { implementation::SlotView::Fresh(n) => {}, implementation::SlotView::Code(v) => {} }
    }
    lemma_numeric_fresh(c);
    result
}

/// The two source equations compose before the parent attaches the compiled difference root.
pub(crate) proof fn lemma_source_failure<E: Event>(left: Rule<E>, right: Rule<E>,
    left_flat: FlatRule<ComponentValue<E>>, right_flat: FlatRule<ComponentValue<E>>,
    left_template: FlatPair<u64>, right_template: FlatPair<u64>, c: Constants<E>, coding: NatCoding<E>,
    candidate: tdsl::EventView<E::Principal, E::Action, E::Resource>, history: Seq<tdsl::EventView<E::Principal, E::Action, E::Resource>>)
    requires left.head@ == right.head@, fl::flattened(left, left_flat), fl::flattened(right, right_flat),
        enc::lowering(left_flat.source, left_template, views::constant_book(c), fl::component_equality::<E>()),
        enc::lowering(right_flat.source, right_template, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(left_flat.source, fl::component_domain::<E>()),
        enc::constants_in_domain(right_flat.source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book(c, coding), covered_event(coding, candidate),
        forall|i: int| 0 <= i < history.len() ==> covered_event(coding, history[i]),
    ensures analyzer::tail_fails(left.head@, left.tail@, right.tail@)(candidate, history) == (
        encoding::n_head_matches(template_head(left_template), numeric_event(coding, candidate))
        && numeric::source_regex(left_template, left_template.root as nat, numeric_event(coding, candidate), numeric_history(coding, history))
        && !numeric::source_regex(right_template, right_template.root as nat, numeric_event(coding, candidate), numeric_history(coding, history))),
{
    lemma_source_language(left, left_flat, left_template, c, coding, candidate, history);
    lemma_source_language(right, right_flat, right_template, c, coding, candidate, history);
}
}
