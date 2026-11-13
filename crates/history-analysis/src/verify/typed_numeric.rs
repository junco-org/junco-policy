//! Typed Eq-class embeddings into Nat and the analyzer's source-language bridge.
//!
//! Real constant books retain their u64 representation. These finite, per-field ghost codings
//! extend equality classes into Nat: the candidate is seeded before history classes, so only
//! its codes need the runtime's u64 bound. Histories remain mathematically unbounded.

use crate::analyzer::{Constants, PolicyAnalyzer};
use crate::verify::{self as views, frontend::*};
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::{analyzer, encoding, implementation, semantics};
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::arity;
use history_syntax::{Component, Event, Rule};
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

pub(crate) type NatCoding<E> = Seq<Seq<(<E as Event>::Component, nat)>>;

pub(crate) open spec fn native_eq<E: Event>() -> spec_fn(E::Component, E::Component) -> bool {
    |a: E::Component, b: E::Component| a.eq_spec(&b)
}

pub(crate) proof fn lemma_native_equivalence<E: Event>()
    requires views::analyzer_obligations::<E>(),
    ensures equivalence(native_eq::<E>()),
{}

pub(crate) open spec fn known_seed<E: Event>(c: Constants<E>, k: int) -> Seq<(E::Component, nat)> {
    views::constant_book(c)[k].map(|i: int, p: (E::Component, u64)| (p.0, p.1 as nat))
}

pub(crate) open spec fn fixes_book<E: Event>(c: Constants<E>, coding: NatCoding<E>) -> bool {
    1 <= coding.len() <= history_syntax::MAX_ARITY && coding.len() == arity::<E>()
        && forall|k: int| #![trigger coding[k]] 0 <= k < coding.len() ==> {
        &&& coding_wf(coding[k], native_eq::<E>())
        &&& forall|i: int| 0 <= i < known_seed::<E>(c, k).len() ==> coding[k][i] == known_seed::<E>(c, k)[i]
        &&& known_seed::<E>(c, k).len() <= coding[k].len()
    }
}

pub(crate) open spec fn covered_event<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>) -> bool {
    1 <= coding.len() <= history_syntax::MAX_ARITY && coding.len() == arity::<E>() && event.len() == coding.len()
        && forall|k: int| #![trigger coding[k]] 0 <= k < coding.len()
            ==> has_code(coding[k], native_eq::<E>(), event[k])
}

pub(crate) open spec fn code_value<E: Event>(coding: NatCoding<E>, field: Component, value: E::Component) -> nat {
    lookup_code(coding[portable::field_index(field)], native_eq::<E>(), value)
}

pub(crate) open spec fn numeric_event<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>) -> EventView {
    Seq::new(event.len(), |k: int| code_value::<E>(coding, enc::field_at(k), event[k]))
}

pub(crate) open spec fn numeric_history<E: Event>(coding: NatCoding<E>, history: Seq<Seq<E::Component>>) -> Seq<EventView> {
    history.map(|i: int, e: Seq<E::Component>| numeric_event::<E>(coding, e))
}

pub(crate) proof fn lemma_numeric_field<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>, field: Component)
    requires field.0 < event.len(),
    ensures language::field_value(numeric_event::<E>(coding, event), field)
        == code_value::<E>(coding, field, event[portable::field_index(field)]),
{}

proof fn lemma_known_seed<E: Event>(c: Constants<E>, k: int)
    requires constants_wf(c), views::analyzer_obligations::<E>(), 0 <= k < arity::<E>(),
    ensures coding_wf(known_seed::<E>(c, k), native_eq::<E>()),
        forall|i: int| 0 <= i < known_seed::<E>(c, k).len() ==> known_seed::<E>(c, k)[i].1 <= c.values@.len(),
{
    lemma_constants_maps(c);
    let field = enc::field_at(k);
    assert(portable::field_index(field) == k);
    lemma_field_book(c, field);
    assert forall|i: int| 0 <= i < known_seed::<E>(c, k).len() implies known_seed::<E>(c, k)[i].1 > 0
        && known_seed::<E>(c, k)[i].1 <= c.values@.len() by {
        lemma_field_entry_source::<E>(c.values@, field, i);
        let j = choose|j: int| 0 <= j < c.values@.len()
            && field_entries::<E>(c.values@, field)[i] == (c.values@[j], (j + 1) as u64);
        assert(known_seed::<E>(c, k)[i].1 == (j + 1) as nat);
    }
    assert forall|i: int, j: int| #![trigger known_seed::<E>(c, k)[i], known_seed::<E>(c, k)[j]]
        0 <= i < known_seed::<E>(c, k).len() && 0 <= j < known_seed::<E>(c, k).len()
        implies (native_eq::<E>()(known_seed::<E>(c, k)[i].0, known_seed::<E>(c, k)[j].0)
            == (known_seed::<E>(c, k)[i].1 == known_seed::<E>(c, k)[j].1)) by {
        assert(known_seed::<E>(c, k)[i].0 == views::constant_book(c)[k][i].0);
        assert(known_seed::<E>(c, k)[j].0 == views::constant_book(c)[k][j].0);
    }
}

pub(crate) proof fn lemma_pair_embedding<E: Event>(c: Constants<E>, candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>) -> (coding: NatCoding<E>)
    requires constants_wf(c), views::analyzer_obligations::<E>(),
        candidate.len() == arity::<E>(),
        forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len(),
    ensures fixes_book::<E>(c, coding), covered_event::<E>(coding, candidate),
        language::event_wf(numeric_event::<E>(coding, candidate), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> covered_event::<E>(coding, history[i]),
        numeric_history::<E>(coding, history).len() == history.len(),
{
    lemma_native_equivalence::<E>();
    lemma_constants_maps(c);
    assert(1 <= arity::<E>() <= history_syntax::MAX_ARITY);
    let eq = native_eq::<E>();
    let result = Seq::new(arity::<E>(), |k: int| {
        let seed = known_seed::<E>(c, k);
        let v = candidate[k];
        extend_codes(seed.push((v, new_code(seed, eq, v))),
            history.map(|i: int, e: Seq<E::Component>| e[k]), eq)
    });
    assert forall|k: int| #![trigger result[k]] 0 <= k < arity::<E>() implies {
        &&& coding_wf(result[k], eq)
        &&& known_seed::<E>(c, k).len() <= result[k].len()
        &&& forall|i: int| 0 <= i < known_seed::<E>(c, k).len() ==> result[k][i] == known_seed::<E>(c, k)[i]
        &&& has_code(result[k], eq, candidate[k])
        &&& lookup_code(result[k], eq, candidate[k]) <= u32::MAX + 1
        &&& forall|i: int| 0 <= i < history.len() ==> has_code(result[k], eq, history[i][k])
    } by {
        let seed = known_seed::<E>(c, k);
        let v = candidate[k];
        lemma_known_seed::<E>(c, k);
        lemma_max_code_bound(seed, u32::MAX as nat);
        lemma_seed_code_bound(seed, eq, v);
        let before = seed.push((v, new_code(seed, eq, v)));
        let vs = history.map(|i: int, e: Seq<E::Component>| e[k]);
        lemma_push_coding(seed, eq, v);
        lemma_extend_codes(before, vs, eq);
        assert(result[k] == extend_codes(before, vs, eq));
        assert(before.len() == seed.len() + 1);
        assert(result[k].len() == before.len() + vs.len());
        assert(result[k][seed.len() as int] == before[seed.len() as int]);
        assert(result[k][seed.len() as int].0 == v);
        assert(eq(v, v));
        assert(has_code(result[k], eq, v));
        assert forall|i: int| 0 <= i < seed.len() implies result[k][i] == seed[i] by {
            assert(result[k][i] == before[i]);
        }
        assert forall|i: int| 0 <= i < history.len()
            implies has_code(result[k], eq, history[i][k]) by {
            assert(vs[i] == history[i][k]);
            assert(has_code(result[k], eq, vs[i]));
        }
        lemma_prefix_coding_stable(before, result[k], eq, v, seed.len() as int);
    }
    assert forall|k: int| #![trigger numeric_event::<E>(result, candidate)[k]] 0 <= k < candidate.len() implies
        numeric_event::<E>(result, candidate)[k] <= u64::MAX by {
        assert(enc::field_at(k).0 as int == k);
        assert(lookup_code(result[k], eq, candidate[k]) <= u32::MAX + 1);
        lemma_numeric_field::<E>(result, candidate, enc::field_at(k));
    }
    assert forall|i: int| #![trigger covered_event::<E>(result, history[i])]
        0 <= i < history.len() implies covered_event::<E>(result, history[i]) by {
        assert(history[i].len() == result.len());
        assert forall|k: int| #![trigger result[k]] 0 <= k < result.len() implies
            has_code(result[k], eq, history[i][k]) by {
            assert(forall|j: int| 0 <= j < history.len() ==> has_code(result[k], eq, history[j][k]));
        }
    }
    result
}

pub(crate) proof fn lemma_fixed_code<E: Event>(c: Constants<E>, coding: NatCoding<E>, field: Component, value: E::Component, id: u64)
    requires views::analyzer_obligations::<E>(), fixes_book::<E>(c, coding),
        enc::encoded(views::constant_book(c), fl::component_equality::<E>(), field, value, id),
    ensures has_code(coding[portable::field_index(field)], native_eq::<E>(), value),
        code_value::<E>(coding, field, value) == id as nat,
{
    lemma_native_equivalence::<E>();
    let k = portable::field_index(field);
    let i = choose|i: int| 0 <= i < views::constant_book(c)[k].len()
        && views::constant_book(c)[k][i].1 == id
        && fl::component_equality::<E>()(field, value, views::constant_book(c)[k][i].0);
    let rep = views::constant_book(c)[k][i].0;
    assert(rep == coding[k][i].0);
    assert(native_eq::<E>()(coding[k][i].0, value));
    lemma_lookup_code(coding[k], native_eq::<E>(), value, i);
}

pub(crate) open spec fn flat_event_encoded<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>, n: EventView) -> bool {
    1 <= coding.len() <= history_syntax::MAX_ARITY && coding.len() == arity::<E>()
        && event.len() == coding.len() && n.len() == event.len()
        && forall|k: int| #![trigger event[k]] 0 <= k < event.len() ==> {
        &&& has_code(coding[k], native_eq::<E>(), event[k])
        &&& language::field_value(n, enc::field_at(k)) == lookup_code(coding[k], native_eq::<E>(), event[k])
    }
}

proof fn lemma_flat_encoded_field<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>, n: EventView, field: Component)
    requires flat_event_encoded::<E>(coding, event, n), field.0 < event.len(),
    ensures
        has_code(coding[portable::field_index(field)], native_eq::<E>(), event[portable::field_index(field)]),
        language::field_value(n, field) == code_value::<E>(coding, field, event[portable::field_index(field)]),
{}

pub(crate) proof fn lemma_typed_event_encoded<E: Event>(coding: NatCoding<E>, event: Seq<E::Component>)
    requires covered_event::<E>(coding, event),
    ensures flat_event_encoded::<E>(coding, event, numeric_event::<E>(coding, event)),
{
    assert forall|k: int| #![trigger coding[k]] 0 <= k < arity::<E>() implies {
        &&& enc::field_at(k).0 == k
        &&& has_code(coding[k], native_eq::<E>(), event[k])
        &&& language::field_value(numeric_event::<E>(coding, event), enc::field_at(k))
            == lookup_code(coding[k], native_eq::<E>(), event[k])
    } by { lemma_numeric_field::<E>(coding, event, enc::field_at(k)); }
}

proof fn lemma_reflect_component<E: Event>(coding: NatCoding<E>, field: Component, a: E::Component, b: E::Component)
    requires views::analyzer_obligations::<E>(), coding.len() == arity::<E>(),
        field.0 < coding.len(),
        coding_wf(coding[portable::field_index(field)], native_eq::<E>()),
        has_code(coding[portable::field_index(field)], native_eq::<E>(), a),
        has_code(coding[portable::field_index(field)], native_eq::<E>(), b),
    ensures fl::component_equality::<E>()(field, a, b) == (code_value::<E>(coding, field, a) == code_value::<E>(coding, field, b)),
        native_eq::<E>()(a, b) == (code_value::<E>(coding, field, a) == code_value::<E>(coding, field, b)),
{
    lemma_native_equivalence::<E>();
    let es = coding[portable::field_index(field)];
    let eq = native_eq::<E>();
    let i = choose|i: int| 0 <= i < es.len() && eq(es[i].0, a);
    let j = choose|j: int| 0 <= j < es.len() && eq(es[j].0, b);
    lemma_coding_reflects_eq(es, eq, a, b, i, j);
}

proof fn lemma_flat_source_test<E: Event>(source: FlatPair<E::Component>, target: FlatPair<u64>, id: nat,
    c: Constants<E>, coding: NatCoding<E>, request: Seq<E::Component>, theta: Subst,
    event: Seq<E::Component>, n: EventView)
    requires portable::structural_wf(source), id < source.tests@.len(),
        request.len() == source.head@.len(),
        enc::lowering(source, target, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book::<E>(c, coding),
        flat_event_encoded::<E>(coding, request, theta), flat_event_encoded::<E>(coding, event, n),
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
            lemma_fixed_code::<E>(c, coding, field, value, code);
            let k = portable::field_index(field);
            assert(enc::field_at(k) == field);
            lemma_flat_encoded_field::<E>(coding, event, n, field);
            lemma_reflect_component::<E>(coding, field, event[k], value);
        },
        (FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. }, _) => {
            assert(field == variable);
            let k = portable::field_index(field);
            assert(enc::field_at(k) == field);
            lemma_flat_encoded_field::<E>(coding, event, n, field);
            lemma_flat_encoded_field::<E>(coding, request, theta, field);
            lemma_reflect_component::<E>(coding, field, event[k], request[k]);
        },
        (FlatTest::And(children), _) | (FlatTest::Or(children), _) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                portable::test_sem(source.tests@, children@[i] as nat, request, event, fl::component_equality::<E>())
                    == numeric::source_test(target, children@[i] as nat, theta, n) by {
                lemma_flat_source_test::<E>(source, target, children@[i] as nat, c, coding, request, theta, event, n);
            }
        },
        _ => {},
    }
}

proof fn lemma_flat_source_regex<E: Event>(source: FlatPair<E::Component>, target: FlatPair<u64>, id: nat,
    c: Constants<E>, coding: NatCoding<E>, request: Seq<E::Component>, theta: Subst,
    word: Seq<Seq<E::Component>>, w: Seq<EventView>)
    requires portable::structural_wf(source), id < source.regexes@.len(),
        request.len() == source.head@.len(),
        enc::lowering(source, target, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book::<E>(c, coding),
        flat_event_encoded::<E>(coding, request, theta),
        enc::pointwise(word, w, |e: Seq<E::Component>, n: EventView| flat_event_encoded::<E>(coding, e, n)),
    ensures portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>())
        == numeric::source_regex(target, id, theta, w),
    decreases id,
{
    reveal_with_fuel(portable::lang, 1);
    reveal_with_fuel(numeric::source_regex, 1);
    assert(portable::regex_wf(source.regexes@[id as int], id, source.tests@.len()));
    assert(enc::regex_same(source.regexes@[id as int], target.regexes@[id as int]));
    let rel = |e: Seq<E::Component>, n: EventView| flat_event_encoded::<E>(coding, e, n);
    let rev = |n: EventView, e: Seq<E::Component>| flat_event_encoded::<E>(coding, e, n);
    assert forall|i: int| 0 <= i < word.len() implies portable::event_wf(word[i], request.len()) by {}
    match source.regexes@[id as int] {
        FlatRegex::Test(test) => {
            if word.len() == 1 { lemma_flat_source_test::<E>(source, target, test as nat, c, coding, request, theta, word[0], w[0]); }
        },
        FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, word, fl::component_equality::<E>())
                    == numeric::source_regex(target, children@[i] as nat, theta, w) by {
                lemma_flat_source_regex::<E>(source, target, children@[i] as nat, c, coding, request, theta, word, w);
            }
        },
        FlatRegex::Complement(child) => { lemma_flat_source_regex::<E>(source, target, child as nat, c, coding, request, theta, word, w); },
        FlatRegex::Concat(children) => {
            if portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<E::Component>>>| parts.len() == children@.len() && word == parts.flatten()
                    && forall|i: int| 0 <= i < children@.len() ==> portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, parts[i], fl::component_equality::<E>());
                assert(enc::pointwise(w, word, rev));
                enc::lemma_partition_lift(w, word, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && w == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < children@.len() implies children@[i] < id
                    && numeric::source_regex(target, children@[i] as nat, theta, lifted[i]) by {
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_flat_source_regex::<E>(source, target, children@[i] as nat, c, coding, request, theta, parts[i], lifted[i]);
                }
            }
            if numeric::source_regex(target, id, theta, w) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children@.len() && w == parts.flatten()
                    && forall|i: int| 0 <= i < children@.len() ==> children@[i] < id && numeric::source_regex(target, children@[i] as nat, theta, parts[i]);
                enc::lemma_partition_lift(word, w, parts, rel);
                let lifted = choose|lifted: Seq<Seq<Seq<E::Component>>>| lifted.len() == parts.len() && word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < children@.len() implies
                    portable::lang(source.tests@, source.regexes@, children@[i] as nat, request, lifted[i], fl::component_equality::<E>()) by {
                    lemma_flat_source_regex::<E>(source, target, children@[i] as nat, c, coding, request, theta, lifted[i], parts[i]);
                }
            }
        },
        FlatRegex::Star(child) => {
            if portable::lang(source.tests@, source.regexes@, id, request, word, fl::component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<E::Component>>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> portable::lang(source.tests@, source.regexes@, child as nat, request, parts[i], fl::component_equality::<E>());
                assert(enc::pointwise(w, word, rev));
                enc::lemma_partition_lift(w, word, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| w == lifted.flatten() && lifted.len() == parts.len()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < parts.len() implies numeric::source_regex(target, child as nat, theta, lifted[i]) by {
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_flat_source_regex::<E>(source, target, child as nat, c, coding, request, theta, parts[i], lifted[i]);
                }
            }
            if numeric::source_regex(target, id, theta, w) {
                let parts = choose|parts: Seq<Seq<EventView>>| w == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> numeric::source_regex(target, child as nat, theta, parts[i]);
                enc::lemma_partition_lift(word, w, parts, rel);
                let lifted = choose|lifted: Seq<Seq<Seq<E::Component>>>| word == lifted.flatten() && lifted.len() == parts.len()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < parts.len() implies
                    portable::lang(source.tests@, source.regexes@, child as nat, request, lifted[i], fl::component_equality::<E>()) by {
                    lemma_flat_source_regex::<E>(source, target, child as nat, c, coding, request, theta, lifted[i], parts[i]);
                }
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_source_language<E: Event>(rule: Rule<E>, flat: FlatRule<E::Component>, template: FlatPair<u64>,
    c: Constants<E>, coding: NatCoding<E>, candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>)
    requires fl::flattened(rule, flat), enc::lowering(flat.source, template, views::constant_book(c), fl::component_equality::<E>()),
        candidate.len() == rule.head@.len(),
        enc::constants_in_domain(flat.source, fl::component_domain::<E>()), constants_wf(c), views::analyzer_obligations::<E>(),
        fixes_book::<E>(c, coding), covered_event::<E>(coding, candidate),
        forall|i: int| 0 <= i < history.len() ==> covered_event::<E>(coding, history[i]),
    ensures tdsl::lang(rule.tail@, rule.head@, candidate, history)
        == numeric::source_regex(template, template.root as nat, numeric_event::<E>(coding, candidate), numeric_history::<E>(coding, history)),
        tdsl::head_matches(rule.head@, candidate) == encoding::n_head_matches(template_head(template), numeric_event::<E>(coding, candidate)),
{
    fl::flattening_preserves_semantics(rule, flat, candidate, history);
    lemma_typed_event_encoded::<E>(coding, candidate);
    let word = history;
    let w = numeric_history::<E>(coding, history);
    assert forall|i: int| 0 <= i < history.len() implies flat_event_encoded::<E>(coding, word[i], w[i]) by {
        lemma_typed_event_encoded::<E>(coding, history[i]);
    }
    lemma_flat_source_regex::<E>(flat.source, template, flat.source.root as nat, c, coding, candidate, numeric_event::<E>(coding, candidate), word, w);
    lemma_constants_maps(c);
    assert forall|k: int| 0 <= k < candidate.len() implies match #[trigger] flat.source.head@[k] {
        FlatHead::Constant(v) => fl::component_equality::<E>()(enc::field_at(k), candidate[k], v)
            == (numeric_event::<E>(coding, candidate)[k] == template_head(template)[k]->Some_0),
        _ => true,
    } by {
        let field = enc::field_at(k);
        assert(portable::field_index(field) == k);
        if let FlatHead::Constant(v) = flat.source.head@[k] {
            let id = match template.head@[k] { FlatHead::Constant(id) => id, _ => arbitrary() };
            lemma_fixed_code::<E>(c, coding, field, v, id);
            lemma_reflect_component::<E>(coding, field, candidate[k], v);
            lemma_numeric_field::<E>(coding, candidate, field);
        }
    }
}

pub(crate) open spec fn template_head(template: FlatPair<u64>) -> encoding::NHead {
    template.head@.map(|i: int, h: FlatHead<u64>| encoding::head_code(h))
}

/// Native books contain tagged constants, but abstract typed events may contain any component
/// value. Equality is reflected by a coordinate's book without imposing a tag on that value.
proof fn lemma_domain_coordinate<E: Event>(a: PolicyAnalyzer<E>, coding: NatCoding<E>,
    event: Seq<E::Component>, k: int)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(),
        fixes_book::<E>(a.constants, coding), covered_event::<E>(coding, event),
        0 <= k < event.len(),
    ensures semantics::in_domain(a@.domains[k], event[k]) == match views::domain_view(a.universes[k]) {
        None => true, Some(ids) => ids.contains(numeric_event::<E>(coding, event)[k]),
    },
{
    let c = a.constants;
    let field = enc::field_at(k);
    lemma_constants_maps(c);
    lemma_native_equivalence::<E>();
    lemma_numeric_field::<E>(coding, event, field);
    if let Some(raw) = a.universes[k] {
        views::lemma_codes((*raw)@);
        let selected = (*raw)@.to_set().map(|id: u32| c.values@[id as int - 1]);
        let domain = selected;
        assert(a@.domains[k] == Some(domain));
        if semantics::in_domain(a@.domains[k], event[k]) {
            let rep = choose|rep: E::Component| domain.contains(rep) && event[k].eq_spec(&rep);
            let id = choose|id: u32| (*raw)@.to_set().contains(id) && c.values@[id as int - 1] == rep;
            let j = choose|j: int| 0 <= j < (*raw)@.len() && (*raw)@[j] == id;
            assert(stored_code(c, rep, id));
            lemma_stored_encoded(c, rep, id);
            lemma_fixed_code::<E>(c, coding, field, rep, id as u64);
            lemma_reflect_component::<E>(coding, field, event[k], rep);
            assert(views::codes((*raw)@).contains(id as nat));
        }
        if views::codes((*raw)@).contains(code_value::<E>(coding, field, event[k])) {
            let j = choose|j: int| 0 <= j < (*raw)@.len()
                && (*raw)@[j] as nat == code_value::<E>(coding, field, event[k]);
            let id = (*raw)@[j];
            let rep = c.values@[id as int - 1];
            assert((*raw)@.to_set().contains(id));
            assert(selected.contains(rep));
            assert(value_field::<E>(rep) == field);
            assert(domain.contains(rep));
            lemma_stored_encoded(c, rep, id);
            lemma_fixed_code::<E>(c, coding, field, rep, id as u64);
            lemma_reflect_component::<E>(coding, field, event[k], rep);
            assert(event[k].eq_spec(&rep));
        }
    }
}

pub(crate) proof fn lemma_domain_event<E: Event>(a: PolicyAnalyzer<E>, coding: NatCoding<E>, event: Seq<E::Component>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), fixes_book::<E>(a.constants, coding), covered_event::<E>(coding, event),
    ensures semantics::event_in(a@.domains, event)
        == encoding::n_event_in(views::ndomains(a.universes), numeric_event::<E>(coding, event)),
{
    let domains = a@.domains;
    let numeric_domains = views::ndomains(a.universes);
    let n = numeric_event::<E>(coding, event);
    assert(domains.len() == event.len());
    assert(numeric_domains.len() == event.len());
    assert(n.len() == event.len());
    assert(1 <= event.len() <= history_syntax::MAX_ARITY);
    assert forall|k: int| #![trigger domains[k]] #![trigger numeric_domains[k]]
        0 <= k < event.len() implies
        semantics::in_domain(domains[k], event[k]) == match numeric_domains[k] {
            None => true, Some(ids) => ids.contains(n[k]),
        } by {
        assert(numeric_domains[k] == views::domain_view(a.universes[k]));
        lemma_domain_coordinate::<E>(a, coding, event, k);
    }
    if semantics::event_in(domains, event) {
        assert forall|k: int| #![trigger numeric_domains[k]] 0 <= k < numeric_domains.len() implies
            (numeric_domains[k] matches Some(values) ==> values.contains(n[k])) by {
            assert(semantics::in_domain(domains[k], event[k]));
        }
        assert(encoding::n_event_in(numeric_domains, n));
    }
    if encoding::n_event_in(numeric_domains, n) {
        assert forall|k: int| #![trigger domains[k]] 0 <= k < domains.len() implies
            semantics::in_domain(domains[k], event[k]) by {
            match numeric_domains[k] {
                None => {},
                Some(values) => { assert(values.contains(n[k])); },
            }
        }
        assert(semantics::event_in(domains, event));
    }
}

pub(crate) proof fn lemma_analyzer_domain_embedding<E: Event>(a: PolicyAnalyzer<E>, coding: NatCoding<E>, candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>)
    requires analyzer_state_wf(a), views::analyzer_obligations::<E>(), fixes_book::<E>(a.constants, coding),
        covered_event::<E>(coding, candidate), language::event_wf(numeric_event::<E>(coding, candidate), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> covered_event::<E>(coding, history[i]),
        semantics::event_in(a@.domains, candidate), semantics::history_in(a@.domains, history),
    ensures encoding::n_theta_ok(views::ndomains(a.universes), numeric_event::<E>(coding, candidate)),
        encoding::n_history_in(views::ndomains(a.universes), numeric_history::<E>(coding, history)),
{
    lemma_domain_event::<E>(a, coding, candidate);
    assert forall|i: int| 0 <= i < history.len() implies encoding::n_event_in(views::ndomains(a.universes), numeric_history::<E>(coding, history)[i]) by {
        lemma_domain_event::<E>(a, coding, history[i]);
    }
}

pub(crate) open spec fn numeric_fresh<E: Event>(c: Constants<E>) -> spec_fn(nat) -> nat {
    |n: nat| c.values@.len() + n + 1
}

pub(crate) proof fn lemma_numeric_fresh<E: Event>(c: Constants<E>)
    ensures implementation::fresh_codes_ok(numeric_fresh::<E>(c), views::reconstruction::known_codes(c)),
{
    assert forall|n: nat| !#[trigger] views::reconstruction::known_codes(c).contains(numeric_fresh::<E>(c)(n)) by {
        let s = Seq::new(c.values@.len(), |i: int| (i + 1) as nat);
        if s.to_set().contains(numeric_fresh::<E>(c)(n)) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == numeric_fresh::<E>(c)(n);
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


proof fn lemma_fresh_admissible<E: Event>(a: PolicyAnalyzer<E>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>,
    f: analyzer::FreshChoice<E::Component>, k: int)
    requires constants_wf(a.constants), views::analyzer_obligations::<E>(), 0 <= k < arity::<E>(),
        views::reconstruction::slot_wf(a.constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> views::reconstruction::slot_wf(a.constants, history[i]),
        analyzer::admissible(a@, views::reconstruction::cex_of_slots(a.constants, candidate, history), f),
    ensures coding_wf(known_seed::<E>(a.constants, k) + fresh_numbers(field_slots(candidate, history, k)).map(
        |i: int, n: nat| (f[k](n), numeric_fresh::<E>(a.constants)(n))), native_eq::<E>()),
{
    let c = a.constants;
    let numbers = fresh_numbers(field_slots(candidate, history, k));
    lemma_fresh_numbers(field_slots(candidate, history, k));
    views::reconstruction::lemma_used_at(c, candidate, history);
    lemma_known_seed::<E>(c, k);
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
    assert forall|i: int, j: int| #![trigger numbers[i], known_seed::<E>(c, k)[j]]
        0 <= i < numbers.len() && 0 <= j < known_seed::<E>(c, k).len()
        implies !native_eq::<E>()(f[k](numbers[i]), known_seed::<E>(c, k)[j].0) by {
        let field = enc::field_at(k);
        lemma_field_book(c, field);
        lemma_field_entry_source::<E>(c.values@, field, j);
        let rep = known_seed::<E>(c, k)[j].0;
        assert(c.values@.to_set().contains(rep));
        assert(E::coordinate_spec(rep) == k);
        vstd::set::lemma_set_filter(c.values@.to_set(), |v: E::Component| E::coordinate_spec(v) == k, rep);
        assert(a@.known[k].contains(rep));
    }
    assert forall|i: int, j: int| #![trigger numbers[i], numbers[j]]
        0 <= i < numbers.len() && 0 <= j < numbers.len() && numbers[i] != numbers[j]
        implies !native_eq::<E>()(f[k](numbers[i]), f[k](numbers[j])) by {
        assert(analyzer::choice_ok(f[k], analyzer::fresh_used(
            views::reconstruction::cex_of_slots(c, candidate, history), k), a@.known[k], a@.domains[k]));
    }
    lemma_fresh_coding(known_seed::<E>(c, k), numbers, native_eq::<E>(), f[k], c.values@.len());
}

proof fn lemma_slot_event<E: Event>(c: Constants<E>, coding: NatCoding<E>, slots: Seq<implementation::SlotView>,
    f: analyzer::FreshChoice<E::Component>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>)
    requires constants_wf(c), views::analyzer_obligations::<E>(), fixes_book::<E>(c, coding), views::reconstruction::slot_wf(c, slots),
        f.len() == slots.len(),
        forall|k: int| #![trigger slots[k]] 0 <= k < arity::<E>() ==> (slots[k] matches implementation::SlotView::Fresh(n)
            ==> fresh_numbers(field_slots(candidate, history, k)).contains(n)),
        forall|k: int| #![trigger coding[k]] 0 <= k < arity::<E>() ==> coding[k] == known_seed::<E>(c, k)
            + fresh_numbers(field_slots(candidate, history, k)).map(|i: int, n: nat| (f[k](n), numeric_fresh::<E>(c)(n))),
    ensures covered_event::<E>(coding, analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f)),
        numeric_event::<E>(coding, analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f))
            == implementation::slots_event(slots, numeric_fresh::<E>(c)),
{
    lemma_constants_maps(c);
    lemma_native_equivalence::<E>();
    let event = analyzer::event_of(views::reconstruction::components_of_slots(c, slots), f);
    assert forall|k: int| #![trigger coding[k]] 0 <= k < arity::<E>() implies has_code(coding[k], native_eq::<E>(), event[k])
        && language::field_value(numeric_event::<E>(coding, event), enc::field_at(k)) == implementation::slot_value(slots[k], numeric_fresh::<E>(c)) by {
        lemma_numeric_field::<E>(coding, event, enc::field_at(k));
        match slots[k] {
            implementation::SlotView::Code(v) => {
                let value = c.values@[v as int - 1];
                assert(value_field::<E>(value) == enc::field_at(k));
                assert(event[k] == value);
                lemma_stored_encoded(c, value, v as u32);
                lemma_fixed_code::<E>(c, coding, enc::field_at(k), value, v as u64);
            },
            implementation::SlotView::Fresh(n) => {
                let ns = fresh_numbers(field_slots(candidate, history, k));
                let i = choose|i: int| 0 <= i < ns.len() && ns[i] == n;
                let j = known_seed::<E>(c, k).len() as int + i;
                assert(coding[k][j] == (f[k](n), numeric_fresh::<E>(c)(n)));
                assert(event[k] == f[k](n));
                lemma_lookup_code(coding[k], native_eq::<E>(), event[k], j);
            },
        }
    }
    assert(numeric_event::<E>(coding, event) =~= implementation::slots_event(slots, numeric_fresh::<E>(c)));
}

pub(crate) proof fn lemma_slot_embedding<E: Event>(a: PolicyAnalyzer<E>, candidate: Seq<implementation::SlotView>, history: Seq<Seq<implementation::SlotView>>,
    f: analyzer::FreshChoice<E::Component>) -> (coding: NatCoding<E>)
    requires constants_wf(a.constants), views::analyzer_obligations::<E>(), views::reconstruction::slot_wf(a.constants, candidate),
        forall|i: int| 0 <= i < history.len() ==> views::reconstruction::slot_wf(a.constants, history[i]),
        forall|k: int| #![trigger candidate[k]] 0 <= k < arity::<E>() ==> (candidate[k] matches implementation::SlotView::Fresh(n) ==> n < arity::<E>()),
        analyzer::admissible(a@, views::reconstruction::cex_of_slots(a.constants, candidate, history), f),
    ensures fixes_book::<E>(a.constants, coding),
        covered_event::<E>(coding, analyzer::event_of(views::reconstruction::cex_of_slots(a.constants, candidate, history).candidate, f)),
        numeric_event::<E>(coding, analyzer::event_of(views::reconstruction::cex_of_slots(a.constants, candidate, history).candidate, f))
            == implementation::slots_event(candidate, numeric_fresh::<E>(a.constants)),
        language::event_wf(implementation::slots_event(candidate, numeric_fresh::<E>(a.constants)), arity::<E>()),
        forall|i: int| 0 <= i < history.len() ==> covered_event::<E>(coding, analyzer::history_of(views::reconstruction::cex_of_slots(a.constants, candidate, history), f)[i]),
        numeric_history::<E>(coding, analyzer::history_of(views::reconstruction::cex_of_slots(a.constants, candidate, history), f))
            == history.map(|i: int, slots: Seq<implementation::SlotView>| implementation::slots_event(slots, numeric_fresh::<E>(a.constants))),
        implementation::fresh_codes_ok(numeric_fresh::<E>(a.constants), views::reconstruction::known_codes(a.constants)),
{
    let c = a.constants;
    let result = Seq::new(arity::<E>(), |k: int| known_seed::<E>(c, k) + fresh_numbers(field_slots(candidate, history, k)).map(
        |i: int, n: nat| (f[k](n), numeric_fresh::<E>(c)(n))));
    assert forall|k: int| #![trigger result[k]] 0 <= k < arity::<E>() implies coding_wf(result[k], native_eq::<E>())
        && known_seed::<E>(c, k).len() <= result[k].len()
        && forall|j: int| 0 <= j < known_seed::<E>(c, k).len() ==> result[k][j] == known_seed::<E>(c, k)[j] by {
        lemma_fresh_admissible::<E>(a, candidate, history, f, k);
        lemma_fresh_numbers(field_slots(candidate, history, k));
    }
    assert forall|k: int, n: nat| #![trigger fresh_numbers(field_slots(candidate, history, k)).contains(n)]
        0 <= k < arity::<E>() implies fresh_numbers(field_slots(candidate, history, k)).contains(n)
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
    lemma_slot_event::<E>(c, result, candidate, f, candidate, history);
    assert forall|i: int| 0 <= i < history.len() implies covered_event::<E>(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f)[i])
        && numeric_event::<E>(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f)[i])
            == implementation::slots_event(history[i], numeric_fresh::<E>(c)) by {
        lemma_slot_event::<E>(c, result, history[i], f, candidate, history);
    }
    assert(numeric_history::<E>(result, analyzer::history_of(views::reconstruction::cex_of_slots(c, candidate, history), f))
        =~= history.map(|i: int, slots: Seq<implementation::SlotView>| implementation::slots_event(slots, numeric_fresh::<E>(c))));
    assert forall|k: int| 0 <= k < arity::<E>() implies implementation::slot_value(candidate[k], numeric_fresh::<E>(c)) <= u64::MAX by {
        match candidate[k] { implementation::SlotView::Fresh(n) => {}, implementation::SlotView::Code(v) => {} }
    }
    lemma_numeric_fresh::<E>(c);
    result
}

/// The two source equations compose before the parent attaches the compiled difference root.
pub(crate) proof fn lemma_source_failure<E: Event>(left: Rule<E>, right: Rule<E>,
    left_flat: FlatRule<E::Component>, right_flat: FlatRule<E::Component>,
    left_template: FlatPair<u64>, right_template: FlatPair<u64>, c: Constants<E>, coding: NatCoding<E>,
    candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>)
    requires left.head@ == right.head@, fl::flattened(left, left_flat), fl::flattened(right, right_flat),
        enc::lowering(left_flat.source, left_template, views::constant_book(c), fl::component_equality::<E>()),
        enc::lowering(right_flat.source, right_template, views::constant_book(c), fl::component_equality::<E>()),
        enc::constants_in_domain(left_flat.source, fl::component_domain::<E>()),
        enc::constants_in_domain(right_flat.source, fl::component_domain::<E>()),
        constants_wf(c), views::analyzer_obligations::<E>(), fixes_book::<E>(c, coding), covered_event::<E>(coding, candidate),
        candidate.len() == left.head@.len(),
        forall|i: int| 0 <= i < history.len() ==> covered_event::<E>(coding, history[i]),
    ensures analyzer::tail_fails(left.head@, left.tail@, right.tail@)(candidate, history) == (
        encoding::n_head_matches(template_head(left_template), numeric_event::<E>(coding, candidate))
        && numeric::source_regex(left_template, left_template.root as nat, numeric_event::<E>(coding, candidate), numeric_history::<E>(coding, history))
        && !numeric::source_regex(right_template, right_template.root as nat, numeric_event::<E>(coding, candidate), numeric_history::<E>(coding, history))),
{
    lemma_source_language::<E>(left, left_flat, left_template, c, coding, candidate, history);
    lemma_source_language::<E>(right, right_flat, right_template, c, coding, candidate, history);
}
}
