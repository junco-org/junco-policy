//! Policy-reduction theorems and tag-preserving genericity over real events.
//!
//! Denotation, policy questions, and finite structural constants are canonical R2/R3
//! definitions, privately imported here rather than exposed through compatibility paths.
use alloc::boxed::Box;
use history_syntax::spec::events::{
    EventSpec, HeadView, PatternView, RegexView, TestView, arity, event_view, projection_laws,
    surjectivity, well_tagged,
};
use history_syntax::syntax::RuleMode;
use history_syntax::{Event, Rule};
use junco_core::spec::questions::{
    Domains, constants_union, covers, in_domains, lemma_constants_union,
    lemma_regex_constants_index, lemma_test_constants_index, pattern_constant, refines,
    regex_constants, rule_constants, test_constants,
};
use junco_core::spec::semantics::{
    head_matches, lang, policy_denies, rule_violated, rule_wf, test_sem,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Boolean mode utility used by numeric semantics, not a second typed denial predicate.
pub open spec fn violated_by(mode: RuleMode, inside: bool) -> bool {
    match mode { RuleMode::Require => !inside, RuleMode::Forbid => inside }
}

/// `P ⊑ Q` iff `P` covers every rule of `Q` (appendix `app:policy-reduction`).
pub open spec fn stmt_refines_iff_covers<E: Event>() -> bool {
    forall|domains: Domains<E::Component>, p: Seq<Rule<E>>, q: Seq<Rule<E>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
}

/// Appending a covered rule changes no real-event decision (appendix `app:policy-reduction`).
pub open spec fn stmt_redundant_iff_covered<E: Event>() -> bool {
    forall|domains: Domains<E::Component>, others: Seq<Rule<E>>, rule: Rule<E>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: E, history: Seq<E>|
            in_domains(domains, candidate, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
}

/// Equality on used values and comparisons with the fixed constants are preserved.
pub open spec fn renaming_preserves<C: PartialEq>(f: spec_fn(C) -> C, fixed: Set<C>, values: ISet<C>) -> bool {
    &&& forall|x: C, y: C| values.contains(x) && values.contains(y) ==> (#[trigger] f(x).eq_spec(&#[trigger] f(y)) == x.eq_spec(&y))
    &&& forall|x: C, k: C| values.contains(x) && fixed.contains(k) ==> (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k))
}

/// Coordinate renamings never move values to another tagged carrier.
pub open spec fn tags_preserved<E: Event>(f: Seq<spec_fn(E::Component) -> E::Component>) -> bool {
    f.len() == arity::<E>() && forall|i: int, value: E::Component|
        0 <= i < f.len() && E::coordinate_spec(value) == i
            ==> E::coordinate_spec(#[trigger] f[i](value)) == i
}

/// The real event represented by a coordinate-renamed projection.
pub open spec fn rename_event<E: Event>(f: Seq<spec_fn(E::Component) -> E::Component>, e: E) -> E {
    choose|renamed: E| event_view(renamed)
        == Seq::new(arity::<E>(), |i: int| f[i](event_view(e)[i]))
}

pub proof fn lemma_rename_event<E: Event>(f: Seq<spec_fn(E::Component) -> E::Component>, e: E)
    requires projection_laws::<E>(), surjectivity::<E>(), tags_preserved::<E>(f),
    ensures event_view(rename_event(f, e))
        == Seq::new(arity::<E>(), |i: int| f[i](event_view(e)[i])),
{
    let values = Seq::new(arity::<E>(), |i: int| f[i](event_view(e)[i]));
    assert(well_tagged::<E>(event_view(e)));
    assert(well_tagged::<E>(values));
    assert(exists|renamed: E| #[trigger] event_view(renamed) == values);
}

pub open spec fn rename_history<E: Event>(f: Seq<spec_fn(E::Component) -> E::Component>, h: Seq<E>) -> Seq<E> {
    h.map(|i: int, e: E| rename_event(f, e))
}

/// Values actually used at one coordinate of a real-event pair.
pub open spec fn pair_values<E: Event>(candidate: E, history: Seq<E>, coordinate: int) -> ISet<E::Component> {
    ISet::new(|x: E::Component| (0 <= coordinate < arity::<E>() && x == event_view(candidate)[coordinate])
        || exists|i: int| 0 <= i < history.len() && 0 <= coordinate < arity::<E>()
            && #[trigger] event_view(history[i])[coordinate] == x)
}

/// Tag-preserving, equality-preserving renamings preserve canonical rule violation.
/// R1 surjectivity realizes every renamed projection as an actual event.
pub open spec fn stmt_genericity<E: Event>() -> bool {
    forall|rule: Rule<E>, candidate: E, history: Seq<E>, f: Seq<spec_fn(E::Component) -> E::Component>|
        projection_laws::<E>() && surjectivity::<E>() && rule_wf(rule) && tags_preserved::<E>(f)
            && renamings_preserve(f, rule_constants(rule@),
                Seq::new(arity::<E>(), |i: int| pair_values(candidate, history, i)))
            ==> (rule_violated(rule, candidate, history)
                == #[trigger] rule_violated(rule, rename_event(f, candidate), rename_history(f, history)))
}



// ----- proofs -----

/// Appending a rule to a policy adds exactly that rule's denials.
pub proof fn lemma_policy_denies_push<E: Event>(
    policy: Seq<Rule<E>>, rule: Rule<E>, candidate: E, history: Seq<E>,
)
    ensures
        policy_denies(policy.push(rule), candidate, history)
            == (policy_denies(policy, candidate, history) || rule_violated(rule, candidate, history)),
{
    let q = policy.push(rule);
    if policy_denies(policy, candidate, history) {
        let i = choose|i: int| 0 <= i < policy.len() && #[trigger] rule_violated(policy[i], candidate, history);
        assert(q[i] == policy[i]);
        assert(rule_violated(q[i], candidate, history));
    }
    if rule_violated(rule, candidate, history) {
        let n = policy.len() as int;
        assert(q[n] == rule);
        assert(rule_violated(q[n], candidate, history));
    }
    if policy_denies(q, candidate, history) {
        let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_violated(q[i], candidate, history);
        if i < policy.len() {
            assert(q[i] == policy[i]);
            assert(rule_violated(policy[i], candidate, history));
        }
    }
}

pub proof fn theorem_refines_iff_covers<E: Event>()
    ensures stmt_refines_iff_covers::<E>(),
{
    assert forall|domains: Domains<E::Component>, p: Seq<Rule<E>>, q: Seq<Rule<E>>|
        #[trigger] refines(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i])
    by {
        if refines(domains, p, q) {
            assert forall|i: int| 0 <= i < q.len() implies covers(domains, p, #[trigger] q[i]) by {
                assert forall|candidate: E, history: Seq<E>|
                    in_domains(domains, candidate, history) && #[trigger] rule_violated(q[i], candidate, history)
                    implies policy_denies(p, candidate, history) by {
                    assert(policy_denies(q, candidate, history));
                }
            }
        }
        if forall|i: int| 0 <= i < q.len() ==> covers(domains, p, #[trigger] q[i]) {
            assert forall|candidate: E, history: Seq<E>|
                in_domains(domains, candidate, history) && !policy_denies(p, candidate, history)
                implies !#[trigger] policy_denies(q, candidate, history) by {
                if policy_denies(q, candidate, history) {
                    let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_violated(q[i], candidate, history);
                    assert(covers(domains, p, q[i]));
                }
            }
        }
    }
}

pub proof fn theorem_redundant_iff_covered<E: Event>()
    ensures stmt_redundant_iff_covered::<E>(),
{
    assert forall|domains: Domains<E::Component>, others: Seq<Rule<E>>, rule: Rule<E>|
        #[trigger] covers(domains, others, rule) <==> forall|candidate: E, history: Seq<E>|
            in_domains(domains, candidate, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
    by {
        if covers(domains, others, rule) {
            assert forall|candidate: E, history: Seq<E>|
                in_domains(domains, candidate, history)
                implies (#[trigger] policy_denies(others.push(rule), candidate, history)
                    == policy_denies(others, candidate, history)) by {
                lemma_policy_denies_push(others, rule, candidate, history);
            }
        }
        if forall|candidate: E, history: Seq<E>|
            in_domains(domains, candidate, history)
                ==> (#[trigger] policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history))
        {
            assert forall|candidate: E, history: Seq<E>|
                in_domains(domains, candidate, history) && #[trigger] rule_violated(rule, candidate, history)
                implies policy_denies(others, candidate, history) by {
                lemma_policy_denies_push(others, rule, candidate, history);
                assert(policy_denies(others.push(rule), candidate, history) == policy_denies(others, candidate, history));
            }
        }
    }
}

// ----- genericity -----

/// Every component lies in its corresponding value set, at exactly that arity.
pub open spec fn values_in<E: Event>(e: E, values: Seq<ISet<E::Component>>) -> bool {
    arity::<E>() == values.len() && forall|i: int| 0 <= i < arity::<E>()
        ==> #[trigger] values[i].contains(event_view(e)[i])
}

pub open spec fn word_values_in<E: Event>(w: Seq<E>, values: Seq<ISet<E::Component>>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] values_in(w[i], values)
}

pub open spec fn renamings_preserve<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, fixed: Seq<Set<C>>, values: Seq<ISet<C>>,
) -> bool {
    f.len() == fixed.len() && values.len() == fixed.len()
        && forall|i: int| 0 <= i < f.len() ==> renaming_preserves(#[trigger] f[i], fixed[i], values[i])
}

pub open spec fn rename_parts<E: Event>(f: Seq<spec_fn(E::Component) -> E::Component>, parts: Seq<Seq<E>>) -> Seq<Seq<E>> {
    parts.map(|i: int, part: Seq<E>| rename_history(f, part))
}

pub proof fn lemma_renaming_mono<T: PartialEq>(f: spec_fn(T) -> T, small: Set<T>, big: Set<T>, values: ISet<T>)
    requires
        renaming_preserves(f, big, values),
        forall|x: T| #[trigger] small.contains(x) ==> big.contains(x),
    ensures renaming_preserves(f, small, values),
{
    assert forall|x: T, k: T| values.contains(x) && small.contains(k)
        implies (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k)) by {
        assert(big.contains(k));
    }
}

pub proof fn lemma_renamings_mono<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, small: Seq<Set<C>>, big: Seq<Set<C>>, values: Seq<ISet<C>>,
)
    requires renamings_preserve(f, big, values), small.len() == big.len(),
        forall|i: int| 0 <= i < small.len() ==> #[trigger] small[i].subset_of(big[i]),
    ensures renamings_preserve(f, small, values),
{
    assert forall|i: int| 0 <= i < f.len() implies renaming_preserves(#[trigger] f[i], small[i], values[i]) by {
        assert(small[i].subset_of(big[i]));
        assert forall|x: C| #[trigger] small[i].contains(x) implies big[i].contains(x) by {}
        lemma_renaming_mono(f[i], small[i], big[i], values[i]);
    }
}

/// Canonical R2 tests are invariant under a realizable coordinate renaming.
pub proof fn lemma_test_rename<E: Event>(
    test: TestView<E::Component>, head: HeadView<E::Component>, candidate: E, event: E,
    f: Seq<spec_fn(E::Component) -> E::Component>, values: Seq<ISet<E::Component>>,
)
    requires projection_laws::<E>(), surjectivity::<E>(), tags_preserved::<E>(f),
        head.len() == arity::<E>(),
        renamings_preserve(f, test_constants(test, head.len()), values),
        values_in(candidate, values), values_in(event, values),
    ensures test_sem(test, head, rename_event(f, candidate), rename_event(f, event))
        == test_sem(test, head, candidate, event),
    decreases test,
{
    let rc = rename_event(f, candidate);
    let re = rename_event(f, event);
    lemma_rename_event(f, candidate);
    lemma_rename_event(f, event);
    reveal_with_fuel(test_sem, 1);
    match test {
        TestView::True | TestView::False => {},
        TestView::Atom { comparison, pattern } => {
            let j = pattern.component as int;
            if j < head.len() {
                lemma_test_constants_index(test, head.len(), j);
                assert(test_constants(test, head.len())[j] == pattern_constant(pattern.pattern));
                let c = event_view(candidate)[j];
                let e = event_view(event)[j];
                let fixed = test_constants(test, head.len())[j];
                assert(renaming_preserves(f[j], fixed, values[j]));
                assert(values[j].contains(c) && values[j].contains(e));
                match pattern.pattern {
                    PatternView::Constant(k) => {
                        assert(fixed.contains(k));
                        assert(f[j](e).eq_spec(&k) == e.eq_spec(&k));
                    },
                    PatternView::Variable(_) => {
                        assert(f[j](e).eq_spec(&f[j](c)) == e.eq_spec(&c));
                    },
                }
            }
        },
        TestView::And(cs) | TestView::Or(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                test_sem(cs[i], head, rc, re) == test_sem(cs[i], head, candidate, event) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] test_constants(cs[i], head.len())[j].subset_of(test_constants(test, head.len())[j]) by {
                    lemma_test_constants_index(test, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { test_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == test_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, test_constants(cs[i], head.len()), test_constants(test, head.len()), values);
                lemma_test_rename(cs[i], head, candidate, event, f, values);
            }
        },
    }
}

/// Renaming commutes with flattening.
pub proof fn lemma_flatten_rename<E: Event>(
    f: Seq<spec_fn(E::Component) -> E::Component>, parts: Seq<Seq<E>>,
)
    ensures rename_history(f, parts.flatten()) == rename_parts(f, parts).flatten(),
    decreases parts.len(),
{
    let rp = rename_parts(f, parts);
    if parts.len() == 0 {
        assert(rename_history(f, parts.flatten()) =~= rp.flatten());
    } else {
        lemma_flatten_rename(f, parts.drop_first());
        assert(rp.drop_first() =~= rename_parts(f, parts.drop_first()));
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(rename_history(f, a + b) =~= rename_history(f, a) + rename_history(f, b));
        assert(rp.first() == rename_history(f, a));
    }
}

/// A word whose renaming is split into parts splits into parts with those renamings.
pub proof fn lemma_unflatten_rename<E: Event>(
    f: Seq<spec_fn(E::Component) -> E::Component>, rparts: Seq<Seq<E>>,
    w: Seq<E>,
) -> (parts: Seq<Seq<E>>)
    requires rparts.flatten() == rename_history(f, w),
    ensures
        parts.len() == rparts.len(),
        parts.flatten() == w,
        forall|i: int| 0 <= i < parts.len() ==> rename_history(f, #[trigger] parts[i]) == rparts[i],
    decreases rparts.len(),
{
    if rparts.len() == 0 {
        assert(w =~= Seq::<E>::empty());
        Seq::empty()
    } else {
        let first = rparts.first();
        let rest = rparts.drop_first();
        let k = first.len() as int;
        let rw = rename_history(f, w);
        assert(rw == first + rest.flatten());
        let w0 = w.subrange(0, k);
        let w1 = w.subrange(k, w.len() as int);
        assert(rename_history(f, w0) =~= first) by {
            assert forall|j: int| 0 <= j < k implies rename_history(f, w0)[j] == first[j] by {
                assert(rw[j] == (first + rest.flatten())[j]);
            }
        }
        assert(rename_history(f, w1) =~= rest.flatten()) by {
            assert forall|j: int| 0 <= j < w.len() - k implies rename_history(f, w1)[j] == rest.flatten()[j] by {
                assert(rw[k + j] == (first + rest.flatten())[k + j]);
            }
        }
        let tail = lemma_unflatten_rename(f, rest, w1);
        let parts = seq![w0] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.first() == w0);
        assert(parts.flatten() == w0 + tail.flatten());
        assert(w0 + w1 =~= w);
        assert forall|i: int| 0 <= i < parts.len() implies rename_history(f, #[trigger] parts[i]) == rparts[i] by {
            if i > 0 {
                assert(parts[i] == tail[i - 1]);
                assert(rparts[i] == rest[i - 1]);
            }
        }
        parts
    }
}

/// The parts of a word only contain the word's values.
pub proof fn lemma_flatten_values_in<E: Event>(parts: Seq<Seq<E>>, values: Seq<ISet<E::Component>>)
    requires word_values_in(parts.flatten(), values),
    ensures forall|i: int| 0 <= i < parts.len() ==> word_values_in(#[trigger] parts[i], values),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(parts.flatten() == a + b);
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] values_in(a[j], values) by {
            assert((a + b)[j] == a[j]);
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] values_in(b[j], values) by {
            assert((a + b)[a.len() + j] == b[j]);
        }
        lemma_flatten_values_in(parts.drop_first(), values);
        assert forall|i: int| 0 <= i < parts.len() implies word_values_in(#[trigger] parts[i], values) by {
            if i > 0 {
                assert(parts[i] == parts.drop_first()[i - 1]);
            }
        }
    }
}

pub proof fn lemma_lang_rename<E: Event>(
    regex: RegexView<E::Component>, head: HeadView<E::Component>, candidate: E, w: Seq<E>,
    f: Seq<spec_fn(E::Component) -> E::Component>, values: Seq<ISet<E::Component>>,
)
    requires projection_laws::<E>(), surjectivity::<E>(), tags_preserved::<E>(f),
        head.len() == arity::<E>(),
        renamings_preserve(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == lang(regex, head, candidate, w),
    decreases regex, 1nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    reveal_with_fuel(lang, 1);
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => {},
        RegexView::Test(t) => {
            assert(regex_constants(regex, head.len()) =~= test_constants(t, head.len()));
            if w.len() == 1 {
                assert(values_in(w[0], values));
                lemma_test_rename(t, head, candidate, w[0], f, values);
            }
        },
        RegexView::Star(b) | RegexView::Not(b) => {
            lemma_lang_rename_star_not(regex, *b, head, candidate, w, f, values);
        },
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] renamings_preserve(f, regex_constants(cs[i], head.len()), values) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] regex_constants(cs[i], head.len())[j].subset_of(regex_constants(regex, head.len())[j]) by {
                    lemma_regex_constants_index(regex, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { regex_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == regex_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, regex_constants(cs[i], head.len()), regex_constants(regex, head.len()), values);
            }
            if regex is Concat {
                if lang(regex, head, candidate, w) {
                    let parts = choose|parts: Seq<Seq<E>>| parts.len() == cs.len() && w == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> lang(cs[i], head, candidate, parts[i]);
                    lemma_flatten_values_in(parts, values);
                    lemma_flatten_rename(f, parts);
                    let rp = rename_parts(f, parts);
                    assert forall|i: int| 0 <= i < cs.len() implies lang(cs[i], head, rc, rp[i]) by {
                        assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                    assert(rp.len() == cs.len() && rw == rp.flatten());
                }
                if lang(regex, head, rc, rw) {
                    let rparts = choose|parts: Seq<Seq<E>>| parts.len() == cs.len() && rw == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> lang(cs[i], head, rc, parts[i]);
                    let parts = lemma_unflatten_rename(f, rparts, w);
                    lemma_flatten_values_in(parts, values);
                    assert forall|i: int| 0 <= i < cs.len() implies lang(cs[i], head, candidate, parts[i]) by {
                        assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        assert(rename_history(f, parts[i]) == rparts[i]);
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                }
            } else {
                assert forall|i: int| 0 <= i < cs.len() implies
                    lang(cs[i], head, rc, rw) == lang(cs[i], head, candidate, w) by {
                    assert(renamings_preserve(f, regex_constants(cs[i], head.len()), values));
                    lemma_lang_rename(cs[i], head, candidate, w, f, values);
                }
            }
        },
    }
}

proof fn lemma_lang_rename_star_not<E: Event>(
    regex: RegexView<E::Component>, b: RegexView<E::Component>, head: HeadView<E::Component>, candidate: E,
    w: Seq<E>, f: Seq<spec_fn(E::Component) -> E::Component>,
    values: Seq<ISet<E::Component>>,
)
    requires projection_laws::<E>(), surjectivity::<E>(), tags_preserved::<E>(f),
        head.len() == arity::<E>(),
        regex == RegexView::Star(Box::new(b)) || regex == RegexView::Not(Box::new(b)),
        renamings_preserve(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == lang(regex, head, candidate, w),
    decreases regex, 0nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    reveal_with_fuel(lang, 1);
    assert(regex_constants(b, head.len()) =~= regex_constants(regex, head.len()));
    if regex is Not {
        lemma_lang_rename(b, head, candidate, w, f, values);
    } else {
        if lang(regex, head, candidate, w) {
            let parts = choose|parts: Seq<Seq<E>>| w == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> lang(b, head, candidate, parts[i]);
            lemma_flatten_values_in(parts, values);
            lemma_flatten_rename(f, parts);
            let rp = rename_parts(f, parts);
            assert forall|i: int| 0 <= i < rp.len() implies lang(b, head, rc, rp[i]) by {
                assert(word_values_in(parts[i], values));
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
            assert(rw == rp.flatten());
        }
        if lang(regex, head, rc, rw) {
            let rparts = choose|parts: Seq<Seq<E>>| rw == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> lang(b, head, rc, parts[i]);
            let parts = lemma_unflatten_rename(f, rparts, w);
            lemma_flatten_values_in(parts, values);
            assert forall|i: int| 0 <= i < parts.len() implies lang(b, head, candidate, parts[i]) by {
                assert(word_values_in(parts[i], values));
                assert(rename_history(f, parts[i]) == rparts[i]);
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
        }
    }
}

/// Canonical rule violation is invariant under equality- and tag-preserving renamings.
pub proof fn lemma_rule_rename<E: Event>(
    rule: Rule<E>, candidate: E, history: Seq<E>,
    f: Seq<spec_fn(E::Component) -> E::Component>, values: Seq<ISet<E::Component>>,
)
    requires projection_laws::<E>(), surjectivity::<E>(), tags_preserved::<E>(f), rule_wf(rule),
        renamings_preserve(f, rule_constants(rule@), values),
        values_in(candidate, values), word_values_in(history, values),
    ensures
        rule_violated(rule, candidate, history)
            == rule_violated(rule, rename_event(f, candidate), rename_history(f, history)),
{
    let k = rule_constants(rule@);
    let head = rule.head@;
    lemma_rename_event(f, candidate);
    assert forall|i: int| 0 <= i < head.len() implies
        (match #[trigger] head[i] {
            PatternView::Constant(value) => event_view(candidate)[i].eq_spec(&value)
                == event_view(rename_event(f, candidate))[i].eq_spec(&value),
            PatternView::Variable(_) => true,
        }) by {
        if let PatternView::Constant(value) = head[i] {
            assert(k[i].contains(value));
            assert(renaming_preserves(f[i], k[i], values[i]));
            assert(values[i].contains(event_view(candidate)[i]));
        }
    }
    assert(head_matches(head, candidate) == head_matches(head, rename_event(f, candidate)));
    assert forall|i: int| 0 <= i < head.len() implies
        #[trigger] regex_constants(rule.tail@, head.len())[i].subset_of(k[i]) by {}
    lemma_renamings_mono(f, regex_constants(rule.tail@, head.len()), k, values);
    lemma_lang_rename(rule.tail@, head, candidate, history, f, values);
}

pub proof fn lemma_pair_values_contains<E: Event>(candidate: E, history: Seq<E>, coordinate: int, i: int)
    requires 0 <= i < history.len(), 0 <= coordinate < arity::<E>(),
    ensures pair_values(candidate, history, coordinate).contains(event_view(history[i])[coordinate]),
{
    let x = event_view(history[i])[coordinate];
    assert(exists|j: int| 0 <= j < history.len() && 0 <= coordinate < arity::<E>()
        && #[trigger] event_view(history[j])[coordinate] == x);
}

pub proof fn theorem_genericity<E: Event>()
    ensures stmt_genericity::<E>(),
{
    assert forall|rule: Rule<E>, candidate: E, history: Seq<E>, f: Seq<spec_fn(E::Component) -> E::Component>|
        projection_laws::<E>() && surjectivity::<E>() && rule_wf(rule) && tags_preserved::<E>(f)
            && renamings_preserve(f, rule_constants(rule@),
                Seq::new(arity::<E>(), |i: int| pair_values(candidate, history, i)))
        implies (rule_violated(rule, candidate, history)
            == #[trigger] rule_violated(rule, rename_event(f, candidate), rename_history(f, history))) by {
        let values = Seq::new(arity::<E>(), |i: int| pair_values(candidate, history, i));
        assert(values_in(candidate, values));
        assert forall|i: int| 0 <= i < history.len() implies #[trigger] values_in(history[i], values) by {
            assert forall|j: int| 0 <= j < arity::<E>() implies #[trigger] values[j].contains(event_view(history[i])[j]) by {
                lemma_pair_values_contains(candidate, history, j, i);
            }
        }
        lemma_rule_rename(rule, candidate, history, f, values);
    }
}

} // verus!
