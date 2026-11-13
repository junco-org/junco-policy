//! R3: policy questions and symbolic counterexamples interpreted as real events.
//! Declared domains restrict both the candidate and every event in the history.

use super::semantics::{head_matches, lang, policy_denies, rule_violated};
use super::hypotheses::eq_equivalence;
use history_syntax::Event;
use history_syntax::Rule;
use history_syntax::spec::events::EventSpec;
use history_syntax::spec::events::{
    HeadView, PatternView, RegexView, RuleView, TestView, arity, event_view,
};
use history_syntax::spec::events::{surjectivity, well_tagged};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// Each coordinate is unrestricted or has a nonempty declared finite domain.
pub type Domains<C> = Seq<Option<Set<C>>>;

/// The literal constants of one pattern (paper Section 3).
pub open spec fn pattern_constant<C>(pattern: PatternView<C>) -> Set<C> {
    match pattern { PatternView::Constant(c) => Set::empty().insert(c), PatternView::Variable(_) => Set::empty() }
}

/// A finite union, built from finite sets rather than an unrestricted comprehension.
pub open spec fn constants_union<C>(sets: Seq<Set<C>>) -> Set<C>
    decreases sets.len(),
{
    if sets.len() == 0 { Set::empty() }
    else { constants_union(sets.drop_last()).union(sets.last()) }
}

/// Literals mentioned by a test at one coordinate (paper Section 3).
pub open spec fn test_constant_at<C>(test: TestView<C>, coordinate: int) -> Set<C>
    decreases test,
{
    match test {
        TestView::True | TestView::False => Set::empty(),
        TestView::Atom { pattern, .. } =>
            if coordinate == pattern.component { pattern_constant(pattern.pattern) } else { Set::empty() },
        TestView::And(cs) | TestView::Or(cs) => test_constant_forest(cs, coordinate),
    }
}

/// Literals mentioned by a finite test family at one coordinate (paper Section 3).
pub open spec fn test_constant_forest<C>(tests: Seq<TestView<C>>, coordinate: int) -> Set<C>
    decreases tests,
{
    if tests.len() == 0 { Set::empty() }
    else { test_constant_forest(tests.drop_last(), coordinate).union(test_constant_at(tests.last(), coordinate)) }
}

/// Test literals, separated by coordinate (paper Section 3).
pub open spec fn test_constants<C>(test: TestView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| test_constant_at(test, j))
}

/// Literals mentioned by a tail at one coordinate (paper Section 3).
pub open spec fn regex_constant_at<C>(regex: RegexView<C>, coordinate: int) -> Set<C>
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => Set::empty(),
        RegexView::Test(test) => test_constant_at(test, coordinate),
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => regex_constant_forest(cs, coordinate),
        RegexView::Star(child) | RegexView::Not(child) => regex_constant_at(*child, coordinate),
    }
}

/// Literals mentioned by a finite tail family at one coordinate (paper Section 3).
pub open spec fn regex_constant_forest<C>(regexes: Seq<RegexView<C>>, coordinate: int) -> Set<C>
    decreases regexes,
{
    if regexes.len() == 0 { Set::empty() }
    else { regex_constant_forest(regexes.drop_last(), coordinate).union(regex_constant_at(regexes.last(), coordinate)) }
}

/// Tail literals, separated by coordinate (paper Section 3).
pub open spec fn regex_constants<C>(regex: RegexView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| regex_constant_at(regex, j))
}

/// Head literals, separated by coordinate (paper Section 3).
pub open spec fn head_constants<C>(head: HeadView<C>) -> Seq<Set<C>> {
    head.map(|i: int, pattern: PatternView<C>| pattern_constant(pattern))
}

/// Exact finite constants of the head and tail, separately at every coordinate.
pub open spec fn rule_constants<C>(rule: RuleView<C>) -> Seq<Set<C>> {
    Seq::new(rule.head.len(), |i: int|
        regex_constants(rule.tail, rule.head.len())[i].union(head_constants(rule.head)[i]))
}

/// A policy witness may exclude only registered-rule literals and declared domain values.
pub open spec fn knowable_constants<E: Event>(
    domains: Domains<E::Component>, rules: Seq<Rule<E>>,
) -> Seq<Set<E::Component>> {
    Seq::new(arity::<E>(), |i: int| {
        let declared = if 0 <= i < domains.len() {
            match domains[i] { Some(values) => values, None => Set::empty() }
        } else { Set::empty() };
        let registered = rules.map_values(|rule: Rule<E>| {
            let literals = rule_constants(rule@);
            if 0 <= i < literals.len() { literals[i] } else { Set::empty() }
        });
        declared.union(constants_union(registered))
    })
}

/// A tail witness may exclude only this head, both tails, and declared domain values.
pub open spec fn tail_knowable_constants<E: Event>(
    domains: Domains<E::Component>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>,
) -> Seq<Set<E::Component>> {
    let heads = head_constants(head);
    Seq::new(arity::<E>(), |i: int| {
        let declared = if 0 <= i < domains.len() {
            match domains[i] { Some(values) => values, None => Set::empty() }
        } else { Set::empty() };
        let literals = if 0 <= i < heads.len() { heads[i] } else { Set::empty() };
        declared.union(literals).union(regex_constant_at(left, i)).union(regex_constant_at(right, i))
    })
}

/// Declared values are nonempty and tagged for their own coordinate (implementation domains).
pub open spec fn domains_wf<E: Event>(domains: Domains<E::Component>) -> bool {
    domains.len() == arity::<E>() && forall|i: int| 0 <= i < domains.len() ==> match #[trigger] domains[i] {
        None => true,
        Some(values) => values.len() > 0 && forall|value: E::Component| #[trigger] values.contains(value)
            ==> E::coordinate_spec(value) == i,
    }
}

/// A real event lies in every declared coordinate domain, using native modeled equality.
pub open spec fn event_in_domains<E: Event>(domains: Domains<E::Component>, event: E) -> bool {
    domains.len() == arity::<E>() && forall|i: int| 0 <= i < domains.len() ==> match #[trigger] domains[i] {
        None => true,
        Some(values) => exists|value: E::Component| values.contains(value)
            && event_view(event)[i].eq_spec(&value),
    }
}

/// The candidate and all committed history events satisfy the declared domains.
pub open spec fn in_domains<E: Event>(domains: Domains<E::Component>, candidate: E, history: Seq<E>) -> bool {
    event_in_domains(domains, candidate) && forall|j: int| 0 <= j < history.len()
        ==> event_in_domains(domains, #[trigger] history[j])
}

/// Coverage means every denial of the rule is also a denial of the covering policy (Section 5).
pub open spec fn covers<E: Event>(domains: Domains<E::Component>, policy: Seq<Rule<E>>, rule: Rule<E>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        && #[trigger] rule_violated(rule, candidate, history) ==> policy_denies(policy, candidate, history)
}

/// Refinement means every pair permitted by P is permitted by Q (Section 5).
pub open spec fn refines<E: Event>(domains: Domains<E::Component>, p: Seq<Rule<E>>, q: Seq<Rule<E>>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        && !#[trigger] policy_denies(p, candidate, history) ==> !policy_denies(q, candidate, history)
}

/// Removes every occurrence of the indexed target; other ids retain their order and duplicates.
pub open spec fn without_rule(ids: Seq<nat>, rule: nat) -> Seq<nat> {
    ids.filter(|id: nat| id != rule)
}

/// Removing the selected rule preserves every deny/permit decision (Section 5, redundancy).
pub open spec fn redundant_in<E: Event>(domains: Domains<E::Component>, policy: Seq<Rule<E>>, others: Seq<Rule<E>>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        ==> (#[trigger] policy_denies(policy, candidate, history) == policy_denies(others, candidate, history))
}

/// Vacuity: no domain-valid candidate/history pair violates the rule (Section 5).
pub open spec fn never_denies<E: Event>(domains: Domains<E::Component>, rule: Rule<E>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        ==> !#[trigger] rule_violated(rule, candidate, history)
}

/// Every matching domain-valid candidate violates the rule after every valid history.
pub open spec fn always_denies<E: Event>(domains: Domains<E::Component>, rule: Rule<E>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        && head_matches(rule.head@, candidate) ==> #[trigger] rule_violated(rule, candidate, history)
}

/// The left tail's real-event language is included in the right tail under a matching head.
pub open spec fn tails_included<E: Event>(domains: Domains<E::Component>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains(domains, candidate, history)
        && head_matches(head, candidate) && #[trigger] lang(left, head, candidate, history)
        ==> lang(right, head, candidate, history)
}

/// A symbolic value is a literal constant or a coordinate-local fresh name.
pub enum SymbolicValue<C> { Constant(C), Fresh(nat) }

/// A symbolic pair and the finite constant context avoided by its fresh names.
pub struct Counterexample<C> {
    pub candidate: Seq<SymbolicValue<C>>,
    pub history: Seq<Seq<SymbolicValue<C>>>,
    pub known: Seq<Set<C>>,
}

/// Symbolic values have the event arity; literals are correctly tagged and obey declared domains.
pub open spec fn symbolic_event_wf<E: Event>(domains: Domains<E::Component>, values: Seq<SymbolicValue<E::Component>>) -> bool {
    domains.len() == arity::<E>() && values.len() == arity::<E>()
        && forall|i: int| 0 <= i < values.len() ==> match #[trigger] values[i] {
            SymbolicValue::Constant(value) => E::coordinate_spec(value) == i && match domains[i] {
                None => true,
                Some(domain) => exists|member: E::Component| domain.contains(member) && value.eq_spec(&member),
            },
            SymbolicValue::Fresh(_) => domains[i] is None,
        }
}

/// A symbolic counterexample has valid coordinate shapes, literals, and a tagged finite constant context.
pub open spec fn counterexample_wf<E: Event>(domains: Domains<E::Component>, cex: Counterexample<E::Component>) -> bool {
    symbolic_event_wf::<E>(domains, cex.candidate) && cex.known.len() == arity::<E>()
        && (forall|j: int| 0 <= j < cex.history.len() ==> symbolic_event_wf::<E>(domains, #[trigger] cex.history[j]))
        && (forall|i: int, value: E::Component| 0 <= i < cex.known.len() && #[trigger] cex.known[i].contains(value)
            ==> E::coordinate_spec(value) == i)
}

/// A counterexample cannot hide arbitrary carrier values in its excluded constant context.
pub open spec fn known_within<C>(cex: Counterexample<C>, allowed: Seq<Set<C>>) -> bool {
    cex.known.len() == allowed.len()
        && forall|i: int| 0 <= i < cex.known.len()
            ==> #[trigger] cex.known[i].subset_of(allowed[i])
}

/// Fresh names appearing in one coordinate of a finite symbolic word.
pub open spec fn fresh_names<C>(word: Seq<Seq<SymbolicValue<C>>>, coordinate: int) -> Set<nat>
    decreases word.len(),
{
    if word.len() == 0 { Set::empty() } else {
        let rest = fresh_names(word.drop_last(), coordinate);
        if 0 <= coordinate < word.last().len() {
            match word.last()[coordinate] {
                SymbolicValue::Constant(_) => rest,
                SymbolicValue::Fresh(name) => rest.insert(name),
            }
        } else { rest }
    }
}

/// Number of distinct fresh names used by this counterexample at one coordinate.
pub open spec fn fresh_count<C>(cex: Counterexample<C>, coordinate: int) -> nat {
    fresh_names(seq![cex.candidate] + cex.history, coordinate).len()
}

/// At least k pairwise unequal, well-tagged domain values remain outside the known constants.
pub open spec fn fresh_capacity<E: Event>(domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat) -> bool {
    domains.len() == arity::<E>() && known.len() == arity::<E>() && 0 <= coordinate < arity::<E>()
        && exists|values: Seq<E::Component>| values.len() == k
            && (forall|j: int| 0 <= j < values.len() ==> E::coordinate_spec(#[trigger] values[j]) == coordinate
                && (forall|constant: E::Component| known[coordinate].contains(constant) ==> !values[j].eq_spec(&constant))
                && match domains[coordinate] {
                    None => true,
                    Some(domain) => exists|value: E::Component| domain.contains(value) && values[j].eq_spec(&value),
                })
            && (forall|j: int, l: int| 0 <= j < l < values.len() ==> !#[trigger] values[j].eq_spec(&values[l]))
}

/// Capacity is requested only for this returned counterexample's actual fresh-name counts.
pub open spec fn counterexample_capacity<E: Event>(domains: Domains<E::Component>, cex: Counterexample<E::Component>) -> bool {
    forall|i: int| 0 <= i < arity::<E>() ==> fresh_capacity::<E>(domains, cex.known, i, fresh_count(cex, i))
}

/// Substitutes a literal or a fresh name using one coordinate's choice function.
pub open spec fn value_of<C>(value: SymbolicValue<C>, choice: spec_fn(nat) -> C) -> C {
    match value { SymbolicValue::Constant(value) => value, SymbolicValue::Fresh(name) => choice(name) }
}

/// A choice is tag-correct, injective on used names, and avoids every known constant.
pub open spec fn choice_ok<E: Event>(cex: Counterexample<E::Component>, coordinate: int,
    choice: spec_fn(nat) -> E::Component) -> bool {
    let used = fresh_names(seq![cex.candidate] + cex.history, coordinate);
    &&& 0 <= coordinate < cex.known.len()
    &&& forall|name: nat| #[trigger] used.contains(name) ==> E::coordinate_spec(choice(name)) == coordinate
        && forall|constant: E::Component| cex.known[coordinate].contains(constant) ==> !choice(name).eq_spec(&constant)
    &&& forall|m: nat, n: nat| used.contains(m) && used.contains(n) && m != n
        ==> !#[trigger] choice(m).eq_spec(&choice(n))
}

/// An instance is a domain-valid pair of real events respecting one shared fresh-name choice.
pub open spec fn instance<E: Event>(domains: Domains<E::Component>, cex: Counterexample<E::Component>,
    candidate: E, history: Seq<E>) -> bool {
    in_domains(domains, candidate, history) && cex.candidate.len() == arity::<E>()
        && cex.history.len() == history.len() && cex.known.len() == arity::<E>()
        && exists|choices: Seq<spec_fn(nat) -> E::Component>| choices.len() == arity::<E>()
            && (forall|i: int| 0 <= i < arity::<E>() ==> choice_ok::<E>(cex, i, choices[i])
                && event_view(candidate)[i].eq_spec(&value_of(cex.candidate[i], choices[i])))
            && (forall|j: int| 0 <= j < history.len() ==> cex.history[j].len() == arity::<E>()
                && forall|i: int| 0 <= i < arity::<E>()
                    ==> event_view(history[j])[i].eq_spec(&value_of(cex.history[j][i], choices[i])))
}

/// The symbolic pair has at least one domain-valid real-event instance.
pub open spec fn has_instance<E: Event>(domains: Domains<E::Component>, cex: Counterexample<E::Component>) -> bool {
    exists|candidate: E, history: Seq<E>| #[trigger] instance(domains, cex, candidate, history)
}

/// Every admissible real-event instance witnesses the named semantic failure.
pub open spec fn every_instance<E: Event>(domains: Domains<E::Component>, cex: Counterexample<E::Component>,
    failure: spec_fn(E, Seq<E>) -> bool) -> bool {
    forall|candidate: E, history: Seq<E>| #[trigger] instance(domains, cex, candidate, history) ==> failure(candidate, history)
}

/// Candidates have the same split-case profile when they agree on every known constant.
pub open spec fn same_profile<E: Event>(known: Seq<Set<E::Component>>, candidate: E, other: E) -> bool {
    known.len() == arity::<E>()
        && forall|i: int, constant: E::Component| 0 <= i < known.len() && #[trigger] known[i].contains(constant)
            ==> (event_view(candidate)[i].eq_spec(&constant) == event_view(other)[i].eq_spec(&constant))
}

/// No domain-valid real-event failure has a history shorter than `n`, among all candidates.
pub open spec fn shortest<E: Event>(
    domains: Domains<E::Component>, n: nat, fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|candidate: E, history: Seq<E>| in_domains::<E>(domains, candidate, history) && history.len() < n
        ==> !#[trigger] fails(candidate, history)
}

/// No shorter real-event failure has the returned candidate's constant profile (PR #10).
pub open spec fn shortest_in_case<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>, candidate: E, n: nat,
    fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|other: E, history: Seq<E>| in_domains::<E>(domains, other, history) && history.len() < n
        && same_profile::<E>(known, candidate, other) ==> !#[trigger] fails(other, history)
}

/// Instantiate the canonical equivalence law at one native-equality value.
pub proof fn lemma_native_eq_reflexive<C: PartialEq>(value: C)
    requires eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true),
    ensures value.eq_spec(&value),
{
    let eq = |a: C, b: C| a.eq_spec(&b);
    let domain = |_: C| true;
    assert(eq_equivalence(eq, domain));
    assert(domain(value));
    assert(eq(value, value));
}

/// Instantiate symmetry without requiring callers to match a higher-order equality trigger.
pub proof fn lemma_native_eq_symmetric<C: PartialEq>(left: C, right: C)
    requires eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true),
    ensures left.eq_spec(&right) == right.eq_spec(&left),
{
    let eq = |a: C, b: C| a.eq_spec(&b);
    let domain = |_: C| true;
    assert(eq_equivalence(eq, domain));
    assert(domain(left) && domain(right));
    assert(eq(left, right) == eq(right, left));
}

/// Instantiate transitivity on the full native-equality carrier.
pub proof fn lemma_native_eq_transitive<C: PartialEq>(left: C, middle: C, right: C)
    requires
        eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true),
        left.eq_spec(&middle), middle.eq_spec(&right),
    ensures left.eq_spec(&right),
{
    let eq = |a: C, b: C| a.eq_spec(&b);
    let domain = |_: C| true;
    assert(eq_equivalence(eq, domain));
    assert(domain(left) && domain(middle) && domain(right));
    assert(eq(left, middle) && eq(middle, right));
    assert(eq(left, right));
}

/// Membership in the fresh-name set is exactly an occurrence in the finite word.
pub proof fn lemma_fresh_names_member<C>(word: Seq<Seq<SymbolicValue<C>>>, coordinate: int, name: nat)
    ensures
        fresh_names(word, coordinate).contains(name) <==> exists|j: int|
            0 <= j < word.len() && 0 <= coordinate < word[j].len()
                && #[trigger] word[j][coordinate] == SymbolicValue::Fresh(name),
    decreases word.len(),
{
    if word.len() > 0 {
        lemma_fresh_names_member(word.drop_last(), coordinate, name);
        assert forall|j: int| 0 <= j < word.len() - 1 implies
            word.drop_last()[j] == word[j] by {}
        if 0 <= coordinate < word.last().len()
            && word.last()[coordinate] == SymbolicValue::Fresh(name) {
            assert(word[(word.len() - 1) as int][coordinate] == SymbolicValue::Fresh(name));
        }
        if exists|j: int| 0 <= j < word.len() && 0 <= coordinate < word[j].len()
            && #[trigger] word[j][coordinate] == SymbolicValue::Fresh(name) {
            let j = choose|j: int| 0 <= j < word.len() && 0 <= coordinate < word[j].len()
                && #[trigger] word[j][coordinate] == SymbolicValue::Fresh(name);
            if j < word.len() - 1 {
                assert(word.drop_last()[j][coordinate] == SymbolicValue::Fresh(name));
            }
        }
    }
}

/// Distinct names, rather than their largest numeric label, bound the requested capacity.
pub proof fn lemma_fresh_names_count<C>(word: Seq<Seq<SymbolicValue<C>>>, coordinate: int)
    ensures fresh_names(word, coordinate).len() <= word.len(),
    decreases word.len(),
{
    if word.len() > 0 {
        lemma_fresh_names_count(word.drop_last(), coordinate);
    }
}

/// Every candidate/history fresh occurrence is counted, with at most one per event.
pub proof fn lemma_fresh_count<C>(cex: Counterexample<C>, coordinate: int)
    ensures
        fresh_count(cex, coordinate) <= 1 + cex.history.len(),
        forall|name: nat| 0 <= coordinate < cex.candidate.len()
            && cex.candidate[coordinate] == SymbolicValue::Fresh(name)
            ==> #[trigger] fresh_names(seq![cex.candidate] + cex.history, coordinate).contains(name),
        forall|j: int, name: nat| #![trigger cex.history[j][coordinate], fresh_names(seq![cex.candidate] + cex.history, coordinate).contains(name)]
            0 <= j < cex.history.len() && 0 <= coordinate < cex.history[j].len()
            && cex.history[j][coordinate] == SymbolicValue::Fresh(name)
            ==> fresh_names(seq![cex.candidate] + cex.history, coordinate).contains(name),
{
    let word = seq![cex.candidate] + cex.history;
    lemma_fresh_names_count(word, coordinate);
    assert forall|name: nat| 0 <= coordinate < cex.candidate.len()
        && cex.candidate[coordinate] == SymbolicValue::Fresh(name)
        implies fresh_names(word, coordinate).contains(name) by {
        lemma_fresh_names_member(word, coordinate, name);
        assert(word[0][coordinate] == SymbolicValue::Fresh(name));
    }
    assert forall|j: int, name: nat| 0 <= j < cex.history.len() && 0 <= coordinate < cex.history[j].len()
        && cex.history[j][coordinate] == SymbolicValue::Fresh(name)
        implies fresh_names(word, coordinate).contains(name) by {
        lemma_fresh_names_member(word, coordinate, name);
        assert(word[j + 1][coordinate] == SymbolicValue::Fresh(name));
    }
}

/// Enumerating the used names assigns each one a distinct capacity witness.
pub proof fn lemma_choice_from_capacity<E: Event>(
    domains: Domains<E::Component>, cex: Counterexample<E::Component>, coordinate: int,
) -> (choice: spec_fn(nat) -> E::Component)
    requires
        fresh_capacity::<E>(domains, cex.known, coordinate, fresh_count(cex, coordinate)),
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures choice_ok::<E>(cex, coordinate, choice),
{
    let used = fresh_names(seq![cex.candidate] + cex.history, coordinate);
    let names = used.to_seq();
    used.lemma_to_seq_len();
    used.lemma_to_seq_to_set_id();
    names.to_set_ensures();
    let values = choose|values: Seq<E::Component>| values.len() == used.len()
        && (forall|j: int| 0 <= j < values.len() ==> E::coordinate_spec(#[trigger] values[j]) == coordinate
            && (forall|constant: E::Component| cex.known[coordinate].contains(constant) ==> !values[j].eq_spec(&constant))
            && match domains[coordinate] {
                None => true,
                Some(domain) => exists|value: E::Component| domain.contains(value) && values[j].eq_spec(&value),
            })
        && (forall|j: int, l: int| 0 <= j < l < values.len() ==> !#[trigger] values[j].eq_spec(&values[l]));
    let choice = |name: nat| values[names.index_of(name)];
    assert forall|name: nat| used.contains(name) implies
        E::coordinate_spec(choice(name)) == coordinate
            && forall|constant: E::Component| cex.known[coordinate].contains(constant)
                ==> !choice(name).eq_spec(&constant) by {
        assert(names.contains(name));
        assert(0 <= names.index_of(name) < names.len());
    }
    assert forall|m: nat, n: nat| used.contains(m) && used.contains(n) && m != n
        implies !choice(m).eq_spec(&choice(n)) by {
        assert(names.contains(m) && names.contains(n));
        let j = names.index_of(m);
        let l = names.index_of(n);
        assert(0 <= j < names.len() && names[j] == m);
        assert(0 <= l < names.len() && names[l] == n);
        assert(j != l);
        if l < j {
            assert(!values[l].eq_spec(&values[j]));
            lemma_native_eq_symmetric(values[j], values[l]);
            assert(values[j].eq_spec(&values[l]) == values[l].eq_spec(&values[j]));
        }
    }
    choice
}

/// Capacity supplies one shared, tagged, injective choice per coordinate.
pub proof fn lemma_counterexample_choices<E: Event>(
    domains: Domains<E::Component>, cex: Counterexample<E::Component>,
) -> (choices: Seq<spec_fn(nat) -> E::Component>)
    requires
        counterexample_wf::<E>(domains, cex),
        counterexample_capacity::<E>(domains, cex),
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures
        choices.len() == arity::<E>(),
        forall|i: int| 0 <= i < arity::<E>() ==> choice_ok::<E>(cex, i, #[trigger] choices[i]),
{
    let choices = Seq::new(arity::<E>(), |i: int|
        choose|choice: spec_fn(nat) -> E::Component| choice_ok::<E>(cex, i, choice));
    assert forall|i: int| 0 <= i < arity::<E>() implies choice_ok::<E>(cex, i, #[trigger] choices[i]) by {
        let witness = lemma_choice_from_capacity::<E>(domains, cex, i);
        assert(exists|choice: spec_fn(nat) -> E::Component| choice_ok::<E>(cex, i, choice));
    }
    choices
}

/// A symbolic event in the returned word becomes a real event under the shared choices.
pub proof fn lemma_symbolic_event_instance<E: Event>(
    domains: Domains<E::Component>, cex: Counterexample<E::Component>,
    values: Seq<SymbolicValue<E::Component>>, choices: Seq<spec_fn(nat) -> E::Component>,
) -> (event: E)
    requires
        symbolic_event_wf::<E>(domains, values),
        values == cex.candidate || cex.history.contains(values),
        choices.len() == arity::<E>(),
        forall|i: int| 0 <= i < arity::<E>() ==> choice_ok::<E>(cex, i, #[trigger] choices[i]),
        surjectivity::<E>(),
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures
        event_in_domains::<E>(domains, event),
        forall|i: int| 0 <= i < arity::<E>()
            ==> #[trigger] event_view(event)[i] == value_of(values[i], choices[i]),
{
    let tuple = Seq::new(arity::<E>(), |i: int| value_of(values[i], choices[i]));
    assert forall|i: int| 0 <= i < arity::<E>() implies
        E::coordinate_spec(#[trigger] tuple[i]) == i by {
        match values[i] {
            SymbolicValue::Constant(_) => {},
            SymbolicValue::Fresh(name) => {
                lemma_fresh_count(cex, i);
                if values != cex.candidate {
                    let j = choose|j: int| 0 <= j < cex.history.len() && cex.history[j] == values;
                    assert(cex.history[j][i] == SymbolicValue::Fresh(name));
                }
                assert(fresh_names(seq![cex.candidate] + cex.history, i).contains(name));
            },
        }
    }
    assert(well_tagged::<E>(tuple));
    let event = choose|event: E| event_view(event) == tuple;
    assert forall|i: int| 0 <= i < domains.len() implies match #[trigger] domains[i] {
        None => true,
        Some(domain) => exists|member: E::Component| domain.contains(member) && event_view(event)[i].eq_spec(&member),
    } by {
        if domains[i] is Some {
            assert(values[i] is Constant);
        }
    }
    event
}

/// R3 capacity and well-formedness produce a domain-valid pair of actual R1 events.
pub proof fn lemma_counterexample_has_instance<E: Event>(
    domains: Domains<E::Component>, cex: Counterexample<E::Component>,
)
    requires
        counterexample_wf::<E>(domains, cex),
        counterexample_capacity::<E>(domains, cex),
        surjectivity::<E>(),
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures has_instance::<E>(domains, cex),
{
    let choices = lemma_counterexample_choices::<E>(domains, cex);
    let candidate = lemma_symbolic_event_instance::<E>(domains, cex, cex.candidate, choices);
    assert forall|j: int| #![trigger cex.history[j]] 0 <= j < cex.history.len() implies
        exists|event: E| event_in_domains::<E>(domains, event)
            && forall|i: int| 0 <= i < arity::<E>()
                ==> #[trigger] event_view(event)[i] == value_of(cex.history[j][i], choices[i]) by {
        assert(cex.history.contains(cex.history[j]));
        let event = lemma_symbolic_event_instance::<E>(domains, cex, cex.history[j], choices);
    }
    let history = Seq::new(cex.history.len(), |j: int| choose|event: E|
        event_in_domains::<E>(domains, event)
            && forall|i: int| 0 <= i < arity::<E>()
                ==> #[trigger] event_view(event)[i] == value_of(cex.history[j][i], choices[i]));
    assert forall|i: int| 0 <= i < arity::<E>() implies choice_ok::<E>(cex, i, choices[i])
        && event_view(candidate)[i].eq_spec(&value_of(cex.candidate[i], choices[i])) by {
        let value = value_of(cex.candidate[i], choices[i]);
        lemma_native_eq_reflexive(value);
        assert(value.eq_spec(&value));
    }
    assert forall|j: int| 0 <= j < history.len() implies cex.history[j].len() == arity::<E>()
        && forall|i: int| 0 <= i < arity::<E>()
            ==> event_view(history[j])[i].eq_spec(&value_of(cex.history[j][i], choices[i])) by {
        assert forall|i: int| 0 <= i < arity::<E>() implies
            event_view(history[j])[i].eq_spec(&value_of(cex.history[j][i], choices[i])) by {
            let value = value_of(cex.history[j][i], choices[i]);
            lemma_native_eq_reflexive(value);
            assert(value.eq_spec(&value));
        }
    }
    assert(instance::<E>(domains, cex, candidate, history));
}

/// A finite initial segment embeds into a coordinate with native equality reflecting indices.
/// The embedding may wrap a primitive value in any event's coordinate tag.
pub open spec fn coordinate_embedding<E: Event>(
    coordinate: int, size: nat, embed: spec_fn(nat) -> E::Component,
) -> bool {
    0 <= coordinate < arity::<E>()
        && (forall|n: nat| n < size ==> E::coordinate_spec(#[trigger] embed(n)) == coordinate)
        && (forall|m: nat, n: nat| m < size && n < size && #[trigger] embed(m).eq_spec(&embed(n)) ==> m == n)
}

/// At most one embedded index can collide with each known constant's equality class.
pub proof fn lemma_embedding_collision_bound<C: PartialEq>(
    known: Set<C>, size: nat, embed: spec_fn(nat) -> C,
)
    requires
        eq_equivalence::<C>(|a: C, b: C| a.eq_spec(&b), |_: C| true),
        forall|m: nat, n: nat| m < size && n < size && #[trigger] embed(m).eq_spec(&embed(n)) ==> m == n,
    ensures
        Set::<nat>::range(0, size).filter(|n: nat|
            exists|constant: C| known.contains(constant) && embed(n).eq_spec(&constant)).len() <= known.len(),
{
    broadcast use vstd::set_lib::range_set_properties, vstd::set::lemma_set_filter;
    let bad = Set::<nat>::range(0, size).filter(|n: nat|
        exists|constant: C| known.contains(constant) && embed(n).eq_spec(&constant));
    let representative = |n: nat| choose|constant: C| known.contains(constant) && embed(n).eq_spec(&constant);
    assert forall|m: nat, n: nat| bad.contains(m) && bad.contains(n)
        && representative(m) == representative(n) implies m == n by {
        let constant = representative(m);
        assert(embed(m).eq_spec(&constant));
        assert(embed(n).eq_spec(&constant));
        lemma_native_eq_symmetric(embed(n), constant);
        lemma_native_eq_transitive(embed(m), constant, embed(n));
        assert(constant.eq_spec(&embed(n)));
        assert(embed(m).eq_spec(&embed(n)));
    }
    assert(bad.injective_on(representative));
    let image = bad.map(representative);
    assert forall|constant: C| image.contains(constant) implies known.contains(constant) by {
        bad.lemma_map_contains(representative, constant);
        let n = choose|n: nat| bad.contains(n) && representative(n) == constant;
        assert(known.contains(representative(n)));
    }
    assert(image.subset_of(known));
    vstd::set_lib::lemma_map_size(bad, image, representative);
    vstd::set_lib::lemma_len_subset(image, known);
}

/// A tagged embedding of `size` equality classes leaves at least `size - known.len()` fresh values.
/// This is a cardinality argument, not an assumption of the capacity witness being constructed.
pub proof fn lemma_fresh_capacity_from_embedding<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, size: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(),
        known.len() == arity::<E>(),
        coordinate_embedding::<E>(coordinate, size, embed),
        domains[coordinate] is None,
        k + known[coordinate].len() <= size,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    broadcast use vstd::set_lib::range_set_properties, vstd::set::lemma_set_filter;
    let universe = Set::<nat>::range(0, size);
    let bad = universe.filter(|n: nat| exists|constant: E::Component|
        known[coordinate].contains(constant) && embed(n).eq_spec(&constant));
    lemma_embedding_collision_bound(known[coordinate], size, embed);
    let good = universe.difference(bad);
    vstd::set_lib::lemma_set_difference_len(universe, bad);
    assert(universe.intersect(bad) =~= bad);
    assert(good.len() >= k);
    good.lemma_to_seq_len();
    good.lemma_to_seq_no_duplicates();
    good.lemma_to_seq_to_set_id();
    let indices = good.to_seq();
    indices.to_set_ensures();
    let values = Seq::new(k, |j: int| embed(indices[j]));
    assert forall|j: int| 0 <= j < values.len() implies
        E::coordinate_spec(#[trigger] values[j]) == coordinate
            && (forall|constant: E::Component| known[coordinate].contains(constant)
                ==> !values[j].eq_spec(&constant))
            && match domains[coordinate] {
                None => true,
                Some(domain) => exists|value: E::Component| domain.contains(value) && values[j].eq_spec(&value),
            } by {
        assert(good.contains(indices[j]));
        assert(indices[j] < size);
        assert(!bad.contains(indices[j]));
    }
    assert forall|j: int, l: int| 0 <= j < l < values.len()
        implies !#[trigger] values[j].eq_spec(&values[l]) by {
        assert(good.contains(indices[j]) && good.contains(indices[l]));
        assert(indices[j] != indices[l]);
    }
    assert(fresh_capacity::<E>(domains, known, coordinate, k));
}

/// An empty fresh-name request is satisfiable even at a declared coordinate.
pub proof fn lemma_fresh_capacity_zero<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>, coordinate: int,
)
    requires domains.len() == arity::<E>(), known.len() == arity::<E>(), 0 <= coordinate < arity::<E>(),
    ensures fresh_capacity::<E>(domains, known, coordinate, 0),
{
    let values = Seq::<E::Component>::empty();
    assert(values.len() == 0);
    assert(fresh_capacity::<E>(domains, known, coordinate, 0));
}

/// A tagged u8-sized coordinate has capacity whenever `k + known.len() <= 256`.
pub proof fn lemma_fresh_capacity_u8<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(), known.len() == arity::<E>(),
        coordinate_embedding::<E>(coordinate, u8::MAX as nat + 1, embed),
        domains[coordinate] is None,
        k + known[coordinate].len() <= u8::MAX as nat + 1,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    lemma_fresh_capacity_from_embedding::<E>(domains, known, coordinate, k, u8::MAX as nat + 1, embed);
}

/// A tagged u16-sized coordinate has capacity below its size minus the known constants.
pub proof fn lemma_fresh_capacity_u16<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(), known.len() == arity::<E>(),
        coordinate_embedding::<E>(coordinate, u16::MAX as nat + 1, embed),
        domains[coordinate] is None,
        k + known[coordinate].len() <= u16::MAX as nat + 1,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    lemma_fresh_capacity_from_embedding::<E>(domains, known, coordinate, k, u16::MAX as nat + 1, embed);
}

/// A tagged u32-sized coordinate has capacity below its size minus the known constants.
pub proof fn lemma_fresh_capacity_u32<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(), known.len() == arity::<E>(),
        coordinate_embedding::<E>(coordinate, u32::MAX as nat + 1, embed),
        domains[coordinate] is None,
        k + known[coordinate].len() <= u32::MAX as nat + 1,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    lemma_fresh_capacity_from_embedding::<E>(domains, known, coordinate, k, u32::MAX as nat + 1, embed);
}

/// A tagged u64-sized coordinate has capacity below its size minus the known constants.
pub proof fn lemma_fresh_capacity_u64<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(), known.len() == arity::<E>(),
        coordinate_embedding::<E>(coordinate, u64::MAX as nat + 1, embed),
        domains[coordinate] is None,
        k + known[coordinate].len() <= u64::MAX as nat + 1,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    lemma_fresh_capacity_from_embedding::<E>(domains, known, coordinate, k, u64::MAX as nat + 1, embed);
}

/// A tagged natural-number embedding supplies every finite requested capacity.
pub proof fn lemma_fresh_capacity_nat<E: Event>(
    domains: Domains<E::Component>, known: Seq<Set<E::Component>>,
    coordinate: int, k: nat, embed: spec_fn(nat) -> E::Component,
)
    requires
        domains.len() == arity::<E>(), known.len() == arity::<E>(),
        0 <= coordinate < arity::<E>(), domains[coordinate] is None,
        forall|n: nat| E::coordinate_spec(#[trigger] embed(n)) == coordinate,
        forall|m: nat, n: nat| #[trigger] embed(m).eq_spec(&embed(n)) ==> m == n,
        eq_equivalence::<E::Component>(|a: E::Component, b: E::Component| a.eq_spec(&b), |_: E::Component| true),
    ensures fresh_capacity::<E>(domains, known, coordinate, k),
{
    let size = k + known[coordinate].len();
    assert(coordinate_embedding::<E>(coordinate, size, embed));
    lemma_fresh_capacity_from_embedding::<E>(domains, known, coordinate, k, size, embed);
}

}
