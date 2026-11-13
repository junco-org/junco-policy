//! R3: policy questions and symbolic counterexamples interpreted as real events.
//! Declared domains restrict both the candidate and every event in the history.

use super::semantics::{head_matches, lang, policy_denies, rule_violated};
use history_syntax::Event;
use history_syntax::Rule;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{HeadView, RegexView, arity, event_view};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

/// Each coordinate is unrestricted or has a nonempty declared finite domain.
pub type Domains<C> = Seq<Option<Set<C>>>;

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

}
