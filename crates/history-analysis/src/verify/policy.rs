//! Interfaces of the policy queries `covered`, `redundant` and `at_least_as_strict`: stored rules
//! as the numeric rules of `refinement::policy`, the generalized per-query contract of `decide`,
//! the atoms whose split decides the head constants of a policy, and capacities.

use super::frontend::*;
use super::search_exec as exec;
use super::typed_numeric as typed;
use super::verdict::{constraint_codes_wf, source_codes_wf};
use super::{analyzer_obligations, constraint_wf, ndomains};
use crate::analyzer::{AnalyzedRule, Inclusion, PolicyAnalyzer};
use crate::constraint::{Atom, ConstId, Constraint, Letter, Operand};
use alloc::boxed::Box;
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::{encoding, implementation, inclusion, search};
use history_syntax::{Event, RuleMode};
use junco_core::flat::{FlatPair, FlatRegex, FlatTest};
use junco_core::kernel::verify as model;
use junco_core::verify::flatten as fl;
use junco_core::verify::history_specs::{self as language, EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

// ----- stored rules as numeric rules -----

/// A template's test as a kernel test; `numeric::source_test` is its meaning.
pub(crate) open spec fn template_test(t: FlatPair<u64>, index: nat) -> model::Test
    decreases index, 1nat,
{
    if index >= t.tests@.len() { model::Test::False } else {
        match t.tests@[index as int] {
            FlatTest::Bool(value) => if value { model::Test::True } else { model::Test::False },
            FlatTest::Atom { field, term, positive } =>
                model::Test::Atom(model::Primitive::Eq(field, numeric::term_view(term)), positive),
            FlatTest::And(children) => model::Test::And(template_tests(t, children@, index)),
            FlatTest::Or(children) => model::Test::Or(template_tests(t, children@, index)),
        }
    }
}

pub(crate) open spec fn template_tests(t: FlatPair<u64>, children: Seq<u32>, bound: nat) -> Seq<model::Test>
    decreases bound, 0nat,
{
    Seq::new(children.len(), |j: int| if 0 <= j < children.len() && (children[j] as nat) < bound {
        template_test(t, children[j] as nat) } else { model::Test::False })
}

/// A template's regex node as a regular expression over kernel tests; for a template with
/// backward references its language is `numeric::source_regex` (`lemma_template_regex`).
pub(crate) open spec fn template_regex(t: FlatPair<u64>, index: nat) -> Regex<model::Test>
    decreases index, 1nat,
{
    if index >= t.regexes@.len() { Regex::Empty } else {
        match t.regexes@[index as int] {
            FlatRegex::Empty => Regex::Empty,
            FlatRegex::All => Regex::All,
            FlatRegex::Epsilon => Regex::Epsilon,
            FlatRegex::Test(test) => Regex::Test(template_test(t, test as nat)),
            FlatRegex::Union(children) => Regex::Union(template_regexes(t, children@, index)),
            FlatRegex::Concat(children) => Regex::Concat(template_regexes(t, children@, index)),
            FlatRegex::Intersect(children) => Regex::Intersect(template_regexes(t, children@, index)),
            FlatRegex::Star(child) => Regex::Star(Box::new(
                if (child as nat) < index { template_regex(t, child as nat) } else { Regex::Empty })),
            FlatRegex::Complement(child) => Regex::Not(Box::new(
                if (child as nat) < index { template_regex(t, child as nat) } else { Regex::Empty })),
        }
    }
}

pub(crate) open spec fn template_regexes(t: FlatPair<u64>, children: Seq<u32>, bound: nat) -> Seq<Regex<model::Test>>
    decreases bound, 0nat,
{
    Seq::new(children.len(), |j: int| if 0 <= j < children.len() && (children[j] as nat) < bound {
        template_regex(t, children[j] as nat) } else { Regex::Empty })
}

/// The numeric rule a stored rule stands for (`encoding::represents`): its mode, the head
/// constants of its template, and the template's tail.
pub(crate) open spec fn numeric_rule(mode: RuleMode, t: FlatPair<u64>) -> encoding::NRule {
    encoding::NRule { mode, head: typed::template_head(t), tail: template_regex(t, t.root as nat) }
}

pub(crate) open spec fn stored_numeric<E: Event>(r: AnalyzedRule<E>) -> encoding::NRule {
    numeric_rule(r.mode, r.tail)
}

/// The numeric policy of the stored rules with the given ids, in order.
pub(crate) open spec fn numeric_policy<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>) -> Seq<encoding::NRule> {
    ids.map_values(|id: nat| stored_numeric(a.rules@[id as int]))
}

/// Every id names a stored rule.
pub open(crate) spec fn ids_valid<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> #[trigger] ids[i] < a.rules@.len()
}

// ----- the atoms that decide a policy's head constants -----

/// `x_c = κ_c` and `x_c = v` for a head constant `v` at component `k`.
pub(crate) open spec fn component_atoms(k: usize, constant: Option<ConstId>) -> Seq<Atom> {
    match constant {
        Some(v) => seq![Atom { component: k, operand: Operand::Register },
            Atom { component: k, operand: Operand::Constant(v) }],
        None => Seq::empty(),
    }
}

pub(crate) open spec fn head_atoms(constants: [Option<ConstId>; 3]) -> Seq<Atom> {
    component_atoms(0, constants[0]) + component_atoms(1, constants[1]) + component_atoms(2, constants[2])
}

/// The atoms of the head constants of the rules with the given ids, in order. A split on their
/// operands decides `inclusion::head_pairs` of the numeric policy.
pub(crate) open spec fn policy_atoms<E: Event>(rules: Seq<AnalyzedRule<E>>, ids: Seq<nat>) -> Seq<Atom>
    decreases ids.len(),
{
    if ids.len() == 0 { Seq::empty() } else {
        policy_atoms(rules, ids.drop_last()) + head_atoms(rules[ids.last() as int].constants)
    }
}

// ----- one constrained inclusion -----

/// The template's language is `left & ¬right` under every well-formed valuation.
pub(crate) open spec fn difference_of(p: FlatPair<u64>, left: Regex<model::Test>, right: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta)
        ==> (#[trigger] numeric::source_regex(p, p.root as nat, theta, w)
            == (encoding::n_lang(theta, left, w) && !encoding::n_lang(theta, right, w)))
}

/// What `decide` requires for the query `left ⊑_g right` (Definition `def:constrained`): a
/// structurally well-formed difference over known codes with the language of `left & ¬right`, a
/// satisfiable constraint over known codes, and per-state products that fit `usize`.
pub(crate) open spec fn query_ready<E: Event>(a: PolicyAnalyzer<E>, g: Constraint, difference: FlatPair<u64>,
    left: Regex<model::Test>, right: Regex<model::Test>) -> bool {
    &&& analyzer_state_wf(a) && analyzer_obligations::<E>()
    &&& junco_core::flat::verify::structural_wf(difference)
    &&& source_codes_wf(a.constants, difference)
    &&& difference_of(difference, left, right)
    &&& constraint_wf(g) && constraint_codes_wf(a.constants, g@)
    &&& inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(g@))
    &&& forall|v: [Set<nat>; 3]| v[0].len() <= a.constants.values@.len()
        && v[1].len() <= a.constants.values@.len() && v[2].len() <= a.constants.values@.len()
            ==> #[trigger] exec::resource_capacity(v)
}

/// What `decide` establishes for the query `left ⊑_g right`: `Holds` is the inclusion under `g`;
/// a counterexample is the reconstruction of a refutation whose outcome satisfies
/// `search::outcome_ok` (realizable, every realization a counterexample, of minimum length).
pub(crate) open spec fn decided<E: Event>(a: PolicyAnalyzer<E>, g: implementation::ConstraintView,
    left: Regex<model::Test>, right: Regex<model::Test>, v: Inclusion<E>) -> bool {
    let d = ndomains(a.universes);
    let g0 = implementation::constraint_of(g);
    match v {
        Inclusion::Holds => inclusion::included_under(d, g0, left, right),
        Inclusion::Counterexample(cex) => exists|r: Constraint, letters: Seq<Letter>,
            alphabets: Seq<Set<model::Primitive>>|
            #[trigger] super::reconstruction::reconstructed(a.constants, a.universes, r, letters, alphabets, cex)
            && search::outcome_ok(d, g0, left, right, search::Outcome::Refuted(
                implementation::constraint_of(r@), exec::chain_assignments(letters, alphabets))),
        Inclusion::Exhausted => true,
    }
}

// ----- capacities -----

/// Sufficient capacity for policy queries over stored rules: the per-state split and letter
/// products of every search fit `usize`. Holds whenever the constant book has at most 1000
/// entries.
pub open(crate) spec fn policy_capacity<E: Event>(a: PolicyAnalyzer<E>) -> bool {
    let count = a.constants.values@.len();
    (count + 2) * (count + 2) * (count + 2) <= usize::MAX
}

/// Sufficient capacity for adding `rule`: constant ids of the rule's constants fit `u32`.
pub open(crate) spec fn rule_capacity<E: Event>(a: PolicyAnalyzer<E>, rule: history_syntax::Rule<E>) -> bool {
    a.constants.values@.len() + 3 + fl::regex_cost::<E>(rule.tail@) <= u32::MAX
}

} // verus!
