//! Exact firing and the policy split (R3): the cases of a split on the head constants of a
//! policy decide those constants, so `Constraint::entails` against a rule's head constraint is
//! exactly semantic entailment; the cases satisfy `inclusion::split_ok` on `head_pairs`; and a
//! stored template's tail has the template's language (`policy::template_regex`).

use super::constraint_unique::universe_distinct;
use super::frontend::*;
use super::policy::{
    component_atoms, head_atoms, ids_valid, numeric_policy, policy_atoms, policy_capacity,
    stored_numeric, template_regex, template_regexes, template_test, template_tests,
};
use super::reconstruction::code_field;
use super::search_exec as exec;
use super::verdict::{constraint_codes_wf, lemma_lowered_payload};
use super::{
    atom_set, atoms_wf, codes, component_index, component_of, constraint_views, constraint_wf,
    domain_view, head_view, lemma_codes, lemma_constraint_entails, lemma_constraint_view,
    lemma_constraint_view_at, lemma_register_product_members, lemma_split_contract, ndomains,
    operands_of, option_code, register_codes, register_count, register_entails, register_options,
    split_capacity, split_views, table,
};
use crate::analyzer::{AnalyzedRule, Constants, PolicyAnalyzer};
use crate::constraint::{Atom, ConstId, Constraint, Operand, Operands, RegisterConstraint, Universes};
use alloc::vec::Vec;
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::{encoding, implementation, inclusion, search};
use history_syntax::Event;
use history_syntax::syntax::Component;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTest};
use junco_core::kernel::verify as model;
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::encoding as enc;
use junco_core::verify::history_specs::{self as language, EventView, Subst};
use vstd::prelude::*;

verus! {
broadcast use {vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas};

// ----- F1: a stored template's tail as a regular expression -----

/// The kernel test of a template node holds exactly when the template's test does.
pub(crate) proof fn lemma_template_test(t: FlatPair<u64>, index: nat, theta: Subst, e: EventView)
    requires table::dag(t),
    ensures model::test_holds(theta, template_test(t, index), e) == numeric::source_test(t, index, theta, e),
    decreases index,
{
    reveal_with_fuel(model::test_holds, 2);
    reveal_with_fuel(numeric::source_test, 2);
    if index < t.tests@.len() {
        assert(table::test_dag(t.tests@[index as int], index));
        match t.tests@[index as int] {
            FlatTest::And(children) => {
                let cs = template_tests(t, children@, index);
                assert(template_test(t, index) == model::Test::And(cs));
                assert(cs.len() == children@.len());
                lemma_test_and(theta, cs, e);
                lemma_source_and(t, index, children, theta, e);
                if model::test_holds(theta, template_test(t, index), e) {
                    assert forall|i: int| 0 <= i < children@.len() implies children@[i] < index
                        && #[trigger] numeric::source_test(t, children@[i] as nat, theta, e) by {
                        lemma_template_test(t, children@[i] as nat, theta, e);
                        assert(model::test_holds(theta, cs[i], e));
                    }
                    assert(numeric::source_test(t, index, theta, e));
                }
                if numeric::source_test(t, index, theta, e) {
                    assert forall|i: int| 0 <= i < cs.len() implies
                        #[trigger] model::test_holds(theta, cs[i], e) by {
                        lemma_template_test(t, children@[i] as nat, theta, e);
                        assert(numeric::source_test(t, children@[i] as nat, theta, e));
                    }
                    assert(model::test_holds(theta, template_test(t, index), e));
                }
            },
            FlatTest::Or(children) => {
                let cs = template_tests(t, children@, index);
                if model::test_holds(theta, template_test(t, index), e) {
                    let i = choose|i: int| 0 <= i < cs.len() && model::test_holds(theta, cs[i], e);
                    lemma_template_test(t, children@[i] as nat, theta, e);
                    assert(children@[i] < index && numeric::source_test(t, children@[i] as nat, theta, e));
                }
                if numeric::source_test(t, index, theta, e) {
                    let i = choose|i: int| 0 <= i < children@.len() && children@[i] < index
                        && numeric::source_test(t, children@[i] as nat, theta, e);
                    lemma_template_test(t, children@[i] as nat, theta, e);
                    assert(model::test_holds(theta, cs[i], e));
                }
            },
            _ => {},
        }
    }
}

proof fn lemma_test_and(theta: Subst, cs: Seq<model::Test>, e: EventView)
    ensures model::test_holds(theta, model::Test::And(cs), e)
        == (forall|i: int| 0 <= i < cs.len() ==> model::test_holds(theta, cs[i], e)),
{
    reveal_with_fuel(model::test_holds, 2);
    assert(model::Test::And(cs)->And_0 == cs);
    if model::test_holds(theta, model::Test::And(cs), e) {
        assert forall|i: int| 0 <= i < cs.len() implies model::test_holds(theta, cs[i], e) by {
            assert(model::test_holds(theta, model::Test::And(cs), e));
        }
    }
}

proof fn lemma_source_and(t: FlatPair<u64>, index: nat, node: Vec<u32>, theta: Subst, e: EventView)
    requires index < t.tests@.len(), t.tests@[index as int] == FlatTest::<u64>::And(node),
    ensures numeric::source_test(t, index, theta, e) == (forall|i: int| 0 <= i < node@.len()
        ==> node@[i] < index && numeric::source_test(t, node@[i] as nat, theta, e)),
{
    reveal_with_fuel(numeric::source_test, 2);
    let children = node@;
    if numeric::source_test(t, index, theta, e) {
        assert forall|i: int| 0 <= i < children.len() implies children[i] < index
            && numeric::source_test(t, children[i] as nat, theta, e) by {
            assert(numeric::source_test(t, index, theta, e));
        }
    }
}

proof fn lemma_source_intersect(t: FlatPair<u64>, index: nat, node: Vec<u32>, theta: Subst, w: Seq<EventView>)
    requires index < t.regexes@.len(), t.regexes@[index as int] == FlatRegex::Intersect(node),
    ensures numeric::source_regex(t, index, theta, w) == (forall|i: int| 0 <= i < node@.len()
        ==> node@[i] < index && numeric::source_regex(t, node@[i] as nat, theta, w)),
{
    reveal_with_fuel(numeric::source_regex, 2);
    let children = node@;
    if numeric::source_regex(t, index, theta, w) {
        assert forall|i: int| 0 <= i < children.len() implies children[i] < index
            && numeric::source_regex(t, children[i] as nat, theta, w) by {
            assert(numeric::source_regex(t, index, theta, w));
        }
    }
}

/// The language of a template node as a regular expression is the template's language.
pub(crate) proof fn lemma_template_regex(t: FlatPair<u64>, index: nat, theta: Subst, w: Seq<EventView>)
    requires table::dag(t),
    ensures encoding::n_lang(theta, template_regex(t, index), w) == numeric::source_regex(t, index, theta, w),
{
    lemma_template_language(t, index, theta);
}

proof fn lemma_template_language(t: FlatPair<u64>, index: nat, theta: Subst)
    requires table::dag(t),
    ensures forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
        == numeric::source_regex(t, index, theta, w),
    decreases index, 1nat,
{
    reveal_with_fuel(language::lang, 2);
    reveal_with_fuel(numeric::source_regex, 2);
    if index < t.regexes@.len() {
        let sem = model::gsem(theta);
        assert(junco_core::flat::verify::regex_wf(t.regexes@[index as int], index, t.tests@.len()));
        match t.regexes@[index as int] {
            FlatRegex::Test(test) => {
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    if w.len() == 1 { lemma_template_test(t, test as nat, theta, w[0]); }
                }
            },
            FlatRegex::Union(children) => {
                let cs = template_regexes(t, children@, index);
                lemma_children_language(t, children@, index, theta);
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    if language::lang(sem, language::Regex::Union(cs), w) {
                        let i = choose|i: int| 0 <= i < cs.len() && language::lang(sem, cs[i], w);
                        assert(language::lang(sem, cs[i], w) == numeric::source_regex(t, children@[i] as nat, theta, w));
                    }
                    if numeric::source_regex(t, index, theta, w) {
                        let i = choose|i: int| 0 <= i < children@.len() && children@[i] < index
                            && numeric::source_regex(t, children@[i] as nat, theta, w);
                        assert(language::lang(sem, cs[i], w) == numeric::source_regex(t, children@[i] as nat, theta, w));
                    }
                }
            },
            FlatRegex::Intersect(children) => {
                let cs = template_regexes(t, children@, index);
                lemma_children_language(t, children@, index, theta);
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    language::lemma_lang_intersect(sem, cs, w);
                    lemma_source_intersect(t, index, children, theta, w);
                    assert(template_regex(t, index) == language::Regex::Intersect(cs));
                    if language::lang(sem, language::Regex::Intersect(cs), w) {
                        assert forall|i: int| 0 <= i < children@.len() implies children@[i] < index
                            && #[trigger] numeric::source_regex(t, children@[i] as nat, theta, w) by {
                            assert(language::lang(sem, cs[i], w));
                        }
                        assert(numeric::source_regex(t, index, theta, w));
                    }
                    if numeric::source_regex(t, index, theta, w) {
                        assert forall|i: int| 0 <= i < cs.len() implies #[trigger] language::lang(sem, cs[i], w) by {
                            assert(numeric::source_regex(t, children@[i] as nat, theta, w));
                        }
                        assert(language::lang(sem, language::Regex::Intersect(cs), w));
                    }
                }
            },
            FlatRegex::Concat(children) => {
                let cs = template_regexes(t, children@, index);
                lemma_children_language(t, children@, index, theta);
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    if language::lang(sem, language::Regex::Concat(cs), w) {
                        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
                            && forall|i: int| 0 <= i < cs.len() ==> language::lang(sem, cs[i], parts[i]);
                        assert forall|i: int| 0 <= i < children@.len() implies children@[i] < index
                            && numeric::source_regex(t, children@[i] as nat, theta, #[trigger] parts[i]) by {
                            assert(language::lang(sem, cs[i], parts[i]));
                        }
                    }
                    if numeric::source_regex(t, index, theta, w) {
                        let parts = choose|parts: Seq<Seq<EventView>>|
                            parts.len() == children@.len() && parts.flatten() == w
                            && forall|i: int| 0 <= i < children@.len()
                                ==> children@[i] < index && numeric::source_regex(t, children@[i] as nat, theta, parts[i]);
                        assert forall|i: int| 0 <= i < cs.len() implies
                            language::lang(sem, cs[i], #[trigger] parts[i]) by {
                            assert(numeric::source_regex(t, children@[i] as nat, theta, parts[i]));
                        }
                    }
                }
            },
            FlatRegex::Star(child) => {
                lemma_template_language(t, child as nat, theta);
                let c = template_regex(t, child as nat);
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    if language::lang(sem, template_regex(t, index), w) {
                        let parts = choose|parts: Seq<Seq<EventView>>| w == parts.flatten()
                            && forall|i: int| 0 <= i < parts.len() ==> language::lang(sem, c, parts[i]);
                        assert forall|i: int| 0 <= i < parts.len() implies
                            numeric::source_regex(t, child as nat, theta, #[trigger] parts[i]) by {
                            assert(encoding::n_lang(theta, c, parts[i]));
                        }
                    }
                    if numeric::source_regex(t, index, theta, w) {
                        let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == w
                            && forall|i: int| 0 <= i < parts.len() ==> numeric::source_regex(t, child as nat, theta, parts[i]);
                        assert forall|i: int| 0 <= i < parts.len() implies
                            language::lang(sem, c, #[trigger] parts[i]) by {
                            assert(numeric::source_regex(t, child as nat, theta, parts[i]));
                            assert(encoding::n_lang(theta, c, parts[i]));
                        }
                    }
                }
            },
            FlatRegex::Complement(child) => {
                lemma_template_language(t, child as nat, theta);
                let c = template_regex(t, child as nat);
                assert forall|w: Seq<EventView>| #[trigger] encoding::n_lang(theta, template_regex(t, index), w)
                    == numeric::source_regex(t, index, theta, w) by {
                    assert(encoding::n_lang(theta, c, w) == numeric::source_regex(t, child as nat, theta, w));
                }
            },
            _ => {},
        }
    }
}

/// The children of a union, intersection or concatenation node have the template's languages.
proof fn lemma_children_language(t: FlatPair<u64>, children: Seq<u32>, index: nat, theta: Subst)
    requires
        table::dag(t),
        junco_core::flat::verify::references_before(children, index),
    ensures
        forall|i: int, w: Seq<EventView>| 0 <= i < children.len() ==>
            #[trigger] language::lang(model::gsem(theta), template_regexes(t, children, index)[i], w)
                == numeric::source_regex(t, children[i] as nat, theta, w),
    decreases index, 0nat,
{
    assert forall|i: int, w: Seq<EventView>| 0 <= i < children.len() implies
        #[trigger] language::lang(model::gsem(theta), template_regexes(t, children, index)[i], w)
            == numeric::source_regex(t, children[i] as nat, theta, w) by {
        assert(children[i] < index);
        lemma_template_language(t, children[i] as nat, theta);
        assert(encoding::n_lang(theta, template_regex(t, children[i] as nat), w)
            == numeric::source_regex(t, children[i] as nat, theta, w));
    }
}

// ----- the atoms of a policy's head constants -----

/// The head constant of the `j`-th listed rule at component `k`.
pub(crate) open spec fn policy_constant<E: Event>(rules: Seq<AnalyzedRule<E>>, ids: Seq<nat>, j: int, k: int) -> Option<ConstId> {
    rules[ids[j] as int].constants[k]
}

/// `atom` compares a component with its register or with a head constant that a listed rule has
/// at that component.
pub(crate) open spec fn policy_atom<E: Event>(rules: Seq<AnalyzedRule<E>>, ids: Seq<nat>, atom: Atom) -> bool {
    atom.component < 3 && exists|j: int| 0 <= j < ids.len()
        && #[trigger] policy_constant(rules, ids, j, atom.component as int) is Some
        && (atom.operand is Register
            || atom.operand == Operand::Constant(policy_constant(rules, ids, j, atom.component as int)->Some_0))
}

proof fn lemma_seq_contains_concat<T>(s: Seq<T>, t: Seq<T>, x: T)
    ensures (s.contains(x) || t.contains(x)) ==> (s + t).contains(x),
{
    if s.contains(x) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert((s + t)[i] == x);
    } else if t.contains(x) {
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        assert((s + t)[s.len() + i] == x);
    }
}

proof fn lemma_component_atoms(k: usize, constant: Option<ConstId>)
    ensures
        forall|i: int| #![trigger component_atoms(k, constant)[i]] 0 <= i < component_atoms(k, constant).len() ==>
            component_atoms(k, constant)[i].component == k && constant is Some
            && (component_atoms(k, constant)[i].operand is Register
                || component_atoms(k, constant)[i].operand == Operand::Constant(constant->Some_0)),
        constant is Some ==> component_atoms(k, constant).contains(Atom { component: k, operand: Operand::Register })
            && component_atoms(k, constant).contains(Atom { component: k, operand: Operand::Constant(constant->Some_0) }),
{
    if let Some(v) = constant {
        let s = component_atoms(k, constant);
        assert(s[0] == Atom { component: k, operand: Operand::Register });
        assert(s[1] == Atom { component: k, operand: Operand::Constant(v) });
    }
}

/// The atoms of one head: each compares a component with its register or its head constant,
/// and both atoms are present for every head constant.
proof fn lemma_head_atoms(constants: [Option<ConstId>; 3])
    ensures
        forall|i: int| #![trigger head_atoms(constants)[i]] 0 <= i < head_atoms(constants).len() ==> {
            let atom = head_atoms(constants)[i];
            &&& atom.component < 3 && constants[atom.component as int] is Some
            &&& atom.operand is Register || atom.operand == Operand::Constant(constants[atom.component as int]->Some_0)
        },
        forall|k: int| 0 <= k < 3 && #[trigger] constants[k] is Some ==>
            head_atoms(constants).contains(Atom { component: k as usize, operand: Operand::Register })
            && head_atoms(constants).contains(Atom { component: k as usize, operand: Operand::Constant(constants[k]->Some_0) }),
{
    let a0 = component_atoms(0, constants[0]);
    let a1 = component_atoms(1, constants[1]);
    let a2 = component_atoms(2, constants[2]);
    lemma_component_atoms(0, constants[0]);
    lemma_component_atoms(1, constants[1]);
    lemma_component_atoms(2, constants[2]);
    let s = head_atoms(constants);
    assert(s == a0 + a1 + a2);
    assert forall|i: int| #![trigger s[i]] 0 <= i < s.len() implies {
        let atom = s[i];
        &&& atom.component < 3 && constants[atom.component as int] is Some
        &&& atom.operand is Register || atom.operand == Operand::Constant(constants[atom.component as int]->Some_0)
    } by {
        if i < a0.len() { assert(s[i] == a0[i]); }
        else if i < a0.len() + a1.len() { assert(s[i] == a1[i - a0.len()]); }
        else { assert(s[i] == a2[i - a0.len() - a1.len()]); }
    }
    assert forall|k: int| 0 <= k < 3 && #[trigger] constants[k] is Some implies
        s.contains(Atom { component: k as usize, operand: Operand::Register })
        && s.contains(Atom { component: k as usize, operand: Operand::Constant(constants[k]->Some_0) }) by {
        let r = Atom { component: k as usize, operand: Operand::Register };
        let c = Atom { component: k as usize, operand: Operand::Constant(constants[k]->Some_0) };
        if k == 0 {
            lemma_seq_contains_concat(a0, a1, r); lemma_seq_contains_concat(a0 + a1, a2, r);
            lemma_seq_contains_concat(a0, a1, c); lemma_seq_contains_concat(a0 + a1, a2, c);
        } else if k == 1 {
            lemma_seq_contains_concat(a0, a1, r); lemma_seq_contains_concat(a0 + a1, a2, r);
            lemma_seq_contains_concat(a0, a1, c); lemma_seq_contains_concat(a0 + a1, a2, c);
        } else {
            lemma_seq_contains_concat(a0 + a1, a2, r);
            lemma_seq_contains_concat(a0 + a1, a2, c);
        }
    }
}

/// `policy_atoms` has exactly the atoms of the listed rules' head constants: each of its atoms
/// is a `policy_atom`, and both atoms of every head constant are present.
pub(crate) proof fn lemma_policy_atoms<E: Event>(rules: Seq<AnalyzedRule<E>>, ids: Seq<nat>)
    ensures
        forall|i: int| 0 <= i < policy_atoms(rules, ids).len()
            ==> #[trigger] policy_atom(rules, ids, policy_atoms(rules, ids)[i]),
        forall|j: int, k: int| 0 <= j < ids.len() && 0 <= k < 3 && #[trigger] policy_constant(rules, ids, j, k) is Some
            ==> policy_atoms(rules, ids).contains(Atom { component: k as usize, operand: Operand::Register })
                && policy_atoms(rules, ids).contains(Atom { component: k as usize,
                    operand: Operand::Constant(policy_constant(rules, ids, j, k)->Some_0) }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        let prior = ids.drop_last();
        let last = ids.len() - 1;
        let constants = rules[ids[last] as int].constants;
        let before = policy_atoms(rules, prior);
        let head = head_atoms(constants);
        let atoms = policy_atoms(rules, ids);
        assert(atoms == before + head);
        lemma_policy_atoms(rules, prior);
        lemma_head_atoms(constants);
        assert forall|i: int| 0 <= i < atoms.len() implies #[trigger] policy_atom(rules, ids, atoms[i]) by {
            let atom = atoms[i];
            if i < before.len() {
                assert(atom == before[i]);
                assert(policy_atom(rules, prior, atom));
                let j = choose|j: int| 0 <= j < prior.len()
                    && #[trigger] policy_constant(rules, prior, j, atom.component as int) is Some
                    && (atom.operand is Register
                        || atom.operand == Operand::Constant(policy_constant(rules, prior, j, atom.component as int)->Some_0));
                assert(policy_constant(rules, prior, j, atom.component as int) == policy_constant(rules, ids, j, atom.component as int));
            } else {
                assert(atom == head[i - before.len()]);
                assert(policy_constant(rules, ids, last, atom.component as int) == constants[atom.component as int]);
            }
        }
        assert forall|j: int, k: int| 0 <= j < ids.len() && 0 <= k < 3 && #[trigger] policy_constant(rules, ids, j, k) is Some
            implies atoms.contains(Atom { component: k as usize, operand: Operand::Register })
                && atoms.contains(Atom { component: k as usize,
                    operand: Operand::Constant(policy_constant(rules, ids, j, k)->Some_0) }) by {
            let r = Atom { component: k as usize, operand: Operand::Register };
            let c = Atom { component: k as usize, operand: Operand::Constant(policy_constant(rules, ids, j, k)->Some_0) };
            if j < last {
                assert(policy_constant(rules, prior, j, k) == policy_constant(rules, ids, j, k));
            } else {
                assert(constants[k] is Some);
            }
            lemma_seq_contains_concat(before, head, r);
            lemma_seq_contains_concat(before, head, c);
        }
    }
}

/// The operands of a policy's atoms compare the register of every component where a listed rule
/// has a head constant, and that constant.
pub(crate) proof fn lemma_policy_operands<E: Event>(rules: Seq<AnalyzedRule<E>>, ids: Seq<nat>, operands: Operands)
    requires operands_of(operands, policy_atoms(rules, ids)),
    ensures
        forall|j: int, k: int| 0 <= j < ids.len() && 0 <= k < 3 && #[trigger] policy_constant(rules, ids, j, k) is Some
            ==> operands.register[k]
                && codes(operands.constants[k].view()).contains(policy_constant(rules, ids, j, k)->Some_0 as nat),
{
    let atoms = policy_atoms(rules, ids);
    lemma_policy_atoms(rules, ids);
    assert forall|j: int, k: int| 0 <= j < ids.len() && 0 <= k < 3 && #[trigger] policy_constant(rules, ids, j, k) is Some
        implies operands.register[k]
            && codes(operands.constants[k].view()).contains(policy_constant(rules, ids, j, k)->Some_0 as nat) by {
        let v = policy_constant(rules, ids, j, k)->Some_0;
        let r = Atom { component: k as usize, operand: Operand::Register };
        let c = Atom { component: k as usize, operand: Operand::Constant(v) };
        let x = choose|x: int| 0 <= x < atoms.len() && atoms[x] == r;
        let y = choose|y: int| 0 <= y < atoms.len() && atoms[y] == c;
        assert(atoms[x].component == k && atoms[x].operand == Operand::Register);
        assert(operands.register[k]);
        assert(atoms[y].component == k && atoms[y].operand == Operand::Constant(v));
        assert(operands.constants[k].view().contains(v));
        lemma_codes(operands.constants[k].view());
        let i = choose|i: int| 0 <= i < operands.constants[k].view().len() && operands.constants[k].view()[i] == v;
        assert(operands.constants[k].view()[i] as nat == v as nat);
    }
}

// ----- F3: exact firing -----

/// `g` pins the registers of the head constants and leaves the others free.
pub(crate) open spec fn head_registers(g: Constraint, constants: [Option<ConstId>; 3]) -> bool {
    forall|i: int| 0 <= i < 3 ==> g.0[i]@ == match constants[i] {
        Some(v) => implementation::RegisterView::Equals(v as nat),
        None => implementation::RegisterView::Differs(Set::empty()),
    }
}

/// What `Constraint::head(constants, universes)` ensures of its result.
pub(crate) open spec fn head_result(constants: [Option<ConstId>; 3], universes: Universes, result: Option<Constraint>) -> bool {
    match result {
        Some(c) => constraint_wf(c) && head_registers(c, constants)
            && implementation::constraint_of(c@) == inclusion::head_constraint(head_view(constants))
            && inclusion::satisfiable(ndomains(universes), implementation::constraint_of(c@)),
        None => !inclusion::satisfiable(ndomains(universes), inclusion::head_constraint(head_view(constants))),
    }
}

/// The numeric head of a stored rule is the head of its constants.
pub(crate) proof fn lemma_stored_head<E: Event>(a: PolicyAnalyzer<E>, i: int)
    requires analyzer_state_wf(a), 0 <= i < a.rules@.len(),
    ensures stored_numeric(a.rules@[i]).head == head_view(a.rules@[i].constants),
{
    assert(stored_rule_wf(a.constants, a.rules@[i]));
}

/// θ with component `c` set to `x`.
pub(crate) open spec fn with_field(theta: Subst, c: Component, x: nat) -> Subst {
    match c {
        Component::Principal => EventView { principal: x, action: theta.action, resource: theta.resource },
        Component::Action => EventView { principal: theta.principal, action: x, resource: theta.resource },
        Component::Resource => EventView { principal: theta.principal, action: theta.action, resource: x },
    }
}

proof fn lemma_with_field(theta: Subst, c: Component, x: nat)
    ensures forall|c2: Component| #[trigger] language::field_value(with_field(theta, c, x), c2)
        == if c2 == c { x } else { language::field_value(theta, c2) },
{
    assert forall|c2: Component| #[trigger] language::field_value(with_field(theta, c, x), c2)
        == if c2 == c { x } else { language::field_value(theta, c2) } by {
        match c { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        match c2 { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
    }
}

/// The first value outside `u32`.
pub(crate) open spec fn beyond_codes() -> nat { 0x1_0000_0000nat }

/// A case that leaves an unrestricted component's register differing from finitely many codes is
/// satisfied after moving that component beyond every code.
proof fn lemma_escape(d: encoding::NDomains, g: implementation::ConstraintView, theta: Subst, c: Component)
    requires
        encoding::n_theta_ok(d, theta), inclusion::sat_by(theta, implementation::constraint_of(g)),
        encoding::n_domain(d, c) is None,
        implementation::register_of(g, c) matches implementation::RegisterView::Differs(vs)
            && forall|x: nat| vs.contains(x) ==> x <= u32::MAX,
    ensures
        encoding::n_theta_ok(d, with_field(theta, c, beyond_codes())),
        inclusion::sat_by(with_field(theta, c, beyond_codes()), implementation::constraint_of(g)),
{
    let moved = with_field(theta, c, beyond_codes());
    lemma_with_field(theta, c, beyond_codes());
    lemma_constraint_view(g);
    assert(language::event_wf(moved)) by {
        assert(language::field_value(moved, Component::Principal) <= u64::MAX);
        assert(language::field_value(moved, Component::Action) <= u64::MAX);
        assert(language::field_value(moved, Component::Resource) <= u64::MAX);
    }
    assert forall|c2: Component| #[trigger] encoding::n_domain(d, c2) is Some
        implies encoding::n_domain(d, c2)->Some_0.contains(language::field_value(moved, c2)) by {
        assert(c2 != c);
    }
    assert forall|l: inclusion::Literal| #[trigger] implementation::constraint_of(g).contains(l)
        implies inclusion::literal_holds(moved, l) by {
        if l.component != c { assert(inclusion::literal_holds(theta, l)); }
    }
}

/// In a satisfiable case that entails `x_c = v` for a `u32` code `v`, a register that is an
/// equality or differs from finitely many codes at an unrestricted component is `x_c = v`.
proof fn lemma_case_register(d: encoding::NDomains, g: implementation::ConstraintView,
    head: inclusion::Constraint, theta: Subst, c: Component, v: nat)
    requires
        encoding::n_theta_ok(d, theta), inclusion::sat_by(theta, implementation::constraint_of(g)),
        inclusion::entails(d, implementation::constraint_of(g), head),
        head.contains(inclusion::eq_literal(c, v)), v <= u32::MAX,
        implementation::register_of(g, c) is Equals || (encoding::n_domain(d, c) is None
            && forall|x: nat| implementation::register_of(g, c)->Differs_0.contains(x) ==> x <= u32::MAX),
    ensures implementation::register_of(g, c) == implementation::RegisterView::Equals(v),
{
    lemma_constraint_view(g);
    match implementation::register_of(g, c) {
        implementation::RegisterView::Equals(w) => {
            assert(implementation::constraint_of(g).contains(inclusion::eq_literal(c, w)));
            assert(inclusion::sat_by(theta, head));
            assert(inclusion::literal_holds(theta, inclusion::eq_literal(c, v)));
            assert(inclusion::literal_holds(theta, inclusion::eq_literal(c, w)));
        },
        implementation::RegisterView::Differs(vs) => {
            lemma_escape(d, g, theta, c);
            let moved = with_field(theta, c, beyond_codes());
            lemma_with_field(theta, c, beyond_codes());
            assert(inclusion::sat_by(moved, head));
            assert(inclusion::literal_holds(moved, inclusion::eq_literal(c, v)));
        },
    }
}

/// With the register flag set, a split option is an equality unless the component is
/// unrestricted.
proof fn lemma_option_decided(current: implementation::RegisterView, constants: Set<nat>,
    universe: Option<Set<nat>>, r: implementation::RegisterView)
    requires register_options(current, true, constants, universe).contains(r),
    ensures r is Equals || universe is None,
{
    if let implementation::RegisterView::Differs(differs) = current {
        if let Some(values) = universe {
            let v = choose|v: nat| values.difference(differs).contains(v) && implementation::RegisterView::Equals(v) == r;
        }
    }
}

/// One component of the exact firing test: where the `j`-th listed rule has head constant `v`,
/// a satisfiable split case that entails the rule's head constraint pins the register to `v`.
proof fn lemma_firing_component<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>, base: Constraint,
    operands: Operands, case: Constraint, j: int, theta: Subst, k: int)
    requires
        0 <= j < ids.len(), 0 <= k < 3,
        operands_of(operands, policy_atoms(a.rules@, ids)),
        register_options(base.0[k]@, operands.register[k], codes(operands.constants[k].view()),
            domain_view(a.universes[k])).contains(case.0[k]@),
        encoding::n_theta_ok(ndomains(a.universes), theta),
        inclusion::sat_by(theta, implementation::constraint_of(case@)),
        inclusion::entails(ndomains(a.universes), implementation::constraint_of(case@),
            inclusion::head_constraint(head_view(a.rules@[ids[j] as int].constants))),
    ensures
        register_entails(case.0[k]@, match a.rules@[ids[j] as int].constants[k] {
            Some(v) => implementation::RegisterView::Equals(v as nat),
            None => implementation::RegisterView::Differs(Set::empty()),
        }),
{
    let constants = a.rules@[ids[j] as int].constants;
    match constants[k] {
        None => {
            match case.0[k]@ {
                implementation::RegisterView::Equals(_) => {},
                implementation::RegisterView::Differs(vs) => { assert(Set::<nat>::empty().subset_of(vs)); },
            }
        },
        Some(v) => {
            let c = component_of(k as usize);
            let d = ndomains(a.universes);
            assert(policy_constant(a.rules@, ids, j, k) == Some(v));
            lemma_policy_operands(a.rules@, ids, operands);
            lemma_option_decided(base.0[k]@, codes(operands.constants[k].view()), domain_view(a.universes[k]), case.0[k]@);
            assert(implementation::register_of(case@, c) == case.0[k]@);
            assert(encoding::n_domain(d, c) == domain_view(a.universes[k]));
            inclusion::lemma_head_constraint(head_view(constants));
            assert(encoding::n_head_field(head_view(constants), c) == Some(v as nat));
            if let RegisterConstraint::Differs(values) = case.0[k] {
                lemma_codes(values.view());
            }
            lemma_case_register(d, case@, inclusion::head_constraint(head_view(constants)), theta, c, v as nat);
        },
    }
}

/// Exact firing (R3): for a satisfiable case of the split on a policy's head constants, the
/// syntactic test `Constraint::head` then `Constraint::entails` against the `j`-th listed rule
/// is semantic entailment of the rule's head constraint.
pub(crate) proof fn lemma_exact_firing<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>, base: Constraint,
    operands: Operands, case: Constraint, j: int, hc: Option<Constraint>)
    requires
        analyzer_state_wf(a), ids_valid(a, ids), 0 <= j < ids.len(),
        operands_of(operands, policy_atoms(a.rules@, ids)),
        split_views(base, operands, a.universes).contains(case@),
        inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(case@)),
        head_result(a.rules@[ids[j] as int].constants, a.universes, hc),
    ensures
        (hc matches Some(h) && register_entails(case@.principal, h@.principal)
            && register_entails(case@.action, h@.action) && register_entails(case@.resource, h@.resource))
        == inclusion::entails(ndomains(a.universes), implementation::constraint_of(case@),
            inclusion::head_constraint(numeric_policy(a, ids)[j].head)),
{
    let d = ndomains(a.universes);
    let g = case@;
    let id = ids[j] as int;
    let constants = a.rules@[id].constants;
    assert(ids[j] < a.rules@.len());
    lemma_stored_head(a, id);
    assert(numeric_policy(a, ids)[j] == stored_numeric(a.rules@[id]));
    let head = inclusion::head_constraint(head_view(constants));
    if let Some(h) = hc {
        if register_entails(g.principal, h@.principal) && register_entails(g.action, h@.action)
            && register_entails(g.resource, h@.resource) {
            lemma_constraint_entails(g, h@);
        }
    }
    if inclusion::entails(d, implementation::constraint_of(g), head) {
        let theta = choose|theta: Subst| encoding::n_theta_ok(d, theta) && inclusion::sat_by(theta, implementation::constraint_of(g));
        assert(inclusion::sat_by(theta, head));
        assert(inclusion::satisfiable(d, head));
        let h = hc->Some_0;
        lemma_register_product_members(
            register_options(base.0[0]@, operands.register[0], codes(operands.constants[0].view()), domain_view(a.universes[0])),
            register_options(base.0[1]@, operands.register[1], codes(operands.constants[1].view()), domain_view(a.universes[1])),
            register_options(base.0[2]@, operands.register[2], codes(operands.constants[2].view()), domain_view(a.universes[2])));
        lemma_firing_component(a, ids, base, operands, case, j, theta, 0);
        lemma_firing_component(a, ids, base, operands, case, j, theta, 1);
        lemma_firing_component(a, ids, base, operands, case, j, theta, 2);
    }
}

// ----- F2: the policy split -----

/// The cases of a split as a family of constraints (`split_contract`).
pub(crate) open spec fn case_set(cases: Seq<Constraint>) -> Set<inclusion::Constraint> {
    constraint_views(cases).map(|v: implementation::ConstraintView| implementation::constraint_of(v))
}

/// The codes of the constant book at one component.
pub(crate) open spec fn book_codes<E: Event>(c: Constants<E>, field: Component) -> Set<nat> {
    Set::new(|n: nat| code_field(c, field, n)).unwrap_or(Set::empty())
}

pub(crate) open spec fn book_vocabulary<E: Event>(c: Constants<E>) -> [Set<nat>; 3] {
    [book_codes(c, Component::Principal), book_codes(c, Component::Action), book_codes(c, Component::Resource)]
}

proof fn lemma_book_codes<E: Event>(c: Constants<E>, field: Component)
    ensures
        forall|n: nat| #[trigger] book_codes(c, field).contains(n) == code_field(c, field, n),
        book_codes(c, field).len() <= c.values@.len(),
{
    let all = Seq::new(c.values@.len(), |i: int| (i + 1) as nat);
    let f = |n: nat| code_field(c, field, n);
    assert forall|n: nat| f(n) implies all.to_set().to_iset().contains(n) by {
        assert(all[n - 1] == n);
        assert(all.contains(n));
    }
    inclusion::lemma_set_new_bounded(f, all.to_set().to_iset());
    assert(book_codes(c, field).subset_of(all.to_set()));
    vstd::set_lib::lemma_len_subset(book_codes(c, field), all.to_set());
    all.lemma_cardinality_of_set();
}

/// A head constant of a stored rule is a book code of its component.
pub(crate) proof fn lemma_head_constant_code<E: Event>(a: PolicyAnalyzer<E>, i: int, k: int)
    requires analyzer_state_wf(a), 0 <= i < a.rules@.len(), 0 <= k < 3, a.rules@[i].constants[k] is Some,
    ensures code_field(a.constants, component_of(k as usize), a.rules@[i].constants[k]->Some_0 as nat),
{
    let r = a.rules@[i];
    assert(stored_rule_wf(a.constants, r));
    lemma_lowered_payload(a.constants, r.source@.1.source, r.tail);
    assert(head_view(r.constants) == pins(r.tail.head@));
    assert(option_code(r.constants[k]) == encoding::head_code(r.tail.head@[k])) by {
        if k == 0 {} else if k == 1 {} else {}
    }
    assert(enc::field_at(k) == component_of(k as usize));
    if let FlatHead::Constant(v) = r.tail.head@[k] {
        assert(code_field(a.constants, enc::field_at(k), v as nat));
    }
}

/// The book codes per component bound the operands of a policy split and the declared
/// universes.
proof fn lemma_policy_vocabulary<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>, operands: Operands)
    requires analyzer_state_wf(a), ids_valid(a, ids), operands_of(operands, policy_atoms(a.rules@, ids)),
    ensures
        atoms_wf(policy_atoms(a.rules@, ids)),
        forall|k: int| 0 <= k < 3 ==> {
            &&& codes(operands.constants[k].view()).subset_of(#[trigger] book_vocabulary(a.constants)[k])
            &&& operands.constants[k].view().no_duplicates()
            &&& exec::domain_values(a.universes[k]).subset_of(book_vocabulary(a.constants)[k])
            &&& universe_distinct(a.universes[k])
            &&& book_vocabulary(a.constants)[k].len() <= a.constants.values@.len()
            &&& forall|n: nat| #[trigger] book_vocabulary(a.constants)[k].contains(n)
                == code_field(a.constants, component_of(k as usize), n)
        },
{
    let c = a.constants;
    let v = book_vocabulary(c);
    let atoms = policy_atoms(a.rules@, ids);
    lemma_book_codes(c, Component::Principal);
    lemma_book_codes(c, Component::Action);
    lemma_book_codes(c, Component::Resource);
    lemma_policy_atoms(a.rules@, ids);
    assert forall|i: int| 0 <= i < atoms.len() implies atoms[i].component < 3 by {
        assert(policy_atom(a.rules@, ids, atoms[i]));
    }
    assert(exec::atoms_in_vocabulary(atoms, v)) by {
        assert forall|i: int| #![trigger atoms[i]] 0 <= i < atoms.len() implies atoms[i].component < 3
            && match atoms[i].operand { Operand::Constant(code) => v[atoms[i].component as int].contains(code as nat), _ => true } by {
            let atom = atoms[i];
            assert(policy_atom(a.rules@, ids, atom));
            let k = atom.component as int;
            let j = choose|j: int| 0 <= j < ids.len() && #[trigger] policy_constant(a.rules@, ids, j, k) is Some
                && (atom.operand is Register || atom.operand == Operand::Constant(policy_constant(a.rules@, ids, j, k)->Some_0));
            assert(ids[j] < a.rules@.len());
            lemma_head_constant_code(a, ids[j] as int, k);
        }
    }
    exec::lemma_operand_vocabulary(operands, atoms, v);
    assert forall|k: int| 0 <= k < 3 implies exec::domain_values(a.universes[k]).subset_of(v[k])
        && universe_distinct(a.universes[k]) by {
        assert(universes_wf(c, a.universes));
        if let Some(values) = a.universes[k] {
            lemma_codes((*values)@);
            assert forall|n: nat| exec::domain_values(a.universes[k]).contains(n) implies v[k].contains(n) by {
                let x = choose|x: int| 0 <= x < (*values)@.len() && (*values)@[x] as nat == n;
                assert(enc::field_at(k) == component_of(k as usize));
            }
        }
    }
}

/// The head constants of a policy are pairs of the split's atoms.
proof fn lemma_head_pairs_atoms<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>)
    requires analyzer_state_wf(a), ids_valid(a, ids),
    ensures inclusion::head_pairs(numeric_policy(a, ids)).subset_of(
        search::domain_pairs(ndomains(a.universes), atom_set(policy_atoms(a.rules@, ids)))),
{
    let p = numeric_policy(a, ids);
    let atoms = policy_atoms(a.rules@, ids);
    let set = atom_set(atoms);
    inclusion::lemma_head_pairs(p);
    search::lemma_atom_pairs_members(set);
    search::lemma_domain_pairs_members(ndomains(a.universes), set);
    lemma_policy_atoms(a.rules@, ids);
    assert forall|pair: (Component, nat)| inclusion::head_pairs(p).contains(pair) implies
        search::domain_pairs(ndomains(a.universes), set).contains(pair) by {
        let j = choose|j: int| 0 <= j < p.len() && #[trigger] encoding::n_head_field(p[j].head, pair.0) == Some(pair.1);
        let id = ids[j] as int;
        let k = component_index(pair.0) as int;
        assert(ids[j] < a.rules@.len());
        lemma_stored_head(a, id);
        assert(p[j] == stored_numeric(a.rules@[id]));
        let constants = a.rules@[id].constants;
        assert(encoding::n_head_field(head_view(constants), pair.0) == option_code(constants[k])) by {
            match pair.0 { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
        assert(policy_constant(a.rules@, ids, j, k) == constants[k]);
        let x = constants[k]->Some_0;
        let r = Atom { component: k as usize, operand: Operand::Register };
        let c = Atom { component: k as usize, operand: Operand::Constant(x) };
        assert(component_of(k as usize) == pair.0) by {
            match pair.0 { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
        }
        assert(atoms.contains(r) && atoms.contains(c));
        assert(atoms.to_set().contains(r) && atoms.to_set().contains(c));
        assert(set.contains(r@));
        assert(set.contains(c@));
        assert(r@ == model::Primitive::Eq(pair.0, model::GTerm::Variable(pair.0)));
        assert(c@ == model::Primitive::Eq(pair.0, model::GTerm::Constant(pair.1)));
        assert(search::atom_pairs(set).contains(pair));
    }
}

/// The split of a stored rule's head constraint on a policy's head constants (F2): its cases
/// satisfy `inclusion::split_ok` on the policy's head pairs, and each is satisfiable and over
/// book codes.
pub(crate) proof fn lemma_policy_split<E: Event>(a: PolicyAnalyzer<E>, rule: int, ids: Seq<nat>,
    base: Constraint, operands: Operands, cases: Seq<Constraint>)
    requires
        analyzer_state_wf(a), ids_valid(a, ids), 0 <= rule < a.rules@.len(),
        head_result(a.rules@[rule].constants, a.universes, Some(base)),
        operands_of(operands, policy_atoms(a.rules@, ids)),
        constraint_views(cases) == split_views(base, operands, a.universes),
    ensures
        implementation::constraint_of(base@) == inclusion::head_constraint(stored_numeric(a.rules@[rule]).head),
        inclusion::split_ok(ndomains(a.universes), implementation::constraint_of(base@),
            inclusion::head_pairs(numeric_policy(a, ids)), case_set(cases)),
        forall|i: int| 0 <= i < cases.len() ==> split_views(base, operands, a.universes).contains(#[trigger] cases[i]@)
            && constraint_codes_wf(a.constants, cases[i]@)
            && inclusion::satisfiable(ndomains(a.universes), implementation::constraint_of(cases[i]@)),
{
    let d = ndomains(a.universes);
    let atoms = policy_atoms(a.rules@, ids);
    let v = book_vocabulary(a.constants);
    let g = implementation::constraint_of(base@);
    lemma_stored_head(a, rule);
    lemma_policy_vocabulary(a, ids, operands);
    lemma_split_contract(base, operands, a.universes, cases);
    assert(inclusion::split_ok(d, g, search::domain_pairs(d, atom_set(atoms)), case_set(cases)));
    lemma_head_pairs_atoms(a, ids);
    inclusion::lemma_split_ok_mono(d, g, inclusion::head_pairs(numeric_policy(a, ids)), search::domain_pairs(d, atom_set(atoms)), case_set(cases));
    assert(exec::constraint_in_vocabulary(base@, v)) by {
        let constants = a.rules@[rule].constants;
        assert forall|k: int| 0 <= k < 3 implies exec::register_in_vocabulary(base.0[k]@, v[k]) by {
            if constants[k] is Some { lemma_head_constant_code(a, rule, k); }
            else { assert(Set::<nat>::empty().subset_of(v[k])); }
        }
        assert(exec::register_in_vocabulary(base.0[0]@, v[0]));
        assert(exec::register_in_vocabulary(base.0[1]@, v[1]));
        assert(exec::register_in_vocabulary(base.0[2]@, v[2]));
    }
    assert forall|i: int| 0 <= i < cases.len() implies split_views(base, operands, a.universes).contains(#[trigger] cases[i]@)
        && constraint_codes_wf(a.constants, cases[i]@)
        && inclusion::satisfiable(d, implementation::constraint_of(cases[i]@)) by {
        let case = cases[i]@;
        lemma_constraint_view_at(cases, i);
        assert(case_set(cases).contains(implementation::constraint_of(case)));
        exec::lemma_refined_vocabulary(base, operands, a.universes, v, case);
        assert forall|field: Component, n: nat| #[trigger] register_codes(implementation::register_of(case, field)).contains(n)
            implies code_field(a.constants, field, n) by {
            let k = component_index(field) as int;
            assert(component_of(k as usize) == field) by {
                match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} }
            }
            match field {
                Component::Principal => assert(exec::register_in_vocabulary(case.principal, v[0])),
                Component::Action => assert(exec::register_in_vocabulary(case.action, v[1])),
                Component::Resource => assert(exec::register_in_vocabulary(case.resource, v[2])),
            }
            assert(v[k].contains(n));
        }
    }
}

/// Capacity of a policy split: every register has at most `|book| + 1` options.
pub(crate) proof fn lemma_split_capacity<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<nat>, base: Constraint, operands: Operands)
    requires
        analyzer_state_wf(a), ids_valid(a, ids), policy_capacity(a),
        operands_of(operands, policy_atoms(a.rules@, ids)),
    ensures split_capacity(base, operands, a.universes),
{
    let v = book_vocabulary(a.constants);
    let n = a.constants.values@.len();
    lemma_policy_vocabulary(a, ids, operands);
    exec::lemma_register_sequence_count(base.0[0]@, operands.register[0], operands.constants[0].view(), a.universes[0], v[0]);
    exec::lemma_register_sequence_count(base.0[1]@, operands.register[1], operands.constants[1].view(), a.universes[1], v[1]);
    exec::lemma_register_sequence_count(base.0[2]@, operands.register[2], operands.constants[2].view(), a.universes[2], v[2]);
    let x = v[0].len() + 2;
    let y = v[1].len() + 2;
    let z = v[2].len() + 2;
    assert(v[0].len() <= n && v[1].len() <= n && v[2].len() <= n);
    assert(x <= (n + 2) * (n + 2) * (n + 2) && y <= (n + 2) * (n + 2) * (n + 2) && z <= (n + 2) * (n + 2) * (n + 2)
        && x * y <= (n + 2) * (n + 2) * (n + 2) && x * y * z <= (n + 2) * (n + 2) * (n + 2)) by (nonlinear_arith)
        requires x <= n + 2, y <= n + 2, z <= n + 2, 2 <= x, 2 <= y, 2 <= z;
    assert(exec::resource_capacity(v));
    exec::lemma_product_capacity(
        register_count(base.0[0]@, operands.register[0], operands.constants[0].view(), a.universes[0]),
        register_count(base.0[1]@, operands.register[1], operands.constants[1].view(), a.universes[1]),
        register_count(base.0[2]@, operands.register[2], operands.constants[2].view(), a.universes[2]), v);
}

} // verus!
