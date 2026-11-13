//! Exact firing and the policy split (R3): the cases of a split on the head constants of a
//! policy decide those constants, so `Constraint::entails` against a rule's head constraint is
//! exactly semantic entailment; the cases satisfy `inclusion::split_ok` on `head_pairs`; and a
//! stored template's tail has the template's language (`policy::template_regex`).

use super::policy::{template_regex, template_regexes, template_test, template_tests};
use super::table;
use history_semantics::compile_verify as numeric;
use history_semantics::verify::refinement::encoding;
use junco_core::flat::{FlatPair, FlatRegex, FlatTest};
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::{self as language, EventView, Subst};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

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

} // verus!
