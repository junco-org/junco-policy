//! Semantic invariants for the executable simulation memo.

use crate::native::{key_obligations, representatives};
use crate::simulation::{Node, Simulation, TestNode};
use history_semantics::verify::refinement::pruning as paper;
use history_semantics::{
    SymbolicLanguage, normalize_verify as norm, symbolic_language_verify as facade,
};
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TestId};
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::history_specs::{self as language, Regex};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;

pub(crate) open spec fn memo_obligations() -> bool {
    key_obligations::<(RegexId, RegexId)>() && key_obligations::<(TestId, TestId)>()
}

pub(crate) open spec fn semantic_le() -> spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool {
    |x: Regex<model::Test>, y: Regex<model::Test>| paper::lang_le(x, y)
}

pub(crate) open spec fn semantic_tle() -> spec_fn(model::Test, model::Test) -> bool {
    |x: model::Test, y: model::Test| paper::test_le_sem(x, y)
}

pub(crate) open spec fn ids_valid(l: SymbolicLanguage, ids: Seq<RegexId>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < facade::graph(l).regexes.len()
}

pub(crate) open spec fn test_ids_valid(l: SymbolicLanguage, ids: Seq<TestId>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < facade::graph(l).tests.len()
}

pub(crate) open spec fn lifts(l: SymbolicLanguage, ids: Seq<RegexId>) -> Seq<Regex<model::Test>> {
    Seq::new(ids.len(), |i: int| facade::abs(l, ids[i]))
}

pub(crate) open spec fn test_lifts(l: SymbolicLanguage, ids: Seq<TestId>) -> Seq<model::Test> {
    Seq::new(ids.len(), |i: int| model::lift_test(facade::graph(l), ids[i]@))
}

pub(crate) open spec fn regex_le(l: SymbolicLanguage, x: RegexId, y: RegexId) -> bool {
    paper::lang_le(facade::abs(l, x), facade::abs(l, y))
}

pub(crate) open spec fn test_le(l: SymbolicLanguage, x: TestId, y: TestId) -> bool {
    paper::test_le_sem(model::lift_test(facade::graph(l), x@),
        model::lift_test(facade::graph(l), y@))
}

pub(crate) open spec fn memo_wf(s: Simulation, l: SymbolicLanguage) -> bool {
    &&& forall|i: int| #![trigger representatives(s.known)[i]]
        0 <= i < representatives(s.known).len() ==> {
        let entry = representatives(s.known)[i];
        entry.0.0@ < facade::graph(l).regexes.len()
            && entry.0.1@ < facade::graph(l).regexes.len()
            && (entry.1 ==> regex_le(l, entry.0.0, entry.0.1))
    }
    &&& forall|i: int| #![trigger representatives(s.known_tests)[i]]
        0 <= i < representatives(s.known_tests).len() ==> {
        let entry = representatives(s.known_tests)[i];
        entry.0.0@ < facade::graph(l).tests.len()
            && entry.0.1@ < facade::graph(l).tests.len()
            && (entry.1 ==> test_le(l, entry.0.0, entry.0.1))
    }
}

// Only new regex entries are rank-bounded; test ids belong to a different arena.
pub(crate) open spec fn memo_grows(a: Simulation, b: Simulation, bound: nat) -> bool {
    &&& representatives(a.known).is_prefix_of(representatives(b.known))
    &&& representatives(a.known_tests).is_prefix_of(representatives(b.known_tests))
    &&& forall|i: int| #![trigger representatives(b.known)[i]]
        representatives(a.known).len() <= i
        < representatives(b.known).len() ==> {
        let key = representatives(b.known)[i].0;
        key.0@ + key.1@ < bound
    }
}

pub(crate) open spec fn tests_grow(a: Simulation, b: Simulation, bound: nat) -> bool {
    &&& representatives(a.known) == representatives(b.known)
    &&& representatives(a.known_tests).is_prefix_of(representatives(b.known_tests))
    &&& forall|i: int| #![trigger representatives(b.known_tests)[i]]
        representatives(a.known_tests).len() <= i
        < representatives(b.known_tests).len() ==> {
        let key = representatives(b.known_tests)[i].0;
        key.0@ + key.1@ < bound
    }
}

pub(crate) proof fn lemma_growth_trans(a: Simulation, b: Simulation, c: Simulation,
    smaller: nat, bound: nat)
    requires memo_grows(a, b, bound), memo_grows(b, c, smaller), smaller <= bound,
    ensures memo_grows(a, c, bound),
{
    assert forall|i: int| #![trigger representatives(c.known)[i]]
        representatives(a.known).len() <= i
        < representatives(c.known).len() implies {
        let key = representatives(c.known)[i].0;
        key.0@ + key.1@ < bound
    } by {
        if i < representatives(b.known).len() {
            assert(representatives(c.known)[i] == representatives(b.known)[i]);
        }
    }
}

pub(crate) proof fn lemma_tests_trans(a: Simulation, b: Simulation, c: Simulation,
    smaller: nat, bound: nat)
    requires tests_grow(a, b, bound), tests_grow(b, c, smaller), smaller <= bound,
    ensures tests_grow(a, c, bound),
{
    assert forall|i: int| #![trigger representatives(c.known_tests)[i]]
        representatives(a.known_tests).len() <= i
        < representatives(c.known_tests).len() implies {
        let key = representatives(c.known_tests)[i].0;
        key.0@ + key.1@ < bound
    } by {
        if i < representatives(b.known_tests).len() {
            assert(representatives(c.known_tests)[i] == representatives(b.known_tests)[i]);
        }
    }
}

pub(crate) proof fn lemma_regex_absent(a: Simulation, b: Simulation, x: RegexId, y: RegexId)
    requires memo_grows(a, b, x@ + y@),
        forall|i: int| 0 <= i < representatives(a.known).len()
            ==> !(x, y).eq_spec(&representatives(a.known)[i].0),
    ensures forall|i: int| 0 <= i < representatives(b.known).len()
        ==> !(x, y).eq_spec(&representatives(b.known)[i].0),
{
    assert forall|i: int| 0 <= i < representatives(b.known).len() implies
        !(x, y).eq_spec(&representatives(b.known)[i].0) by {
        if i < representatives(a.known).len() {
            assert(representatives(b.known)[i] == representatives(a.known)[i]);
        }
    }
}

pub(crate) proof fn lemma_test_absent(a: Simulation, b: Simulation, x: TestId, y: TestId)
    requires tests_grow(a, b, x@ + y@),
        forall|i: int| 0 <= i < representatives(a.known_tests).len()
            ==> !(x, y).eq_spec(&representatives(a.known_tests)[i].0),
    ensures forall|i: int| 0 <= i < representatives(b.known_tests).len()
        ==> !(x, y).eq_spec(&representatives(b.known_tests)[i].0),
{
    assert forall|i: int| 0 <= i < representatives(b.known_tests).len() implies
        !(x, y).eq_spec(&representatives(b.known_tests)[i].0) by {
        if i < representatives(a.known_tests).len() {
            assert(representatives(b.known_tests)[i] == representatives(a.known_tests)[i]);
        }
    }
}

pub(crate) proof fn lemma_memo_frame(s: Simulation, before: SymbolicLanguage,
    after: SymbolicLanguage)
    requires facade::language_wf(before), facade::language_wf(after),
        facade::frame(before, after), memo_wf(s, before),
    ensures memo_wf(s, after),
{
    facade::lemma_language_wf(before);
    model::lemma_graph_wf_elim(facade::graph(before));
    model::lemma_lift_stable_under_extends(facade::graph(before), facade::graph(after));
    assert forall|i: int| #![trigger representatives(s.known)[i]]
        0 <= i < representatives(s.known).len() implies {
        let entry = representatives(s.known)[i];
        entry.0.0@ < facade::graph(after).regexes.len()
            && entry.0.1@ < facade::graph(after).regexes.len()
            && (entry.1 ==> regex_le(after, entry.0.0, entry.0.1))
    } by {}
    assert forall|i: int| #![trigger representatives(s.known_tests)[i]]
        0 <= i < representatives(s.known_tests).len() implies {
        let entry = representatives(s.known_tests)[i];
        entry.0.0@ < facade::graph(after).tests.len()
            && entry.0.1@ < facade::graph(after).tests.len()
            && (entry.1 ==> test_le(after, entry.0.0, entry.0.1))
    } by {}
}

impl View for Node {
    type V = model::RegexKindNode;
    open(crate) spec fn view(&self) -> model::RegexKindNode {
        match self {
            Node::Empty => model::RegexKindNode::Empty,
            Node::All => model::RegexKindNode::All,
            Node::Epsilon => model::RegexKindNode::Epsilon,
            Node::Test(t) => model::RegexKindNode::Test(t@),
            Node::Union(cs) => model::RegexKindNode::Union(model::regex_ids(cs.view())),
            Node::Concat(cs) => model::RegexKindNode::Concat(model::regex_ids(cs.view())),
            Node::Star(r) => model::RegexKindNode::Star(r@),
            Node::Intersect(cs) => model::RegexKindNode::Intersect(model::regex_ids(cs.view())),
            Node::Not(r) => model::RegexKindNode::Not(r@),
        }
    }
}

pub(crate) open spec fn node_wf(l: SymbolicLanguage, id: RegexId, n: Node) -> bool {
    id@ < facade::graph(l).regexes.len()
        && n@ == facade::graph(l).regexes[id@ as int].kind
        && model::regex_kind_wf_at(facade::graph(l), n@, id@)
        && facade::abs(l, id) == norm::regex_unbounded_kind(facade::graph(l), n@)
        && match n {
            Node::Union(cs) | Node::Concat(cs) | Node::Intersect(cs) =>
                ids_valid(l, cs.view()) && forall|i: int| #![trigger cs.view()[i]]
                    0 <= i < cs.view().len() ==> cs.view()[i]@ < id@,
            _ => true,
        }
}

pub(crate) open spec fn test_matches(n: TestNode, k: model::TestNode) -> bool {
    match n {
        TestNode::True => k == model::TestNode::True,
        TestNode::False => k == model::TestNode::False,
        TestNode::Atom => k is Atom,
        TestNode::And(cs) => k == model::TestNode::And(model::test_ids(cs.view())),
        TestNode::Or(cs) => k == model::TestNode::Or(model::test_ids(cs.view())),
    }
}

pub(crate) open spec fn test_node_wf(l: SymbolicLanguage, id: TestId, n: TestNode) -> bool {
    id@ < facade::graph(l).tests.len()
        && test_matches(n, facade::graph(l).tests[id@ as int])
        && model::test_node_wf_at(facade::graph(l), facade::graph(l).tests[id@ as int], id@)
        && match n {
            TestNode::True => model::lift_test(facade::graph(l), id@) == model::Test::True,
            TestNode::False => model::lift_test(facade::graph(l), id@) == model::Test::False,
            TestNode::Atom => model::lift_test(facade::graph(l), id@) is Atom,
            TestNode::And(cs) => model::lift_test(facade::graph(l), id@)
                == model::Test::And(test_lifts(l, cs.view())),
            TestNode::Or(cs) => model::lift_test(facade::graph(l), id@)
                == model::Test::Or(test_lifts(l, cs.view())),
        }
        && match n {
            TestNode::And(cs) | TestNode::Or(cs) =>
                test_ids_valid(l, cs.view()) && forall|i: int| #![trigger cs.view()[i]]
                    0 <= i < cs.view().len() ==> cs.view()[i]@ < id@,
            _ => true,
        }
}

pub(crate) proof fn lemma_node(l: SymbolicLanguage, id: RegexId, n: Node)
    requires facade::language_wf(l), id@ < facade::graph(l).regexes.len(),
        n@ == facade::graph(l).regexes[id@ as int].kind,
    ensures node_wf(l, id, n),
{
    facade::lemma_language_wf(l);
    norm::regex_unfold(facade::graph(l), id@);
    match n {
        Node::Union(cs) | Node::Concat(cs) | Node::Intersect(cs) => {
            assert forall|i: int| #![trigger cs.view()[i]] 0 <= i < cs.view().len()
                implies cs.view()[i]@ < id@ by {
                assert(model::regex_ids(cs.view())[i] == cs.view()[i]@);
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_test_node(l: SymbolicLanguage, id: TestId, n: TestNode)
    requires facade::language_wf(l), id@ < facade::graph(l).tests.len(),
        test_matches(n, facade::graph(l).tests[id@ as int]),
    ensures test_node_wf(l, id, n),
{
    facade::lemma_language_wf(l);
    history_semantics::verify::finite_link::lemma_test_lift(facade::graph(l), id@);
    match n {
        TestNode::And(cs) | TestNode::Or(cs) => {
            let ids = model::test_ids(cs.view());
            assert(Seq::new(ids.len(), |i: int| model::lift_test(facade::graph(l), ids[i]))
                =~= test_lifts(l, cs.view()));
            assert forall|i: int| #![trigger cs.view()[i]] 0 <= i < cs.view().len()
                implies cs.view()[i]@ < id@ by {
                assert(ids[i] == cs.view()[i]@);
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_lifts(l: SymbolicLanguage, ids: Seq<RegexId>)
    ensures lifts(l, ids) == model::lift_regexes(facade::graph(l), model::regex_ids(ids)),
{
    assert(lifts(l, ids) =~= model::lift_regexes(facade::graph(l), model::regex_ids(ids)));
}

pub(crate) proof fn lemma_regex_rank(ids: Seq<RegexId>, bound: nat)
    requires model::bounded(model::regex_ids(ids), bound),
    ensures forall|i: int| #![trigger ids[i]] 0 <= i < ids.len() ==> ids[i]@ < bound,
{
    assert forall|i: int| #![trigger ids[i]] 0 <= i < ids.len() implies ids[i]@ < bound by {
        assert(model::regex_ids(ids)[i] == ids[i]@);
    }
}

pub(crate) proof fn lemma_test_rank(ids: Seq<TestId>, bound: nat)
    requires model::bounded(model::test_ids(ids), bound),
    ensures forall|i: int| #![trigger ids[i]] 0 <= i < ids.len() ==> ids[i]@ < bound,
{
    assert forall|i: int| #![trigger ids[i]] 0 <= i < ids.len() implies ids[i]@ < bound by {
        assert(model::test_ids(ids)[i] == ids[i]@);
    }
}

pub(crate) proof fn lemma_padding(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    x: Regex<model::Test>, xs: Seq<Regex<model::Test>>,
    ys: Seq<Regex<model::Test>>, a: nat, b: nat)
    requires paper::sim_sound(le), xs == match x { Regex::Concat(cs) => cs, _ => seq![x] },
        paper::padding_ok(ys, a, b, xs.len()),
        forall|i: int| #![trigger ys[a + i]] 0 <= i < xs.len() ==> le(xs[i], ys[a + i]),
    ensures paper::cat_padded(le, x, ys), paper::lang_le(x, Regex::Concat(ys)),
{
    reveal(paper::cat_padded);
    paper::lemma_padding_trigger(ys, a, b);
    assert(paper::cat_padded(le, x, ys));
    paper::theorem_sim_rules_sound();
    assert(paper::test_sim_sound(semantic_tle()));
    assert(paper::sim_step(le, semantic_tle(), x, Regex::Concat(ys)));
}

pub(crate) proof fn lemma_rule(l: SymbolicLanguage, x: RegexId, y: RegexId)
    requires paper::sim_step(semantic_le(), semantic_tle(),
        facade::abs(l, x), facade::abs(l, y)),
    ensures regex_le(l, x, y),
{
    paper::theorem_sim_rules_sound();
    assert(paper::sim_sound(semantic_le()));
    assert(paper::test_sim_sound(semantic_tle()));
}

pub(crate) proof fn lemma_test_rule(l: SymbolicLanguage, x: TestId, y: TestId)
    requires paper::test_step(semantic_tle(), model::lift_test(facade::graph(l), x@),
        model::lift_test(facade::graph(l), y@)),
    ensures test_le(l, x, y),
{
    paper::theorem_test_rules_sound();
    assert(paper::test_sim_sound(semantic_tle()));
}

pub(crate) proof fn lemma_regex_some(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    tle: spec_fn(model::Test, model::Test) -> bool,
    x: Regex<model::Test>, y: Regex<model::Test>, cs: Seq<Regex<model::Test>>, i: int)
    requires 0 <= i < cs.len(),
        y == Regex::Union(cs) && le(x, cs[i]) || x == Regex::Intersect(cs) && le(cs[i], y),
    ensures paper::sim_step(le, tle, x, y),
{
    if y == Regex::Union(cs) && le(x, cs[i]) {
        assert(y is Union);
        assert(y->Union_0 == cs);
        assert(le(x, y->Union_0[i]));
        assert(exists|j: int| 0 <= j < cs.len() && #[trigger] le(x, cs[j]));
        assert(paper::sim_step(le, tle, x, y));
    } else {
        assert(x is Intersect);
        assert(x->Intersect_0 == cs);
        assert(le(x->Intersect_0[i], y));
        assert(exists|j: int| 0 <= j < cs.len() && #[trigger] le(cs[j], y));
        assert(paper::sim_step(le, tle, x, y));
    }
    reveal(paper::sim_step);
}

pub(crate) proof fn lemma_test_some(le: spec_fn(model::Test, model::Test) -> bool,
    x: model::Test, y: model::Test, cs: Seq<model::Test>, i: int)
    requires 0 <= i < cs.len(),
        x == model::Test::And(cs) && le(cs[i], y) || y == model::Test::Or(cs) && le(x, cs[i]),
    ensures paper::test_step(le, x, y),
{
    if x == model::Test::And(cs) && le(cs[i], y) {
        assert(x is And);
        assert(x->And_0 == cs);
        assert(le(x->And_0[i], y));
        assert(exists|j: int| 0 <= j < cs.len() && #[trigger] le(cs[j], y));
        assert(paper::test_step(le, x, y));
    } else {
        assert(y is Or);
        assert(y->Or_0 == cs);
        assert(le(x, y->Or_0[i]));
        assert(exists|j: int| 0 <= j < cs.len() && #[trigger] le(x, cs[j]));
        assert(paper::test_step(le, x, y));
    }
    reveal(paper::test_step);
}

pub(crate) open spec fn index_range(n: nat, i: int) -> bool {
    0 <= i < n
}

}
