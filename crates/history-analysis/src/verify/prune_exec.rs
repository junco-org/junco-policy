//! Required/excluded decomposition and antichain domination contracts.

use crate::constraint::ConstraintTable;
use crate::native::{groups, key_obligations};
use crate::prune::{Antichain, Decomposition, Entry, Root};
use crate::verify::simulation_exec::semantic_le;
use alloc::boxed::Box;
use history_semantics::verify::refinement::{
    encoding, implementation, inclusion, pruning as paper, search,
};
use junco_core::kernel::{RegexId, verify as model};
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::history_specs::Regex;
use smallvec::SmallVec;
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
broadcast use model::group_kernel_views;


/// Native equality and hashing must identify the same ordered parts represented by the view.
pub open spec fn parts_key_obligations() -> bool {
    key_obligations::<SmallVec<[RegexId; 4]>>()
        && forall|a: SmallVec<[RegexId; 4]>, b: SmallVec<[RegexId; 4]>|
            #[trigger] a.eq_spec(&b) ==> a.view() == b.view()
}

pub(crate) open spec fn valid(g: model::Graph, ids: Seq<RegexId>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.regexes.len()
}

pub(crate) open spec fn ordered(ids: Seq<RegexId>) -> bool {
    forall|i: int,j: int| 0 <= i < j < ids.len() ==> ids[i]@ < ids[j]@
}

pub(crate) proof fn lemma_ordered(ids: Seq<RegexId>)
    requires ordered(ids),
    ensures model::strictly_increasing(model::regex_ids(ids)),
{
    assert forall|i: int,j: int| 0 <= i < j < model::regex_ids(ids).len()
        implies model::regex_ids(ids)[i] < model::regex_ids(ids)[j] by {
        assert(model::regex_ids(ids)[i] == ids[i]@);
        assert(model::regex_ids(ids)[j] == ids[j]@);
    }
}

pub(crate) proof fn lemma_valid_push(g: model::Graph,ids: Seq<RegexId>,id: RegexId)
    requires valid(g,ids),id@ < g.regexes.len(),
    ensures valid(g,ids.push(id)),
{
    assert forall|i: int| 0 <= i < ids.push(id).len() implies ids.push(id)[i]@ < g.regexes.len() by {
        if i < ids.len() { assert(ids.push(id)[i] == ids[i]); }
        else { assert(ids.push(id)[i] == id); }
    }
}

pub(crate) proof fn lemma_ordered_push(ids: Seq<RegexId>,id: RegexId)
    requires ordered(ids),forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < id@,
    ensures ordered(ids.push(id)),
{
    assert forall|i: int,j: int| 0 <= i < j < ids.push(id).len()
        implies ids.push(id)[i]@ < ids.push(id)[j]@ by {
        assert(ids.push(id)[i] == ids[i]);
        if j < ids.len() { assert(ids.push(id)[j] == ids[j]); }
        else { assert(ids.push(id)[j] == id); }
    }
}

pub(crate) proof fn lemma_valid_set(g: model::Graph,before: Seq<RegexId>,after: Seq<RegexId>)
    requires valid(g,before),before.to_set() == after.to_set(),
    ensures valid(g,after),
{
    assert forall|i: int| 0 <= i < after.len() implies after[i]@ < g.regexes.len() by {
        assert(before.to_set().contains(after[i]));
        let j = choose|j: int| 0 <= j < before.len() && before[j] == after[i];
    }
}

pub(crate) open spec fn lifted(g: model::Graph, ids: Seq<RegexId>) -> Set<Regex<model::Test>> {
    ids.to_set().map(|id: RegexId| model::lift_regex(g, id@))
}

pub(crate) open spec fn decomposition_valid(g: model::Graph, d: Decomposition) -> bool {
    valid(g, d.parts.view()) && valid(g, d.pieces.view())
        && ordered(d.parts.view()) && ordered(d.pieces.view())
}

pub(crate) open spec fn decomposition_of(g: model::Graph, q: Regex<model::Test>, d: Decomposition) -> bool {
    decomposition_valid(g, d)
        && (forall|p: Regex<model::Test>| #[trigger] paper::required(q, p)
            == lifted(g, d.parts.view()).contains(p))
        && (forall|p: Regex<model::Test>| #[trigger] paper::excluded(q, p)
            == lifted(g, d.pieces.view()).contains(p))
}

pub(crate) open spec fn root_matches(root: Root, kind: model::RegexKindNode) -> bool {
    match (root, kind) {
        (Root::Intersect(ids), model::RegexKindNode::Intersect(cs)) => model::regex_ids(ids.view()) == cs,
        (Root::Not(id), model::RegexKindNode::Not(child)) => id@ == child,
        (Root::Other, kind) => !(kind is Intersect) && !(kind is Not),
        _ => false,
    }
}

pub(crate) open spec fn root_semantics(g: model::Graph,id: RegexId,root: Root) -> bool {
    match root {
        Root::Intersect(cs) => valid(g,cs.view()) && ordered(cs.view())
            && model::lift_regex(g,id@) == Regex::Intersect(model::lift_regexes(g,model::regex_ids(cs.view()))),
        Root::Not(inner) => inner@ < g.regexes.len()
            && model::lift_regex(g,id@) == Regex::Not(Box::new(model::lift_regex(g,inner@))),
        Root::Other => !(model::lift_regex(g,id@) is Not) && !(model::lift_regex(g,id@) is Intersect),
    }
}

pub(crate) proof fn lemma_root(g: model::Graph,id: RegexId,root: Root)
    requires model::graph_wf(g),id@ < g.regexes.len(),root_matches(root,g.regexes[id@ as int].kind),
    ensures root_semantics(g,id,root),
{
    history_semantics::normalize_verify::regex_unfold(g,id@);
    match root {
        Root::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.view().len() implies cs.view()[i]@ < g.regexes.len() by {
                assert(model::regex_ids(cs.view())[i] == cs.view()[i]@);
            }
            assert forall|i: int,j: int| 0 <= i < j < cs.view().len()
                implies cs.view()[i]@ < cs.view()[j]@ by {
                assert(model::regex_ids(cs.view())[i] == cs.view()[i]@);
                assert(model::regex_ids(cs.view())[j] == cs.view()[j]@);
            }
        },
        _ => {},
    }
}

pub(crate) open spec fn positive(g: model::Graph, cs: Seq<RegexId>) -> Set<Regex<model::Test>> {
    lifted(g, cs).filter(|p: Regex<model::Test>| !(p is Not))
}

pub(crate) open spec fn negative_at(g: model::Graph,cs: Seq<RegexId>,n: Regex<model::Test>,
    iv: (int,Regex<model::Test>)) -> bool {
    0 <= iv.0 < cs.len() && model::lift_regex(g,cs[iv.0]@) == Regex::Not(Box::new(iv.1))
        && paper::union_ops(iv.1).contains(n)
}

pub(crate) open spec fn negative(g: model::Graph,cs: Seq<RegexId>,n: Regex<model::Test>) -> bool {
    exists|iv: (int,Regex<model::Test>)| #[trigger] negative_at(g,cs,n,iv)
}

pub(crate) proof fn lemma_lifted(g: model::Graph, ids: Seq<RegexId>)
    ensures forall|p: Regex<model::Test>| #[trigger] lifted(g, ids).contains(p)
        == (exists|i: int| 0 <= i < ids.len() && model::lift_regex(g, ids[i]@) == p),
{
    assert forall|p: Regex<model::Test>| #[trigger] lifted(g, ids).contains(p)
        implies exists|i: int| 0 <= i < ids.len() && model::lift_regex(g, ids[i]@) == p by {
        let id = choose|id: RegexId| ids.to_set().contains(id) && model::lift_regex(g, id@) == p;
        let i = choose|i: int| 0 <= i < ids.len() && ids[i] == id;
    }
    assert forall|p: Regex<model::Test>| (exists|i: int| 0 <= i < ids.len()
        && model::lift_regex(g, ids[i]@) == p) implies #[trigger] lifted(g, ids).contains(p) by {
        let i = choose|i: int| 0 <= i < ids.len() && model::lift_regex(g, ids[i]@) == p;
        assert(ids.to_set().contains(ids[i]));
    }
}

pub(crate) proof fn lemma_lifted_push(g: model::Graph, ids: Seq<RegexId>, id: RegexId)
    ensures lifted(g, ids.push(id)) == lifted(g, ids).insert(model::lift_regex(g, id@)),
{
    ids.lemma_push_to_set_commute(id);
    ids.to_set().lemma_set_map_insert_commute(id, |id: RegexId| model::lift_regex(g, id@));
}

pub(crate) proof fn lemma_lifted_concat(g: model::Graph, a: Seq<RegexId>, b: Seq<RegexId>)
    ensures lifted(g, a + b) == lifted(g, a).union(lifted(g, b)),
{
    lemma_lifted(g, a); lemma_lifted(g, b); lemma_lifted(g, a + b);
    assert forall|p: Regex<model::Test>| #[trigger] lifted(g,a+b).contains(p)
        == lifted(g,a).union(lifted(g,b)).contains(p) by {
        if lifted(g,a+b).contains(p) {
            let i = choose|i: int| 0 <= i < (a+b).len() && model::lift_regex(g,(a+b)[i]@) == p;
            if i < a.len() { assert(a[i] == (a+b)[i]); assert(lifted(g,a).contains(p)); }
            else { assert(b[i-a.len()] == (a+b)[i]); assert(lifted(g,b).contains(p)); }
        }
        if lifted(g,a).contains(p) {
            let i = choose|i: int| 0 <= i < a.len() && model::lift_regex(g,a[i]@) == p;
            assert((a+b)[i] == a[i]);
        }
        if lifted(g,b).contains(p) {
            let i = choose|i: int| 0 <= i < b.len() && model::lift_regex(g,b[i]@) == p;
            assert((a+b)[a.len()+i] == b[i]);
        }
    }
    assert(lifted(g,a+b) =~= lifted(g,a).union(lifted(g,b)));
}

pub(crate) proof fn lemma_positive_push(g: model::Graph, cs: Seq<RegexId>, id: RegexId)
    ensures positive(g, cs.push(id)) == if model::lift_regex(g, id@) is Not { positive(g, cs) }
        else { positive(g, cs).insert(model::lift_regex(g, id@)) },
{
    lemma_lifted_push(g, cs, id);
    assert(positive(g, cs.push(id)) =~= if model::lift_regex(g, id@) is Not { positive(g, cs) }
        else { positive(g, cs).insert(model::lift_regex(g, id@)) });
}

pub(crate) proof fn lemma_negative_push(g: model::Graph, cs: Seq<RegexId>, id: RegexId)
    ensures forall|n: Regex<model::Test>| #[trigger] negative(g, cs.push(id), n)
        == (negative(g, cs, n) || exists|v: Regex<model::Test>|
            model::lift_regex(g, id@) == Regex::Not(Box::new(v)) && paper::union_ops(v).contains(n)),
{
    assert forall|n: Regex<model::Test>| #[trigger] negative(g, cs.push(id), n)
        implies negative(g, cs, n) || exists|v: Regex<model::Test>|
            model::lift_regex(g, id@) == Regex::Not(Box::new(v)) && paper::union_ops(v).contains(n) by {
        let (i,v) = choose|iv: (int, Regex<model::Test>)| negative_at(g,cs.push(id),n,iv);
        if i < cs.len() { assert(negative_at(g,cs,n,(i,v))); assert(negative(g,cs,n)); }
    }
    assert forall|n: Regex<model::Test>| (negative(g, cs, n) || exists|v: Regex<model::Test>|
        model::lift_regex(g, id@) == Regex::Not(Box::new(v)) && paper::union_ops(v).contains(n))
        implies #[trigger] negative(g, cs.push(id), n) by {
        if negative(g, cs, n) {
            let (i,v) = choose|iv: (int, Regex<model::Test>)| negative_at(g,cs,n,iv);
            assert(cs.push(id)[i] == cs[i]);
            assert(negative_at(g,cs.push(id),n,(i,v)));
        } else {
            let v = choose|v: Regex<model::Test>| model::lift_regex(g,id@) == Regex::Not(Box::new(v))
                && paper::union_ops(v).contains(n);
            assert(cs.push(id)[cs.len() as int] == id);
            assert(negative_at(g,cs.push(id),n,(cs.len() as int,v)));
        }
    }
}

pub(crate) proof fn lemma_negative_not(g: model::Graph,cs: Seq<RegexId>,child: RegexId,inner: RegexId)
    requires model::lift_regex(g,child@) == Regex::Not(Box::new(model::lift_regex(g,inner@))),
    ensures forall|n: Regex<model::Test>| #[trigger] negative(g,cs.push(child),n)
        == (negative(g,cs,n) || paper::union_ops(model::lift_regex(g,inner@)).contains(n)),
{
    lemma_negative_push(g,cs,child);
    assert forall|n: Regex<model::Test>| (exists|v: Regex<model::Test>|
        model::lift_regex(g,child@) == Regex::Not(Box::new(v)) && paper::union_ops(v).contains(n))
        == paper::union_ops(model::lift_regex(g,inner@)).contains(n) by {
        if exists|v: Regex<model::Test>| model::lift_regex(g,child@) == Regex::Not(Box::new(v))
            && paper::union_ops(v).contains(n) {
            let v = choose|v: Regex<model::Test>| model::lift_regex(g,child@) == Regex::Not(Box::new(v))
                && paper::union_ops(v).contains(n);
            assert(v == model::lift_regex(g,inner@));
        }
    }
}

pub(crate) proof fn lemma_not(v: Regex<model::Test>)
    ensures forall|p: Regex<model::Test>| !paper::required(Regex::Not(Box::new(v)),p),
        forall|n: Regex<model::Test>| #[trigger] paper::excluded(Regex::Not(Box::new(v)),n)
            == paper::union_ops(v).contains(n),
{
    let q = Regex::Not(Box::new(v));
    assert forall|n: Regex<model::Test>| #[trigger] paper::excluded(q,n)
        == paper::union_ops(v).contains(n) by {
        if paper::excluded(q,n) {
            let x = choose|x: Regex<model::Test>| paper::inter_ops(q).contains(Regex::Not(Box::new(x)))
                && paper::union_ops(x).contains(n);
            assert(x == v);
        }
        if paper::union_ops(v).contains(n) {
            assert(paper::inter_ops(q) == seq![q]);
            assert(paper::inter_ops(q)[0] == q);
            assert(paper::inter_ops(q).contains(q));
        }
    }
}

pub(crate) proof fn lemma_other(q: Regex<model::Test>)
    requires !(q is Not),!(q is Intersect),
    ensures forall|p: Regex<model::Test>| #[trigger] paper::required(q,p) == (p == q),
        forall|n: Regex<model::Test>| !paper::excluded(q,n),
{
    assert(paper::inter_ops(q) == seq![q]);
    assert(paper::inter_ops(q)[0] == q);
    assert forall|p: Regex<model::Test>| #[trigger] paper::required(q,p) == (p == q) by {
        if paper::required(q,p) {
            let i = choose|i: int| 0 <= i < paper::inter_ops(q).len() && paper::inter_ops(q)[i] == p;
            assert(i == 0);
        }
    }
    assert forall|n: Regex<model::Test>| !paper::excluded(q,n) by {
        if paper::excluded(q,n) {
            let v = choose|v: Regex<model::Test>| paper::inter_ops(q).contains(Regex::Not(Box::new(v)))
                && paper::union_ops(v).contains(n);
            assert(q == Regex::Not(Box::new(v)));
        }
    }
}

pub(crate) proof fn lemma_intersection(g: model::Graph, cs: Seq<RegexId>, q: Regex<model::Test>)
    requires q == Regex::Intersect(model::lift_regexes(g, model::regex_ids(cs))),
    ensures forall|p: Regex<model::Test>| #[trigger] paper::required(q,p) == positive(g,cs).contains(p),
        forall|n: Regex<model::Test>| #[trigger] paper::excluded(q,n) == negative(g,cs,n),
{
    lemma_lifted(g,cs);
    assert forall|p: Regex<model::Test>| #[trigger] paper::inter_ops(q).contains(p)
        == lifted(g,cs).contains(p) by {
        if paper::inter_ops(q).contains(p) {
            let i = choose|i: int| 0 <= i < cs.len() && model::lift_regexes(g,model::regex_ids(cs))[i] == p;
            assert(model::regex_ids(cs)[i] == cs[i]@);
        }
        if lifted(g,cs).contains(p) {
            let i = choose|i: int| 0 <= i < cs.len() && model::lift_regex(g,cs[i]@) == p;
            assert(model::lift_regexes(g,model::regex_ids(cs))[i] == p);
        }
    }
    assert forall|n: Regex<model::Test>| #[trigger] paper::excluded(q,n) implies negative(g,cs,n) by {
        let v = choose|v: Regex<model::Test>| paper::inter_ops(q).contains(Regex::Not(Box::new(v)))
            && paper::union_ops(v).contains(n);
        let i = choose|i: int| 0 <= i < cs.len() && model::lift_regex(g,cs[i]@) == Regex::Not(Box::new(v));
        assert(negative_at(g,cs,n,(i,v)));
    }
    assert forall|n: Regex<model::Test>| negative(g,cs,n) implies #[trigger] paper::excluded(q,n) by {
        let (i,v) = choose|iv: (int, Regex<model::Test>)| negative_at(g,cs,n,iv);
        assert(lifted(g,cs).contains(Regex::Not(Box::new(v))));
    }
}

pub(crate) open spec fn valid_entry(g: model::Graph,table: ConstraintTable,key: SmallVec<[RegexId;4]>,
    entry: Entry) -> bool {
    valid(g,key.view()) && entry.constraint < table@.len() && valid(g,entry.pieces@)
}

pub(crate) open spec fn entries_valid(a: Antichain, g: model::Graph, table: ConstraintTable) -> bool {
    forall|key: SmallVec<[RegexId;4]>, i: int| #![trigger groups(a.groups)[key][i]] groups(a.groups).dom().contains(key)
        && 0 <= i < groups(a.groups)[key].len() ==> valid_entry(g,table,key,groups(a.groups)[key][i])
}

pub(crate) open spec fn entry_matches(g: model::Graph, table: ConstraintTable,
    key: SmallVec<[RegexId;4]>, entry: Entry, item: search::Item) -> bool {
    item.constraint == implementation::constraint_of(table@[entry.constraint as int])
        && (forall|p: Regex<model::Test>| #[trigger] paper::required(item.state,p)
            == lifted(g,key.view()).contains(p))
        && (forall|p: Regex<model::Test>| #[trigger] paper::excluded(item.state,p)
            == lifted(g,entry.pieces@).contains(p))
}

pub(crate) open spec fn indexed_entry(g: model::Graph,table: ConstraintTable,key: SmallVec<[RegexId;4]>,
    entry: Entry,nodes: Seq<search::Node>) -> bool {
    valid_entry(g,table,key,entry)
        && exists|k: int| 0 <= k < nodes.len() && entry_matches(g,table,key,entry,nodes[k].item)
}

pub(crate) open spec fn antichain_wf(a: Antichain, g: model::Graph, table: ConstraintTable,
    nodes: Seq<search::Node>) -> bool {
    forall|key: SmallVec<[RegexId;4]>,i: int| #![trigger groups(a.groups)[key][i]]
        groups(a.groups).dom().contains(key) && 0 <= i < groups(a.groups)[key].len()
        ==> #[trigger] indexed_entry(g,table,key,groups(a.groups)[key][i],nodes)
}

pub(crate) proof fn lemma_antichain_valid(a: Antichain,g: model::Graph,table: ConstraintTable,
    nodes: Seq<search::Node>)
    requires antichain_wf(a,g,table,nodes),
    ensures entries_valid(a,g,table),
{
    assert forall|key: SmallVec<[RegexId;4]>,i: int| #![trigger groups(a.groups)[key][i]]
        groups(a.groups).dom().contains(key) && 0 <= i < groups(a.groups)[key].len()
        implies valid_entry(g,table,key,groups(a.groups)[key][i]) by {
        assert(indexed_entry(g,table,key,groups(a.groups)[key][i],nodes));
    }
}

pub(crate) open spec fn entry_subsumes(a: Antichain,g: model::Graph,table: ConstraintTable,
    constraint: implementation::ConstraintView,d: Decomposition,key: SmallVec<[RegexId;4]>,i: int) -> bool {
    groups(a.groups).dom().contains(key) && 0 <= i < groups(a.groups)[key].len()
        && key.view().to_set().subset_of(d.parts.view().to_set())
        && (forall|domains: encoding::NDomains| inclusion::entails(domains,
            implementation::constraint_of(constraint),
            implementation::constraint_of(table@[groups(a.groups)[key][i].constraint as int])))
        && (forall|j: int| #![trigger groups(a.groups)[key][i].pieces@[j]]
            0 <= j < groups(a.groups)[key][i].pieces@.len() ==> exists|k: int|
            0 <= k < d.pieces.view().len() && paper::lang_le(
                model::lift_regex(g,groups(a.groups)[key][i].pieces@[j]@),
                model::lift_regex(g,d.pieces.view()[k]@)))
}

pub(crate) open spec fn raw_subsumes(a: Antichain,g: model::Graph,table: ConstraintTable,
    constraint: implementation::ConstraintView,d: Decomposition) -> bool {
    exists|ki: (SmallVec<[RegexId;4]>,int)| #[trigger] entry_subsumes(a,g,table,constraint,d,ki.0,ki.1)
}

pub(crate) open spec fn dominates_some(domains: encoding::NDomains,nodes: Seq<search::Node>,
    item: search::Item) -> bool {
    exists|k: int| 0 <= k < nodes.len() && paper::dominated(domains,semantic_le(),item,nodes[k].item)
}

pub(crate) proof fn lemma_domination(a: Antichain, g: model::Graph, table: ConstraintTable,
    c: implementation::ConstraintView, d: Decomposition, q: Regex<model::Test>,
    domains: encoding::NDomains, nodes: Seq<search::Node>)
    requires raw_subsumes(a,g,table,c,d), antichain_wf(a,g,table,nodes), decomposition_of(g,q,d),
    ensures exists|k: int| 0 <= k < nodes.len() && paper::dominated(domains,semantic_le(),
        search::Item { constraint: implementation::constraint_of(c), state: q },nodes[k].item),
{
    reveal(raw_subsumes);
    reveal(entry_subsumes); reveal(antichain_wf); reveal(entry_matches); reveal(decomposition_of);
    let (key,i) = choose|ki: (SmallVec<[RegexId;4]>,int)| entry_subsumes(a,g,table,c,d,ki.0,ki.1);
    assert(entry_subsumes(a,g,table,c,d,key,i));
    let entry = groups(a.groups)[key][i];
    let k = choose|k: int| 0 <= k < nodes.len() && entry_matches(g,table,key,entry,nodes[k].item);
    lemma_lifted(g,key.view()); lemma_lifted(g,d.parts.view());
    lemma_lifted(g,entry.pieces@); lemma_lifted(g,d.pieces.view());
    assert forall|p: Regex<model::Test>| #[trigger] paper::required(nodes[k].item.state,p)
        implies paper::required(q,p) by {
        let j = choose|j: int| 0 <= j < key.view().len() && model::lift_regex(g,key.view()[j]@) == p;
        assert(d.parts.view().to_set().contains(key.view()[j]));
    }
    assert forall|n: Regex<model::Test>| #[trigger] paper::excluded(nodes[k].item.state,n)
        implies exists|n2: Regex<model::Test>| paper::excluded(q,n2) && paper::lang_le(n,n2) by {
        let j = choose|j: int| 0 <= j < entry.pieces@.len() && model::lift_regex(g,entry.pieces@[j]@) == n;
        let m = choose|m: int| 0 <= m < d.pieces.view().len()
            && paper::lang_le(n,model::lift_regex(g,d.pieces.view()[m]@));
        assert(lifted(g,d.pieces.view()).contains(model::lift_regex(g,d.pieces.view()[m]@)));
    }
    assert(paper::dominated(domains,semantic_le(),
        search::Item { constraint: implementation::constraint_of(c), state: q },nodes[k].item));
}

pub(crate) proof fn lemma_dead(g: model::Graph, d: Decomposition, q: Regex<model::Test>,
    part: RegexId, members: Seq<RegexId>)
    requires decomposition_of(g,q,d), d.parts.view().contains(part),
        forall|v: Regex<model::Test>| paper::union_ops(model::lift_regex(g,part@)).contains(v)
            == lifted(g,members).contains(v),
        forall|i: int| #![trigger members[i]] 0 <= i < members.len() ==> exists|j: int| 0 <= j < d.pieces.view().len()
            && paper::lang_le(model::lift_regex(g,members[i]@),model::lift_regex(g,d.pieces.view()[j]@)),
    ensures paper::dead(semantic_le(),q),
{
    lemma_lifted(g,d.parts.view()); lemma_lifted(g,d.pieces.view()); lemma_lifted(g,members);
    let p = model::lift_regex(g,part@);
    assert(paper::required(q,p));
    assert forall|v: Regex<model::Test>| #[trigger] paper::union_ops(p).contains(v)
        implies exists|n: Regex<model::Test>| paper::excluded(q,n) && paper::lang_le(v,n) by {
        assert(lifted(g,members).contains(v));
        let i = choose|i: int| 0 <= i < members.len() && model::lift_regex(g,members[i]@) == v;
        let j = choose|j: int| 0 <= j < d.pieces.view().len()
            && paper::lang_le(v,model::lift_regex(g,d.pieces.view()[j]@));
        assert(lifted(g,d.pieces.view()).contains(model::lift_regex(g,d.pieces.view()[j]@)));
    }
}

pub(crate) proof fn lemma_lifted_frame(a: model::Graph,b: model::Graph,ids: Seq<RegexId>)
    requires model::tables_wf(a),model::tables_extend(a,b),valid(a,ids),
    ensures valid(b,ids),lifted(a,ids) == lifted(b,ids),
{
    assert forall|i: int| 0 <= i < ids.len() implies
        model::lift_regex(a,ids[i]@) == model::lift_regex(b,ids[i]@) by {
        model::lemma_lift_regex_stable(a,b,ids[i]@);
    }
    lemma_lifted(a,ids); lemma_lifted(b,ids);
    assert(lifted(a,ids) =~= lifted(b,ids));
}

pub(crate) proof fn lemma_decomposition_frame(a: model::Graph,b: model::Graph,
    q: Regex<model::Test>,d: Decomposition)
    requires model::tables_wf(a),model::tables_extend(a,b),decomposition_of(a,q,d),
    ensures decomposition_of(b,q,d),
{
    lemma_lifted_frame(a,b,d.parts.view()); lemma_lifted_frame(a,b,d.pieces.view());
}

pub(crate) proof fn lemma_antichain_frame(chain: Antichain,a: model::Graph,b: model::Graph,
    before: ConstraintTable,after: ConstraintTable,nodes: Seq<search::Node>)
    requires model::tables_wf(a),model::tables_extend(a,b),before@.is_prefix_of(after@),
        antichain_wf(chain,a,before,nodes),
    ensures antichain_wf(chain,b,after,nodes),
{
    reveal(antichain_wf); reveal(entries_valid); reveal(entry_matches);
    assert forall|key: SmallVec<[RegexId;4]>,i: int| #![trigger groups(chain.groups)[key][i]] groups(chain.groups).dom().contains(key)
        && 0 <= i < groups(chain.groups)[key].len() implies
        indexed_entry(b,after,key,groups(chain.groups)[key][i],nodes) by {
        let entry = groups(chain.groups)[key][i];
        lemma_lifted_frame(a,b,key.view()); lemma_lifted_frame(a,b,entry.pieces@);
        let k = choose|k: int| 0 <= k < nodes.len() && entry_matches(a,before,key,entry,nodes[k].item);
        assert(before@[entry.constraint as int] == after@[entry.constraint as int]);
        assert(entry_matches(b,after,key,entry,nodes[k].item));
        assert(indexed_entry(b,after,key,entry,nodes));
    }
}

pub(crate) proof fn lemma_checks_discard(domains: encoding::NDomains,nodes: Seq<search::Node>,
    item: search::Item,depth: nat)
    requires paper::dead(semantic_le(),item.state) || exists|k: int| 0 <= k < nodes.len()
        && nodes[k].depth <= depth && paper::dominated(domains,semantic_le(),item,nodes[k].item),
    ensures search::may_discard(domains,nodes,item,depth),
{
    paper::theorem_checks_discard();
    assert(paper::sim_sound(semantic_le()));
}
}
