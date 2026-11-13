//! Executable search trace, retained cases, and finite-state resource bounds.

use crate::constraint::{Atom, ConstraintId, ConstraintTable, Letter, Universes};
use history_store::native::members;
use crate::search::{Item, Search};
use crate::verify::{atom_set, atoms_wf, ndomains, table_wf};
use history_semantics::symbolic_verify as symbolic;
use history_semantics::verify::{
    finite_impl,
    refinement::{encoding, finiteness, implementation, inclusion, search as paper},
};
use history_semantics::{SymbolicLanguage, symbolic_language_verify as facade};
use junco_core::kernel::{RegexId, TestId, verify as model};
use junco_core::observation::SmallVecSpecFns;
use junco_core::verify::history_specs::{self as language, EventView, Regex, Subst};
use vstd::prelude::*;

verus! {
broadcast use model::group_kernel_views;
broadcast use junco_core::spec::hypotheses::internal_keys::group_internal_key_laws;


pub(crate) open spec fn truth_bits(atoms: Seq<Atom>, letter: Letter, words: Seq<u64>) -> bool {
    words.len() == (atoms.len() + 63) / 64
        && forall|i: int| 0 <= i < atoms.len() ==> symbolic::truth_word_bit(words, i as nat)
            == implementation::letter_holds(letter@, atoms[i]@)
}

pub(crate) proof fn lemma_truth_set(before: Seq<u64>, after: Seq<u64>, index: nat)
    requires index / 64 < before.len(),
        after == before.update((index / 64) as int,
            before[(index / 64) as int] | (1u64 << ((index % 64) as u32))),
    ensures symbolic::truth_word_bit(after, index),
        forall|j: nat| j != index ==> symbolic::truth_word_bit(after, j)
            == symbolic::truth_word_bit(before, j),
{
    let bit = (index % 64) as u32;
    let value = before[(index / 64) as int];
    assert(bit < 64);
    assert((((value | (1u64 << bit)) >> bit) & 1u64) != 0) by(bit_vector)
        requires bit < 64;
    assert forall|j: nat| j != index implies symbolic::truth_word_bit(after, j)
        == symbolic::truth_word_bit(before, j) by {
        if j / 64 < before.len() && j / 64 == index / 64 {
            let other = (j % 64) as u32;
            assert(other < 64 && other != bit);
            assert((((value | (1u64 << bit)) >> other) & 1u64)
                == ((value >> other) & 1u64)) by(bit_vector)
                requires bit < 64, other < 64, other != bit;
        }
    }
}

pub(crate) proof fn lemma_truth_realizes(g: model::Graph, ids: Seq<TestId>, atoms: Seq<Atom>,
    letter: Letter, words: Seq<u64>)
    requires truth_bits(atoms, letter, words), ids.len() == atoms.len(),
        forall|i: int| 0 <= i < ids.len()
            ==> model::lift_test(g, ids[i]@) == model::Test::Atom(atoms[i]@, true),
    ensures forall|theta: Subst, e: EventView|
        paper::realizes(theta, e, implementation::letter_assignment(letter@, atom_set(atoms)))
            == symbolic::truth_words_realize(g, ids, words, theta, e),
{
    assert forall|theta: Subst, e: EventView|
        paper::realizes(theta, e, implementation::letter_assignment(letter@, atom_set(atoms)))
        implies symbolic::truth_words_realize(g, ids, words, theta, e) by {
        assert forall|i: int| 0 <= i < ids.len() implies symbolic::truth_word_bit(words, i as nat)
            == model::test_holds(theta, model::lift_test(g, ids[i]@), e) by {
            assert(atoms.to_set().contains(atoms[i]));
            assert(atom_set(atoms).contains(atoms[i]@));
        }
    }
    assert forall|theta: Subst, e: EventView|
        symbolic::truth_words_realize(g, ids, words, theta, e) implies
        paper::realizes(theta, e, implementation::letter_assignment(letter@, atom_set(atoms))) by {
        assert forall|p: model::Primitive| atom_set(atoms).contains(p) implies
            implementation::letter_holds(letter@, p) == model::primitive_holds(theta, p, e) by {
            let a = choose|a: Atom| atoms.to_set().contains(a) && a@ == p;
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i] == a;
        }
    }
}

/// The archive is ghost-only; the runtime successor LRU may evict any old entry.
pub(crate) open spec fn archive_cases(archive: Map<paper::Item, Set<paper::Case>>)
    -> spec_fn(paper::Item) -> Set<paper::Case> {
    |i: paper::Item| if archive.dom().contains(i) { archive[i] } else { Set::empty() }
}

pub(crate) open spec fn archive_follows(archive: Map<paper::Item, Set<paper::Case>>) -> bool {
    finiteness::cases_follow(finite_impl::m_impl(), archive_cases(archive))
}

pub(crate) open spec fn archive_within(archive: Map<paper::Item,Set<paper::Case>>,
    nodes: Seq<paper::Node>,limit: nat) -> bool {
    forall|item: paper::Item| #[trigger] archive.dom().contains(item)
        ==> exists|j: int| 0 <= j < limit && j < nodes.len() && nodes[j].item == item
}

pub(crate) proof fn lemma_archive_insert_within(archive: Map<paper::Item,Set<paper::Case>>,
    before: Seq<paper::Node>,after: Seq<paper::Node>,limit: nat,p: int,cases: Set<paper::Case>)
    requires archive_within(archive,before,limit),before.is_prefix_of(after),
        0 <= p < limit,p < after.len(),
        forall|i: int,j: int| 0 <= i < j < after.len() ==> after[i].item != after[j].item,
    ensures archive_within(archive.insert(after[p].item,cases),after,limit),
        forall|j: int| limit <= j < after.len()
            ==> !archive.insert(after[p].item,cases).dom().contains(after[j].item),
{
    let updated = archive.insert(after[p].item,cases);
    assert forall|item: paper::Item| #[trigger] updated.dom().contains(item) implies
        exists|j: int| 0 <= j < limit && j < after.len() && after[j].item == item by {
        if item == after[p].item { assert(after[p].item == item); }
        else {
            let j = choose|j: int| 0 <= j < limit && j < before.len() && before[j].item == item;
            assert(after[j] == before[j]);
        }
    }
    assert forall|j: int| limit <= j < after.len() implies
        !updated.dom().contains(after[j].item) by {
        if updated.dom().contains(after[j].item) {
            let i = choose|i: int| 0 <= i < limit && i < after.len() && after[i].item == after[j].item;
            assert(after[i].item != after[j].item);
        }
    }
}

pub(crate) proof fn lemma_trace_steps_archive(d: encoding::NDomains,
    archive: Map<paper::Item,Set<paper::Case>>,before: paper::Trace,after: paper::Trace,
    cases: Set<paper::Case>)
    requires paper::trace_steps_ok(d,archive_cases(archive),before),
        before.expanded < before.nodes.len(),before.nodes.is_prefix_of(after.nodes),
        before.expanded == after.expanded,
        forall|p: int| #![trigger after.nodes[p]] 0 <= p < after.expanded
            ==> after.nodes[p].item != after.nodes[after.expanded as int].item,
    ensures paper::trace_steps_ok(d,archive_cases(archive.insert(
        after.nodes[after.expanded as int].item,cases)),after),
{
    hide(paper::steps_ok);
    let updated = archive.insert(after.nodes[after.expanded as int].item,cases);
    assert forall|p: int| 0 <= p < after.expanded implies
        #[trigger] paper::steps_ok(d,after.nodes[p].item,archive_cases(updated)(after.nodes[p].item)) by {
        assert(before.nodes[p] == after.nodes[p]);
        assert(archive_cases(updated)(after.nodes[p].item) == archive_cases(archive)(before.nodes[p].item));
    }
}

pub(crate) proof fn lemma_successor_nf(before: model::Graph, q: nat, t: nat,
    after: model::Graph, v: nat)
    requires model::graph_wf(before), model::graph_extends(before, after),
        q < before.regexes.len(), finite_impl::regex_nf(model::lift_regex(before, q)),
        history_semantics::verify::finite_deriv::dbound(before, q, t),
        history_semantics::verify::finite_interp::entry_val(after, t, v),
    ensures finiteness::step_abstracts(finite_impl::m_impl(), before, q, after, v),
        finite_impl::regex_nf(model::lift_regex(after, v)),
{
    finiteness::lemma_impl_successor_abstracts(before, q, t, after, v);
    finite_impl::theorem_impl_contract();
}

pub(crate) proof fn lemma_discard_grows(d: encoding::NDomains, before: Seq<paper::Node>,
    after: Seq<paper::Node>, item: paper::Item, depth: nat)
    requires before.is_prefix_of(after), paper::may_discard(d, before, item, depth),
    ensures paper::may_discard(d, after, item, depth),
{
    if exists|k: int| 0 <= k < before.len() && before[k].depth <= depth
        && paper::witnesses_within(d, item, before[k].item) {
        let k = choose|k: int| 0 <= k < before.len() && before[k].depth <= depth
            && paper::witnesses_within(d, item, before[k].item);
        assert(after[k] == before[k]);
    }
}

pub(crate) proof fn lemma_discard_later(d: encoding::NDomains, nodes: Seq<paper::Node>,
    item: paper::Item, earlier: nat, later: nat)
    requires earlier <= later, paper::may_discard(d, nodes, item, earlier),
    ensures paper::may_discard(d, nodes, item, later),
{
    if exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= earlier
        && paper::witnesses_within(d, item, nodes[k].item) {
        let k = choose|k: int| 0 <= k < nodes.len() && nodes[k].depth <= earlier
            && paper::witnesses_within(d, item, nodes[k].item);
    }
}

/// A repeated key may designate a discarded candidate, not necessarily a queued node.
pub(crate) proof fn lemma_seen_discard(d: encoding::NDomains, nodes: Seq<paper::Node>,
    item: paper::Item, previous_depth: nat, current_depth: nat)
    requires previous_depth <= current_depth,
        paper::may_discard(d, nodes, item, previous_depth),
    ensures paper::may_discard(d, nodes, item, current_depth),
{
    lemma_discard_later(d, nodes, item, previous_depth, current_depth);
}

pub(crate) proof fn lemma_queued_discard(d: encoding::NDomains, nodes: Seq<paper::Node>,
    node: paper::Node)
    ensures paper::may_discard(d, nodes.push(node), node.item, node.depth),
{
    assert(paper::witnesses_within(d, node.item, node.item));
    assert(nodes.push(node)[nodes.len() as int] == node);
}

pub(crate) proof fn lemma_archive_add(archive: Map<paper::Item, Set<paper::Case>>,
    item: paper::Item, cases: Set<paper::Case>)
    requires archive_follows(archive),
        forall|c: paper::Case| cases.contains(c) ==> (finite_impl::m_impl().succ)(item.state, c.next)
            || item.state == c.next,
    ensures archive_follows(archive.insert(item, cases)),
{
    assert forall|i: paper::Item, c: paper::Case| finite_impl::m_impl().st(i.state)
        && archive_cases(archive.insert(item, cases))(i).contains(c) implies
        (finite_impl::m_impl().succ)(i.state, c.next) || i.state == c.next by {
        if i == item { assert(cases.contains(c)); }
        else { assert(archive_cases(archive)(i).contains(c)); }
    }
}

pub(crate) open spec fn parents_wf(items: Seq<Item>) -> bool {
    forall|j: int| #![trigger items[j]] 0 <= j < items.len() ==> match items[j].parent {
        None => j == 0,
        Some((p, _)) => p < j,
    }
}

pub(crate) open spec fn letter_chain(items: Seq<Item>, j: int) -> Seq<Letter>
    decreases j,
{
    if j < 0 || j >= items.len() { Seq::empty() }
    else { match items[j].parent {
        None => Seq::empty(),
        Some((p, l)) => if p < j { letter_chain(items, p as int).push(l) }
            else { Seq::empty() },
    } }
}

pub(crate) proof fn lemma_letter_chain_len(items: Seq<Item>, j: int)
    requires parents_wf(items), 0 <= j < items.len(),
    ensures letter_chain(items, j).len() <= j,
    decreases j,
{
    if let Some((p, l)) = items[j].parent { lemma_letter_chain_len(items, p as int); }
}

pub(crate) open spec fn impl_item(g: model::Graph,
    table: Seq<implementation::ConstraintView>, it: Item) -> paper::Item {
    paper::Item { constraint: implementation::constraint_of(table[it.constraint as int]),
        state: model::lift_regex(g, it.residual@) }
}

pub(crate) open spec fn depth(items: Seq<Item>, j: int) -> nat {
    letter_chain(items, j).len()
}

pub(crate) open spec fn impl_nodes(g: model::Graph,
    table: Seq<implementation::ConstraintView>, items: Seq<Item>,
    alphabets: Map<nat, Set<model::Primitive>>) -> Seq<paper::Node> {
    items.map(|j: int, it: Item| paper::Node {
        item: impl_item(g, table, it), depth: depth(items, j),
        parent: match it.parent { None => None, Some((p, l)) =>
            Some((p as nat, implementation::letter_assignment(l@,
                if alphabets.dom().contains(p as nat) { alphabets[p as nat] }
                else { Set::empty() }))) },
    })
}

pub(crate) open spec fn ids_valid(g: model::Graph,
    table: Seq<implementation::ConstraintView>, items: Seq<Item>) -> bool {
    forall|j: int| #![trigger items[j]] 0 <= j < items.len()
        ==> items[j].constraint < table.len() && items[j].residual@ < g.regexes.len()
}

pub(crate) proof fn lemma_nodes_frame(a: model::Graph, b: model::Graph,
    table_a: Seq<implementation::ConstraintView>, table_b: Seq<implementation::ConstraintView>,
    items: Seq<Item>, alphabets: Map<nat, Set<model::Primitive>>)
    requires model::tables_wf(a), model::tables_extend(a,b), table_a.is_prefix_of(table_b),
        ids_valid(a,table_a,items),
    ensures ids_valid(b,table_b,items),
        impl_nodes(a,table_a,items,alphabets) == impl_nodes(b,table_b,items,alphabets),
{
    assert forall|j: int| 0 <= j < items.len() implies
        model::lift_regex(a,items[j].residual@) == model::lift_regex(b,items[j].residual@) by {
        model::lemma_lift_regex_stable(a,b,items[j].residual@);
    }
    assert(impl_nodes(a,table_a,items,alphabets) =~= impl_nodes(b,table_b,items,alphabets));
}

pub(crate) open spec fn alphabet_chain(items: Seq<Item>, alphabets: Map<nat, Set<model::Primitive>>,
    j: int) -> Seq<Set<model::Primitive>>
    decreases j,
{
    if j < 0 || j >= items.len() { Seq::empty() }
    else { match items[j].parent {
        None => Seq::empty(),
        Some((p, _)) => if p < j {
            alphabet_chain(items, alphabets, p as int).push(
                if alphabets.dom().contains(p as nat) { alphabets[p as nat] }
                else { Set::empty() })
        } else { Seq::empty() },
    } }
}

pub(crate) open spec fn chain_assignments(letters: Seq<Letter>, alphabets: Seq<Set<model::Primitive>>)
    -> Seq<paper::Assignment> {
    letters.map(|j: int, l: Letter| implementation::letter_assignment(l@, alphabets[j]))
}

pub(crate) proof fn lemma_chain_assignments_views(before: Seq<Letter>,after: Seq<Letter>,alphabets: Seq<Set<model::Primitive>>)
    requires before.map_values(|l: Letter| l@) == after.map_values(|l: Letter| l@),
    ensures chain_assignments(before,alphabets) == chain_assignments(after,alphabets),
{
    assert(before.map_values(|l: Letter| l@).len() == before.len());
    assert(after.map_values(|l: Letter| l@).len() == after.len());
    assert(before.len() == after.len());
    assert forall|i: int| 0 <= i < before.len() implies
        chain_assignments(before,alphabets)[i] == chain_assignments(after,alphabets)[i] by {
        assert(before.map_values(|l: Letter| l@)[i] == before[i]@);
        assert(after.map_values(|l: Letter| l@)[i] == after[i]@);
        assert(before[i]@ == after[i]@);
    }
    assert(chain_assignments(before,alphabets) =~= chain_assignments(after,alphabets));
}

pub(crate) proof fn lemma_chain_correspondence(g: model::Graph,
    table: Seq<implementation::ConstraintView>, items: Seq<Item>,
    alphabets: Map<nat, Set<model::Primitive>>, j: int, fuel: nat)
    requires parents_wf(items), 0 <= j < items.len(), fuel >= depth(items,j),
    ensures alphabet_chain(items,alphabets,j).len() == letter_chain(items,j).len(),
        paper::chain(impl_nodes(g,table,items,alphabets),j,fuel)
            == chain_assignments(letter_chain(items,j),alphabet_chain(items,alphabets,j)),
    decreases j,
{
    reveal(paper::chain);
    if let Some((p,l)) = items[j].parent {
        assert(depth(items,j) == depth(items,p as int) + 1);
        lemma_chain_correspondence(g,table,items,alphabets,p as int,(fuel-1) as nat);
        let prefix = letter_chain(items,p as int);
        let fields = alphabet_chain(items,alphabets,p as int);
        let atoms = if alphabets.dom().contains(p as nat) { alphabets[p as nat] }
            else { Set::empty() };
        assert(chain_assignments(prefix.push(l),fields.push(atoms)) =~=
            chain_assignments(prefix,fields).push(implementation::letter_assignment(l@,atoms)));
    }
}

pub(crate) open spec fn insertion_depth(items: Seq<Item>, parent: Option<(usize,Letter)>) -> nat {
    match parent { None => 0, Some((p,_)) => depth(items,p as int) + 1 }
}

pub(crate) open spec fn seen_certified(s: Search<'_>) -> bool {
    let g = facade::graph(*s.language);
    let nodes = impl_nodes(g,s.constraints@,s.items@,s.alphabets@);
    &&& members(s.seen) == s.seen_records@.to_set().map(
        |entry: (ConstraintId,RegexId,nat)| (entry.0,entry.1))
    &&& forall|j: int| #![trigger s.seen_records@[j]] 0 <= j < s.seen_records@.len() ==> {
        let record = s.seen_records@[j];
        record.0 < s.constraints@.len() && record.1@ < g.regexes.len()
            && paper::may_discard(ndomains(*s.universes),nodes,
                paper::Item { constraint: implementation::constraint_of(s.constraints@[record.0 as int]),
                    state: model::lift_regex(g,record.1@) },record.2)
    }
}

pub(crate) open spec fn state_wf(s: Search<'_>) -> bool {
    let g = facade::graph(*s.language);
    let nodes = impl_nodes(g,s.constraints@,s.items@,s.alphabets@);
    facade::language_wf(*s.language) && table_wf(s.constraints)
        && parents_wf(s.items@) && ids_valid(g,s.constraints@,s.items@)
        && 1 <= s.universes@.len() <= history_syntax::MAX_ARITY
        && (forall|i: int| 0 <= i < s.constraints@.len() ==> s.constraints@[i].len() == s.universes@.len())
        && crate::verify::simulation_exec::memo_wf(s.simulation,*s.language)
        && crate::verify::prune_exec::antichain_wf(s.antichain,g,s.constraints,nodes)
        && seen_certified(s)
}

pub(crate) proof fn lemma_seen_trace_frame(a: Search<'_>,b: Search<'_>)
    requires seen_certified(a),*a.language == *b.language,a.constraints@ == b.constraints@,
        a.items@ == b.items@,*a.universes == *b.universes,
        a.seen == b.seen,a.seen_records@ == b.seen_records@,
        trace(a,0).nodes == trace(b,0).nodes,
    ensures seen_certified(b),
{}

pub(crate) open spec fn seen_depth_bounded(s: Search<'_>, limit: nat) -> bool {
    forall|j: int| #![trigger s.seen_records@[j]] 0 <= j < s.seen_records@.len()
        ==> s.seen_records@[j].2 <= limit
}

pub(crate) proof fn lemma_nodes_push(g: model::Graph, table: Seq<implementation::ConstraintView>,
    items: Seq<Item>, alphabets: Map<nat,Set<model::Primitive>>, item: Item)
    requires parents_wf(items), item.parent matches Some((p,_)) ==> p < items.len(),
        item.parent is None ==> items.len() == 0,
    ensures parents_wf(items.push(item)),
        impl_nodes(g,table,items,alphabets).is_prefix_of(impl_nodes(g,table,items.push(item),alphabets)),
        forall|j: int| 0 <= j < items.len() ==> depth(items,j) == depth(items.push(item),j),
{
    assert forall|j: int| 0 <= j < items.len() implies
        letter_chain(items,j) == letter_chain(items.push(item),j) by {
        lemma_letter_chain_prefix(items,items.push(item),j);
    }
}

pub(crate) proof fn lemma_nodes_successor(g: model::Graph,table: Seq<implementation::ConstraintView>,
    items: Seq<Item>,alphabets: Map<nat,Set<model::Primitive>>,item: Item,p: usize,l: Letter)
    requires parents_wf(items),p < items.len(),item.parent == Some((p,l)),
        alphabets.dom().contains(p as nat),
    ensures impl_nodes(g,table,items.push(item),alphabets)
        == impl_nodes(g,table,items,alphabets).push(paper::Node {
            item:impl_item(g,table,item),depth:depth(items,p as int)+1,
            parent:Some((p as nat,implementation::letter_assignment(l@,alphabets[p as nat]))) }),
        forall|j: int| 0 <= j < items.len() ==> depth(items,j) == depth(items.push(item),j),
        depth(items.push(item),items.len() as int) == depth(items,p as int)+1,
{
    lemma_nodes_push(g,table,items,alphabets,item);
    assert(letter_chain(items.push(item),items.len() as int)
        == letter_chain(items.push(item),p as int).push(l));
    assert(impl_nodes(g,table,items.push(item),alphabets) =~=
        impl_nodes(g,table,items,alphabets).push(paper::Node {
            item:impl_item(g,table,item),depth:depth(items,p as int)+1,
            parent:Some((p as nat,implementation::letter_assignment(l@,alphabets[p as nat]))) }));
}

pub(crate) proof fn lemma_letter_chain_prefix(before: Seq<Item>, after: Seq<Item>, j: int)
    requires before.is_prefix_of(after), parents_wf(before), 0 <= j < before.len(),
    ensures letter_chain(before,j) == letter_chain(after,j),
    decreases j,
{
    if let Some((p,_)) = before[j].parent { lemma_letter_chain_prefix(before,after,p as int); }
}

pub(crate) proof fn lemma_seen_add(before: Search<'_>, after: Search<'_>,
    key: (ConstraintId,RegexId), d: nat)
    requires seen_certified(before), *before.language == *after.language,
        before.constraints == after.constraints, *before.universes == *after.universes,
        before.alphabets@ == after.alphabets@,
        impl_nodes(facade::graph(*before.language),before.constraints@,before.items@,before.alphabets@)
            .is_prefix_of(impl_nodes(facade::graph(*after.language),after.constraints@,after.items@,after.alphabets@)),
        after.seen_records@ == before.seen_records@.push((key.0,key.1,d)),
        members(after.seen) == members(before.seen).insert(key),
        key.0 < after.constraints@.len(),key.1@ < facade::graph(*after.language).regexes.len(),
        paper::may_discard(ndomains(*after.universes),
            impl_nodes(facade::graph(*after.language),after.constraints@,after.items@,after.alphabets@),
            paper::Item { constraint: implementation::constraint_of(after.constraints@[key.0 as int]),
                state: model::lift_regex(facade::graph(*after.language),key.1@) },d),
    ensures seen_certified(after),
{
    before.seen_records@.lemma_push_to_set_commute((key.0,key.1,d));
    before.seen_records@.to_set().lemma_set_map_insert_commute((key.0,key.1,d),
        |entry: (ConstraintId,RegexId,nat)| (entry.0,entry.1));
    assert forall|j: int| #![trigger after.seen_records@[j]] 0 <= j < after.seen_records@.len() implies {
        let record = after.seen_records@[j];
        record.0 < after.constraints@.len() && record.1@ < facade::graph(*after.language).regexes.len()
            && paper::may_discard(ndomains(*after.universes),
                impl_nodes(facade::graph(*after.language),after.constraints@,after.items@,after.alphabets@),
                paper::Item { constraint: implementation::constraint_of(after.constraints@[record.0 as int]),
                    state: model::lift_regex(facade::graph(*after.language),record.1@) },record.2)
    } by {
        if j < before.seen_records@.len() {
            let record = before.seen_records@[j];
            lemma_discard_grows(ndomains(*after.universes),
                impl_nodes(facade::graph(*before.language),before.constraints@,before.items@,before.alphabets@),
                impl_nodes(facade::graph(*after.language),after.constraints@,after.items@,after.alphabets@),
                paper::Item { constraint: implementation::constraint_of(after.constraints@[record.0 as int]),
                    state: model::lift_regex(facade::graph(*after.language),record.1@) },record.2);
        }
    }
}


pub(crate) struct Emission {
    pub(crate) group: int,
    pub(crate) letter: int,
    pub(crate) case: paper::Case,
}

#[verifier::opaque]
pub(crate) open spec fn emitted_cases(records: Seq<Emission>) -> Set<paper::Case> {
    records.to_set().map(|record: Emission| record.case)
}

pub(crate) open spec fn emitted_valid(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    atoms: Seq<Atom>, record: Emission) -> bool {
    0 <= record.group < groups.len() && 0 <= record.letter < groups[record.group].1@.len()
        && record.case.constraint == implementation::constraint_of(groups[record.group].0@)
        && record.case.alpha == implementation::letter_assignment(
            groups[record.group].1@[record.letter]@,atom_set(atoms))
}

#[verifier::opaque]
pub(crate) open spec fn coordinate(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    b: int,j: int) -> bool { 0 <= b < groups.len() && 0 <= j < groups[b].1@.len() }

pub(crate) proof fn lemma_coordinate(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,b: int,j: int)
    requires 0 <= b < groups.len(),0 <= j < groups[b].1@.len(),
    ensures coordinate(groups,b,j),
{ reveal(coordinate); }

pub(crate) open spec fn enumeration_prefix(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    atoms: Seq<Atom>, records: Seq<Emission>, group: int, letter: int) -> bool {
    &&& 0 <= group <= groups.len()
    &&& 0 <= letter
    &&& (group < groups.len() ==> letter <= groups[group].1@.len())
    &&& (group == groups.len() ==> letter == 0)
    &&& (forall|n: int| #![trigger records[n]] 0 <= n < records.len() ==>
        emitted_valid(groups,atoms,records[n])
            && (records[n].group < group || records[n].group == group && records[n].letter < letter))
    &&& (forall|b: int, j: int| #[trigger] coordinate(groups,b,j)
            && (b < group || b == group && j < letter)
        ==> (exists|n: int| 0 <= n < records.len() && records[n].group == b && records[n].letter == j))
    &&& (forall|m: int,n: int| #![trigger records[m],records[n]] 0 <= m < records.len()
        && 0 <= n < records.len() && records[m].group == records[n].group
        && records[m].letter == records[n].letter ==> m == n)
}

pub(crate) proof fn lemma_emitted_member(records: Seq<Emission>, c: paper::Case)
    ensures emitted_cases(records).contains(c)
        == (exists|n: int| 0 <= n < records.len() && records[n].case == c),
{
    reveal(emitted_cases);
    if emitted_cases(records).contains(c) {
        let r = choose|r: Emission| records.to_set().contains(r) && r.case == c;
        let n = choose|n: int| 0 <= n < records.len() && records[n] == r;
    }
    if exists|n: int| 0 <= n < records.len() && records[n].case == c {
        let n = choose|n: int| 0 <= n < records.len() && records[n].case == c;
        assert(records.to_set().contains(records[n]));
    }
}

pub(crate) proof fn lemma_steps_group_evidence(g: crate::constraint::Constraint,atoms: Seq<Atom>,u: Universes,
    groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,b: int)
    requires crate::verify::steps_result(g,atoms,u,groups),0 <= b < groups.len(),
    ensures crate::verify::constraint_wf(groups[b].0),groups[b].0@.len() == u@.len(),
        forall|j: int| 0 <= j < groups[b].1@.len() ==> crate::verify::letter_wf(groups[b].1@[j])
            && groups[b].1@[j]@.classes.len() == u@.len(),
{
    reveal(crate::verify::steps_result);
}

#[verifier::rlimit(20)]
pub(crate) proof fn lemma_emitted_steps(g: crate::constraint::Constraint,atoms: Seq<Atom>,
    universes: Universes,groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    records: Seq<Emission>,state: Regex<model::Test>)
    requires atoms_wf(atoms,universes@.len()),crate::verify::steps_result(g,atoms,universes,groups),
        inclusion::satisfiable(ndomains(universes),implementation::constraint_of(g@)),
        enumeration_prefix(groups,atoms,records,groups.len() as int,0),
        groups.map_values(|group: (crate::constraint::Constraint,alloc::vec::Vec<Letter>)| group.0@).no_duplicates(),
        crate::verify::constraint_unique::steps_alphas_unique(g,atoms,universes,groups),
        forall|n: int| 0 <= n < records.len() ==>
            paper::successor_ok(state,records[n].case.alpha,records[n].case.next),
    ensures paper::steps_ok(ndomains(universes),
        paper::Item { constraint: implementation::constraint_of(g@),state },emitted_cases(records)),
{
    hide(language::lang); hide(paper::successor_ok); hide(paper::realizes);
    hide(crate::verify::split_views);
    hide(crate::verify::letters_views);
    hide(crate::verify::register_options);
    hide(crate::verify::class_options);
    hide(inclusion::sat_by);
    hide(inclusion::satisfiable);
    hide(inclusion::entails);
    hide(encoding::n_theta_ok);
    hide(encoding::n_event_in);
    let d = ndomains(universes);
    let operands = choose|operands: crate::constraint::Operands|
        crate::verify::operands_of(operands,atoms)
        && crate::verify::shape_wf(g,operands,universes)
        && crate::verify::constraint_views(crate::verify::group_constraints(groups))
            == crate::verify::split_views(g,operands,universes)
        && forall|b: int| 0 <= b < groups.len() ==> crate::verify::constraint_wf(groups[b].0)
            && groups[b].0@.len() == universes@.len()
            && crate::verify::letter_views(groups[b].1@)
                == crate::verify::letters_views(groups[b].0,operands,universes);
    let splits = crate::verify::split_views(g,operands,universes).map(
        |v: implementation::ConstraintView| implementation::constraint_of(v));
    crate::verify::lemma_split_views_ok(g,operands,universes,atoms);
    crate::verify::lemma_group_constraints(groups);
    assert forall|c: paper::Case| emitted_cases(records).contains(c) implies {
        inclusion::satisfiable(d,c.constraint) && inclusion::entails(d,c.constraint,implementation::constraint_of(g@))
            && paper::successor_ok(state,c.alpha,c.next)
            && forall|theta: Subst| encoding::n_theta_ok(d,theta) && inclusion::sat_by(theta,c.constraint)
                ==> exists|e: EventView| encoding::n_event_in(d,e) && paper::realizes(theta,e,c.alpha)
    } by {
        lemma_emitted_member(records,c);
        let n = choose|n: int| 0 <= n < records.len() && records[n].case == c;
        let b = records[n].group; let j = records[n].letter;
        assert(emitted_valid(groups,atoms,records[n]));
        assert(groups[b].1@.to_set().contains(groups[b].1@[j]));
        assert(crate::verify::letter_views(groups[b].1@).contains(groups[b].1@[j]@));
        assert(crate::verify::split_views(g,operands,universes).contains(groups[b].0@));
        crate::verify::lemma_split_options_sound(g,operands,universes,groups[b].0@);
        crate::verify::lemma_refined_letters_ready(g,operands,universes,groups[b].0);
        assert forall|theta: Subst| encoding::n_theta_ok(d,theta) && inclusion::sat_by(theta,c.constraint)
            implies exists|e: EventView| encoding::n_event_in(d,e) && paper::realizes(theta,e,c.alpha) by {
            crate::verify::lemma_letters_realize(groups[b].0,operands,atoms,universes,groups[b].1@[j]@,theta);
        }
    }
    assert forall|theta: Subst,e: EventView| encoding::n_theta_ok(d,theta)
        && encoding::n_event_in(d,e) && inclusion::sat_by(theta,implementation::constraint_of(g@)) implies
        exists|c: paper::Case| emitted_cases(records).contains(c)
            && inclusion::sat_by(theta,c.constraint) && paper::realizes(theta,e,c.alpha) by {
        let gamma = choose|gamma: inclusion::Constraint| splits.contains(gamma) && inclusion::sat_by(theta,gamma);
        let view = choose|view: implementation::ConstraintView|
            crate::verify::split_views(g,operands,universes).contains(view)
                && implementation::constraint_of(view) == gamma;
        let b = choose|b: int| 0 <= b < groups.len() && groups[b].0@ == view;
        crate::verify::lemma_refined_letters_ready(g,operands,universes,groups[b].0);
        let l = crate::verify::lemma_letters_complete(groups[b].0,operands,atoms,universes,theta,e);
        let concrete = choose|concrete: Letter| groups[b].1@.to_set().contains(concrete) && concrete@ == l;
        let j = choose|j: int| 0 <= j < groups[b].1@.len() && groups[b].1@[j] == concrete;
        lemma_coordinate(groups,b,j);
        let n = choose|n: int| 0 <= n < records.len() && records[n].group == b && records[n].letter == j;
        lemma_emitted_member(records,records[n].case);
        assert(emitted_cases(records).contains(records[n].case));
    }
    assert forall|theta: Subst,e: EventView,c1: paper::Case,c2: paper::Case|
        encoding::n_theta_ok(d,theta) && emitted_cases(records).contains(c1) && emitted_cases(records).contains(c2)
        && inclusion::sat_by(theta,c1.constraint) && inclusion::sat_by(theta,c2.constraint)
        && paper::realizes(theta,e,c1.alpha) && paper::realizes(theta,e,c2.alpha) implies c1 == c2 by {
        lemma_emitted_member(records,c1); lemma_emitted_member(records,c2);
        let n1 = choose|n: int| 0 <= n < records.len() && records[n].case == c1;
        let n2 = choose|n: int| 0 <= n < records.len() && records[n].case == c2;
        let b1 = records[n1].group; let b2 = records[n2].group;
        let j1 = records[n1].letter; let j2 = records[n2].letter;
        assert(crate::verify::split_views(g,operands,universes).contains(groups[b1].0@));
        assert(crate::verify::split_views(g,operands,universes).contains(groups[b2].0@));
        assert(splits.contains(c1.constraint) && splits.contains(c2.constraint));
        assert(c1.constraint == c2.constraint);
        crate::verify::lemma_constraint_literals_injective(groups[b1].0@,groups[b2].0@);
        let views = groups.map_values(|group: (crate::constraint::Constraint,alloc::vec::Vec<Letter>)| group.0@);
        assert(views[b1] == groups[b1].0@ && views[b2] == groups[b2].0@);
        if b1 < b2 { assert(views[b1] != views[b2]); }
        if b2 < b1 { assert(views[b2] != views[b1]); }
        assert(b1 == b2);
        paper::lemma_realizes_unique(theta,e,atom_set(atoms),c1.alpha,c2.alpha);
        let assignments = groups[b1].1@.map_values(|l: Letter|
            implementation::letter_assignment(l@,atom_set(atoms)));
        assert(assignments[j1] == c1.alpha && assignments[j2] == c2.alpha);
        assert(j1 == j2);
        assert(n1 == n2);
    }
}

pub(crate) open spec fn register_literal(g: implementation::RegisterView,equal: bool,value: nat) -> bool {
    match g { implementation::RegisterView::Equals(v) => equal && value == v,
        implementation::RegisterView::Differs(values) => !equal && values.contains(value) }
}

pub(crate) proof fn lemma_option_literals(source: implementation::RegisterView,
    target: implementation::RegisterView,register: bool,constants: Set<nat>,
    domain: Option<Set<nat>>,equal: bool,value: nat)
    requires crate::verify::register_options(source,register,constants,domain).contains(target),
        register_literal(target,equal,value),
    ensures register_literal(source,equal,value) || constants.contains(value)
        || match domain { Some(values) => values.contains(value), None => false },
{
    match source {
        implementation::RegisterView::Equals(_) => {},
        implementation::RegisterView::Differs(differs) => {
            if register { match domain {
                Some(values) => {
                    let v = choose|v: nat| values.difference(differs).contains(v)
                        && implementation::RegisterView::Equals(v) == target;
                },
                None => { match target {
                    implementation::RegisterView::Equals(v) => {
                        if constants.difference(differs).len() > 0 {
                            let w = choose|w: nat| constants.difference(differs).contains(w)
                                && implementation::RegisterView::Equals(w) == target;
                        }
                    },
                    implementation::RegisterView::Differs(_) => {},
                } },
            } }
        },
    }
}

pub(crate) proof fn lemma_emitted_literals(g: crate::constraint::Constraint,atoms: Seq<Atom>,
    universes: Universes,groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    records: Seq<Emission>)
    requires atoms_wf(atoms,universes@.len()),crate::verify::steps_result(g,atoms,universes,groups),
        forall|n: int| 0 <= n < records.len() ==> emitted_valid(groups,atoms,records[n]),
    ensures forall|c: paper::Case,l: inclusion::Literal|
        emitted_cases(records).contains(c) && c.constraint.contains(l) ==>
            implementation::constraint_of(g@).contains(l)
            || finiteness::atom_codes(atom_set(atoms)).contains(l.value)
            || match encoding::n_domain(ndomains(universes),l.component) {
                Some(values) => values.contains(l.value),None => false },
{
    let operands = choose|operands: crate::constraint::Operands|
        crate::verify::operands_of(operands,atoms)
        && crate::verify::shape_wf(g,operands,universes)
        && crate::verify::constraint_views(crate::verify::group_constraints(groups))
            == crate::verify::split_views(g,operands,universes)
        && forall|b: int| 0 <= b < groups.len() ==> crate::verify::constraint_wf(groups[b].0)
            && groups[b].0@.len() == universes@.len()
            && crate::verify::letter_views(groups[b].1@)
                == crate::verify::letters_views(groups[b].0,operands,universes);
    crate::verify::lemma_operand_atoms(operands,atoms);
    crate::verify::lemma_group_constraints(groups);
    crate::verify::lemma_register_product_members(crate::verify::split_axes(g,operands,universes));
    assert forall|c: paper::Case,l: inclusion::Literal|
        emitted_cases(records).contains(c) && c.constraint.contains(l) implies
            implementation::constraint_of(g@).contains(l)
            || finiteness::atom_codes(atom_set(atoms)).contains(l.value)
            || match encoding::n_domain(ndomains(universes),l.component) {
                Some(values) => values.contains(l.value),None => false } by {
        lemma_emitted_member(records,c);
        let n = choose|n: int| 0 <= n < records.len() && records[n].case == c;
        let b = records[n].group;
        let target = groups[b].0@;
        assert(crate::verify::split_views(g,operands,universes).contains(target));
        crate::verify::lemma_constraint_view(target);crate::verify::lemma_constraint_view(g@);
        let k = crate::verify::component_index(l.component) as int;
        assert(l.component.0 < target.len());
        assert(target.len() == g@.len() && target.len() == universes@.len());
        lemma_option_literals(implementation::register_of(g@,l.component),implementation::register_of(target,l.component),
            operands.register[k],crate::verify::codes(operands.constants[k].view()),
            crate::verify::domain_view(universes[k]),l.equal,l.value);
        if crate::verify::codes(operands.constants[k].view()).contains(l.value) {
            assert(atom_set(atoms).contains(model::Primitive::Eq(l.component,model::GTerm::Constant(l.value))));
            assert(finiteness::atom_codes(atom_set(atoms)).contains(l.value));
        }
    }
}

pub(crate) open spec fn register_in_vocabulary(g: implementation::RegisterView,values: Set<nat>) -> bool {
    match g { implementation::RegisterView::Equals(v) => values.contains(v),
        implementation::RegisterView::Differs(ds) => ds.subset_of(values) }
}

pub(crate) open spec fn constraint_in_vocabulary(g: implementation::ConstraintView,v: Seq<Set<nat>>) -> bool {
    g.len() == v.len() && forall|i: int| 0 <= i < g.len() ==> register_in_vocabulary(g[i],v[i])
}

pub(crate) open spec fn atoms_in_vocabulary(atoms: Seq<Atom>,v: Seq<Set<nat>>) -> bool {
    forall|i: int| #![trigger atoms[i]] 0 <= i < atoms.len() ==> atoms[i].component < v.len()
        && match atoms[i].operand { crate::constraint::Operand::Constant(code) =>
            v[atoms[i].component as int].contains(code as nat),_ => true }
}

/// A sufficient product bound, not a precondition of search or successor generation.
pub(crate) open spec fn resource_prefix(v: Seq<Set<nat>>,count: nat) -> nat
    recommends count <= v.len(),
    decreases count,
{
    if count == 0 { 1 } else { resource_prefix(v,(count-1) as nat)*(v[count as int-1].len()+2) }
}

pub(crate) open spec fn resource_capacity(v: Seq<Set<nat>>) -> bool {
    forall|count: nat| count <= v.len() ==> resource_prefix(v,count) <= usize::MAX
}


#[verifier::opaque]
pub(crate) open spec fn partial_parent(cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace,
    j: int,limit: nat) -> bool {
    match t.nodes[j].parent {
        None => false,Some((p,alpha)) => p < limit && p < j && t.nodes[j].depth == t.nodes[p as int].depth+1
            && exists|c: paper::Case| cases(t.nodes[p as int].item).contains(c) && c.alpha == alpha
                && t.nodes[j].item == paper::case_item(c),
    }
}

#[verifier::opaque]
pub(crate) open spec fn partial_coverage(d: encoding::NDomains,cases: spec_fn(paper::Item)->Set<paper::Case>,
    t: paper::Trace,p: int) -> bool {
    !paper::nullable_state(t.nodes[p].item.state)
        && forall|c: paper::Case| cases(t.nodes[p].item).contains(c) ==>
            (exists|j: int| 0 < j < t.nodes.len() && t.nodes[j].parent == Some((p as nat,c.alpha))
                && t.nodes[j].item == paper::case_item(c))
            || paper::may_discard(d,t.nodes,paper::case_item(c),t.nodes[p].depth+1)
}

pub(crate) proof fn lemma_parent_limit(cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace,
    j: int,old: nat,new: nat)
    requires partial_parent(cases,t,j,old),old <= new,
    ensures partial_parent(cases,t,j,new),
{ reveal(partial_parent); }

pub(crate) proof fn lemma_coverage_empty(d: encoding::NDomains,cases: spec_fn(paper::Item)->Set<paper::Case>,
    t: paper::Trace,p: int)
    requires !paper::nullable_state(t.nodes[p].item.state),cases(t.nodes[p].item) == Set::<paper::Case>::empty(),
    ensures partial_coverage(d,cases,t,p),
{ hide(language::nullable);hide(paper::may_discard);reveal(partial_coverage); }

/// Current-parent coverage refers only to emitted cases until the expansion finishes.
#[verifier::opaque]
pub(crate) open spec fn partial_trace_wf(d: encoding::NDomains,start: paper::Item,
    cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace,expanding: bool) -> bool {
    let nodes = t.nodes;
    let limit = t.expanded + if expanding { 1nat } else { 0nat };
    &&& t.expanded <= nodes.len()
    &&& if nodes.len() == 0 { paper::may_discard(d,nodes,start,0) }
        else { nodes[0] == paper::Node { item:start,parent:None,depth:0 } }
    &&& if expanding {
        forall|j: int| 0 < j < nodes.len() ==> #[trigger] partial_parent(cases,t,j,t.expanded+1)
    } else {
        forall|j: int| 0 < j < nodes.len() ==> #[trigger] partial_parent(cases,t,j,t.expanded)
    }
    &&& forall|i: int,j: int| #![trigger nodes[i],nodes[j]] 0 <= i < j < nodes.len()
        ==> nodes[i].depth <= nodes[j].depth && nodes[i].item != nodes[j].item
    &&& forall|p: int| 0 <= p < limit && p < nodes.len() ==> #[trigger] partial_coverage(d,cases,t,p)
}

pub(crate) proof fn lemma_partial_trace_complete(d: encoding::NDomains,start: paper::Item,
    cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace)
    requires partial_trace_wf(d,start,cases,t,false),
    ensures paper::trace_wf(d,start.constraint,start.state,cases,t),
{
    hide(language::lang); hide(language::nullable); hide(paper::may_discard);
    reveal(partial_trace_wf);
    assert forall|j: int| 0 < j < t.nodes.len() implies #[trigger] paper::parent_ok(cases,t,j) by {
        reveal(partial_parent);
        assert(partial_parent(cases,t,j,t.expanded));
    }
    assert forall|p: int| #![trigger t.nodes[p]] 0 <= p < t.expanded implies
        !paper::nullable_state(t.nodes[p].item.state)
            && forall|c: paper::Case| cases(t.nodes[p].item).contains(c) ==>
                (exists|j: int| 0 < j < t.nodes.len() && t.nodes[j].parent == Some((p as nat,c.alpha))
                    && t.nodes[j].item == paper::case_item(c))
                || paper::may_discard(d,t.nodes,paper::case_item(c),t.nodes[p].depth+1) by {
        reveal(partial_coverage);assert(partial_coverage(d,cases,t,p));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub(crate) proof fn lemma_partial_begin(d: encoding::NDomains,start: paper::Item,
    cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace)
    requires partial_trace_wf(d,start,cases,t,false),t.expanded < t.nodes.len(),
        !paper::nullable_state(t.nodes[t.expanded as int].item.state),
        cases(t.nodes[t.expanded as int].item) == Set::<paper::Case>::empty(),
    ensures partial_trace_wf(d,start,cases,t,true),
{
    reveal(partial_trace_wf);
    assert forall|j: int| 0 < j < t.nodes.len() implies #[trigger] partial_parent(cases,t,j,t.expanded+1) by {
        lemma_parent_limit(cases,t,j,t.expanded,t.expanded+1);
    }
    assert forall|p: int| 0 <= p < t.expanded+1 && p < t.nodes.len()
        implies #[trigger] partial_coverage(d,cases,t,p) by {
        if p == t.expanded { lemma_coverage_empty(d,cases,t,p); }
    }
}

pub(crate) proof fn lemma_partial_end(d: encoding::NDomains,start: paper::Item,
    cases: spec_fn(paper::Item)->Set<paper::Case>,t: paper::Trace)
    requires partial_trace_wf(d,start,cases,t,true),t.expanded < t.nodes.len(),
    ensures partial_trace_wf(d,start,cases,paper::Trace { nodes:t.nodes,expanded:t.expanded+1 },false),
{
    reveal(partial_trace_wf);
    let next = paper::Trace { nodes:t.nodes,expanded:t.expanded+1 };
    assert forall|j: int| 0 < j < t.nodes.len() implies #[trigger] partial_parent(cases,next,j,next.expanded) by {
        lemma_partial_clauses_frame(d,cases,t,next,t.expanded+1,j);
        assert(partial_parent(cases,t,j,t.expanded+1));
    }
    assert forall|p: int| 0 <= p < next.expanded && p < next.nodes.len()
        implies #[trigger] partial_coverage(d,cases,next,p) by {
        lemma_partial_clauses_frame(d,cases,t,next,t.expanded+1,p);
        assert(partial_coverage(d,cases,t,p));
    }
}

pub(crate) proof fn lemma_archive_grows(archive: Map<paper::Item,Set<paper::Case>>,
    item: paper::Item,c: paper::Case)
    ensures forall|i: paper::Item,v: paper::Case| #![trigger archive_cases(archive)(i).contains(v)]
        archive_cases(archive)(i).contains(v) ==>
            archive_cases(archive.insert(item,archive_cases(archive)(item).insert(c)))(i).contains(v),
{}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub(crate) proof fn lemma_partial_case(d: encoding::NDomains,start: paper::Item,
    archive: Map<paper::Item,Set<paper::Case>>,before: paper::Trace,after: paper::Trace,c: paper::Case)
    requires partial_trace_wf(d,start,archive_cases(archive),before,true),before.expanded < before.nodes.len(),
        after.expanded == before.expanded,
        after.nodes == before.nodes || after.nodes == before.nodes.push(paper::Node {
            item:paper::case_item(c),parent:Some((before.expanded,c.alpha)),
            depth:before.nodes[before.expanded as int].depth+1 }),
        forall|i: int,j: int| 0 <= i < j < after.nodes.len()
            ==> after.nodes[i].depth <= after.nodes[j].depth && after.nodes[i].item != after.nodes[j].item,
        paper::may_discard(d,after.nodes,paper::case_item(c),before.nodes[before.expanded as int].depth+1),
    ensures partial_trace_wf(d,start,archive_cases(archive.insert(before.nodes[before.expanded as int].item,
        archive_cases(archive)(before.nodes[before.expanded as int].item).insert(c))),after,true),
{
    hide(paper::may_discard);
    reveal(partial_trace_wf);
    let item = before.nodes[before.expanded as int].item;
    let updated = archive.insert(item,archive_cases(archive)(item).insert(c));
    lemma_archive_grows(archive,item,c);
    assert(before.nodes.is_prefix_of(after.nodes));
    assert forall|j: int| 0 < j < after.nodes.len() implies #[trigger] partial_parent(archive_cases(updated),after,j,after.expanded+1) by {
        if j < before.nodes.len() { lemma_parent_archive_frame(archive,before,after,c,j); }
        else {
            reveal(partial_parent);
            assert(archive_cases(updated)(item).contains(c));
        }
    }
    assert forall|p: int| 0 <= p < after.expanded+1 && p < after.nodes.len()
        implies #[trigger] partial_coverage(d,archive_cases(updated),after,p) by {
        assert(p < before.nodes.len());
        assert(before.nodes[p].item == item ==> p == before.expanded) by {
            if p < before.expanded { assert(before.nodes[p].item != item); }
        }
        lemma_coverage_archive_frame(d,archive,before,after,c,p);
    }
}


pub(crate) proof fn lemma_option_vocabulary(source: implementation::RegisterView,
    target: implementation::RegisterView,register: bool,constants: Set<nat>,
    domain: Option<Set<nat>>,values: Set<nat>)
    requires crate::verify::register_options(source,register,constants,domain).contains(target),
        register_in_vocabulary(source,values),constants.subset_of(values),
        match domain { Some(ds) => ds.subset_of(values),None => true },
    ensures register_in_vocabulary(target,values),
{
    match target {
        implementation::RegisterView::Equals(v) => {
            lemma_option_literals(source,target,register,constants,domain,true,v);
        },
        implementation::RegisterView::Differs(ds) => {
            assert forall|v: nat| ds.contains(v) implies values.contains(v) by {
                lemma_option_literals(source,target,register,constants,domain,false,v);
            }
        },
    }
}

pub(crate) open spec fn syntactic_entails(a: implementation::ConstraintView,b: implementation::ConstraintView) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> crate::verify::register_entails(a[i],b[i])
}

pub(crate) proof fn lemma_register_entails_trans(a: implementation::RegisterView,
    b: implementation::RegisterView,c: implementation::RegisterView)
    requires crate::verify::register_entails(a,b),crate::verify::register_entails(b,c),
    ensures crate::verify::register_entails(a,c),
{
    match a { implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {} }
    match b { implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {} }
    match c { implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {} }
}

pub(crate) proof fn lemma_syntactic_entails_trans(a: implementation::ConstraintView,
    b: implementation::ConstraintView,c: implementation::ConstraintView)
    requires syntactic_entails(a,b),syntactic_entails(b,c),
    ensures syntactic_entails(a,c),
{
    assert forall|i: int| 0 <= i < a.len() implies crate::verify::register_entails(a[i],c[i]) by {
        lemma_register_entails_trans(a[i],b[i],c[i]);
    }
}

pub(crate) proof fn lemma_letter_coherent_strengthen(a: implementation::ConstraintView,
    b: implementation::ConstraintView,l: implementation::LetterView,atoms: Set<model::Primitive>)
    requires syntactic_entails(a,b),crate::verify::reconstruction::letter_coherent(b,l,atoms),
    ensures crate::verify::reconstruction::letter_coherent(a,l,atoms),
{
    assert forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_register(l,c)] c.0 < a.len() implies match implementation::letter_register(l,c) {
        implementation::ClassView::Constant(v) => implementation::register_of(a,c) == implementation::RegisterView::Equals(v),
        implementation::ClassView::Register => (atoms.contains(model::Primitive::Eq(c,model::GTerm::Variable(c)))
            || implementation::letter_class(l,c) == Some(implementation::ClassView::Register)) ==> {
            &&& forall|v: nat| atoms.contains(model::Primitive::Eq(c,model::GTerm::Constant(v))) ==>
                crate::verify::register_entails(implementation::register_of(a,c),implementation::RegisterView::Differs(Set::empty().insert(v)))
            &&& implementation::letter_class(l,c) matches Some(implementation::ClassView::Constant(v)) ==>
                crate::verify::register_entails(implementation::register_of(a,c),implementation::RegisterView::Differs(Set::empty().insert(v)))
        },
    } by {
        assert(crate::verify::register_entails(implementation::register_of(a,c),implementation::register_of(b,c)));
        match implementation::letter_register(l,c) {
            implementation::ClassView::Constant(_) => {},
            implementation::ClassView::Register => {
                if atoms.contains(model::Primitive::Eq(c,model::GTerm::Variable(c)))
                    || implementation::letter_class(l,c) == Some(implementation::ClassView::Register) {
                    assert forall|v: nat| atoms.contains(model::Primitive::Eq(c,model::GTerm::Constant(v))) implies
                        crate::verify::register_entails(implementation::register_of(a,c),implementation::RegisterView::Differs(Set::empty().insert(v))) by {
                        lemma_register_entails_trans(implementation::register_of(a,c),implementation::register_of(b,c),
                            implementation::RegisterView::Differs(Set::empty().insert(v)));
                    }
                    if let Some(implementation::ClassView::Constant(v)) = implementation::letter_class(l,c) {
                        lemma_register_entails_trans(implementation::register_of(a,c),implementation::register_of(b,c),
                            implementation::RegisterView::Differs(Set::empty().insert(v)));
                    }
                }
            },
        }
    }
}

pub(crate) proof fn lemma_generated_letter_coherent(g: crate::constraint::Constraint,
    operands: crate::constraint::Operands,atoms: Seq<Atom>,universes: Universes,
    l: implementation::LetterView)
    requires atoms_wf(atoms,universes@.len()),crate::verify::operands_of(operands,atoms),
        crate::verify::letters_ready(g@,operands,universes),
        crate::verify::shape_wf(g,operands,universes),
        crate::verify::letters_views(g,operands,universes).contains(l),
    ensures crate::verify::reconstruction::letter_coherent(g@,l,atom_set(atoms)),
{
    crate::verify::lemma_letters_members(g,operands,universes);
    crate::verify::lemma_operand_atoms(operands,atoms);
    assert forall|p: model::Primitive| atom_set(atoms).contains(p) implies match p {
        model::Primitive::Eq(c,model::GTerm::Variable(c2)) => c == c2 && c.0 < g@.len(),
        model::Primitive::Eq(c,model::GTerm::Constant(_)) => c.0 < g@.len(),
    } by {
        let a = choose|a: Atom| atoms.to_set().contains(a) && a@ == p;
        let i = choose|i: int| 0 <= i < atoms.len() && atoms[i] == a;
    }
    assert forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_register(l,c)] c.0 < g@.len() implies match implementation::letter_register(l,c) {
        implementation::ClassView::Constant(v) => implementation::register_of(g@,c) == implementation::RegisterView::Equals(v),
        implementation::ClassView::Register => (atom_set(atoms).contains(model::Primitive::Eq(c,model::GTerm::Variable(c)))
            || implementation::letter_class(l,c) == Some(implementation::ClassView::Register)) ==> {
            &&& forall|v: nat| atom_set(atoms).contains(model::Primitive::Eq(c,model::GTerm::Constant(v))) ==>
                crate::verify::register_entails(implementation::register_of(g@,c),implementation::RegisterView::Differs(Set::empty().insert(v)))
            &&& implementation::letter_class(l,c) matches Some(implementation::ClassView::Constant(v)) ==>
                crate::verify::register_entails(implementation::register_of(g@,c),implementation::RegisterView::Differs(Set::empty().insert(v)))
        },
    } by {
        let k = crate::verify::component_index(c) as int;
        let r = implementation::register_of(g@,c);
        let names = crate::verify::codes(operands.constants[k].view());
        crate::verify::lemma_class_options_members(r,operands.register[k],names,universes[k],implementation::letter_class(l,c));
        assert(implementation::letter_register(l,c) == crate::verify::register_class(r));
        match r {
            implementation::RegisterView::Equals(_) => {},
            implementation::RegisterView::Differs(ds) => {
                if atom_set(atoms).contains(model::Primitive::Eq(c,model::GTerm::Variable(c)))
                    || implementation::letter_class(l,c) == Some(implementation::ClassView::Register) {
                    assert(operands.register[k]);
                    assert(crate::verify::field_ready(r,true,names,crate::verify::domain_view(universes[k])));
                    assert forall|v: nat| atom_set(atoms).contains(model::Primitive::Eq(c,model::GTerm::Constant(v))) implies
                        crate::verify::register_entails(r,implementation::RegisterView::Differs(Set::empty().insert(v))) by {
                        assert(names.contains(v));
                    }
                    if let Some(implementation::ClassView::Constant(v)) = implementation::letter_class(l,c) {
                        assert(crate::verify::domain_view(universes[k]) is None);
                        assert(names.contains(v));
                    }
                }
            },
        }
    }
    assert forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_class(l,c)]
        c.0 < g@.len() && implementation::letter_class(l,c) == Some(implementation::ClassView::Register) implies
        implementation::letter_register(l,c) == implementation::ClassView::Register by {
        let k = crate::verify::component_index(c) as int;
        crate::verify::lemma_class_options_members(implementation::register_of(g@,c),operands.register[k],
            crate::verify::codes(operands.constants[k].view()),universes[k],implementation::letter_class(l,c));
    }
}


pub(crate) open spec fn domain_values(universe: crate::constraint::Universe) -> Set<nat> {
    match crate::verify::domain_view(universe) { Some(values) => values,None => Set::empty() }
}

pub(crate) open spec fn root_vocabulary(l: SymbolicLanguage,u: Universes,g: implementation::ConstraintView)
    -> Seq<Set<nat>> {
    let ps = symbolic::regex_primitives(model::lift_regex(facade::graph(l),facade::root(l)));
    Seq::new(u@.len(),|i: int| facade::primitive_codes(ps,crate::verify::component_at(i as usize))
        .union(crate::verify::register_codes(g[i])).union(domain_values(u[i])))
}

pub(crate) open spec fn queue_order(s: Search<'_>) -> bool {
    &&& forall|i: int,j: int| #![trigger s.items@[i],s.items@[j]] 0 <= i < j < s.items@.len()
        ==> depth(s.items@,i) <= depth(s.items@,j)
            && (s.items@[i].constraint,s.items@[i].residual) != (s.items@[j].constraint,s.items@[j].residual)
    &&& forall|j: int| #![trigger s.items@[j]] 0 <= j < s.items@.len()
        ==> members(s.seen).contains((s.items@[j].constraint,s.items@[j].residual))
}

pub(crate) proof fn lemma_node_items_distinct(l: SymbolicLanguage,table: ConstraintTable,
    items: Seq<Item>,alphabets: Map<nat,Set<model::Primitive>>)
    requires facade::language_wf(l),table_wf(table),ids_valid(facade::graph(l),table@,items),
        forall|i: int,j: int| 0 <= i < j < items.len()
            ==> (items[i].constraint,items[i].residual) != (items[j].constraint,items[j].residual),
        forall|i: int,j: int| 0 <= i < items.len() && 0 <= j < items.len()
            ==> table@[items[i].constraint as int].len() == table@[items[j].constraint as int].len(),
    ensures forall|i: int,j: int| 0 <= i < j < items.len()
        ==> impl_nodes(facade::graph(l),table@,items,alphabets)[i].item
            != impl_nodes(facade::graph(l),table@,items,alphabets)[j].item,
{
    facade::lemma_language_wf(l);
    assert forall|i: int,j: int| 0 <= i < j < items.len() implies
        impl_item(facade::graph(l),table@,items[i]) != impl_item(facade::graph(l),table@,items[j]) by {
        if impl_item(facade::graph(l),table@,items[i]) == impl_item(facade::graph(l),table@,items[j]) {
            crate::verify::lemma_constraint_literals_injective(table@[items[i].constraint as int],table@[items[j].constraint as int]);
            crate::verify::lemma_table_injective(table,items[i].constraint as int,items[j].constraint as int);
            finiteness::lemma_lift_regex_injective(facade::graph(l),items[i].residual@,items[j].residual@);
            assert(items[i].residual == items[j].residual);
        }
    }
}

pub(crate) proof fn lemma_queue_nodes_distinct(s: Search<'_>)
    requires state_wf(s),queue_order(s),
    ensures forall|i: int,j: int| 0 <= i < j < s.items@.len()
        ==> trace(s,0).nodes[i].depth <= trace(s,0).nodes[j].depth
            && trace(s,0).nodes[i].item != trace(s,0).nodes[j].item,
{
    lemma_node_items_distinct(*s.language,s.constraints,s.items@,s.alphabets@);
}

pub(crate) open spec fn outcome_view(outcome: crate::search::SearchOutcome) -> paper::Outcome {
    match outcome { crate::search::SearchOutcome::Holds => paper::Outcome::Holds,
        crate::search::SearchOutcome::Refuted(r) => paper::Outcome::Refuted(
            implementation::constraint_of(r.constraint@),r.assignments@) }
}

pub(crate) proof fn lemma_trace_query_ok(d: encoding::NDomains,start: paper::Item,
    archive: Map<paper::Item,Set<paper::Case>>,t: paper::Trace,outcome: paper::Outcome)
    requires inclusion::satisfiable(d,start.constraint),
        paper::trace_wf(d,start.constraint,start.state,archive_cases(archive),t),
        paper::trace_steps_ok(d,archive_cases(archive),t),paper::trace_outcome(t,outcome),
    ensures forall|r: Regex<model::Test>,s: Regex<model::Test>| paper::initial_ok(start.state,r,s)
        ==> paper::outcome_ok(d,start.constraint,r,s,outcome),
{
    assert forall|r: Regex<model::Test>,s: Regex<model::Test>| paper::initial_ok(start.state,r,s) implies
        paper::outcome_ok(d,start.constraint,r,s,outcome) by {
        paper::lemma_search_correct(d,start.constraint,r,s,start.state,archive_cases(archive),t,outcome);
    }
}

pub(crate) proof fn theorem_retained_search_bounded(d: encoding::NDomains,
    archive: Map<paper::Item,Set<paper::Case>>,start: paper::Item)
    requires finite_impl::regex_nf(start.state),archive_follows(archive),
        finiteness::cases_from_atoms(d,archive_cases(archive),|q: Regex<model::Test>| symbolic::regex_primitives(q)),
    ensures paper::finitely_many_items(archive_cases(archive),start),
        exists|bound: nat| #[trigger] paper::traces_bounded(start.constraint,start.state,archive_cases(archive),bound),
{
    implementation::theorem_impl_search_bounded(d,archive_cases(archive),
        |q: Regex<model::Test>| symbolic::regex_primitives(q),start.constraint,start.state);
}

pub(crate) open spec fn letter_numeric_codes(v: Seq<Set<nat>>,u: Universes,
    l: implementation::LetterView,atoms: Set<model::Primitive>) -> bool {
    &&& 1 <= v.len() <= history_syntax::MAX_ARITY
    &&& v.len() == u@.len() && l.classes.len() == v.len() && l.registers.len() == v.len()
    &&& paper::atoms_bounded(atoms,v.len())
    &&& forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_class(l,c)]
        c.0 < v.len() ==> match implementation::letter_class(l,c) {
            None => encoding::n_domain(ndomains(u),c) is None,
            Some(implementation::ClassView::Register) => true,
            Some(implementation::ClassView::Constant(code)) => v[crate::verify::component_index(c) as int].contains(code)
                && match encoding::n_domain(ndomains(u),c) { Some(ds) => ds.contains(code),None => true },
        }
    &&& forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_register(l,c)]
        c.0 < v.len() ==> (implementation::letter_register(l,c) matches implementation::ClassView::Constant(code)
            ==> v[crate::verify::component_index(c) as int].contains(code))
    &&& forall|p: model::Primitive| atoms.contains(p) ==> match p {
        model::Primitive::Eq(c,model::GTerm::Constant(code)) => v[crate::verify::component_index(c) as int].contains(code),
        _ => true,
    }
}

pub(crate) proof fn lemma_letter_payload<E: history_syntax::Event>(constants: crate::analyzer::Constants<E>,
    v: Seq<Set<nat>>,u: Universes,l: implementation::LetterView,atoms: Set<model::Primitive>)
    requires letter_numeric_codes(v,u,l,atoms),
        v.len() == history_syntax::event::specs::arity::<E>(),
        forall|c: history_syntax::syntax::Component,code: nat| c.0 < v.len()
            && v[crate::verify::component_index(c) as int].contains(code)
            ==> crate::verify::reconstruction::code_field(constants,c,code),
    ensures crate::verify::reconstruction::letter_codes_ok(constants,ndomains(u),l,atoms),
{}

pub(crate) open spec fn atom_valid(p: junco_core::kernel::Primitive) -> bool {
    match p { junco_core::kernel::Primitive::Eq { field,term } => match term {
        junco_core::kernel::Term::Constant(code) => code <= u32::MAX as u64,
        junco_core::kernel::Term::Variable(component) => component == field,
    } }
}

pub(crate) open spec fn trace(s: Search<'_>, expanded: nat) -> paper::Trace {
    paper::Trace { nodes: impl_nodes(facade::graph(*s.language),s.constraints@,s.items@,
        s.alphabets@), expanded }
}

#[verifier::opaque]
pub(crate) open spec fn vocabulary_wf(s: Search<'_>, v: Seq<Set<nat>>) -> bool {
    &&& 1 <= v.len() <= history_syntax::MAX_ARITY && v.len() == s.universes@.len()
    &&& crate::verify::constraint_unique::universes_distinct(*s.universes)
    &&& forall|k: int| 0 <= k < v.len() ==> domain_values(s.universes[k]).subset_of(v[k])
    &&& forall|k: int| #![trigger s.constraints@[k]] 0 <= k < s.constraints@.len()
        ==> constraint_in_vocabulary(s.constraints@[k],v)
    &&& forall|j: int| #![trigger s.items@[j]] 0 <= j < s.items@.len() ==> {
        let q = s.items@[j].residual;
        finite_impl::regex_nf(facade::abs(*s.language,q))
            && (facade::primitives_search_safe(symbolic::regex_primitives(s.start@.state))
                ==> facade::residual_search_safe(*s.language,q))
            && paper::atoms_bounded(facade::residual_primitives(*s.language,q),v.len())
            && forall|c: history_syntax::syntax::Component| c.0 < v.len() ==>
                facade::residual_codes(*s.language,q,c).subset_of(v[crate::verify::component_index(c) as int])
    }
}

#[verifier::opaque]
pub(crate) open spec fn running(s: Search<'_>, expanded: nat, start: paper::Item,
    v: Seq<Set<nat>>) -> bool {
    &&& state_wf(s) && queue_order(s) && vocabulary_wf(s,v) && edges_wf(s)
    &&& inclusion::satisfiable(ndomains(*s.universes),start.constraint)
    &&& finite_impl::regex_nf(start.state)
    &&& partial_trace_wf(ndomains(*s.universes),start,archive_cases(s.archive@),trace(s,expanded),false)
    &&& paper::trace_steps_ok(ndomains(*s.universes),archive_cases(s.archive@),trace(s,expanded))
    &&& archive_follows(s.archive@)
    &&& archive_within(s.archive@,trace(s,expanded).nodes,expanded)
    &&& finiteness::cases_from_atoms(ndomains(*s.universes),archive_cases(s.archive@),
        |q: Regex<model::Test>| symbolic::regex_primitives(q))
    &&& forall|j: int| #![trigger s.items@[j]] expanded <= j < s.items@.len()
        ==> !s.archive@.dom().contains(impl_item(facade::graph(*s.language),s.constraints@,s.items@[j]))
    &&& (expanded < s.items@.len() ==> {
        let level = depth(s.items@,expanded as int)+1;
        seen_depth_bounded(s,level)
            && (forall|j: int| 0 <= j < s.items@.len() ==> depth(s.items@,j) <= level)
    })
}

pub(crate) proof fn lemma_state_frame(a: Search<'_>,b: Search<'_>)
    requires state_wf(a),facade::language_wf(*b.language),facade::frame(*a.language,*b.language),
        table_wf(b.constraints),a.constraints@.is_prefix_of(b.constraints@),
        a.items@ == b.items@,a.alphabets@ == b.alphabets@,*a.universes == *b.universes,
        a.seen == b.seen,a.seen_records@ == b.seen_records@,
        forall|i: int| 0 <= i < b.constraints@.len() ==> b.constraints@[i].len() == b.universes@.len(),
        a.antichain == b.antichain,a.simulation == b.simulation,
    ensures state_wf(b), trace(a,0).nodes == trace(b,0).nodes,
{
    facade::lemma_language_wf(*a.language);
    model::lemma_graph_wf_elim(facade::graph(*a.language));
    lemma_nodes_frame(facade::graph(*a.language),facade::graph(*b.language),a.constraints@,
        b.constraints@,a.items@,a.alphabets@);
    crate::verify::simulation_exec::lemma_memo_frame(a.simulation,*a.language,*b.language);
    crate::verify::prune_exec::lemma_antichain_frame(a.antichain,facade::graph(*a.language),
        facade::graph(*b.language),a.constraints,b.constraints,trace(a,0).nodes);
    assert forall|j: int| #![trigger b.seen_records@[j]] 0 <= j < b.seen_records@.len() implies {
        let record = b.seen_records@[j];
        record.0 < b.constraints@.len() && record.1@ < facade::graph(*b.language).regexes.len()
            && paper::may_discard(ndomains(*b.universes),trace(b,0).nodes,
                paper::Item { constraint: implementation::constraint_of(b.constraints@[record.0 as int]),
                    state: model::lift_regex(facade::graph(*b.language),record.1@) },record.2)
    } by {
        model::lemma_lift_regex_stable(facade::graph(*a.language),facade::graph(*b.language),
            b.seen_records@[j].1@);
    }
}

pub(crate) proof fn lemma_archive_atoms_add(d: encoding::NDomains,
    archive: Map<paper::Item,Set<paper::Case>>,item: paper::Item,cases: Set<paper::Case>)
    requires finiteness::cases_from_atoms(d,archive_cases(archive),
        |q: Regex<model::Test>| symbolic::regex_primitives(q)),
        forall|c: paper::Case,l: inclusion::Literal| cases.contains(c) && c.constraint.contains(l)
            ==> item.constraint.contains(l) || finiteness::atom_codes(symbolic::regex_primitives(item.state)).contains(l.value)
                || match encoding::n_domain(d,l.component) { Some(vs) => vs.contains(l.value),None => false },
    ensures finiteness::cases_from_atoms(d,archive_cases(archive.insert(item,cases)),
        |q: Regex<model::Test>| symbolic::regex_primitives(q)),
{
    assert forall|i: paper::Item,c: paper::Case,l: inclusion::Literal|
        archive_cases(archive.insert(item,cases))(i).contains(c) && c.constraint.contains(l) implies
        i.constraint.contains(l) || finiteness::atom_codes(symbolic::regex_primitives(i.state)).contains(l.value)
            || match encoding::n_domain(d,l.component) { Some(vs) => vs.contains(l.value),None => false } by {
        if i != item { assert(archive_cases(archive)(i).contains(c)); }
    }
}

pub(crate) proof fn lemma_running_outcome(s: Search<'_>, expanded: nat,start: paper::Item,
    v: Seq<Set<nat>>, outcome: paper::Outcome)
    requires running(s,expanded,start,v),paper::trace_outcome(trace(s,expanded),outcome),
    ensures paper::trace_wf(ndomains(*s.universes),start.constraint,start.state,
            archive_cases(s.archive@),trace(s,expanded)),
        paper::finitely_many_items(archive_cases(s.archive@),start),
        exists|bound: nat| paper::traces_bounded(start.constraint,start.state,archive_cases(s.archive@),bound),
        forall|r: Regex<model::Test>,t: Regex<model::Test>| paper::initial_ok(start.state,r,t)
            ==> paper::outcome_ok(ndomains(*s.universes),start.constraint,r,t,outcome),
{
    reveal(running);
    lemma_partial_trace_complete(ndomains(*s.universes),start,archive_cases(s.archive@),trace(s,expanded));
    lemma_trace_query_ok(ndomains(*s.universes),start,s.archive@,trace(s,expanded),outcome);
    theorem_retained_search_bounded(ndomains(*s.universes),s.archive@,start);
}


pub(crate) proof fn lemma_refined_vocabulary(g: crate::constraint::Constraint,operands: crate::constraint::Operands,
    u: Universes,v: Seq<Set<nat>>,target: implementation::ConstraintView)
    requires crate::verify::split_views(g,operands,u).contains(target),constraint_in_vocabulary(g@,v),
        crate::verify::shape_wf(g,operands,u),
        forall|k: int| 0 <= k < v.len() ==> crate::verify::codes(operands.constants[k].view()).subset_of(v[k])
            && domain_values(u[k]).subset_of(v[k]),
    ensures constraint_in_vocabulary(target,v),
{
    crate::verify::lemma_register_product_members(crate::verify::split_axes(g,operands,u));
    assert forall|k: int| 0 <= k < target.len() implies register_in_vocabulary(target[k],v[k]) by {
        lemma_option_vocabulary(g@[k],target[k],operands.register[k],
            crate::verify::codes(operands.constants[k].view()),crate::verify::domain_view(u[k]),v[k]);
    }
}


pub(crate) proof fn lemma_operand_vocabulary(operands: crate::constraint::Operands,atoms: Seq<Atom>,v: Seq<Set<nat>>)
    requires crate::verify::operands_of(operands,atoms),atoms_in_vocabulary(atoms,v),operands.register@.len() == v.len(),
    ensures forall|k: int| 0 <= k < v.len() ==> crate::verify::codes(operands.constants[k].view()).subset_of(v[k])
        && operands.constants[k].view().no_duplicates(),
{
    assert forall|k: int| 0 <= k < v.len() implies crate::verify::codes(operands.constants[k].view()).subset_of(v[k])
        && operands.constants[k].view().no_duplicates() by {
        assert forall|code: nat| crate::verify::codes(operands.constants[k].view()).contains(code) implies v[k].contains(code) by {
            let raw = choose|raw: u32| operands.constants[k].view().to_set().contains(raw) && raw as nat == code;
            let i = choose|i: int| 0 <= i < atoms.len() && atoms[i].component == k
                && atoms[i].operand == crate::constraint::Operand::Constant(raw);
        }
        assert forall|i: int,j: int| 0 <= i < j < operands.constants[k].view().len() implies
            operands.constants[k].view()[i] != operands.constants[k].view()[j] by {}
    }
}


#[verifier::opaque]
pub(crate) open spec fn search_result(d: encoding::NDomains,start: paper::Item,outcome: paper::Outcome) -> bool {
    &&& forall|r: Regex<model::Test>,s: Regex<model::Test>| paper::initial_ok(start.state,r,s)
        ==> paper::outcome_ok(d,start.constraint,r,s,outcome)
    &&& exists|archive: Map<paper::Item,Set<paper::Case>>,t: paper::Trace|
        paper::trace_wf(d,start.constraint,start.state,archive_cases(archive),t)
            && paper::trace_steps_ok(d,archive_cases(archive),t) && paper::trace_outcome(t,outcome)
            && archive_follows(archive)
            && finiteness::cases_from_atoms(d,archive_cases(archive),|q: Regex<model::Test>| symbolic::regex_primitives(q))
            && paper::finitely_many_items(archive_cases(archive),start)
            && (exists|bound: nat| paper::traces_bounded(start.constraint,start.state,archive_cases(archive),bound))
}

#[verifier::rlimit(20)]
pub(crate) proof fn lemma_search_result(s: Search<'_>,expanded: nat,start: paper::Item,v: Seq<Set<nat>>,
    outcome: paper::Outcome)
    requires running(s,expanded,start,v),paper::trace_outcome(trace(s,expanded),outcome),
    ensures search_result(ndomains(*s.universes),start,outcome),
{
    hide(paper::outcome_ok); hide(paper::initial_ok); hide(paper::trace_wf);
    hide(paper::trace_steps_ok); hide(paper::trace_outcome); hide(paper::finitely_many_items);
    hide(paper::traces_bounded); hide(finiteness::cases_from_atoms); hide(archive_follows);
    reveal(search_result);
    lemma_running_evidence(s,expanded,start,v);
    lemma_running_outcome(s,expanded,start,v,outcome);
    let archive = s.archive@; let t = trace(s,expanded);
    assert(paper::trace_wf(ndomains(*s.universes),start.constraint,start.state,archive_cases(archive),t));
}

#[verifier::opaque]
pub(crate) open spec fn expansion_state(s: Search<'_>,index: nat,records: Seq<Emission>) -> bool {
    &&& state_wf(s) && queue_order(s) && vocabulary_wf(s,s.vocabulary@) && edges_wf(s)
    &&& index < s.items@.len()
    &&& inclusion::satisfiable(ndomains(*s.universes),s.start@.constraint)
    &&& finite_impl::regex_nf(s.start@.state)
    &&& partial_trace_wf(ndomains(*s.universes),s.start@,archive_cases(s.archive@),trace(s,index),true)
    &&& paper::trace_steps_ok(ndomains(*s.universes),archive_cases(s.archive@),trace(s,index))
    &&& archive_follows(s.archive@)
    &&& archive_within(s.archive@,trace(s,index).nodes,index+1)
    &&& finiteness::cases_from_atoms(ndomains(*s.universes),archive_cases(s.archive@),
        |q: Regex<model::Test>| symbolic::regex_primitives(q))
    &&& archive_cases(s.archive@)(trace(s,index).nodes[index as int].item) == emitted_cases(records)
    &&& forall|j: int| #![trigger s.items@[j]] index < j < s.items@.len()
        ==> !s.archive@.dom().contains(impl_item(facade::graph(*s.language),s.constraints@,s.items@[j]))
    &&& seen_depth_bounded(s,depth(s.items@,index as int)+1)
    &&& forall|j: int| 0 <= j < s.items@.len() ==> depth(s.items@,j) <= depth(s.items@,index as int)+1
}

pub(crate) proof fn lemma_vocabulary_frame(a: Search<'_>,b: Search<'_>,v: Seq<Set<nat>>)
    requires vocabulary_wf(a,v),facade::language_wf(*a.language),facade::language_wf(*b.language),
        facade::frame(*a.language,*b.language),a.items@ == b.items@,a.constraints@ == b.constraints@,
        a.start@ == b.start@,
        *a.universes == *b.universes,ids_valid(facade::graph(*a.language),a.constraints@,a.items@),
    ensures vocabulary_wf(b,v),
{
    reveal(vocabulary_wf);
    facade::lemma_language_wf(*a.language);
    model::lemma_graph_wf_elim(facade::graph(*a.language));
    assert forall|j: int| #![trigger b.items@[j]] 0 <= j < b.items@.len() implies {
        let q = b.items@[j].residual;
        finite_impl::regex_nf(facade::abs(*b.language,q))
            && (facade::primitives_search_safe(symbolic::regex_primitives(b.start@.state))
                ==> facade::residual_search_safe(*b.language,q))
            && paper::atoms_bounded(facade::residual_primitives(*b.language,q),v.len())
            && forall|c: history_syntax::syntax::Component| c.0 < v.len() ==>
                facade::residual_codes(*b.language,q,c).subset_of(v[crate::verify::component_index(c) as int])
    } by {
        facade::lemma_residual_vocabulary_frame(*a.language,*b.language,b.items@[j].residual);
        model::lemma_lift_regex_stable(facade::graph(*a.language),facade::graph(*b.language),b.items@[j].residual@);
    }
}

pub(crate) proof fn lemma_expansion_end(s: Search<'_>,index: nat,records: Seq<Emission>)
    requires expansion_state(s,index,records),
        paper::steps_ok(ndomains(*s.universes),trace(s,index).nodes[index as int].item,
            archive_cases(s.archive@)(trace(s,index).nodes[index as int].item)),
    ensures running(s,index+1,s.start@,s.vocabulary@),
{
    reveal(expansion_state); reveal(running);
    lemma_partial_end(ndomains(*s.universes),s.start@,archive_cases(s.archive@),trace(s,index));
    assert forall|p: int| 0 <= p < index+1 implies #[trigger] paper::steps_ok(ndomains(*s.universes),
        trace(s,index+1).nodes[p].item,archive_cases(s.archive@)(trace(s,index+1).nodes[p].item)) by {}
}

pub(crate) proof fn lemma_emitted_push(before: Seq<Emission>,after: Seq<Emission>,c: paper::Case)
    requires after == before.push(Emission { group:after.last().group,letter:after.last().letter,case:c }),
    ensures emitted_cases(after) == emitted_cases(before).insert(c),
{
    reveal(emitted_cases);
    before.lemma_push_to_set_commute(after.last());
    before.to_set().lemma_set_map_insert_commute(after.last(),|record: Emission| record.case);
}

pub(crate) proof fn lemma_enumeration_push(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    atoms: Seq<Atom>,records: Seq<Emission>,record: Emission)
    requires enumeration_prefix(groups,atoms,records,record.group,record.letter),
        emitted_valid(groups,atoms,record),
    ensures enumeration_prefix(groups,atoms,records.push(record),record.group,record.letter+1),
{
    reveal(coordinate);
    assert forall|b: int,j: int| #[trigger] coordinate(groups,b,j)
        && (b < record.group || b == record.group && j < record.letter+1)
        implies exists|n: int| 0 <= n < records.push(record).len()
            && records.push(record)[n].group == b && records.push(record)[n].letter == j by {
        if b == record.group && j == record.letter {
            assert(records.push(record)[records.len() as int] == record);
        } else {
            let n = choose|n: int| 0 <= n < records.len() && records[n].group == b && records[n].letter == j;
            assert(records.push(record)[n] == records[n]);
        }
    }
}

pub(crate) proof fn lemma_enumeration_advance(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,
    atoms: Seq<Atom>,records: Seq<Emission>,b: int)
    requires 0 <= b < groups.len(),enumeration_prefix(groups,atoms,records,b,groups[b].1@.len() as int),
    ensures enumeration_prefix(groups,atoms,records,b+1,0),
{
    reveal(coordinate);
    assert forall|g: int,j: int| #[trigger] coordinate(groups,g,j) && (g < b+1 || g == b+1 && j < 0)
        implies exists|n: int| 0 <= n < records.len() && records[n].group == g && records[n].letter == j by {
        assert(g < b || g == b && j < groups[b].1@.len());
    }
}

pub(crate) proof fn lemma_atoms_vocabulary(atoms: Seq<Atom>,ps: Set<model::Primitive>,v: Seq<Set<nat>>)
    requires atoms_wf(atoms,v.len()),atom_set(atoms).subset_of(ps),paper::atoms_bounded(ps,v.len()),
        forall|c: history_syntax::syntax::Component| c.0 < v.len() ==>
            facade::primitive_codes(ps,c).subset_of(v[crate::verify::component_index(c) as int]),
    ensures atoms_in_vocabulary(atoms,v),
{
    assert forall|i: int| #![trigger atoms[i]] 0 <= i < atoms.len() implies atoms[i].component < v.len()
        && match atoms[i].operand { crate::constraint::Operand::Constant(code) =>
            v[atoms[i].component as int].contains(code as nat),_ => true } by {
        assert(atoms.to_set().contains(atoms[i]));
        assert(atom_set(atoms).contains(atoms[i]@));
        if let crate::constraint::Operand::Constant(code) = atoms[i].operand {
            let c = crate::verify::component_at(atoms[i].component);
            assert(atoms.to_set().contains(atoms[i]));
            assert(atom_set(atoms).contains(atoms[i]@));
            facade::lemma_primitive_codes_contains(ps,c,code as nat);
            assert(crate::verify::component_index(c) == atoms[i].component);
        }
    }
}

pub(crate) proof fn lemma_group_vocabulary(g: crate::constraint::Constraint,atoms: Seq<Atom>,u: Universes,
    groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,v: Seq<Set<nat>>)
    requires crate::verify::steps_result(g,atoms,u,groups),constraint_in_vocabulary(g@,v),
        atoms_in_vocabulary(atoms,v),forall|k: int| 0 <= k < v.len() ==> domain_values(u[k]).subset_of(v[k]),
    ensures forall|b: int| 0 <= b < groups.len() ==> constraint_in_vocabulary(groups[b].0@,v),
{
    let o = choose|o: crate::constraint::Operands| crate::verify::operands_of(o,atoms)
        && crate::verify::shape_wf(g,o,u)
        && crate::verify::constraint_views(crate::verify::group_constraints(groups)) == crate::verify::split_views(g,o,u)
        && forall|b: int| 0 <= b < groups.len() ==> crate::verify::constraint_wf(groups[b].0)
            && groups[b].0@.len() == u@.len()
            && crate::verify::letter_views(groups[b].1@) == crate::verify::letters_views(groups[b].0,o,u);
    lemma_operand_vocabulary(o,atoms,v);
    crate::verify::lemma_group_constraints(groups);
    assert forall|b: int| 0 <= b < groups.len() implies constraint_in_vocabulary(groups[b].0@,v) by {
        crate::verify::lemma_constraint_view_at(crate::verify::group_constraints(groups),b);
        lemma_refined_vocabulary(g,o,u,v,groups[b].0@);
    }
}

pub(crate) proof fn lemma_derivative_frame(a: SymbolicLanguage,b: SymbolicLanguage,q: RegexId,t: junco_core::kernel::TransitionId,
    atoms: Seq<Atom>)
    requires facade::language_wf(a),facade::language_wf(b),facade::frame(a,b),facade::has_atoms(a,t),
        facade::has_atoms(b,t),facade::atom_ids(a,t) == facade::atom_ids(b,t),
        symbolic::derivative_correct(facade::graph(a),q@,t),
        history_semantics::verify::finite_deriv::dbound(facade::graph(a),q@,t@),
        facade::atom_ids(a,t).len() == atoms.len(),
        forall|i: int| 0 <= i < atoms.len() ==> model::lift_test(facade::graph(a),facade::atom_ids(a,t)[i]@) == model::Test::Atom(atoms[i]@,true),
    ensures symbolic::derivative_correct(facade::graph(b),q@,t),
        history_semantics::verify::finite_deriv::dbound(facade::graph(b),q@,t@),
        facade::atom_ids(b,t).len() == atoms.len(),
        forall|i: int| 0 <= i < atoms.len() ==> model::lift_test(facade::graph(b),facade::atom_ids(b,t)[i]@) == model::Test::Atom(atoms[i]@,true),
{
    facade::lemma_language_wf(a);model::lemma_graph_wf_elim(facade::graph(a));
    symbolic::derivative_extends(facade::graph(a),facade::graph(b));
    history_semantics::verify::finite_deriv::lemma_dbound_stable(facade::graph(a),facade::graph(b),q@,t@);
    assert forall|i: int| 0 <= i < atoms.len() implies
        model::lift_test(facade::graph(b),facade::atom_ids(b,t)[i]@) == model::Test::Atom(atoms[i]@,true) by {
        model::lemma_lift_test_stable(facade::graph(a),facade::graph(b),facade::atom_ids(a,t)[i]@);
    }
}

pub(crate) proof fn lemma_resolved_successor(l: SymbolicLanguage,q: RegexId,t: junco_core::kernel::TransitionId,v: RegexId,
    atoms: Seq<Atom>,letter: Letter,words: Seq<u64>)
    requires facade::language_wf(l),symbolic::derivative_correct(facade::graph(l),q@,t),
        truth_bits(atoms,letter,words),facade::atom_ids(l,t).len() == atoms.len(),
        forall|i: int| 0 <= i < atoms.len() ==> model::lift_test(facade::graph(l),facade::atom_ids(l,t)[i]@) == model::Test::Atom(atoms[i]@,true),
        forall|theta: Subst,e: EventView,w: Seq<EventView>| language::event_wf(theta,theta.len())
            && symbolic::truth_words_realize(facade::graph(l),facade::atom_ids(l,t),words,theta,e)
                ==> model::regex_lang(facade::graph(l),theta,v@,w)
                    == history_semantics::normalize_verify::transition_lang(facade::graph(l),theta,t,e,w),
    ensures paper::successor_ok(facade::abs(l,q),implementation::letter_assignment(letter@,atom_set(atoms)),facade::abs(l,v)),
{
    hide(language::lang);hide(history_semantics::normalize_verify::transition_lang);
    lemma_truth_realizes(facade::graph(l),facade::atom_ids(l,t),atoms,letter,words);
    assert forall|theta: Subst,e: EventView,w: Seq<EventView>| language::event_wf(theta,theta.len())
        && paper::realizes(theta,e,implementation::letter_assignment(letter@,atom_set(atoms))) implies
        encoding::n_lang(theta,facade::abs(l,v),w) == encoding::n_lang(theta,facade::abs(l,q),seq![e]+w) by {
        assert(symbolic::truth_words_realize(facade::graph(l),facade::atom_ids(l,t),words,theta,e));
        assert(model::regex_lang(facade::graph(l),theta,v@,w)
            == history_semantics::normalize_verify::transition_lang(facade::graph(l),theta,t,e,w));
        assert(history_semantics::normalize_verify::transition_lang(facade::graph(l),theta,t,e,w)
            == model::regex_lang(facade::graph(l),theta,q@,seq![e]+w));
    }
}

pub(crate) open spec fn refutation_packed(outcome: crate::search::SearchOutcome) -> bool {
    match outcome {
        crate::search::SearchOutcome::Holds => true,
        crate::search::SearchOutcome::Refuted(r) => r.letters@.len() == r.alphabets@.len()
            && r.assignments@ == chain_assignments(r.letters@,r.alphabets@),
    }
}

pub(crate) open spec fn edge_ready(s: Search<'_>,constraint: ConstraintId,parent: Option<(usize,Letter)>) -> bool {
    match parent {
        None => true,
        Some((p,l)) => p < s.items@.len() && constraint < s.constraints@.len()
            && s.alphabets@.dom().contains(p as nat)
            && syntactic_entails(s.constraints@[constraint as int],s.constraints@[s.items@[p as int].constraint as int])
            && crate::verify::reconstruction::letter_coherent(s.constraints@[constraint as int],l@,s.alphabets@[p as nat])
            && letter_numeric_codes(s.vocabulary@,*s.universes,l@,s.alphabets@[p as nat]),
    }
}

#[verifier::opaque]
pub(crate) open spec fn edges_wf(s: Search<'_>) -> bool {
    forall|j: int| #![trigger s.items@[j]] 0 <= j < s.items@.len()
        ==> edge_ready(s,s.items@[j].constraint,s.items@[j].parent)
}

pub(crate) proof fn lemma_edges_insert(a: Search<'_>,b: Search<'_>,it: Item)
    requires edges_wf(a),edge_ready(a,it.constraint,it.parent),
        b.items@ == a.items@ || b.items@ == a.items@.push(it),a.constraints@ == b.constraints@,
        a.alphabets@ == b.alphabets@,a.vocabulary@ == b.vocabulary@,*a.universes == *b.universes,
    ensures edges_wf(b),
{
    reveal(edges_wf);
    assert forall|j: int| #![trigger b.items@[j]] 0 <= j < b.items@.len()
        implies edge_ready(b,b.items@[j].constraint,b.items@[j].parent) by {
        if j < a.items@.len() {
            if let Some((p,_)) = a.items@[j].parent { assert(b.items@[p as int] == a.items@[p as int]); }
        } else {
            if let Some((p,_)) = it.parent { assert(b.items@[p as int] == a.items@[p as int]); }
        }
    }
}

pub(crate) proof fn lemma_option_strengthens(source: implementation::RegisterView,target: implementation::RegisterView,
    register: bool,constants: Set<nat>,domain: Option<Set<nat>>)
    requires crate::verify::register_options(source,register,constants,domain).contains(target),
    ensures crate::verify::register_entails(target,source),
{
    crate::verify::lemma_register_options_members(source,register,constants,domain,target);
    match source { implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {
        match target { implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {} }
    } }
}

pub(crate) proof fn lemma_refined_strengthens(g: crate::constraint::Constraint,o: crate::constraint::Operands,
    u: Universes,target: implementation::ConstraintView)
    requires crate::verify::split_views(g,o,u).contains(target),
        crate::verify::shape_wf(g,o,u),
    ensures syntactic_entails(target,g@),
{
    crate::verify::lemma_register_product_members(crate::verify::split_axes(g,o,u));
    assert forall|k: int| 0 <= k < target.len() implies crate::verify::register_entails(target[k],g@[k]) by {
        lemma_option_strengthens(g@[k],target[k],o.register[k],
            crate::verify::codes(o.constants[k].view()),crate::verify::domain_view(u[k]));
    }
}

pub(crate) proof fn lemma_numeric_letter(g: crate::constraint::Constraint,o: crate::constraint::Operands,
    atoms: Seq<Atom>,u: Universes,v: Seq<Set<nat>>,l: implementation::LetterView)
    requires crate::verify::operands_of(o,atoms),atoms_in_vocabulary(atoms,v),atoms_wf(atoms,u@.len()),
        constraint_in_vocabulary(g@,v),crate::verify::letters_views(g,o,u).contains(l),
        inclusion::satisfiable(ndomains(u),implementation::constraint_of(g@)),
        crate::verify::shape_wf(g,o,u),
        forall|k: int| 0 <= k < v.len() ==> domain_values(u[k]).subset_of(v[k]),
    ensures letter_numeric_codes(v,u,l,atom_set(atoms)),
{
    lemma_operand_vocabulary(o,atoms,v);
    crate::verify::lemma_letters_members(g,o,u);
    assert forall|i: int| 0 <= i < g@.len() implies
        crate::verify::class_options(g.0[i]@,o.register[i],crate::verify::codes(o.constants[i].view()),u[i]).contains(l.classes[i])
            && l.registers[i] == crate::verify::register_class(g.0[i]@) by {}
    let theta = choose|theta: Subst| encoding::n_theta_ok(ndomains(u),theta)
        && inclusion::sat_by(theta,implementation::constraint_of(g@));
    crate::verify::lemma_constraint_sat(g@,theta);crate::verify::lemma_theta_allowed(u,theta);
    assert forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_class(l,c)]
        c.0 < v.len() implies match implementation::letter_class(l,c) {
            None => encoding::n_domain(ndomains(u),c) is None,
            Some(implementation::ClassView::Register) => true,
            Some(implementation::ClassView::Constant(code)) => v[crate::verify::component_index(c) as int].contains(code)
                && match encoding::n_domain(ndomains(u),c) { Some(ds) => ds.contains(code),None => true },
        } by {
        let k = crate::verify::component_index(c) as int;
        let r = implementation::register_of(g@,c);
        let constants = crate::verify::codes(o.constants[k].view());
        let names = crate::verify::named_codes(r,o.register[k],constants,crate::verify::domain_view(u[k]));
        assert(0 <= k < g@.len() && k < u@.len());
        assert(r == g.0[k]@ && implementation::letter_class(l,c) == l.classes[k]);
        assert(l.registers[k] == crate::verify::register_class(g.0[k]@));
        assert(crate::verify::class_options(g.0[k]@,o.register[k],crate::verify::codes(o.constants[k].view()),u[k]).contains(l.classes[k]));
        assert(crate::verify::class_options(r,o.register[k],constants,u[k]).contains(implementation::letter_class(l,c)));
        assert(register_in_vocabulary(r,v[k]));
        assert(constants.subset_of(v[k]));
        assert(crate::verify::register_sat(r,theta[k]));
        assert(crate::verify::register_allowed(crate::verify::domain_view(u[k]),theta[k]));
        assert forall|code: nat| names.contains(code) implies v[k].contains(code) by {
            match r {
                implementation::RegisterView::Equals(value) => {},
                implementation::RegisterView::Differs(_) => {},
            }
        }
        if let Some(ids) = u[k] {
            assert forall|code: nat| names.contains(code) implies crate::verify::codes((*ids)@).contains(code) by {
                match r {
                    implementation::RegisterView::Equals(value) => {
                        assert(theta[k] == value);
                    },
                    implementation::RegisterView::Differs(_) => {},
                }
            }
        }
        crate::verify::lemma_class_options_members(r,o.register[k],constants,u[k],implementation::letter_class(l,c));
        match implementation::letter_class(l,c) {
            None => {},Some(implementation::ClassView::Register) => {},
            Some(implementation::ClassView::Constant(code)) => {
                if let Some(ids) = u[k] {
                    crate::verify::lemma_first_other((*ids)@,names);
                    if !names.contains(code) {
                        assert(crate::verify::first_other((*ids)@,names) matches Some(w) && w as nat == code);
                        assert(crate::verify::first_other_index((*ids)@,names) is Some);
                        let j = crate::verify::first_other_index((*ids)@,names)->Some_0;
                        assert(0 <= j < (*ids)@.len());
                        assert((*ids)@[j] as nat == code);
                        assert((*ids)@.to_set().contains((*ids)@[j]));
                        assert(crate::verify::codes((*ids)@).contains(code));
                        assert(domain_values(u[k]).contains(code));
                    }
                }
                match r { implementation::RegisterView::Equals(value) => {
                    assert(crate::verify::register_sat(r,language::field_value(theta,c)));
                    assert(crate::verify::register_allowed(crate::verify::domain_view(u[k]),language::field_value(theta,c)));
                },implementation::RegisterView::Differs(_) => {} }
            },
        }
    }
    assert forall|c: history_syntax::syntax::Component| #![trigger implementation::letter_register(l,c)]
        c.0 < v.len() implies match implementation::letter_register(l,c) {
            implementation::ClassView::Constant(code) => v[crate::verify::component_index(c) as int].contains(code),
            implementation::ClassView::Register => true,
        } by {
        match implementation::register_of(g@,c) {
            implementation::RegisterView::Equals(_) => {},implementation::RegisterView::Differs(_) => {},
        }
    }
    assert forall|p: model::Primitive| atom_set(atoms).contains(p) implies match p {
        model::Primitive::Eq(c,model::GTerm::Constant(code)) => v[crate::verify::component_index(c) as int].contains(code),
        _ => true,
    } by {
        let a = choose|a: Atom| atoms.to_set().contains(a) && a@ == p;
        let i = choose|i: int| 0 <= i < atoms.len() && atoms[i] == a;
    }
    assert forall|p: model::Primitive| atom_set(atoms).contains(p) implies match p {
        model::Primitive::Eq(c,model::GTerm::Constant(_)) => c.0 < v.len(),
        model::Primitive::Eq(c,model::GTerm::Variable(r)) => c.0 < v.len() && r.0 < v.len(),
    } by {
        let a = choose|a: Atom| atoms.to_set().contains(a) && a@ == p;
        let i = choose|i: int| 0 <= i < atoms.len() && atoms[i] == a;
    }
}

pub(crate) proof fn lemma_generated_edge(g: crate::constraint::Constraint,atoms: Seq<Atom>,u: Universes,
    groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,v: Seq<Set<nat>>,b: int,j: int)
    requires crate::verify::steps_result(g,atoms,u,groups),atoms_wf(atoms,u@.len()),atoms_in_vocabulary(atoms,v),
        constraint_in_vocabulary(g@,v),0 <= b < groups.len(),0 <= j < groups[b].1@.len(),
        inclusion::satisfiable(ndomains(u),implementation::constraint_of(g@)),
        forall|k: int| 0 <= k < v.len() ==> domain_values(u[k]).subset_of(v[k]),
    ensures syntactic_entails(groups[b].0@,g@),
        crate::verify::reconstruction::letter_coherent(groups[b].0@,groups[b].1@[j]@,atom_set(atoms)),
        letter_numeric_codes(v,u,groups[b].1@[j]@,atom_set(atoms)),
{
    let o = choose|o: crate::constraint::Operands| crate::verify::operands_of(o,atoms)
        && crate::verify::shape_wf(g,o,u)
        && crate::verify::constraint_views(crate::verify::group_constraints(groups)) == crate::verify::split_views(g,o,u)
        && forall|b: int| 0 <= b < groups.len() ==> crate::verify::constraint_wf(groups[b].0)
            && groups[b].0@.len() == u@.len()
            && crate::verify::letter_views(groups[b].1@) == crate::verify::letters_views(groups[b].0,o,u);
    crate::verify::lemma_constraint_view_at(crate::verify::group_constraints(groups),b);
    crate::verify::lemma_group_constraints(groups);
    lemma_refined_strengthens(g,o,u,groups[b].0@);
    lemma_operand_vocabulary(o,atoms,v);lemma_refined_vocabulary(g,o,u,v,groups[b].0@);
    crate::verify::lemma_split_options_sound(g,o,u,groups[b].0@);
    crate::verify::lemma_refined_letters_ready(g,o,u,groups[b].0);
    assert(groups[b].1@.to_set().contains(groups[b].1@[j]));
    assert(crate::verify::letters_views(groups[b].0,o,u).contains(groups[b].1@[j]@));
    lemma_generated_letter_coherent(groups[b].0,o,atoms,u,groups[b].1@[j]@);
    lemma_numeric_letter(groups[b].0,o,atoms,u,v,groups[b].1@[j]@);
}

pub(crate) proof fn lemma_chain_ready(s: Search<'_>,j: int,final_constraint: implementation::ConstraintView)
    requires parents_wf(s.items@),ids_valid(facade::graph(*s.language),s.constraints@,s.items@),
        edges_wf(s),0 <= j < s.items@.len(),
        syntactic_entails(final_constraint,s.constraints@[s.items@[j].constraint as int]),
    ensures alphabet_chain(s.items@,s.alphabets@,j).len() == letter_chain(s.items@,j).len(),
        forall|k: int| 0 <= k < letter_chain(s.items@,j).len() ==>
            crate::verify::reconstruction::letter_coherent(final_constraint,letter_chain(s.items@,j)[k]@,
                alphabet_chain(s.items@,s.alphabets@,j)[k])
            && letter_numeric_codes(s.vocabulary@,*s.universes,letter_chain(s.items@,j)[k]@,
                alphabet_chain(s.items@,s.alphabets@,j)[k]),
    decreases j,
{
    reveal(edges_wf);
    if let Some((p,l)) = s.items@[j].parent {
        let gamma = s.constraints@[s.items@[j].constraint as int];
        let previous = s.constraints@[s.items@[p as int].constraint as int];
        lemma_syntactic_entails_trans(final_constraint,gamma,previous);
        lemma_chain_ready(s,p as int,final_constraint);
        lemma_letter_coherent_strengthen(final_constraint,gamma,l@,s.alphabets@[p as nat]);
        let letters = letter_chain(s.items@,p as int);
        let alphabets = alphabet_chain(s.items@,s.alphabets@,p as int);
        assert(letter_chain(s.items@,j) == letters.push(l));
        assert(alphabet_chain(s.items@,s.alphabets@,j) == alphabets.push(s.alphabets@[p as nat]));
        assert forall|k: int| 0 <= k < letter_chain(s.items@,j).len() implies
            crate::verify::reconstruction::letter_coherent(final_constraint,letter_chain(s.items@,j)[k]@,
                alphabet_chain(s.items@,s.alphabets@,j)[k])
            && letter_numeric_codes(s.vocabulary@,*s.universes,letter_chain(s.items@,j)[k]@,
                alphabet_chain(s.items@,s.alphabets@,j)[k]) by {
            if k < letters.len() { assert(letters.push(l)[k] == letters[k]); }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn refutation_ready(outcome: crate::search::SearchOutcome,u: Universes,v: Seq<Set<nat>>) -> bool {
    refutation_packed(outcome) && match outcome {
        crate::search::SearchOutcome::Holds => true,
        crate::search::SearchOutcome::Refuted(r) => crate::verify::constraint_wf(r.constraint)
            && constraint_in_vocabulary(r.constraint@,v)
            && r.constraint@.len() == u@.len()
            && (forall|k: int| #![trigger r.letters@[k]] 0 <= k < r.letters@.len() ==>
                crate::verify::reconstruction::letter_coherent(r.constraint@,r.letters@[k]@,r.alphabets@[k])
                    && letter_numeric_codes(v,u,r.letters@[k]@,r.alphabets@[k])),
    }
}

pub(crate) proof fn lemma_edges_frame(a: Search<'_>,b: Search<'_>)
    requires edges_wf(a),ids_valid(facade::graph(*a.language),a.constraints@,a.items@),
        a.items@ == b.items@,a.constraints@.is_prefix_of(b.constraints@),
        a.vocabulary@ == b.vocabulary@,*a.universes == *b.universes,
        forall|j: int| #![trigger a.items@[j]] 0 <= j < a.items@.len() ==> match a.items@[j].parent {
            None => true,Some((p,_)) => a.alphabets@.dom().contains(p as nat) == b.alphabets@.dom().contains(p as nat)
                && (a.alphabets@.dom().contains(p as nat) ==> a.alphabets@[p as nat] == b.alphabets@[p as nat]),
        },
    ensures edges_wf(b),
{
    reveal(edges_wf);
    assert forall|j: int| #![trigger b.items@[j]] 0 <= j < b.items@.len()
        implies edge_ready(b,b.items@[j].constraint,b.items@[j].parent) by {
        if let Some((p,l)) = a.items@[j].parent {
            assert(b.constraints@[b.items@[j].constraint as int] == a.constraints@[a.items@[j].constraint as int]);
            assert(b.constraints@[b.items@[p as int].constraint as int] == a.constraints@[a.items@[p as int].constraint as int]);
        }
    }
}

pub(crate) proof fn lemma_enumeration_empty(groups: Seq<(crate::constraint::Constraint,alloc::vec::Vec<Letter>)>,atoms: Seq<Atom>)
    ensures enumeration_prefix(groups,atoms,Seq::empty(),0,0),
{ reveal(coordinate); }

#[verifier::rlimit(20)]
pub(crate) proof fn lemma_expansion_language_frame(a: Search<'_>,b: Search<'_>,index: nat,records: Seq<Emission>)
    requires expansion_state(a,index,records),facade::language_wf(*b.language),facade::frame(*a.language,*b.language),
        a.constraints == b.constraints,a.items@ == b.items@,a.alphabets@ == b.alphabets@,
        a.archive@ == b.archive@,a.start@ == b.start@,a.vocabulary@ == b.vocabulary@,*a.universes == *b.universes,
        a.seen == b.seen,a.seen_records@ == b.seen_records@,a.antichain == b.antichain,a.simulation == b.simulation,
    ensures expansion_state(b,index,records),trace(a,index).nodes == trace(b,index).nodes,
{
    hide(paper::steps_ok);hide(paper::trace_steps_ok);hide(partial_trace_wf);hide(archive_follows);
    hide(finiteness::cases_from_atoms);hide(language::lang);
    hide(state_wf);hide(queue_order);hide(edges_wf);
    reveal(expansion_state);
    lemma_state_evidence(a);lemma_queue_frame(a,b);
    lemma_state_frame(a,b);lemma_vocabulary_frame(a,b,a.vocabulary@);lemma_edges_frame(a,b);
    assert(trace(a,index) == trace(b,index));
    assert forall|j: int| #![trigger b.items@[j]] 0 <= j < b.items@.len() implies
        impl_item(facade::graph(*a.language),a.constraints@,a.items@[j])
            == impl_item(facade::graph(*b.language),b.constraints@,b.items@[j]) by {
        assert(trace(a,index).nodes[j] == trace(b,index).nodes[j]);
    }
}

#[verifier::rlimit(20)]
pub(crate) proof fn lemma_expansion_table_frame(a: Search<'_>,b: Search<'_>,index: nat,records: Seq<Emission>)
    requires expansion_state(a,index,records),*a.language == *b.language,table_wf(b.constraints),
        a.constraints@.is_prefix_of(b.constraints@),a.items@ == b.items@,a.alphabets@ == b.alphabets@,
        a.archive@ == b.archive@,a.start@ == b.start@,a.vocabulary@ == b.vocabulary@,*a.universes == *b.universes,
        a.seen == b.seen,a.seen_records@ == b.seen_records@,a.antichain == b.antichain,a.simulation == b.simulation,
        forall|k: int| 0 <= k < b.constraints@.len() ==> constraint_in_vocabulary(b.constraints@[k],b.vocabulary@),
    ensures expansion_state(b,index,records),
{
    hide(paper::steps_ok);hide(paper::trace_steps_ok);hide(partial_trace_wf);hide(archive_follows);
    hide(finiteness::cases_from_atoms);hide(language::lang);
    hide(state_wf);hide(queue_order);hide(edges_wf);
    reveal(expansion_state);reveal(vocabulary_wf);
    lemma_state_evidence(a);lemma_queue_frame(a,b);
    lemma_state_frame(a,b);lemma_edges_frame(a,b);
}

pub(crate) proof fn lemma_expansion_begin(a: Search<'_>,b: Search<'_>,index: nat)
    requires running(a,index,a.start@,a.vocabulary@),index < a.items@.len(),
        state_wf(b),queue_order(b),vocabulary_wf(b,b.vocabulary@),edges_wf(b),
        trace(a,index).nodes == trace(b,index).nodes,
        a.items@ == b.items@,a.archive@ == b.archive@,a.start@ == b.start@,a.vocabulary@ == b.vocabulary@,
        a.seen_records@ == b.seen_records@,
        a.constraints == b.constraints,facade::frame(*a.language,*b.language),
        *a.universes == *b.universes,!paper::nullable_state(trace(b,index).nodes[index as int].item.state),
    ensures expansion_state(b,index,Seq::empty()),
{
    hide(paper::steps_ok);hide(paper::trace_steps_ok);hide(archive_follows);hide(finiteness::cases_from_atoms);
    hide(language::lang);
    reveal(running);reveal(expansion_state);reveal(emitted_cases);
    assert(trace(a,index) == trace(b,index));
    assert(archive_cases(a.archive@)(trace(a,index).nodes[index as int].item) == Set::<paper::Case>::empty());
    assert(emitted_cases(Seq::empty()) =~= Set::<paper::Case>::empty());
    lemma_partial_begin(ndomains(*a.universes),a.start@,archive_cases(a.archive@),trace(a,index));
    facade::lemma_language_wf(*a.language);model::lemma_graph_wf_elim(facade::graph(*a.language));
    assert forall|j: int| #![trigger b.items@[j]] 0 <= j < b.items@.len() implies
        impl_item(facade::graph(*a.language),a.constraints@,a.items@[j])
            == impl_item(facade::graph(*b.language),b.constraints@,b.items@[j]) by {
        model::lemma_lift_regex_stable(facade::graph(*a.language),facade::graph(*b.language),a.items@[j].residual@);
    }
}

pub(crate) proof fn lemma_running_limits(s: Search<'_>,n: nat,start: paper::Item,v: Seq<Set<nat>>)
    requires running(s,n,start,v),
    ensures n <= s.items@.len(),
{
    reveal(running);reveal(partial_trace_wf);
}

/// `f` contains every item reachable from `start` by cases that follow implemented steps and
/// add only literals over atoms or domains (`finiteness::theorem_impl_items_bound`).
pub(crate) open spec fn items_bound_ok(u: Universes,start: paper::Item,f: Set<paper::Item>) -> bool {
    forall|cases_of: spec_fn(paper::Item) -> Set<paper::Case>|
        finiteness::cases_follow(finite_impl::m_impl(),cases_of)
        && finiteness::cases_from_atoms(ndomains(u),cases_of,|q: Regex<model::Test>| symbolic::regex_primitives(q))
            ==> #[trigger] paper::items_within(cases_of,start,f)
}

/// The queue of a running search is a paper trace, whose nodes are distinct reachable items, so
/// it never exceeds the finite item bound (Lemma Finitely many residuals, `lem:finite-states`, lifted to items) for the implementation's model.
pub(crate) proof fn lemma_running_items_bound(s: Search<'_>,n: nat,start: paper::Item,
    v: Seq<Set<nat>>,f: Set<paper::Item>)
    requires running(s,n,start,v),items_bound_ok(*s.universes,start,f),
    ensures s.items@.len() <= f.len(),
{
    reveal(running);
    let d = ndomains(*s.universes);
    let cases = archive_cases(s.archive@);
    let t = trace(s,n);
    lemma_partial_trace_complete(d,start,cases,t);
    assert(paper::items_within(cases,start,f));
    assert(paper::Item { constraint: start.constraint, state: start.state } == start);
    paper::lemma_trace_nodes_bounded(start.constraint,start.state,cases,f,d,t);
}

pub(crate) proof fn lemma_trace_refuted(s: Search<'_>,index: nat,outcome: crate::search::SearchOutcome)
    requires parents_wf(s.items@),index < s.items@.len(),
        paper::nullable_state(trace(s,index).nodes[index as int].item.state),
        outcome matches crate::search::SearchOutcome::Refuted(r)
            && r.constraint@ == s.constraints@[s.items@[index as int].constraint as int]
            && r.letters@.map_values(|l: Letter| l@) == letter_chain(s.items@,index as int).map_values(|l: Letter| l@)
            && r.alphabets@ == alphabet_chain(s.items@,s.alphabets@,index as int)
            && r.assignments@ == chain_assignments(r.letters@,r.alphabets@),
    ensures paper::trace_outcome(trace(s,index),outcome_view(outcome)),
{
    hide(paper::chain);
    lemma_chain_correspondence(facade::graph(*s.language),s.constraints@,s.items@,s.alphabets@,
        index as int,depth(s.items@,index as int));
    if let crate::search::SearchOutcome::Refuted(r) = outcome {
        lemma_chain_assignments_views(r.letters@,letter_chain(s.items@,index as int),r.alphabets@);
    }
}

pub(crate) proof fn lemma_parent_archive_frame(archive: Map<paper::Item,Set<paper::Case>>,
    before: paper::Trace,after: paper::Trace,c: paper::Case,j: int)
    requires before.expanded < before.nodes.len(),after.expanded == before.expanded,
        before.nodes.is_prefix_of(after.nodes),0 < j < before.nodes.len(),
        partial_parent(archive_cases(archive),before,j,before.expanded+1),
    ensures partial_parent(archive_cases(archive.insert(before.nodes[before.expanded as int].item,
        archive_cases(archive)(before.nodes[before.expanded as int].item).insert(c))),after,j,after.expanded+1),
{
    reveal(partial_parent);
    let item = before.nodes[before.expanded as int].item;
    let updated = archive.insert(item,archive_cases(archive)(item).insert(c));
    lemma_archive_grows(archive,item,c);
    let (p,alpha) = before.nodes[j].parent->Some_0;
    let v = choose|v: paper::Case| archive_cases(archive)(before.nodes[p as int].item).contains(v)
        && v.alpha == alpha && before.nodes[j].item == paper::case_item(v);
    assert(after.nodes[p as int] == before.nodes[p as int]);
    assert(archive_cases(updated)(after.nodes[p as int].item).contains(v));
}

pub(crate) proof fn lemma_coverage_archive_frame(d: encoding::NDomains,archive: Map<paper::Item,Set<paper::Case>>,
    before: paper::Trace,after: paper::Trace,c: paper::Case,p: int)
    requires before.expanded < before.nodes.len(),before.nodes.is_prefix_of(after.nodes),
        0 <= p < before.nodes.len(),partial_coverage(d,archive_cases(archive),before,p),
        before.nodes[p].item == before.nodes[before.expanded as int].item ==> p == before.expanded,
        paper::may_discard(d,after.nodes,paper::case_item(c),before.nodes[before.expanded as int].depth+1),
    ensures partial_coverage(d,archive_cases(archive.insert(before.nodes[before.expanded as int].item,
        archive_cases(archive)(before.nodes[before.expanded as int].item).insert(c))),after,p),
{
    hide(paper::may_discard);hide(language::nullable);
    reveal(partial_coverage);
    let item = before.nodes[before.expanded as int].item;
    let updated = archive.insert(item,archive_cases(archive)(item).insert(c));
    assert(after.nodes[p] == before.nodes[p]);
    assert forall|v: paper::Case| archive_cases(updated)(after.nodes[p].item).contains(v) implies
        (exists|j: int| 0 < j < after.nodes.len() && after.nodes[j].parent == Some((p as nat,v.alpha))
            && after.nodes[j].item == paper::case_item(v))
        || paper::may_discard(d,after.nodes,paper::case_item(v),after.nodes[p].depth+1) by {
        if archive_cases(archive)(before.nodes[p].item).contains(v) {
            if paper::may_discard(d,before.nodes,paper::case_item(v),before.nodes[p].depth+1) {
                lemma_discard_grows(d,before.nodes,after.nodes,paper::case_item(v),before.nodes[p].depth+1);
            } else {
                let j = choose|j: int| 0 < j < before.nodes.len()
                    && before.nodes[j].parent == Some((p as nat,v.alpha)) && before.nodes[j].item == paper::case_item(v);
                assert(after.nodes[j] == before.nodes[j]);
            }
        } else {
            assert(before.nodes[p].item == item && v == c);
            assert(p == before.expanded);
        }
    }
}

pub(crate) proof fn lemma_trace_holds(s: Search<'_>,n: nat)
    requires n == s.items@.len(),
    ensures paper::trace_outcome(trace(s,n),paper::Outcome::Holds),
{}

pub(crate) proof fn lemma_partial_clauses_frame(d: encoding::NDomains,cases: spec_fn(paper::Item)->Set<paper::Case>,
    a: paper::Trace,b: paper::Trace,limit: nat,j: int)
    requires a.nodes == b.nodes,0 <= j < a.nodes.len(),
    ensures partial_parent(cases,a,j,limit) == partial_parent(cases,b,j,limit),
        partial_coverage(d,cases,a,j) == partial_coverage(d,cases,b,j),
{
    hide(language::lang);hide(language::nullable);hide(paper::may_discard);
    reveal(partial_parent);reveal(partial_coverage);
}

pub(crate) proof fn lemma_state_evidence(s: Search<'_>)
    requires state_wf(s),
    ensures facade::language_wf(*old(s.language)),table_wf(s.constraints),parents_wf(s.items@),
        ids_valid(facade::graph(*old(s.language)),s.constraints@,s.items@),
        1 <= s.universes@.len() <= history_syntax::MAX_ARITY,
        forall|i: int| 0 <= i < s.constraints@.len() ==> s.constraints@[i].len() == s.universes@.len(),
{
    hide(crate::verify::table_wf);hide(parents_wf);hide(ids_valid);hide(seen_certified);
    hide(crate::verify::simulation_exec::memo_wf);hide(crate::verify::prune_exec::antichain_wf);
    reveal(state_wf);
}

pub(crate) proof fn lemma_queue_frame(a: Search<'_>,b: Search<'_>)
    requires queue_order(a),a.items@ == b.items@,a.seen == b.seen,
    ensures queue_order(b),
{ hide(letter_chain);reveal(queue_order); }

pub(crate) proof fn lemma_running_evidence(s: Search<'_>,n: nat,start: paper::Item,v: Seq<Set<nat>>)
    requires running(s,n,start,v),
    ensures state_wf(s),queue_order(s),vocabulary_wf(s,v),edges_wf(s),
        paper::trace_steps_ok(ndomains(*s.universes),archive_cases(s.archive@),trace(s,n)),
        archive_follows(s.archive@),finiteness::cases_from_atoms(ndomains(*s.universes),archive_cases(s.archive@),
            |q: Regex<model::Test>| symbolic::regex_primitives(q)),
{
    hide(state_wf);hide(queue_order);hide(vocabulary_wf);hide(edges_wf);
    hide(paper::trace_steps_ok);hide(archive_follows);hide(finiteness::cases_from_atoms);
    reveal(running);
}

pub(crate) proof fn lemma_queue_atoms_vocabulary(s: Search<'_>,index: int,atoms: Seq<Atom>,v: Seq<Set<nat>>)
    requires vocabulary_wf(s,v),0 <= index < s.items@.len(),atoms_wf(atoms,v.len()),
        atom_set(atoms).subset_of(facade::residual_primitives(*s.language,s.items@[index].residual)),
    ensures atoms_in_vocabulary(atoms,v),
{
    reveal(vocabulary_wf);
    reveal(facade::residual_codes);reveal(facade::residual_primitives);
    let q = s.items@[index].residual;
    let l = *s.language;
    assert forall|i: int| #![trigger atoms[i]] 0 <= i < atoms.len() implies atoms[i].component < v.len()
        && match atoms[i].operand { crate::constraint::Operand::Constant(code) =>
            v[atoms[i].component as int].contains(code as nat),_ => true } by {
        assert(atoms.to_set().contains(atoms[i]));
        assert(atom_set(atoms).contains(atoms[i]@));
        if let crate::constraint::Operand::Constant(code) = atoms[i].operand {
            let c = crate::verify::component_at(atoms[i].component);
            assert(atoms.to_set().contains(atoms[i]));
            assert(atom_set(atoms).contains(atoms[i]@));
            facade::lemma_primitive_codes_contains(facade::residual_primitives(l,q),c,code as nat);
            assert(facade::residual_codes(l,q,c).contains(code as nat));
            assert(crate::verify::component_index(c) == atoms[i].component);
        }
    }
}

pub(crate) proof fn lemma_running_language_frame(a: Search<'_>,b: Search<'_>,n: nat,start: paper::Item,v: Seq<Set<nat>>)
    requires running(a,n,start,v),*a.language == *b.language,
        a.constraints == b.constraints,a.items@ == b.items@,a.alphabets@ == b.alphabets@,
        a.archive@ == b.archive@,a.start@ == b.start@,a.vocabulary@ == b.vocabulary@,*a.universes == *b.universes,
        a.seen == b.seen,a.seen_records@ == b.seen_records@,a.antichain == b.antichain,a.simulation == b.simulation,
    ensures running(b,n,start,v),
{
    hide(state_wf);hide(queue_order);hide(edges_wf);hide(vocabulary_wf);
    hide(partial_trace_wf);hide(paper::trace_steps_ok);hide(archive_follows);hide(finiteness::cases_from_atoms);
    reveal(running);
    lemma_state_evidence(a);lemma_queue_frame(a,b);
    lemma_state_frame(a,b);lemma_vocabulary_frame(a,b,v);lemma_edges_frame(a,b);
    assert(trace(a,n) == trace(b,n));
}

}
