//! Pruning of search states by antichains, up to simulation.
//!
//! Required parts are compared by identity; excluded pieces are compared by simulation.
//! Inserted states are never removed, preserving breadth-first counterexample order.

use crate::native::NativeGroups;
#[cfg(verus_keep_ghost)]
use crate::verify::{prune_exec::*, simulation_exec::*, table_wf};
use alloc::boxed::Box;
use alloc::vec::Vec;
use history_semantics::SymbolicLanguage;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::{
    encoding, implementation, pruning as paper, search as paper_search,
};
#[cfg(verus_keep_ghost)]
use history_semantics::{normalize_verify as norm, symbolic_language_verify as facade};
use junco_core::HistoryError;
use junco_core::kernel::{RegexId, RegexKindView, RegexView};
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::Regex;
#[cfg(verus_keep_ghost)]
use junco_core::{kernel::verify as model, observation::SmallVecSpecFns};
use smallvec::SmallVec;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

use crate::constraint::{Constraint, ConstraintId, ConstraintTable};
use crate::simulation::Simulation;

#[cfg(verus_keep_ghost)]
verus! { broadcast use model::group_kernel_views; }
#[verus_verify]
const ENUMERATED_PARTS: usize = 4;

#[verus_verify]
pub(crate) enum Root {
    Intersect(SmallVec<[RegexId; 4]>),
    Not(RegexId),
    Other,
}

#[verus_verify]
pub(crate) struct Decomposition {
    pub(crate) parts: SmallVec<[RegexId; 4]>,
    pub(crate) pieces: SmallVec<[RegexId; 8]>,
}

#[verus_verify]
impl Decomposition {
    #[verus_spec(result => requires facade::language_wf(*old(language)),
        ensures *final(language) == *old(language),
            residual@ < facade::graph(*final(language)).regexes.len()
                ==> junco_core::verify::history_specs::no_invariant_failure(result),
            residual@ < facade::graph(*final(language)).regexes.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result matches Ok(d) ==> residual@ < facade::graph(*final(language)).regexes.len()
                && decomposition_of(facade::graph(*final(language)), facade::abs(*final(language),residual),d))]
    pub(crate) fn of(
        language: &mut SymbolicLanguage,
        residual: RegexId,
    ) -> Result<Self, HistoryError> {
        proof_decl! { let ghost g = facade::graph(*language); }
        proof! { facade::lemma_language_wf(*language); }
        let root = node(language, residual)?;
        proof! { norm::regex_unfold(g,residual@); }
        let mut parts = SmallVec::<[RegexId; 4]>::new();
        let mut pieces = SmallVec::<[RegexId; 8]>::new();
        proof! { lemma_lifted(g,parts.view()); lemma_lifted(g,pieces.view()); }
        match root {
            Root::Intersect(children) => {
                proof! {
                    lemma_intersection(g,children.view(),facade::abs(*language,residual));
                    lemma_lifted(g,parts.view()); lemma_lifted(g,pieces.view());
                    assert(lifted(g,parts.view()) =~= positive(g,children.view().take(0)));
                }
                let mut index = 0;
                #[cfg_attr(verus_keep_ghost, verus_spec(invariant
                    *language == *old(language), facade::language_wf(*language),
                    g == facade::graph(*language), model::graph_wf(g),
                    residual@ < g.regexes.len(), index <= children.view().len(),
                    facade::abs(*language,residual) == Regex::Intersect(model::lift_regexes(g,model::regex_ids(children.view()))),
                    valid(g,children.view()), valid(g,parts.view()),valid(g,pieces.view()),
                    ordered(children.view()),ordered(parts.view()),
                    forall|i: int| 0 <= i < parts.view().len() ==> parts.view()[i]@ < children.view()[index as int]@
                        || index == children.view().len(),
                    lifted(g,parts.view()) == positive(g,children.view().take(index as int)),
                    forall|n: Regex<model::Test>| lifted(g,pieces.view()).contains(n)
                        == negative(g,children.view().take(index as int),n),
                    decreases children.view().len() - index))]
                while index < children.len() {
                    let slice: &[RegexId] = &children;
                    let child = slice[index];
                    let child_node = complemented(language, child)?;
                    proof! {
                        norm::regex_unfold(g,child@);
                        lemma_positive_push(g,children.view().take(index as int),child);
                        lemma_negative_push(g,children.view().take(index as int),child);
                        assert(children.view().take(index as int + 1)
                            =~= children.view().take(index as int).push(child));
                    }
                    match child_node {
                        Some(inner) => {
                            proof! { lemma_negative_not(g,children.view().take(index as int),child,inner); }
                            proof_decl! { let ghost before = pieces.view(); }
                            pieces = push_pieces(language, inner, pieces)?;
                            proof! {
                                assert forall|n: Regex<model::Test>| lifted(g,pieces.view()).contains(n)
                                    == negative(g,children.view().take(index as int + 1),n) by {
                                    assert(lifted(g,before).contains(n)
                                        == negative(g,children.view().take(index as int),n));
                                    assert(lifted(g,pieces.view()).contains(n) == (lifted(g,before).contains(n)
                                        || paper::union_ops(model::lift_regex(g,inner@)).contains(n)));
                                    assert(negative(g,children.view().take(index as int).push(child),n)
                                        == (negative(g,children.view().take(index as int),n)
                                            || paper::union_ops(model::lift_regex(g,inner@)).contains(n)));
                                }
                            }
                        }
                        None => {
                            proof! {
                                lemma_lifted_push(g,parts.view(),child);
                                lemma_valid_push(g,parts.view(),child);
                                lemma_ordered_push(parts.view(),child);
                            }
                            parts.push(child);
                        }
                    }
                    proof! {
                        assert forall|i: int| 0 <= i < parts.view().len()
                            implies parts.view()[i]@ <= child@ by {}
                    }
                    index += 1;
                    proof! {
                        assert forall|i: int| 0 <= i < parts.view().len()
                            && index < children.view().len() implies parts.view()[i]@ < children.view()[index as int]@ by {}
                    }
                }
                proof! {
                    assert(children.view().take(index as int) =~= children.view());
                    lemma_intersection(g,children.view(),facade::abs(*language,residual));
                    assert forall|p: Regex<model::Test>| paper::required(facade::abs(*language,residual),p)
                        == lifted(g,parts.view()).contains(p) by {}
                    assert forall|p: Regex<model::Test>| paper::excluded(facade::abs(*language,residual),p)
                        == lifted(g,pieces.view()).contains(p) by {}
                }
            }
            Root::Not(child) => {
                pieces = push_pieces(language, child, pieces)?;
                proof! {
                    lemma_not(model::lift_regex(g,child@));
                    assert forall|p: Regex<model::Test>| paper::required(facade::abs(*language,residual),p)
                        == lifted(g,parts.view()).contains(p) by {}
                    assert forall|p: Regex<model::Test>| paper::excluded(facade::abs(*language,residual),p)
                        == lifted(g,pieces.view()).contains(p) by {}
                }
            }
            Root::Other => {
                proof! { lemma_lifted_push(g,parts.view(),residual); }
                parts.push(residual);
                proof! {
                    lemma_other(facade::abs(*language,residual));
                    lemma_lifted(g,parts.view());
                    assert forall|p: Regex<model::Test>| paper::required(facade::abs(*language,residual),p)
                        == lifted(g,parts.view()).contains(p) by {}
                    assert forall|p: Regex<model::Test>| paper::excluded(facade::abs(*language,residual),p)
                        == lifted(g,pieces.view()).contains(p) by {}
                }
            }
        }
        proof_decl! { let ghost collected = pieces.view(); }
        normalize_pieces(&mut pieces);
        proof! {
            lemma_valid_set(g,collected,pieces.view());
            assert(lifted(g,pieces.view()) == lifted(g,collected));
        }
        let d = Self { parts, pieces };
        proof! {
            lemma_lifted(g,d.parts.view()); lemma_lifted(g,d.pieces.view());
            assert(decomposition_of(g,facade::abs(*language,residual),d));
        }
        Ok(d)
    }

    #[verus_spec(result => requires facade::language_wf(*old(language)),
        decomposition_valid(facade::graph(*old(language)),*self),
        memo_wf(*old(simulation),*old(language)),memo_obligations(),
        ensures *final(language) == *old(language),memo_wf(*final(simulation),*final(language)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> resource_error(error),
            result == Ok(true) ==> forall|q: Regex<model::Test>|
                decomposition_of(facade::graph(*final(language)),q,*self) ==> paper::dead(semantic_le(),q))]
    pub(crate) fn dead(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
    ) -> Result<bool, HistoryError> {
        if self.pieces.is_empty() {
            return Ok(false);
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost,verus_spec(invariant
            *language == *old(language),facade::language_wf(*language),
            decomposition_valid(facade::graph(*language),*self),
            memo_wf(*simulation,*language),memo_obligations(),index <= self.parts.view().len(),
            decreases self.parts.view().len()-index))]
        while index < self.parts.len() {
            let parts: &[RegexId] = &self.parts;
            let part = parts[index];
            let members = push_pieces(language, part, SmallVec::new())?;
            proof! { lemma_ordered(self.pieces.view()); }
            if simulation.covered(language, &members, &self.pieces)? {
                proof! {
                    assert forall|i: int| #![trigger members.view()[i]] 0 <= i < members.view().len()
                        implies exists|j: int| 0 <= j < self.pieces.view().len()
                            && paper::lang_le(model::lift_regex(facade::graph(*language),members.view()[i]@),
                                model::lift_regex(facade::graph(*language),self.pieces.view()[j]@)) by {
                        let j = choose|j: int| 0 <= j < self.pieces.view().len()
                            && regex_le(*language,members.view()[i],self.pieces.view()[j]);
                    }
                    assert forall|q: Regex<model::Test>| decomposition_of(facade::graph(*language),q,*self)
                        implies paper::dead(semantic_le(),q) by {
                        lemma_dead(facade::graph(*language),*self,q,part,members.view());
                    }
                }
                return Ok(true);
            }
            index += 1;
        }
        Ok(false)
    }
}

#[verus_verify]
#[verus_spec(result => requires facade::language_wf(*old(language)),
    ensures *final(language) == *old(language),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(root) ==>
        residual@ < facade::graph(*final(language)).regexes.len()
        && root_matches(root,facade::graph(*final(language)).regexes[residual@ as int].kind)
        && root_semantics(facade::graph(*final(language)),residual,root))]
fn node(language: &mut SymbolicLanguage, residual: RegexId) -> Result<Root, HistoryError> {
    let result = language.read_regex(
        residual,
        verus_exec_expr! {
            |view: RegexView<'_>| -> (root: Root)
                ensures root_matches(root,view@.kind),
            {
                match view.kind {
                    RegexKindView::Intersect(children) => {
                        let mut copied = SmallVec::new();
                        copied.extend_from_slice(children);
                        Root::Intersect(copied)
                    },
                    RegexKindView::Not(child) => Root::Not(child),
                    _ => Root::Other,
                }
            }
        },
    )?;
    proof! {
        facade::lemma_language_wf(*language);
        norm::regex_unfold(facade::graph(*language),residual@);
        lemma_root(facade::graph(*language),residual,result);
    }
    Ok(result)
}

#[verus_verify]
#[verus_spec(result => requires facade::language_wf(*old(language)),
    ensures *final(language) == *old(language),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(child) ==>
        residual@ < facade::graph(*final(language)).regexes.len()
        && match child {
            Some(inner) => inner@ < facade::graph(*final(language)).regexes.len()
                && facade::abs(*final(language),residual) == Regex::Not(Box::new(facade::abs(*final(language),inner))),
            None => !(facade::abs(*final(language),residual) is Not),
        })]
fn complemented(
    language: &mut SymbolicLanguage,
    residual: RegexId,
) -> Result<Option<RegexId>, HistoryError> {
    let result = language.read_regex(residual,verus_exec_expr! {
        |view: RegexView<'_>| -> (child: Option<RegexId>)
            ensures match child { Some(inner) => view@.kind == model::RegexKindNode::Not(inner@),
                None => !(view@.kind is Not) },
        { match view.kind { RegexKindView::Not(inner) => Some(inner), _ => None } }
    })?;
    proof! { facade::lemma_language_wf(*language); norm::regex_unfold(facade::graph(*language),residual@); }
    Ok(result)
}

#[verus_verify]
#[verus_spec(result => requires facade::language_wf(*old(language)),
    valid(facade::graph(*old(language)),pieces.view()),
    ensures *final(language) == *old(language),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        residual@ < facade::graph(*final(language)).regexes.len()
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(values) ==>
        residual@ < facade::graph(*final(language)).regexes.len()
        && valid(facade::graph(*final(language)),values.view())
        && forall|n: Regex<model::Test>| #[trigger] lifted(facade::graph(*final(language)),values.view()).contains(n)
            == (lifted(facade::graph(*old(language)),pieces.view()).contains(n)
                || paper::union_ops(facade::abs(*final(language),residual)).contains(n)))]
fn push_pieces(
    language: &mut SymbolicLanguage,
    residual: RegexId,
    pieces: SmallVec<[RegexId; 8]>,
) -> Result<SmallVec<[RegexId; 8]>, HistoryError> {
    proof_decl! { let ghost before = pieces.view(); let ghost g = facade::graph(*language); }
    proof! { facade::lemma_language_wf(*language); }
    let values = language.read_regex(residual,verus_exec_expr! {
        move |view: RegexView<'_>| -> (values: SmallVec<[RegexId;8]>)
            requires model::graph_wf(g), residual@ < g.regexes.len(),
                view@ == g.regexes[residual@ as int],valid(g,before),pieces.view() == before,
            ensures valid(g,values.view()), forall|n: Regex<model::Test>|
                lifted(g,values.view()).contains(n) == (lifted(g,before).contains(n)
                    || paper::union_ops(model::lift_regex(g,residual@)).contains(n)),
        {
            let mut pieces = pieces;
            proof! {
                norm::regex_unfold(g,residual@); lemma_lifted(g,before);
                assert(pieces.view() == before); assert(valid(g,pieces.view()));
            }
            match view.kind {
                RegexKindView::Union(children) => {
                    proof! {
                        assert forall|i: int| 0 <= i < children@.len()
                            implies children@[i]@ < g.regexes.len() by {
                            assert(model::regex_ids(children@)[i] == children@[i]@);
                        }
                        lemma_lifted_concat(g,pieces.view(),children@);
                    }
                    pieces.extend_from_slice(children);
                    proof! { assert(lifted(g,pieces.view()) == lifted(g,before).union(lifted(g,children@))); }
                    proof! {
                        assert forall|i: int| 0 <= i < pieces.view().len()
                            implies pieces.view()[i]@ < g.regexes.len() by {
                            if i < before.len() { assert(pieces.view()[i] == before[i]); }
                            else { assert(pieces.view()[i] == children@[i-before.len()]); }
                        }
                        lemma_lifted(g,children@);
                        assert forall|n: Regex<model::Test>| paper::union_ops(model::lift_regex(g,residual@)).contains(n)
                            == lifted(g,children@).contains(n) by {
                            if paper::union_ops(model::lift_regex(g,residual@)).contains(n) {
                                let i = choose|i: int| 0 <= i < children@.len()
                                    && model::lift_regexes(g,model::regex_ids(children@))[i] == n;
                                assert(model::lift_regex(g,children@[i]@) == n);
                            }
                            if lifted(g,children@).contains(n) {
                                let i = choose|i: int| 0 <= i < children@.len()
                                    && model::lift_regex(g,children@[i]@) == n;
                                assert(model::lift_regexes(g,model::regex_ids(children@))[i] == n);
                            }
                        }
                    }
                },
                _ => {
                    proof! { lemma_lifted_push(g,pieces.view(),residual); lemma_valid_push(g,pieces.view(),residual); }
                    pieces.push(residual);
                    proof! {
                        assert(!(model::lift_regex(g,residual@) is Union));
                        assert(paper::union_ops(model::lift_regex(g,residual@))[0] == model::lift_regex(g,residual@));
                    }
                },
            }
            pieces
        }
    });
    proof! { facade::lemma_language_wf(*language); }
    values
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(20))]
#[verus_spec(result => ensures final(values).view().to_set() == old(values).view().to_set(),
    ordered(final(values).view()))]
fn normalize_pieces(values: &mut SmallVec<[RegexId; 8]>) {
    proof_decl! { let ghost before = values.view(); }
    proof! { RegexId::lemma_obeys_cmp(); }
    values.as_mut_slice().sort_unstable();
    proof_decl! { let ghost sorted = values.view(); }
    proof! {
        norm::lemma_multiset_members(before,sorted);
        assert(sorted.to_set() =~= before.to_set());
        assert forall|i: int,j: int| 0 <= i < j < sorted.len() implies sorted[i]@ <= sorted[j]@ by {
            assert(!(vstd::std_specs::cmp::OrdSpec::cmp_spec(&sorted[i],&sorted[j]) is Greater));
        }
    }
    let count = values.len();
    let mut index = 0;
    let mut write = 0;
    #[cfg_attr(verus_keep_ghost,verus_spec(invariant
        index <= count,write <= index,values.view().len() == count,sorted.len() == count,
        sorted.to_set() == before.to_set(),
        forall|i: int,j: int| 0 <= i < j < sorted.len() ==> sorted[i]@ <= sorted[j]@,
        values.view().take(write as int) == junco_core::verify::history_assumptions::dedup_spec(sorted.take(index as int)),
        forall|i: int| index <= i < count ==> values.view()[i] == sorted[i],
        decreases count-index))]
    while index < count {
        let slice: &[RegexId] = values;
        let value = slice[index];
        proof! {
            norm::lemma_dedup_properties(sorted.take(index as int));
            norm::lemma_dedup_push(sorted.take(index as int),value);
            assert(sorted.take(index as int + 1) =~= sorted.take(index as int).push(value));
        }
        let duplicate = if index == 0 {
            false
        } else {
            proof! { assert(write > 0); }
            slice[write - 1] == value
        };
        if !duplicate {
            if write != index {
                values.as_mut_slice()[write] = value;
            }
            write += 1;
        }
        index += 1;
    }
    proof! { assert(sorted.take(index as int) =~= sorted); }
    values.truncate(write);
    proof! {
        norm::lemma_dedup_properties(sorted);
        norm::lemma_dedup_strict(sorted,|id: RegexId| id@);
        assert forall|i: int,j: int| 0 <= i < j < values.view().len()
            implies values.view()[i]@ < values.view()[j]@ by {
            assert((|id: RegexId| id@)(values.view()[i]) < (|id: RegexId| id@)(values.view()[j]));
        }
        assert(values.view().to_set() =~= sorted.to_set());
        assert(ordered(values.view()));
    }
}

#[verus_verify]
pub(crate) struct Antichain {
    pub(crate) groups: NativeGroups<SmallVec<[RegexId; 4]>, Entry>,
}

#[verus_verify]
pub(crate) struct Entry {
    pub(crate) constraint: ConstraintId,
    pub(crate) pieces: Box<[RegexId]>,
}

#[verus_verify]
impl Antichain {
    #[verus_spec(result => ensures forall|g: model::Graph,table: ConstraintTable,nodes: Seq<paper_search::Node>|
        antichain_wf(result,g,table,nodes))]
    pub(crate) fn new() -> Self {
        Self {
            groups: NativeGroups::new(),
        }
    }

    #[verus_spec(result => requires facade::language_wf(*old(language)),table_wf(*constraints),
        constraint < constraints@.len(),entries_valid(*self,facade::graph(*old(language)),*constraints),
        forall|i: int| 0 <= i < constraints@.len()
            ==> constraints@[i].len() == constraints@[constraint as int].len(),
        decomposition_valid(facade::graph(*old(language)),*state),parts_key_obligations(),
        memo_wf(*old(simulation),*old(language)),memo_obligations(),
        ensures *final(language) == *old(language),memo_wf(*final(simulation),*final(language)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> resource_error(error),
            result == Ok(true) ==> raw_subsumes(*self,facade::graph(*final(language)),*constraints,
                constraints@[constraint as int],*state),
            result == Ok(true) ==> forall|q: Regex<model::Test>,domains: encoding::NDomains,nodes: Seq<paper_search::Node>|
                decomposition_of(facade::graph(*final(language)),q,*state)
                && antichain_wf(*self,facade::graph(*final(language)),*constraints,nodes) ==>
                #[trigger] dominates_some(domains,nodes,
                    paper_search::Item { constraint: implementation::constraint_of(constraints@[constraint as int]),state:q }))]
    pub(crate) fn subsumes(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
        constraints: &ConstraintTable,
        constraint: ConstraintId,
        state: &Decomposition,
    ) -> Result<bool, HistoryError> {
        let c = constraints.get(constraint);
        let parts = &state.parts;
        let result = if parts.len() > ENUMERATED_PARTS {
            self.group_subsumes(language, simulation, constraints, c, parts, state)
        } else {
            let limit = 1usize << parts.len();
            let mut mask = 0;
            let mut found = false;
            #[cfg_attr(verus_keep_ghost,verus_spec(invariant
                *language == *old(language),facade::language_wf(*language),table_wf(*constraints),
                entries_valid(*self,facade::graph(*language),*constraints),
                decomposition_valid(facade::graph(*language),*state),parts_key_obligations(),
                memo_wf(*simulation,*language),memo_obligations(),
                mask <= limit, parts.view().len() <= ENUMERATED_PARTS,
                constraint < constraints@.len(),parts.view() == state.parts.view(),
                c@ == constraints@[constraint as int], crate::verify::constraint_wf(*c),
                forall|i: int| 0 <= i < constraints@.len() ==> constraints@[i].len() == c@.len(),
                found ==> raw_subsumes(*self,facade::graph(*language),*constraints,c@,*state),
                decreases limit-mask))]
            while mask < limit && !found {
                let mut subset = SmallVec::new();
                let mut bit = 0;
                #[cfg_attr(verus_keep_ghost,verus_spec(invariant
                    bit <= parts.view().len(),parts.view().len() <= ENUMERATED_PARTS,
                    parts.view() == state.parts.view(),valid(facade::graph(*language),parts.view()),
                    subset.view().to_set().subset_of(parts.view().to_set()),
                    valid(facade::graph(*language),subset.view()),
                    decomposition_valid(facade::graph(*language),*state),
                    decreases parts.view().len()-bit))]
                while bit < parts.len() {
                    if mask & (1usize << bit) != 0 {
                        let slice: &[RegexId] = parts;
                        proof! { lemma_valid_push(facade::graph(*language),subset.view(),slice[bit as int]); }
                        subset.push(slice[bit]);
                        proof! { assert(subset.view().to_set().subset_of(parts.view().to_set())); }
                    }
                    bit += 1;
                }
                found =
                    self.group_subsumes(language, simulation, constraints, c, &subset, state)?;
                mask += 1;
            }
            Ok(found)
        };
        proof! {
            if result == Ok(true) {
                assert forall|q: Regex<model::Test>,domains: encoding::NDomains,nodes: Seq<paper_search::Node>|
                    decomposition_of(facade::graph(*language),q,*state)
                    && antichain_wf(*self,facade::graph(*language),*constraints,nodes) implies
                    #[trigger] dominates_some(domains,nodes,
                        paper_search::Item { constraint: implementation::constraint_of(c@),state:q }) by {
                    lemma_domination(*self,facade::graph(*language),*constraints,c@,*state,q,domains,nodes);
                }
            }
        }
        result
    }

    #[verus_spec(result => requires facade::language_wf(*old(language)),table_wf(*constraints),
        crate::verify::constraint_wf(*constraint),entries_valid(*self,facade::graph(*old(language)),*constraints),
        forall|i: int| 0 <= i < constraints@.len() ==> constraints@[i].len() == constraint@.len(),
        decomposition_valid(facade::graph(*old(language)),*state),parts_key_obligations(),
        parts.view().to_set().subset_of(state.parts.view().to_set()),valid(facade::graph(*old(language)),parts.view()),
        memo_wf(*old(simulation),*old(language)),memo_obligations(),
        ensures *final(language) == *old(language),memo_wf(*final(simulation),*final(language)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> resource_error(error),
            result == Ok(true) ==> raw_subsumes(*self,facade::graph(*final(language)),*constraints,constraint@,*state))]
    fn group_subsumes(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
        constraints: &ConstraintTable,
        constraint: &Constraint,
        parts: &SmallVec<[RegexId; 4]>,
        state: &Decomposition,
    ) -> Result<bool, HistoryError> {
        let Some(entries) = self.groups.get(parts) else {
            return Ok(false);
        };
        proof_decl! {
            let ghost key = choose|key: SmallVec<[RegexId;4]>|
                crate::native::groups(self.groups).dom().contains(key)
                && parts.eq_spec(&key) && entries@ == crate::native::groups(self.groups)[key];
        }
        proof! { assert(key.view() == parts.view()); }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost,verus_spec(invariant
            index <= entries@.len(),*language == *old(language),facade::language_wf(*language),
            table_wf(*constraints),crate::verify::constraint_wf(*constraint),
            forall|i: int| 0 <= i < constraints@.len() ==> constraints@[i].len() == constraint@.len(),
            entries_valid(*self,facade::graph(*language),*constraints),
            decomposition_valid(facade::graph(*language),*state),parts_key_obligations(),
            parts.view().to_set().subset_of(state.parts.view().to_set()),key.view() == parts.view(),
            crate::native::groups(self.groups).dom().contains(key),
            entries@ == crate::native::groups(self.groups)[key],
            memo_wf(*simulation,*language),memo_obligations(),
            decreases entries@.len()-index))]
        while index < entries.len() {
            let entry = &entries[index];
            let older: &[RegexId] = &entry.pieces;
            let excluded: &[RegexId] = &state.pieces;
            proof! { assert(older@ == entry.pieces@); assert(excluded@ == state.pieces.view()); }
            proof! { lemma_ordered(state.pieces.view()); }
            if constraint.entails(constraints.get(entry.constraint))
                && simulation.covered(language, older, excluded)?
            {
                proof! {
                    assert forall|j: int| #![trigger entry.pieces@[j]] 0 <= j < entry.pieces@.len()
                        implies exists|k: int| 0 <= k < state.pieces.view().len()
                            && paper::lang_le(model::lift_regex(facade::graph(*language),entry.pieces@[j]@),
                                model::lift_regex(facade::graph(*language),state.pieces.view()[k]@)) by {
                        assert(older@[j] == entry.pieces@[j]);
                        let k = choose|k: int| 0 <= k < excluded@.len()
                            && regex_le(*language,older@[j],excluded@[k]);
                    }
                    assert(entry_subsumes(*self,facade::graph(*language),*constraints,constraint@,*state,key,index as int));
                    reveal(raw_subsumes);
                    assert(entry_subsumes(*self,facade::graph(*language),*constraints,constraint@,*state,
                        (key,index as int).0,(key,index as int).1));
                    assert(raw_subsumes(*self,facade::graph(*language),*constraints,constraint@,*state));
                }
                return Ok(true);
            }
            index += 1;
        }
        Ok(false)
    }

    #[verus_spec(result => requires parts_key_obligations(),
        ensures forall|g: model::Graph,table: ConstraintTable,nodes: Seq<paper_search::Node>,node: paper_search::Node|
            antichain_wf(*old(self),g,table,nodes) && constraint < table@.len()
            && node.item.constraint == implementation::constraint_of(table@[constraint as int])
            && decomposition_of(g,node.item.state,state) ==> antichain_wf(*final(self),g,table,nodes.push(node)))]
    pub(crate) fn insert(&mut self, constraint: ConstraintId, state: Decomposition) {
        proof_decl! { let ghost before = *self; let ghost old_state = state; }
        let slice: &[RegexId] = &state.pieces;
        let mut pieces = Vec::with_capacity(slice.len());
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost,verus_spec(invariant
            index <= slice@.len(),pieces@ == slice@.take(index as int),
            slice@ == old_state.pieces.view(),decreases slice@.len()-index))]
        while index < slice.len() {
            pieces.push(slice[index]);
            index += 1;
        }
        proof! { assert(pieces@ =~= old_state.pieces.view()); }
        let entry = Entry {
            constraint,
            pieces: pieces.into_boxed_slice(),
        };
        proof_decl! { let ghost stored = entry; }
        self.groups.push(state.parts, entry);
        proof! {
            reveal(antichain_wf); reveal(entries_valid); reveal(entry_matches);
            assert forall|g: model::Graph,table: ConstraintTable,nodes: Seq<paper_search::Node>,node: paper_search::Node|
                antichain_wf(before,g,table,nodes) && constraint < table@.len()
                && node.item.constraint == implementation::constraint_of(table@[constraint as int])
                && decomposition_of(g,node.item.state,old_state) implies antichain_wf(*self,g,table,nodes.push(node)) by {
                assert forall|key: SmallVec<[RegexId;4]>,i: int|
                    crate::native::groups(self.groups).dom().contains(key)
                    && 0 <= i < crate::native::groups(self.groups)[key].len() implies
                    indexed_entry(g,table,key,crate::native::groups(self.groups)[key][i],nodes.push(node)) by {
                    if crate::native::groups(before.groups).dom().contains(key)
                        && (!old_state.parts.eq_spec(&key) || i < crate::native::groups(before.groups)[key].len()) {
                        let k = choose|k: int| 0 <= k < nodes.len() && entry_matches(g,table,key,
                            crate::native::groups(before.groups)[key][i],nodes[k].item);
                        assert(nodes.push(node)[k] == nodes[k]);
                    } else {
                        assert(key.view() == old_state.parts.view());
                        assert(crate::native::groups(self.groups)[key][i] == stored);
                        assert(entry_matches(g,table,key,stored,node.item));
                        assert(nodes.push(node)[nodes.len() as int] == node);
                    }
                }
            }
        }
    }
}
