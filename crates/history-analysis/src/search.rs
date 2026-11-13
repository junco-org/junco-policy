//! The breadth-first search for a counterexample.
//!
//! A search state pairs a constraint on the candidate with a residual of the runtime's
//! [`SymbolicLanguage`]. Expanding a state derives its residual once, splits the constraint and
//! builds letters from the atoms the derivative tests, and interprets the derivative under each
//! letter's truth values. A successor is discarded if its residual is `∅` or dead, if the same
//! state was seen before, or if an inserted state subsumes it (see [`crate::prune`]). The
//! first expanded state whose residual accepts the empty history ends the search, and its parent
//! chain yields a counterexample of minimum length.
//! Cartesian-product overflow propagates as `HistoryError::GraphLimit`; it never becomes a
//! successful inclusion verdict or a capacity precondition on the query.

use crate::native::NativeSet;
use alloc::boxed::Box;
use alloc::vec::Vec;
use history_semantics::SymbolicLanguage;
use junco_core::HistoryError;
use junco_core::kernel::{Primitive, RegexId, Term, TransitionId};
use smallvec::SmallVec;

use crate::constraint::{
    Atom, ConstId, Constraint, ConstraintId, ConstraintTable, Letter, Operand, Universes, steps,
};
use crate::prune::{Antichain, Decomposition};
use crate::simulation::Simulation;
#[cfg(verus_keep_ghost)]
use crate::verify::table_wf;
#[cfg(verus_keep_ghost)]
use crate::verify::{atoms_wf, search_exec::*};
#[cfg(verus_keep_ghost)]
use crate::verify::{prune_exec::*, simulation_exec::*};
#[cfg(verus_keep_ghost)]
use history_semantics::symbolic_language_verify as facade;
#[cfg(verus_keep_ghost)]
use history_semantics::symbolic_verify as symbolic;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::pruning as paper_pruning;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::{implementation, search as paper_search};
#[cfg(verus_keep_ghost)]
use junco_core::{kernel::verify as model, observation::SmallVecSpecFns};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

#[cfg(verus_keep_ghost)]
verus! { broadcast use model::group_kernel_views; }

/// Result of one search.
#[verus_verify]
pub(crate) enum SearchOutcome {
    /// No valuation satisfying the constraint admits a history in the residual.
    Holds,
    /// A counterexample exists.
    Refuted(Box<Refutation>),
}

/// A symbolic counterexample: any valuation satisfying `constraint`, with one event from each
/// letter in order.
#[verus_verify]
pub(crate) struct Refutation {
    pub(crate) constraint: Constraint,
    pub(crate) letters: Vec<Letter>,
    #[cfg(verus_keep_ghost)]
    pub(crate) assignments: Ghost<Seq<paper_search::Assignment>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) alphabets: Ghost<Seq<Set<model::Primitive>>>,
}

/// Searches breadth-first for a history in `language` under some valuation satisfying
/// `constraint`.
/// The success contract applies to every well-formed input. Internal errors are additionally
/// excluded when the initial language's primitives use representable constant IDs and compare
/// variables only with their own coordinate; the same property is preserved for queued residuals.
#[verus_verify]
#[verus_spec(result => requires facade::language_wf(*old(language)),search_obligations(),
    crate::verify::constraint_wf(constraint),
    history_semantics::verify::refinement::inclusion::satisfiable(crate::verify::ndomains(*universes),implementation::constraint_of(constraint@)),
    history_semantics::verify::finite_impl::regex_nf(model::lift_regex(facade::graph(*old(language)),facade::root(*old(language)))),
    crate::verify::constraint_unique::universes_distinct(*universes),
    1 <= universes@.len() <= history_syntax::MAX_ARITY, constraint@.len() == universes@.len(),
    paper_search::atoms_bounded(symbolic::regex_primitives(model::lift_regex(facade::graph(*old(language)),facade::root(*old(language)))),universes@.len()),
    ensures facade::primitives_search_safe(symbolic::regex_primitives(
            model::lift_regex(facade::graph(*old(language)),facade::root(*old(language)))))
            ==> junco_core::verify::history_specs::no_internal_error(result),
        result matches Ok(outcome) ==> search_result(crate::verify::ndomains(*universes),
        paper_search::Item { constraint:implementation::constraint_of(constraint@),
            state:model::lift_regex(facade::graph(*old(language)),facade::root(*old(language))) },outcome_view(outcome))
            && refutation_ready(outcome,*universes,root_vocabulary(*old(language),*universes,constraint@)))]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
pub(crate) fn search(
    language: &mut SymbolicLanguage,
    universes: &Universes,
    constraint: Constraint,
) -> Result<SearchOutcome, HistoryError> {
    proof_decl! {
        let ghost initial_constraint = constraint;
        let ghost start = paper_search::Item { constraint:implementation::constraint_of(constraint@),
            state:model::lift_regex(facade::graph(*language),facade::root(*language)) };
        let ghost vocabulary = root_vocabulary(*language,*universes,constraint@);
    }
    let mut search = Search {
        language,
        universes,
        constraints: ConstraintTable::new(),
        items: Vec::new(),
        seen: NativeSet::new(),
        antichain: Antichain::new(),
        simulation: Simulation::new(),
        #[cfg(verus_keep_ghost)]
        alphabets: verus_exec_expr! { Ghost(Map::empty()) },
        #[cfg(verus_keep_ghost)]
        seen_records: verus_exec_expr! { Ghost(Seq::empty()) },
        #[cfg(verus_keep_ghost)]
        archive: verus_exec_expr! { Ghost(Map::empty()) },
        #[cfg(verus_keep_ghost)]
        start: verus_exec_expr! { Ghost(start) },
        #[cfg(verus_keep_ghost)]
        vocabulary: verus_exec_expr! { Ghost(vocabulary) },
    };
    let constraint = search.constraints.intern(constraint)?;
    let root = search.language.root();
    proof! {
        assert(memo_wf(search.simulation,*search.language));
        assert(antichain_wf(search.antichain,facade::graph(*search.language),search.constraints,
            impl_nodes(facade::graph(*search.language),search.constraints@,search.items@,search.alphabets@)));
        assert(search.seen_records@.to_set() =~= Set::<(ConstraintId,RegexId,nat)>::empty());
        assert(search.seen_records@.to_set().map(|r: (ConstraintId,RegexId,nat)| (r.0,r.1))
            =~= Set::<(ConstraintId,RegexId)>::empty());
        reveal(edges_wf);
        assert(seen_certified(search));
        assert(state_wf(search));
        assert(queue_order(search));
    }
    search.insert(constraint, root, None)?;
    proof! {
        reveal(running); reveal(vocabulary_wf); reveal(partial_trace_wf);
        crate::verify::lemma_constraint_key_view(search.constraints.constraints@[constraint as int],initial_constraint);
        assert(search.constraints@.len() == 1);
        assert(running(search,0,start,vocabulary));
    }
    search.run()
}

/// Inserted search state with its parent link, for counterexample reconstruction.
#[verus_verify]
#[derive(Clone)]
pub(crate) struct Item {
    pub(crate) constraint: ConstraintId,
    pub(crate) residual: RegexId,
    pub(crate) parent: Option<(usize, Letter)>,
}

#[verus_verify]
pub(crate) struct Search<'search> {
    pub(crate) language: &'search mut SymbolicLanguage,
    pub(crate) universes: &'search Universes,
    pub(crate) constraints: ConstraintTable,
    /// Inserted states, in insertion order, which is also the order of expansion.
    pub(crate) items: Vec<Item>,
    pub(crate) seen: NativeSet<(ConstraintId, RegexId)>,
    /// Inserted states, for subsumption.
    pub(crate) antichain: Antichain,
    /// Simulation between the language's residuals, for the dead test and subsumption.
    pub(crate) simulation: Simulation,
    #[cfg(verus_keep_ghost)]
    pub(crate) alphabets: Ghost<Map<nat, Set<model::Primitive>>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) seen_records: Ghost<Seq<(ConstraintId, RegexId, nat)>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) archive: Ghost<Map<paper_search::Item, Set<paper_search::Case>>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) start: Ghost<paper_search::Item>,
    #[cfg(verus_keep_ghost)]
    pub(crate) vocabulary: Ghost<Seq<Set<nat>>>,
}

impl Search<'_> {
    verus! {
    #[verifier::rlimit(30)]
    fn run(&mut self) -> (result: Result<SearchOutcome, HistoryError>)
        requires running(*old(self),0,old(self).start@,old(self).vocabulary@),search_obligations(),
        ensures facade::primitives_search_safe(symbolic::regex_primitives(old(self).start@.state))
                ==> junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(outcome) ==> search_result(crate::verify::ndomains(*old(self).universes),old(self).start@,outcome_view(outcome))
            && refutation_ready(outcome,*old(self).universes,old(self).vocabulary@),
    {
        proof_decl! { let ghost initial = *self; let ghost start = self.start@; let ghost vocabulary = self.vocabulary@; let ghost universes = *self.universes; }
        // Termination follows the finite item bound (Lemma Finitely many residuals, `lem:finite-states`, lifted to items) for the implementation's model: one finite item set,
        // fixed before the loop, contains every item the search can queue.
        proof_decl! { let ghost bound = choose|f: Set<paper_search::Item>| items_bound_ok(universes,start,f); }
        proof! {
            reveal(running); reveal(vocabulary_wf);
            let f = history_semantics::verify::refinement::finiteness::theorem_impl_items_bound(
                crate::verify::ndomains(universes),
                |q: junco_core::verify::history_specs::Regex<model::Test>| symbolic::regex_primitives(q),start);
            assert(items_bound_ok(universes,start,f));
            assert(items_bound_ok(universes,start,bound));
        }
        let mut next = 0;
        while next < self.items.len()
            invariant
                running(*self,next as nat,start,vocabulary),search_obligations(),
                self.start@ == start,self.vocabulary@ == vocabulary,
                *self.universes == universes,
                start == initial.start@,vocabulary == initial.vocabulary@,universes == *initial.universes,
                start == old(self).start@,vocabulary == old(self).vocabulary@,universes == *old(self).universes,
                items_bound_ok(universes,start,bound),
            decreases bound.len()-next,
        {
            proof! { reveal(running); reveal(vocabulary_wf); }
            proof! {
                lemma_running_limits(*self,next as nat,start,vocabulary);
                lemma_running_items_bound(*self,next as nat,start,vocabulary,bound);
            }
            proof_decl! { let ghost before_nullable = *self; }
            let nullable = self.language.nullable(self.items[next].residual)?;
            proof! {
                lemma_running_language_frame(before_nullable,*self,next as nat,start,vocabulary);
                lemma_running_evidence(*self,next as nat,start,vocabulary);
            }
            if nullable {
                let outcome = self.counterexample(next);
                proof! {
                    reveal(running);
                    lemma_chain_correspondence(facade::graph(*self.language),self.constraints@,
                        self.items@,self.alphabets@,next as int,depth(self.items@,next as int));
                    lemma_trace_refuted(*self,next as nat,outcome);
                    lemma_search_result(*self,next as nat,start,vocabulary,outcome_view(outcome));
                    assert(start == initial.start@);
                    assert(vocabulary == initial.vocabulary@);
                    assert(universes == *initial.universes);
                    assert(search_result(crate::verify::ndomains(*initial.universes),initial.start@,outcome_view(outcome)));
                    assert(refutation_ready(outcome,*initial.universes,initial.vocabulary@));
                }
                let result = Ok(outcome);
                proof! {
                    assert(result matches Ok(o) ==> search_result(crate::verify::ndomains(*initial.universes),initial.start@,outcome_view(o))
                        && refutation_ready(o,*initial.universes,initial.vocabulary@));
                }
                return result;
            }
            self.expand(next)?;
            proof! {
                lemma_running_limits(*self,next as nat+1,start,vocabulary);
                lemma_running_items_bound(*self,next as nat+1,start,vocabulary,bound);
            }
            next += 1;
        }
        proof! {
            reveal(refutation_ready);
            lemma_running_limits(*self,next as nat,start,vocabulary);
            lemma_trace_holds(*self,next as nat);
            lemma_search_result(*self,next as nat,start,vocabulary,paper_search::Outcome::Holds);
            assert(start == initial.start@ && vocabulary == initial.vocabulary@ && universes == *initial.universes);
            assert(search_result(crate::verify::ndomains(*initial.universes),initial.start@,paper_search::Outcome::Holds));
            assert(refutation_ready(SearchOutcome::Holds,*initial.universes,initial.vocabulary@));
        }
        Ok(SearchOutcome::Holds)
    }
    }

    verus! {
    /// Inserts the successor of the item by each step of its constraint and the atoms its
    /// derivative tests.
    // `?` on `intern` exceeds the verifier's resource limit on the letter loop that follows.
    #[allow(clippy::question_mark)]
    fn expand(&mut self, index: usize) -> (result: Result<(), HistoryError>)
        requires running(*old(self),index as nat,old(self).start@,old(self).vocabulary@),
            search_obligations(),index < old(self).items@.len(),
            !paper_search::nullable_state(trace(*old(self),index as nat).nodes[index as int].item.state),
        ensures facade::primitives_search_safe(symbolic::regex_primitives(old(self).start@.state))
                ==> junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(_) ==> running(*final(self),index as nat+1,old(self).start@,old(self).vocabulary@)
            && final(self).start@ == old(self).start@ && final(self).vocabulary@ == old(self).vocabulary@
            && *final(self).universes == *old(self).universes,
    {
        hide(junco_core::verify::history_specs::lang);
        hide(model::lift_regex);hide(model::lift_test);hide(symbolic::regex_primitives);
        hide(paper_search::successor_ok);
        hide(paper_search::steps_ok);hide(paper_search::trace_steps_ok);
        hide(model::unique_nodes);hide(model::tables_wf);
        hide(Seq::<_>::no_duplicates);
        hide(queue_order);hide(seen_certified);
        hide(crate::verify::steps_result);hide(crate::verify::constraint_unique::steps_alphas_unique);
        hide(crate::verify::split_views);hide(crate::verify::letters_views);
        hide(crate::verify::register_options);hide(crate::verify::class_options);
        hide(implementation::letter_assignment);hide(implementation::letter_holds);
        hide(implementation::constraint_of);
        proof! { reveal(running); reveal(vocabulary_wf); reveal(expansion_state); }
        proof_decl! {
            let ghost entry = *self;
            let ghost start = self.start@;
            let ghost vocabulary = self.vocabulary@;
            let ghost universes = *self.universes;
            let ghost parent = trace(*self,index as nat).nodes[index as int].item;
            let ghost source = self.constraints.constraints@[self.items@[index as int].constraint as int];
        }
        proof! {
            reveal(running); reveal(vocabulary_wf);
            lemma_partial_trace_complete(crate::verify::ndomains(*self.universes),start,
                archive_cases(self.archive@),trace(*self,index as nat));
            paper_search::lemma_node_realizable(crate::verify::ndomains(*self.universes),start.constraint,
                start.state,archive_cases(self.archive@),trace(*self,index as nat),index as int);
        }
        let constraint = self.items[index].constraint;
        let residual = self.items[index].residual;
        let (transition, atoms) = derive_atoms(self.language, residual)?;
        proof! {
            lemma_state_frame(entry,*self);
            lemma_vocabulary_frame(entry,*self,vocabulary);
            assert(paper_search::atoms_bounded(facade::residual_primitives(*self.language,residual),vocabulary.len()));
            assert(atoms_wf(atoms@,vocabulary.len()));
            lemma_edges_frame(entry,*self);
            assert forall|j: int| #![trigger self.items@[j]] 0 < j < self.items@.len() implies match self.items@[j].parent {
                None => false,Some((p,_)) => p < index,
            } by {
                reveal(partial_trace_wf);reveal(partial_parent);
                assert(partial_parent(archive_cases(self.archive@),trace(*self,index as nat),j,index as nat));
            }
            let before_alphabets = *self;
            self.alphabets = Ghost(self.alphabets@.insert(index as nat,crate::verify::atom_set(atoms@)));
            assert(trace(*self,index as nat).nodes == trace(entry,index as nat).nodes);
            lemma_seen_trace_frame(before_alphabets,*self);
            lemma_queue_frame(entry,*self);
            lemma_edges_frame(entry,*self);
            assert(vocabulary_wf(*self,vocabulary));
            assert(state_wf(*self));
            lemma_queue_atoms_vocabulary(*self,index as int,atoms@,vocabulary);
            lemma_expansion_begin(entry,*self,index as nat);
        }
        let source_constraint = &self.constraints.constraints[constraint as usize];
        proof! { assert(*source_constraint == source); }
        let branches = steps(source_constraint, &atoms, self.universes)?;
        proof_decl! {
            let ghost groups = branches@;
            let ghost records: Seq<Emission> = Seq::empty();
        }
        proof! {
            lemma_group_vocabulary(source,atoms@,*self.universes,groups,vocabulary);
            lemma_enumeration_empty(groups,atoms@);
            assert(crate::verify::constraint_unique::constraint_sequence(crate::verify::group_constraints(groups))
                =~= groups.map_values(|row: (Constraint,Vec<Letter>)| row.0@));
            assert(expansion_state(*self,index as nat,records));
        }
        let count = branches.len();
        let mut branches = branches.into_iter();
        let mut group = 0;
        while group < count
            invariant
            expansion_state(*self,index as nat,records),search_obligations(),
            self.start@ == start,self.vocabulary@ == vocabulary,
            *self.universes == universes,
            start == old(self).start@,vocabulary == old(self).vocabulary@,universes == *old(self).universes,
            trace(*self,index as nat).nodes[index as int].item == parent,
            parent.state == facade::abs(*self.language,residual),
            parent.constraint == implementation::constraint_of(source@),
            self.constraints@[constraint as int] == source@,
            self.alphabets@.dom().contains(index as nat),self.alphabets@[index as nat] == crate::verify::atom_set(atoms@),
            crate::verify::constraint_wf(source),constraint_in_vocabulary(source@,vocabulary),
            history_semantics::verify::refinement::inclusion::satisfiable(crate::verify::ndomains(universes),implementation::constraint_of(source@)),
            self.items@[index as int].residual == residual,self.items@[index as int].constraint == constraint,
            group <= count,count == groups.len(),
            branches.obeys_prophetic_iter_laws(),branches.remaining() == groups.subrange(group as int,count as int),
            enumeration_prefix(groups,atoms@,records,group as int,0),
            crate::verify::steps_result(source,atoms@,*self.universes,groups),
            forall|b: int| 0 <= b < groups.len() ==> constraint_in_vocabulary(groups[b].0@,vocabulary),
            groups.map_values(|row: (Constraint,Vec<Letter>)| row.0@).no_duplicates(),
            crate::verify::constraint_unique::steps_alphas_unique(source,atoms@,*self.universes,groups),
            atoms_wf(atoms@,universes@.len()),atoms_in_vocabulary(atoms@,vocabulary),
            atoms@.len() + 63 <= usize::MAX,
            crate::verify::atom_set(atoms@).subset_of(symbolic::regex_primitives(parent.state)),
            forall|n: int| 0 <= n < records.len() ==> paper_search::successor_ok(parent.state,records[n].case.alpha,records[n].case.next),
            facade::has_atoms(*self.language,transition),
            history_semantics::verify::finite_deriv::dbound(facade::graph(*self.language),residual@,transition@),
            symbolic::derivative_correct(facade::graph(*self.language),residual@,transition),
            facade::atom_ids(*self.language,transition).len() == atoms@.len(),
            forall|i: int| 0 <= i < atoms@.len() ==> model::lift_test(facade::graph(*self.language),facade::atom_ids(*self.language,transition)[i]@) == model::Test::Atom(atoms@[i]@,true),
            decreases count-group,
        {
            let (refined,letters) = match branches.next() { Some(value) => value,None => unreachable!() };
            proof_decl! { let ghost prior = *self; let ghost original_refined = refined; }
            proof! {
                reveal(expansion_state); reveal(vocabulary_wf);
                assert(refined == groups[group as int].0);
                lemma_steps_group_evidence(source,atoms@,*self.universes,groups,group as int);
            }
            let refined = match self.constraints.intern(refined) {
                Ok(id) => id,
                Err(error) => return Err(error),
            };
            proof! {
                crate::verify::lemma_constraint_key_view(self.constraints.constraints@[refined as int],original_refined);
                assert forall|k: int| 0 <= k < self.constraints@.len() implies
                    constraint_in_vocabulary(self.constraints@[k],vocabulary) by {
                    if k < prior.constraints@.len() { assert(self.constraints@[k] == prior.constraints@[k]); }
                    else { assert(self.constraints@[k] == original_refined@); }
                }
                lemma_expansion_table_frame(prior,*self,index as nat,records);
            }
            let letter_count = letters.len();
            let mut letters = letters.into_iter();
            let mut letter_index = 0;
            while letter_index < letter_count
                invariant
                expansion_state(*self,index as nat,records),search_obligations(),
                self.start@ == start,self.vocabulary@ == vocabulary,
                *self.universes == universes,
                start == old(self).start@,vocabulary == old(self).vocabulary@,universes == *old(self).universes,
                trace(*self,index as nat).nodes[index as int].item == parent,
                parent.state == facade::abs(*self.language,residual),
                parent.constraint == implementation::constraint_of(source@),
                self.constraints@[constraint as int] == source@,
                self.alphabets@.dom().contains(index as nat),self.alphabets@[index as nat] == crate::verify::atom_set(atoms@),
                crate::verify::constraint_wf(source),constraint_in_vocabulary(source@,vocabulary),
                history_semantics::verify::refinement::inclusion::satisfiable(crate::verify::ndomains(universes),implementation::constraint_of(source@)),
                self.items@[index as int].residual == residual,self.items@[index as int].constraint == constraint,
                group < count,count == groups.len(),letter_index <= letter_count,
                letter_count == groups[group as int].1@.len(),
                letters.obeys_prophetic_iter_laws(),letters.remaining() == groups[group as int].1@.subrange(letter_index as int,letter_count as int),
                enumeration_prefix(groups,atoms@,records,group as int,letter_index as int),
                crate::verify::steps_result(source,atoms@,*self.universes,groups),
                forall|b: int| 0 <= b < groups.len() ==> constraint_in_vocabulary(groups[b].0@,vocabulary),
                groups.map_values(|row: (Constraint,Vec<Letter>)| row.0@).no_duplicates(),
                crate::verify::constraint_unique::steps_alphas_unique(source,atoms@,*self.universes,groups),
                self.constraints@[refined as int] == groups[group as int].0@,refined < self.constraints@.len(),
                forall|j: int| 0 <= j < groups[group as int].1@.len() ==> crate::verify::letter_wf(groups[group as int].1@[j])
                    && groups[group as int].1@[j]@.classes.len() == universes@.len(),
                atoms_wf(atoms@,universes@.len()),atoms_in_vocabulary(atoms@,vocabulary),
                atoms@.len() + 63 <= usize::MAX,
                crate::verify::atom_set(atoms@).subset_of(symbolic::regex_primitives(parent.state)),
                forall|n: int| 0 <= n < records.len() ==> paper_search::successor_ok(parent.state,records[n].case.alpha,records[n].case.next),
                facade::has_atoms(*self.language,transition),
                history_semantics::verify::finite_deriv::dbound(facade::graph(*self.language),residual@,transition@),
                symbolic::derivative_correct(facade::graph(*self.language),residual@,transition),
                facade::atom_ids(*self.language,transition).len() == atoms@.len(),
                forall|i: int| 0 <= i < atoms@.len() ==> model::lift_test(facade::graph(*self.language),facade::atom_ids(*self.language,transition)[i]@) == model::Test::Atom(atoms@[i]@,true),
                decreases letter_count-letter_index,
            {
                let letter = match letters.next() { Some(value) => value,None => unreachable!() };
                proof! { reveal(expansion_state); reveal(vocabulary_wf); }
                proof! {
                    lemma_generated_edge(source,atoms@,*self.universes,groups,vocabulary,group as int,letter_index as int);
                }
                let words = truth(&atoms,&letter);
                proof_decl! { let ghost before_successor = *self; }
                let successor = self.language.successor(transition, &words)?;
                proof_decl! {
                    let ghost emitted = paper_search::Case {
                        constraint:implementation::constraint_of(self.constraints@[refined as int]),
                        alpha:implementation::letter_assignment(letter@,crate::verify::atom_set(atoms@)),
                        next:facade::abs(*self.language,successor) };
                }
                proof! {
                    reveal(expansion_state); reveal(vocabulary_wf);
                    lemma_expansion_language_frame(before_successor,*self,index as nat,records);
                    facade::lemma_language_wf(*before_successor.language);
                    lemma_derivative_frame(*before_successor.language,*self.language,residual,transition,atoms@);
                    model::lemma_graph_wf_elim(facade::graph(*before_successor.language));
                    model::lemma_lift_regex_stable(facade::graph(*before_successor.language),facade::graph(*self.language),residual@);
                    lemma_vocabulary_frame(before_successor,*self,vocabulary);
                    facade::lemma_successor_vocabulary(*before_successor.language,*self.language,residual,transition,successor);
                    assert(facade::primitives_search_safe(symbolic::regex_primitives(start.state))
                        ==> facade::residual_search_safe(*self.language,successor));
                    assert(paper_search::atoms_bounded(facade::residual_primitives(*self.language,successor),vocabulary.len()));
                    lemma_successor_nf(facade::graph(*before_successor.language),residual@,transition@,
                        facade::graph(*self.language),successor@);
                    lemma_resolved_successor(*self.language,residual,transition,successor,atoms@,letter,words.view());
                    assert(parent.state == facade::abs(*self.language,residual));
                    assert(paper_search::successor_ok(parent.state,emitted.alpha,emitted.next));
                    assert(expansion_state(*self,index as nat,records));
                }
                proof_decl! { let ghost before_insert = *self; }
                self.insert(refined, successor, Some((index, letter)))?;
                proof! {
                    reveal(expansion_state); reveal(vocabulary_wf);
                    lemma_queue_nodes_distinct(*self);
                    if self.items@ != before_insert.items@ {
                        lemma_nodes_successor(facade::graph(*self.language),self.constraints@,
                            before_insert.items@,self.alphabets@,
                            Item { constraint:refined,residual:successor,parent:Some((index,letter)) },index,letter);
                    }
                    lemma_partial_case(crate::verify::ndomains(*self.universes),start,before_insert.archive@,
                        trace(before_insert,index as nat),trace(*self,index as nat),emitted);
                    let updated_records = records.push(Emission { group:group as int,letter:letter_index as int,case:emitted });
                    lemma_emitted_push(records,updated_records,emitted);
                    lemma_enumeration_push(groups,atoms@,records,updated_records.last());
                    let updated_cases = emitted_cases(updated_records);
                    lemma_archive_add(self.archive@,parent,updated_cases);
                    lemma_emitted_literals(source,atoms@,*self.universes,groups,updated_records);
                    lemma_archive_atoms_add(crate::verify::ndomains(*self.universes),self.archive@,parent,updated_cases);
                    lemma_archive_insert_within(before_insert.archive@,
                        trace(before_insert,index as nat).nodes,trace(*self,index as nat).nodes,
                        index as nat+1,index as int,updated_cases);
                    lemma_trace_steps_archive(crate::verify::ndomains(*self.universes),before_insert.archive@,
                        trace(before_insert,index as nat),trace(*self,index as nat),updated_cases);
                    let before_archive = *self;
                    self.archive = Ghost(self.archive@.insert(parent,updated_cases));
                    lemma_seen_trace_frame(before_archive,*self);
                    lemma_queue_frame(before_archive,*self);
                    lemma_edges_frame(before_archive,*self);
                    records = updated_records;
                    assert(state_wf(*self));
                    assert(vocabulary_wf(*self,vocabulary));
                    assert(partial_trace_wf(crate::verify::ndomains(*self.universes),start,
                        archive_cases(self.archive@),trace(*self,index as nat),true));
                    assert(paper_search::trace_steps_ok(crate::verify::ndomains(*self.universes),
                        archive_cases(self.archive@),trace(*self,index as nat)));
                    assert(archive_within(self.archive@,trace(*self,index as nat).nodes,index as nat+1));
                    assert(archive_cases(self.archive@)(parent) == emitted_cases(records));
                    assert(seen_depth_bounded(*self,depth(self.items@,index as int)+1));
                    assert forall|j: int| 0 <= j < self.items@.len() implies
                        depth(self.items@,j) <= depth(self.items@,index as int)+1 by {
                        if j < before_insert.items@.len() {
                            assert(depth(self.items@,j) == depth(before_insert.items@,j));
                        } else {
                            assert(j == before_insert.items@.len());
                            assert(depth(self.items@,j) == depth(before_insert.items@,index as int)+1);
                        }
                    }
                    assert(archive_follows(self.archive@));
                    assert(history_semantics::verify::refinement::finiteness::cases_from_atoms(
                        crate::verify::ndomains(*self.universes),archive_cases(self.archive@),
                        |q: junco_core::verify::history_specs::Regex<model::Test>| symbolic::regex_primitives(q)));
                    assert forall|j: int| #![trigger self.items@[j]] index < j < self.items@.len() implies
                        !self.archive@.dom().contains(impl_item(facade::graph(*self.language),self.constraints@,self.items@[j])) by {
                        assert(trace(*self,index as nat).nodes[j].item
                            == impl_item(facade::graph(*self.language),self.constraints@,self.items@[j]));
                    }
                    assert(expansion_state(*self,index as nat,records));
                }
                letter_index += 1;
            }
            proof! { lemma_enumeration_advance(groups,atoms@,records,group as int); }
            group += 1;
        }
        proof! {
            assert(groups.map_values(|row: (Constraint,Vec<Letter>)| row.0@)
                =~= groups.map_values(|group: (Constraint,Vec<Letter>)| group.0@));
            lemma_emitted_steps(source,atoms@,*self.universes,groups,records,parent.state);
            lemma_expansion_end(*self,index as nat,records);
        }
        Ok(())
    }
    }

    /// Queues a state unless its residual is `∅` or dead, the same state was seen before, or
    /// an inserted state subsumes it.
    #[verus_verify]
    #[verus_spec(result => requires state_wf(*old(self)), search_obligations(),
        constraint < old(self).constraints@.len(), residual@ < facade::graph(*old(self).language).regexes.len(),
        match parent { None => old(self).items@.len() == 0, Some((p,_)) => p < old(self).items@.len() },
        seen_depth_bounded(*old(self), insertion_depth(old(self).items@,parent)),
        queue_order(*old(self)),
        edges_wf(*old(self)),edge_ready(*old(self),constraint,parent),
        forall|j: int| 0 <= j < old(self).items@.len()
            ==> depth(old(self).items@,j) <= insertion_depth(old(self).items@,parent),
        ensures junco_core::verify::history_specs::no_internal_error(result),
            result matches Ok(_) ==> state_wf(*final(self))
            && queue_order(*final(self))
            && edges_wf(*final(self))
            && *final(self).language == *old(self).language
            && final(self).constraints == old(self).constraints
            && final(self).alphabets@ == old(self).alphabets@
            && final(self).archive@ == old(self).archive@
            && final(self).start@ == old(self).start@ && final(self).vocabulary@ == old(self).vocabulary@
            && *final(self).universes == *old(self).universes
            && old(self).items@.is_prefix_of(final(self).items@)
            && final(self).items@.len() <= old(self).items@.len()+1
            && seen_depth_bounded(*final(self), insertion_depth(old(self).items@,parent))
            && paper_search::may_discard(crate::verify::ndomains(*old(self).universes),
                impl_nodes(facade::graph(*final(self).language),final(self).constraints@,
                    final(self).items@,final(self).alphabets@),
                paper_search::Item { constraint: implementation::constraint_of(old(self).constraints@[constraint as int]),
                    state: facade::abs(*old(self).language,residual) },insertion_depth(old(self).items@,parent))
            && (final(self).items@ == old(self).items@ && paper_search::may_discard(
                crate::verify::ndomains(*old(self).universes),
                impl_nodes(facade::graph(*final(self).language),final(self).constraints@,
                    final(self).items@,final(self).alphabets@),
                paper_search::Item { constraint: implementation::constraint_of(old(self).constraints@[constraint as int]),
                    state: facade::abs(*old(self).language,residual) },insertion_depth(old(self).items@,parent))
                || final(self).items@ == old(self).items@.push(Item { constraint,residual,parent })))]
    fn insert(
        &mut self,
        constraint: ConstraintId,
        residual: RegexId,
        parent: Option<(usize, Letter)>,
    ) -> Result<(), HistoryError> {
        proof_decl! {
            let ghost entry = *self;
            let ghost g = facade::graph(*self.language);
            let ghost nodes = impl_nodes(g,self.constraints@,self.items@,self.alphabets@);
            let ghost candidate = paper_search::Item {
                constraint: implementation::constraint_of(self.constraints@[constraint as int]),
                state: facade::abs(*self.language,residual) };
            let ghost level = insertion_depth(self.items@,parent);
        }
        proof! {
            facade::lemma_language_wf(*self.language);
            assert forall|a: (ConstraintId,RegexId), b: (ConstraintId,RegexId)|
                a.eq_spec(&b) == (a == b) by {}
        }
        if self.language.is_empty(residual) {
            return Ok(());
        }
        if !self.seen.insert((constraint, residual)) {
            proof! {
                let key = (constraint,residual);
                let record = choose|record: (ConstraintId,RegexId,nat)|
                    entry.seen_records@.to_set().contains(record) && (record.0,record.1) == key;
                let j = choose|j: int| 0 <= j < entry.seen_records@.len()
                    && entry.seen_records@[j] == record;
                lemma_seen_discard(crate::verify::ndomains(*self.universes),nodes,candidate,record.2,level);
                lemma_edges_insert(entry,*self,Item {constraint,residual,parent});
            }
            return Ok(());
        }
        proof! {
            assert(!crate::native::members(entry.seen).contains((constraint,residual))) by {
                if crate::native::members(entry.seen).contains((constraint,residual)) {
                    assert((constraint,residual).eq_spec(&(constraint,residual)));
                }
            }
        }
        let state = Decomposition::of(self.language, residual)?;
        if state.dead(self.language, &mut self.simulation)? {
            proof! {
                paper_pruning::lemma_prune_sound(crate::verify::ndomains(*self.universes),semantic_le(),candidate,candidate);
                self.seen_records = Ghost(entry.seen_records@.push((constraint,residual,level)));
                lemma_seen_add(entry,*self,(constraint,residual),level);
                lemma_edges_insert(entry,*self,Item {constraint,residual,parent});
            }
            return Ok(());
        }
        if self.antichain.subsumes(
            self.language,
            &mut self.simulation,
            &self.constraints,
            constraint,
            &state,
        )? {
            proof! {
                assert(dominates_some(crate::verify::ndomains(*self.universes),nodes,candidate));
                let k = choose|k: int| 0 <= k < nodes.len()
                    && paper_pruning::dominated(crate::verify::ndomains(*self.universes),semantic_le(),candidate,nodes[k].item);
                paper_pruning::lemma_prune_sound(crate::verify::ndomains(*self.universes),semantic_le(),candidate,nodes[k].item);
                assert(nodes[k].depth <= level);
                assert(paper_search::may_discard(crate::verify::ndomains(*self.universes),nodes,candidate,level));
                self.seen_records = Ghost(entry.seen_records@.push((constraint,residual,level)));
                lemma_seen_add(entry,*self,(constraint,residual),level);
                lemma_edges_insert(entry,*self,Item {constraint,residual,parent});
            }
            return Ok(());
        }
        self.antichain.insert(constraint, state);
        self.items.push(Item {
            constraint,
            residual,
            parent,
        });
        proof! {
            assert forall|j: int| 0 <= j < entry.items@.len() implies
                (entry.items@[j].constraint,entry.items@[j].residual) != (constraint,residual) by {
                assert(crate::native::members(entry.seen).contains(
                    (entry.items@[j].constraint,entry.items@[j].residual)));
            }
            let item = Item { constraint,residual,parent };
            lemma_nodes_push(g,self.constraints@,entry.items@,self.alphabets@,item);
            lemma_edges_insert(entry,*self,item);
            assert(queue_order(*self));
            let node = impl_nodes(g,self.constraints@,self.items@,self.alphabets@).last();
            assert(node.item == candidate && node.depth == level);
            assert(impl_nodes(g,self.constraints@,self.items@,self.alphabets@) =~= nodes.push(node));
            lemma_queued_discard(crate::verify::ndomains(*self.universes),nodes,node);
            self.seen_records = Ghost(entry.seen_records@.push((constraint,residual,level)));
            lemma_seen_add(entry,*self,(constraint,residual),level);
            lemma_edges_insert(entry,*self,item);
        }
        Ok(())
    }

    #[verus_verify]
    #[verus_spec(result => requires table_wf(self.constraints), parents_wf(self.items@),
        index < self.items@.len(), self.items@[index as int].constraint < self.constraints@.len(),
        crate::verify::search_exec::ids_valid(facade::graph(*self.language),self.constraints@,self.items@),edges_wf(*self),
        state_wf(*self),queue_order(*self),vocabulary_wf(*self,self.vocabulary@),
        ensures result matches SearchOutcome::Refuted(r)
            && r.constraint@ == self.constraints@[self.items@[index as int].constraint as int]
            && r.letters@.map_values(|l: Letter| l@) == letter_chain(self.items@, index as int).map_values(|l: Letter| l@)
            && r.alphabets@ == alphabet_chain(self.items@, self.alphabets@, index as int)
            && r.assignments@ == chain_assignments(r.letters@, r.alphabets@)
            && r.letters@.len() == r.alphabets@.len()
            && refutation_ready(result,*self.universes,self.vocabulary@))]
    fn counterexample(&self, index: usize) -> SearchOutcome {
        proof! {
            lemma_chain_correspondence(facade::graph(*self.language),self.constraints@,self.items@,
                self.alphabets@,index as int,depth(self.items@,index as int));
            reveal(refutation_ready);
            lemma_chain_ready(*self,index as int,self.constraints@[self.items@[index as int].constraint as int]);
            reveal(vocabulary_wf);
            lemma_letter_chain_len(self.items@,index as int);
        }
        let constraint = self.constraints.get(self.items[index].constraint).copy();
        let mut letters = Vec::new();
        let mut current = index;
        proof! { lemma_letter_chain_len(self.items@, index as int); }
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            current <= index, index < self.items@.len(), parents_wf(self.items@),
            letter_chain(self.items@, current as int).map_values(|l: Letter| l@)
                + letters@.map_values(|l: Letter| l@).reverse()
                == letter_chain(self.items@, index as int).map_values(|l: Letter| l@),
            decreases current))]
        while self.items[current].parent.is_some() {
            let (parent, letter) = match &self.items[current].parent {
                Some((parent, letter)) => (*parent, letter.copy()),
                None => unreachable!(),
            };
            letters.push(letter);
            proof! {
                assert(letter_chain(self.items@, current as int).map_values(|l: Letter| l@)
                    == letter_chain(self.items@, parent as int).map_values(|l: Letter| l@).push(letter@));
            }
            current = parent;
        }
        proof! { assert(letter_chain(self.items@, current as int) == Seq::<Letter>::empty()); }
        proof_decl! { let ghost backwards = letters@; let ghost start = index as int; }
        let count = letters.len();
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= count / 2, count == backwards.len(), letters@.len() == count,
            backwards.map_values(|l: Letter| l@).reverse()
                == letter_chain(self.items@, start).map_values(|l: Letter| l@),
            forall|i: int| 0 <= i < count ==> letters@[i]
                == backwards[if i < index || count - index <= i { count - 1 - i } else { i }],
            decreases count / 2 - index))]
        while index < count / 2 {
            let other = count - 1 - index;
            // The empty vectors allocate nothing; three verified swaps move each letter intact.
            let mut temporary = Letter {
                classes: Vec::new(),
                registers: Vec::new(),
            };
            letters.set_and_swap(index, &mut temporary);
            letters.set_and_swap(other, &mut temporary);
            letters.set_and_swap(index, &mut temporary);
            index += 1;
        }
        proof! {
            assert(letters@ =~= backwards.reverse());
            assert(letters@.map_values(|l: Letter| l@) =~= backwards.map_values(|l: Letter| l@).reverse());
            lemma_chain_assignments_views(letters@,letter_chain(self.items@,start),
                alphabet_chain(self.items@,self.alphabets@,start));
        }
        proof_decl! {
            let ghost returned_alphabets = alphabet_chain(self.items@, self.alphabets@, start);
            let ghost returned_assignments = chain_assignments(letter_chain(self.items@, start),
                returned_alphabets);
        }
        proof! {
            reveal(refutation_ready);reveal(vocabulary_wf);
            lemma_state_evidence(*self);
            lemma_chain_ready(*self,start,self.constraints@[self.items@[start].constraint as int]);
            assert(letters@.len() == returned_alphabets.len());
            assert(constraint@ == self.constraints@[self.items@[start].constraint as int]);
            assert(constraint_in_vocabulary(constraint@,self.vocabulary@));
            assert(constraint@.len() == self.universes@.len());
            assert(returned_assignments == chain_assignments(letters@,returned_alphabets));
            assert forall|k: int| 0 <= k < letters@.len() implies
                crate::verify::reconstruction::letter_coherent(constraint@,letters@[k]@,returned_alphabets[k])
                    && letter_numeric_codes(self.vocabulary@,*self.universes,letters@[k]@,returned_alphabets[k]) by {
                assert(letters@.map_values(|l: Letter| l@)[k] == letters@[k]@);
                assert(letter_chain(self.items@,start).map_values(|l: Letter| l@)[k] == letter_chain(self.items@,start)[k]@);
                assert(letters@[k]@ == letter_chain(self.items@,start)[k]@);
            }
        }
        SearchOutcome::Refuted(Box::new(Refutation {
            constraint,
            letters,
            #[cfg(verus_keep_ghost)]
            assignments: verus_exec_expr! { Ghost(returned_assignments) },
            #[cfg(verus_keep_ghost)]
            alphabets: verus_exec_expr! { Ghost(returned_alphabets) },
        }))
    }
}

#[verus_verify]
#[verus_spec(result => requires facade::language_wf(*old(language)),
    ensures facade::language_wf(*final(language)), facade::frame(*old(language), *final(language)),
        residual@ < facade::graph(*old(language)).regexes.len()
            && facade::residual_search_safe(*old(language),residual)
            ==> junco_core::verify::history_specs::no_internal_error(result),
        result matches Ok((t, atoms)) ==> (forall|arity: nat|
            1 <= arity <= history_syntax::MAX_ARITY
                && paper_search::atoms_bounded(facade::residual_primitives(*final(language),residual),arity)
                ==> atoms_wf(atoms@,arity))
            && paper_search::atoms_local(crate::verify::atom_set(atoms@))
            && facade::has_atoms(*final(language), t)
            && history_semantics::verify::finite_deriv::dbound(facade::graph(*final(language)), residual@, t@)
            && symbolic::derivative_correct(facade::graph(*final(language)), residual@, t)
            && facade::atom_ids(*final(language), t).len() == atoms@.len()
            && atoms@.len() + 63 <= usize::MAX
            && facade::atom_primitives(*final(language), t) == crate::verify::atom_set(atoms@)
            && paper_search::atoms_complete(facade::abs(*final(language), residual), crate::verify::atom_set(atoms@))
            && crate::verify::atom_set(atoms@).subset_of(facade::residual_primitives(*final(language),residual))
            && forall|i: int| 0 <= i < atoms@.len() ==> model::lift_test(facade::graph(*final(language)),
                facade::atom_ids(*final(language), t)[i]@) == model::Test::Atom(atoms@[i]@, true))]
fn derive_atoms(
    language: &mut SymbolicLanguage,
    residual: RegexId,
) -> Result<(TransitionId, Vec<Atom>), HistoryError> {
    let (transition, primitives) = language.derive(residual)?;
    proof! {
        facade::lemma_residual_vocabulary_frame(*old(language),*language,residual);
    }
    proof_decl! { let ghost original = primitives@; }
    // Validate first so the specified infallible collect can reuse the primitive allocation.
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        facade::language_wf(*language), facade::frame(*old(language), *language),
        index <= primitives@.len(),
        facade::residual_search_safe(*old(language),residual)
            ==> facade::residual_search_safe(*language,residual),
        primitives@.len() + 63 <= usize::MAX,
        facade::has_atoms(*language, transition),
        facade::atom_ids(*language, transition).len() == primitives@.len(),
        facade::atom_primitives(*language, transition)
            == primitives@.map_values(|p: Primitive| p@).to_set(),
        history_semantics::verify::finite_deriv::dbound(facade::graph(*language), residual@, transition@),
        symbolic::derivative_correct(facade::graph(*language), residual@, transition),
        paper_search::atoms_complete(facade::abs(*language, residual), facade::atom_primitives(*language, transition)),
        facade::atom_primitives(*language,transition).subset_of(facade::residual_primitives(*language,residual)),
        forall|i: int| 0 <= i < primitives@.len() ==> model::lift_test(facade::graph(*language),
            facade::atom_ids(*language, transition)[i]@) == model::Test::Atom(primitives@[i]@, true),
        forall|i: int| 0 <= i < index ==> atom_valid(primitives@[i]),
        decreases primitives@.len()-index))]
    while index < primitives.len() {
        proof! {
            if facade::residual_search_safe(*old(language),residual) {
                assert(primitives@.to_set().contains(primitives@[index as int]));
                primitives@.lemma_to_set_map_commutes(|p: Primitive| p@);
                assert(facade::atom_primitives(*language,transition).contains(primitives@[index as int]@));
                assert(atom_valid(primitives@[index as int]));
            }
        }
        validate_atom(primitives[index])?;
        index += 1;
    }
    let mapped_iter = primitives.into_iter().map(atom);
    proof_decl! { let ghost mapped = mapped_iter; }
    let atoms: Vec<Atom> = mapped_iter.collect();
    proof! {
        assert(mapped.obeys_prophetic_iter_laws());
        assert(mapped.will_return_none());
        assert(atoms@ == mapped.remaining());
        assert(atoms@.len() == original.len());
        assert forall|i: int| 0 <= i < atoms@.len() implies
            atoms@[i]@ == original[i]@ && atoms@[i].component <= u8::MAX by {}
    }
    proof! {
        assert(atoms@.map_values(|a: Atom| a@) =~= original.map_values(|p: Primitive| p@));
        atoms@.lemma_to_set_map_commutes(|a: Atom| a@);
        assert(crate::verify::atom_set(atoms@) =~= original.map_values(|p: Primitive| p@).to_set());
        assert forall|arity: nat| 1 <= arity <= history_syntax::MAX_ARITY
            && paper_search::atoms_bounded(facade::residual_primitives(*language,residual),arity)
            implies atoms_wf(atoms@,arity) by {
            assert forall|i: int| 0 <= i < atoms@.len() implies atoms@[i].component < arity by {
                assert(atoms@.to_set().contains(atoms@[i]));
                assert(crate::verify::atom_set(atoms@).contains(atoms@[i]@));
            }
        }
        assert forall|c: history_syntax::syntax::Component, c2: history_syntax::syntax::Component|
            crate::verify::atom_set(atoms@).contains(model::Primitive::Eq(c, model::GTerm::Variable(c2)))
            implies c == c2 by {
            let a = choose|a: Atom| atoms@.to_set().contains(a)
                && a@ == model::Primitive::Eq(c, model::GTerm::Variable(c2));
        }
    }
    Ok((transition, atoms))
}

#[verus_verify]
#[verus_spec(result => ensures result.is_ok() == atom_valid(primitive),
    atom_valid(primitive) ==> junco_core::verify::history_specs::no_internal_error(result))]
fn validate_atom(primitive: Primitive) -> Result<(), HistoryError> {
    let Primitive::Eq { field, term } = primitive;
    match term {
        Term::Constant(code) => {
            if code > u32::MAX as u64 {
                return Err(HistoryError::invariant(
                    "constant code is not a constant id",
                ));
            }
        }
        Term::Variable(component) => {
            if component != field {
                return Err(HistoryError::invariant(
                    "tail variable compared with another component",
                ));
            }
        }
    }
    Ok(())
}

/// The atom of a compiled primitive. Compiled tails encode each constant as its constant id, and
/// a tail variable names the candidate's value of its own component.
#[verus_verify]
#[verus_spec(result => requires atom_valid(primitive), ensures result.component <= u8::MAX
    && result@ == primitive@ && paper_search::atoms_local(Set::empty().insert(result@)))]
fn atom(primitive: Primitive) -> Atom {
    let Primitive::Eq { field, term } = primitive;
    let operand = match term {
        Term::Constant(code) => Operand::Constant(code as ConstId),
        Term::Variable(_) => Operand::Register,
    };
    Atom {
        component: field.index(),
        operand,
    }
}

/// Truth words of `atoms` under `letter`: bit `i % 64` of word `i / 64` is atom `i`.
#[verus_verify]
#[verus_spec(result => requires atoms_wf(atoms@,letter.classes@.len()),letter.classes@.len() == letter.registers@.len(),
    atoms@.len() + 63 <= usize::MAX,
    ensures truth_bits(atoms@, *letter, result.view()),
        symbolic::assignment_valid(atoms@.len(),result.view()))]
// vstd specifies `%` but not `is_multiple_of`.
#[allow(clippy::manual_is_multiple_of)]
fn truth(atoms: &[Atom], letter: &Letter) -> SmallVec<[u64; 2]> {
    let mut words: SmallVec<[u64; 2]> = SmallVec::new();
    let count = atoms.len() / 64 + if atoms.len() % 64 == 0 { 0 } else { 1 };
    words.resize(count, 0);
    proof! {
        facade::lemma_zero_truth_words(words.view(),atoms@.len());
        assert forall|j: nat| !symbolic::truth_word_bit(words.view(), j) by {
            if j / 64 < words.view().len() {
                let bit = (j % 64) as u32;
                assert(((0u64 >> bit) & 1u64) == 0) by(bit_vector);
            }
        }
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant
        atoms_wf(atoms@,letter.classes@.len()),letter.classes@.len() == letter.registers@.len(),index <= atoms@.len(),
        words.view().len() == (atoms@.len() + 63) / 64,
        atoms@.len() + 63 <= usize::MAX,
        symbolic::assignment_valid(atoms@.len(),words.view()),
        forall|i: int| 0 <= i < index ==> symbolic::truth_word_bit(words.view(), i as nat)
            == implementation::letter_holds(letter@, atoms@[i]@),
        forall|j: nat| index <= j ==> !symbolic::truth_word_bit(words.view(), j),
        decreases atoms@.len() - index))]
    while index < atoms.len() {
        if letter.holds(atoms[index]) {
            proof_decl! { let ghost before = words.view(); }
            let slice = words.as_mut_slice();
            proof! { assert(index / 64 < before.len()); }
            slice[index / 64] |= 1u64 << (index % 64);
            proof! { lemma_truth_set(before, words.view(), index as nat); }
            proof! { facade::lemma_assignment_set(atoms@.len(),before,words.view(),index as nat); }
        }
        index += 1;
    }
    words
}
