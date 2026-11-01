//! The inclusion search: items, unfolding, successors, pruning, and breadth-first exploration.

use std::collections::VecDeque;
use std::rc::Rc;

use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;

use super::super::component::CompiledAtomPattern;
use super::super::node::{RegexId, RegexKind};
use super::super::store::CanonicalStore;
use super::constraint::{Constraint, ConstraintId, ConstraintTable, Letter, steps};
use super::residual::Residuals;
use super::simple::Expressions;
use super::simulation::Simulation;
use super::term::{Derivatives, Term};
use super::{SearchOptions, SearchStats, Strategy, Subsumption};

/// Result of one inclusion search.
pub(super) enum SearchOutcome<'arena> {
    /// Inclusion holds under the initial constraint.
    Holds,
    /// A counterexample exists.
    Refuted(Box<Refutation<'arena>>),
    /// The search inserted more items than the configured budget allows.
    Exhausted,
}

/// A symbolic counterexample: any valuation satisfying `constraint`, with one event from each
/// letter in order.
pub(super) struct Refutation<'arena> {
    pub(super) constraint: Constraint<'arena>,
    pub(super) letters: Vec<Letter<'arena>>,
}

/// Persistent derivative, residual, simulation and expression caches, reused across searches over
/// one store.
#[derive(Default)]
pub(super) struct InclusionEngine<'arena> {
    residuals: Residuals<'arena>,
    derivatives: Derivatives<'arena>,
    simulation: Simulation<'arena>,
    expressions: Expressions<'arena>,
}

impl<'arena> InclusionEngine<'arena> {
    /// Decides `left ⊑_constraint right`.
    pub(super) fn includes(
        &mut self,
        store: &mut CanonicalStore<'arena>,
        constraint: Constraint<'arena>,
        left: RegexId<'arena>,
        right: RegexId<'arena>,
        options: SearchOptions,
        stats: &mut SearchStats,
    ) -> SearchOutcome<'arena> {
        stats.searches += 1;
        match options.strategy {
            Strategy::Residual => {
                return self
                    .residuals
                    .includes(store, constraint, left, right, options, stats);
            }
            Strategy::Simple => {
                return self
                    .expressions
                    .includes(constraint, left, right, options, stats);
            }
            Strategy::Antichain | Strategy::Brzozowski => {}
        }
        let mut search = Search {
            engine: self,
            store,
            options,
            stats,
            constraints: ConstraintTable::default(),
            nodes: Vec::new(),
            seen: HashSet::new(),
            visited: Vec::new(),
            index: VisitedIndex::default(),
            queue: VecDeque::new(),
        };
        search.run(constraint, left, right)
    }
}

/// Search state: the case splits made so far, positive terms, and macrostates.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Item<'arena> {
    constraint: ConstraintId,
    positive: Box<[Term<'arena>]>,
    negative: Box<[Box<[Term<'arena>]>]>,
}

/// Inserted item with its parent link for counterexample reconstruction.
struct Node<'arena> {
    item: Item<'arena>,
    parent: Option<(usize, Letter<'arena>)>,
    /// Cleared when pruning removes the item from the visited set and queue.
    live: bool,
}

/// Item under construction: unordered terms and macrostates.
struct Draft<'arena> {
    positive: Vec<Term<'arena>>,
    negative: Vec<Vec<Term<'arena>>>,
}

struct Search<'search, 'arena> {
    engine: &'search mut InclusionEngine<'arena>,
    store: &'search mut CanonicalStore<'arena>,
    options: SearchOptions,
    stats: &'search mut SearchStats,
    constraints: ConstraintTable<'arena>,
    nodes: Vec<Node<'arena>>,
    /// Every item ever inserted, including pruned ones.
    seen: HashSet<Item<'arena>>,
    /// Live inserted items: an antichain up to subsumption.
    visited: Vec<usize>,
    /// Index of inserted items by the terms they mention, to find subsuming items.
    index: VisitedIndex<'arena>,
    queue: VecDeque<usize>,
}

impl<'arena> Search<'_, 'arena> {
    fn run(
        &mut self,
        constraint: Constraint<'arena>,
        left: RegexId<'arena>,
        right: RegexId<'arena>,
    ) -> SearchOutcome<'arena> {
        let constraint = self.constraints.intern(constraint);
        for draft in self.initial(left, right) {
            if let Some(item) = self.finish(constraint, draft) {
                self.insert(item, None);
            }
        }
        while let Some(index) = self.queue.pop_front() {
            if !self.nodes[index].live {
                continue;
            }
            if self.accepting(&self.nodes[index].item) {
                return self.counterexample(index);
            }
            if self
                .options
                .max_items
                .is_some_and(|budget| self.nodes.len() > budget)
            {
                return SearchOutcome::Exhausted;
            }
            self.expand(index);
        }
        SearchOutcome::Holds
    }

    /// Initial items: `({β left}, {{β right}})` unfolded, or one block for `left ∩ ¬right`.
    fn initial(&mut self, left: RegexId<'arena>, right: RegexId<'arena>) -> Vec<Draft<'arena>> {
        match self.options.strategy {
            Strategy::Brzozowski => {
                let complement = self.store.regex_not(right);
                let difference = self.store.regex_intersect([left, complement]);
                let epsilon = self.store.epsilon;
                Term::blocked(self.store, difference, epsilon)
                    .map(|term| Draft {
                        positive: vec![term],
                        negative: Vec::new(),
                    })
                    .into_iter()
                    .collect()
            }
            Strategy::Antichain => self.unfold(Draft {
                positive: vec![Term::regex(left)],
                negative: vec![vec![Term::regex(right)]],
            }),
            Strategy::Residual | Strategy::Simple => {
                unreachable!("residual and simple searches run in their own engines")
            }
        }
    }

    /// Applies the unfolding rules (U1)–(U6) to top-level unions, intersections and complements.
    fn unfold(&mut self, draft: Draft<'arena>) -> Vec<Draft<'arena>> {
        let mut pending = vec![draft];
        let mut done = Vec::new();
        while let Some(mut draft) = pending.pop() {
            if let Some(position) = draft
                .positive
                .iter()
                .position(|term| term.block.is_none() && is_boolean(term.rest))
            {
                let term = draft.positive.swap_remove(position);
                match term.rest.get().kind {
                    // (U1) a positive intersection is several positive obligations.
                    RegexKind::Intersect(children) => {
                        draft
                            .positive
                            .extend(children.iter().map(|child| Term::regex(*child)));
                        pending.push(draft);
                    }
                    // (U2) a positive complement is a negative obligation.
                    RegexKind::Not(inner) => {
                        draft.negative.push(vec![Term::regex(inner)]);
                        pending.push(draft);
                    }
                    // (U5) a positive union is a choice between items.
                    RegexKind::Union(children) => {
                        for child in children {
                            let mut positive = draft.positive.clone();
                            positive.push(Term::regex(*child));
                            pending.push(Draft {
                                positive,
                                negative: draft.negative.clone(),
                            });
                        }
                    }
                    _ => unreachable!("only Boolean roots are unfolded"),
                }
                continue;
            }
            let found = draft
                .negative
                .iter()
                .enumerate()
                .find_map(|(index, macrostate)| {
                    macrostate
                        .iter()
                        .position(|term| term.block.is_none() && is_boolean(term.rest))
                        .map(|position| (index, position))
                });
            let Some((index, position)) = found else {
                done.push(draft);
                continue;
            };
            let term = draft.negative[index].swap_remove(position);
            match term.rest.get().kind {
                // (U3) avoiding a complement means matching its operand.
                RegexKind::Not(inner) => {
                    draft.positive.push(Term::regex(inner));
                    pending.push(draft);
                }
                // (U4) avoiding an intersection means avoiding one of its operands.
                RegexKind::Intersect(children) => {
                    for child in children {
                        let mut negative = draft.negative.clone();
                        negative[index].push(Term::regex(*child));
                        pending.push(Draft {
                            positive: draft.positive.clone(),
                            negative,
                        });
                    }
                }
                // (U6) avoiding a union means avoiding each operand.
                RegexKind::Union(children) => {
                    draft.negative[index].extend(children.iter().map(|child| Term::regex(*child)));
                    pending.push(draft);
                }
                _ => unreachable!("only Boolean roots are unfolded"),
            }
        }
        done
    }

    /// Normalizes a draft into an item, or `None` if it is dead; then reduces it.
    fn finish(&mut self, constraint: ConstraintId, draft: Draft<'arena>) -> Option<Item<'arena>> {
        let Draft {
            mut positive,
            negative,
        } = draft;
        let store = &*self.store;
        if positive.iter().any(|term| term.is_empty(store)) {
            self.stats.dead += 1;
            return None;
        }
        positive.sort_unstable();
        positive.dedup();
        let mut macrostates = Vec::with_capacity(negative.len());
        for mut macrostate in negative {
            // Avoiding `∅` imposes nothing; an empty macrostate imposes nothing at all.
            macrostate.retain(|term| !term.is_empty(store));
            if macrostate.is_empty() {
                continue;
            }
            if macrostate.iter().any(|term| term.is_universal(store)) {
                self.stats.dead += 1;
                return None;
            }
            macrostate.sort_unstable();
            macrostate.dedup();
            macrostates.push(macrostate);
        }
        let mut order = Order {
            simulation: &mut self.engine.simulation,
            subsumption: self.options.subsumption,
            constraints: &mut self.constraints,
        };
        if positive
            .iter()
            .any(|p| macrostates.iter().flatten().any(|n| order.le(*p, *n)))
        {
            self.stats.dead += 1;
            return None;
        }
        Some(order.reduce(constraint, positive, macrostates))
    }

    fn insert(&mut self, item: Item<'arena>, parent: Option<(usize, Letter<'arena>)>) {
        if self.seen.contains(&item) {
            self.stats.repeated += 1;
            return;
        }
        let mut order = Order {
            simulation: &mut self.engine.simulation,
            subsumption: self.options.subsumption,
            constraints: &mut self.constraints,
        };
        let nodes = &mut self.nodes;
        let subsumed = self
            .index
            .candidates(&item, &mut order)
            .into_iter()
            .any(|other| nodes[other].live && order.subsumed(&item, &nodes[other].item));
        if subsumed {
            self.stats.subsumed += 1;
            return;
        }
        if self.options.prune_visited {
            let before = self.visited.len();
            self.visited.retain(|other| {
                let keep = !order.subsumed(&nodes[*other].item, &item);
                if !keep {
                    nodes[*other].live = false;
                }
                keep
            });
            self.stats.pruned += before - self.visited.len();
        }
        let index = self.nodes.len();
        self.seen.insert(item.clone());
        self.nodes.push(Node {
            item,
            parent,
            live: true,
        });
        self.visited.push(index);
        self.index.add(index, &self.nodes[index].item);
        self.queue.push_back(index);
        self.stats.inserted += 1;
    }
    fn accepting(&self, item: &Item<'arena>) -> bool {
        item.positive.iter().all(|term| term.nullable())
            && item.negative.iter().flatten().all(|term| !term.nullable())
    }

    fn expand(&mut self, index: usize) {
        self.stats.expanded += 1;
        let item = self.nodes[index].item.clone();
        let atoms = self.first_atoms(&item);
        self.stats.assignments = self
            .stats
            .assignments
            .saturating_add(1_u64.checked_shl(atoms.len() as u32).unwrap_or(u64::MAX));
        let constraint = self.constraints.get(item.constraint).clone();
        for (refined, letters) in steps(&constraint, &atoms, self.options.alphabet) {
            let refined = self.constraints.intern(refined);
            for letter in letters {
                self.stats.steps += 1;
                self.successors(index, &item, refined, letter);
            }
        }
    }

    /// `fst(I)`: the atoms that the derivatives of the item's terms evaluate.
    fn first_atoms(&mut self, item: &Item<'arena>) -> Vec<CompiledAtomPattern<'arena>> {
        let mut atoms = Vec::new();
        for term in item.positive.iter().chain(item.negative.iter().flatten()) {
            atoms.extend(
                self.engine
                    .derivatives
                    .first(self.store, *term)
                    .iter()
                    .copied(),
            );
        }
        super::term::distinct(atoms).to_vec()
    }

    fn successors(
        &mut self,
        parent: usize,
        item: &Item<'arena>,
        constraint: ConstraintId,
        letter: Letter<'arena>,
    ) {
        let mut choices: SmallVec<[Rc<[Term<'arena>]>; 4]> = SmallVec::new();
        for term in &item.positive {
            let derivatives = self.engine.derivatives.partial(self.store, *term, &letter);
            if derivatives.is_empty() {
                return;
            }
            choices.push(derivatives);
        }
        let mut negative = Vec::with_capacity(item.negative.len());
        for macrostate in &item.negative {
            let mut next = Vec::new();
            for term in macrostate {
                next.extend(
                    self.engine
                        .derivatives
                        .partial(self.store, *term, &letter)
                        .iter()
                        .copied(),
                );
            }
            if next.iter().any(|term| term.is_universal(self.store)) {
                // Every successor on this step avoids nothing, so all of them are dead.
                self.stats.dead += 1;
                return;
            }
            negative.push(next);
        }
        let mut selection = vec![0_usize; choices.len()];
        loop {
            let positive = choices
                .iter()
                .zip(&selection)
                .map(|(options, chosen)| options[*chosen])
                .collect();
            self.stats.generated += 1;
            if let Some(successor) = self.finish(
                constraint,
                Draft {
                    positive,
                    negative: negative.clone(),
                },
            ) {
                self.insert(successor, Some((parent, letter)));
            }
            // Advance the mixed-radix counter over positive choices.
            let mut position = 0;
            loop {
                if position == selection.len() {
                    return;
                }
                selection[position] += 1;
                if selection[position] < choices[position].len() {
                    break;
                }
                selection[position] = 0;
                position += 1;
            }
        }
    }

    fn counterexample(&self, index: usize) -> SearchOutcome<'arena> {
        let constraint = self
            .constraints
            .get(self.nodes[index].item.constraint)
            .clone();
        let mut letters = Vec::new();
        let mut current = index;
        while let Some((parent, letter)) = self.nodes[current].parent {
            letters.push(letter);
            current = parent;
        }
        letters.reverse();
        SearchOutcome::Refuted(Box::new(Refutation {
            constraint,
            letters,
        }))
    }
}

/// The term relation `⪯` and the subsumption order it induces on items.
struct Order<'order, 'arena> {
    simulation: &'order mut Simulation<'arena>,
    subsumption: Subsumption,
    constraints: &'order mut ConstraintTable<'arena>,
}

impl<'arena> Order<'_, 'arena> {
    fn le(&mut self, left: Term<'arena>, right: Term<'arena>) -> bool {
        match self.subsumption {
            Subsumption::Identity => left == right,
            Subsumption::Implication => self.simulation.term_le(left, right),
        }
    }

    /// Whether every term of `covered` is simulated by some term of `cover`.
    fn covers(&mut self, cover: &[Term<'arena>], covered: &[Term<'arena>]) -> bool {
        covered
            .iter()
            .all(|term| cover.iter().any(|other| self.le(*term, *other)))
    }

    fn entails(&mut self, left: ConstraintId, right: ConstraintId) -> bool {
        self.constraints.entails(left, right)
    }

    /// `small ⊴ large`: every witness of `small` is a witness of `large`.
    fn subsumed(&mut self, small: &Item<'arena>, large: &Item<'arena>) -> bool {
        self.entails(small.constraint, large.constraint)
            && large
                .positive
                .iter()
                .all(|q| small.positive.iter().any(|p| self.le(*p, *q)))
            && large.negative.iter().all(|wide| {
                small
                    .negative
                    .iter()
                    .any(|narrow| self.covers(narrow, wide))
            })
    }

    /// Drops positive terms implied by retained ones, and negative terms and macrostates covered
    /// by retained ones.
    fn reduce(
        &mut self,
        constraint: ConstraintId,
        positive: Vec<Term<'arena>>,
        macrostates: Vec<Vec<Term<'arena>>>,
    ) -> Item<'arena> {
        let mut kept_positive: Vec<Term<'arena>> = Vec::with_capacity(positive.len());
        for term in positive {
            if !kept_positive.iter().any(|kept| self.le(*kept, term)) {
                kept_positive.push(term);
            }
        }
        let mut reduced = Vec::with_capacity(macrostates.len());
        for macrostate in macrostates {
            let mut kept: Vec<Term<'arena>> = Vec::with_capacity(macrostate.len());
            for term in macrostate {
                if !kept.iter().any(|other| self.le(term, *other)) {
                    kept.push(term);
                }
            }
            kept.sort_unstable();
            reduced.push(kept);
        }
        // Larger macrostates first, so that they can cover the smaller ones.
        reduced.sort_by(|left, right| right.len().cmp(&left.len()).then_with(|| left.cmp(right)));
        let mut kept_negative: Vec<Vec<Term<'arena>>> = Vec::with_capacity(reduced.len());
        for macrostate in reduced {
            if !kept_negative
                .iter()
                .any(|other| self.covers(other, &macrostate))
            {
                kept_negative.push(macrostate);
            }
        }
        kept_positive.sort_unstable();
        kept_negative.sort_unstable();
        Item {
            constraint,
            positive: kept_positive.into_boxed_slice(),
            negative: kept_negative
                .into_iter()
                .map(Vec::into_boxed_slice)
                .collect(),
        }
    }
}

/// Whether a regex has a Boolean root that unfolding moves between the sides of an item.
fn is_boolean(regex: RegexId<'_>) -> bool {
    matches!(
        regex.get().kind,
        RegexKind::Union(_) | RegexKind::Intersect(_) | RegexKind::Not(_)
    )
}

/// Inserted items grouped by positive set.
///
/// If `item ⊴ other`, every positive term of `other` lies above some positive term of `item`. Only
/// groups whose positive set passes that test can hold items that subsume `item`; under identity,
/// these are the groups keyed by subsets of `item`'s positive set.
#[derive(Default)]
struct VisitedIndex<'arena> {
    groups: HashMap<Box<[Term<'arena>]>, Vec<usize>>,
}

impl<'arena> VisitedIndex<'arena> {
    fn add(&mut self, index: usize, item: &Item<'arena>) {
        self.groups
            .entry(item.positive.clone())
            .or_default()
            .push(index);
    }

    /// Inserted items whose positive sets allow them to subsume `item`.
    fn candidates(&self, item: &Item<'arena>, order: &mut Order<'_, 'arena>) -> Vec<usize> {
        let positive = &item.positive;
        let mut candidates = Vec::new();
        if order.subsumption == Subsumption::Identity && positive.len() < ENUMERATED_SUBSETS_BELOW {
            let mut subset = Vec::with_capacity(positive.len());
            for mask in 0..1_usize << positive.len() {
                subset.clear();
                subset.extend(
                    (0..positive.len())
                        .filter(|bit| mask & (1 << bit) != 0)
                        .map(|bit| positive[bit]),
                );
                if let Some(group) = self.groups.get(subset.as_slice()) {
                    candidates.extend_from_slice(group);
                }
            }
        } else {
            for (key, group) in &self.groups {
                if key
                    .iter()
                    .all(|theirs| positive.iter().any(|mine| order.le(*mine, *theirs)))
                {
                    candidates.extend_from_slice(group);
                }
            }
        }
        candidates
    }
}

/// Positive sets smaller than this have their subsets enumerated rather than every group scanned.
const ENUMERATED_SUBSETS_BELOW: usize = 8;
