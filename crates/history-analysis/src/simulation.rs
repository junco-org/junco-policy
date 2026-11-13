//! Syntactic simulation between residuals: a sound under-approximation of language inclusion, cheap
//! to decide, that pruning uses in place of identity.
//!
//! `x ≤ y` holds when one of these rules derives it:
//!
//! - `x ≤ x`, `∅ ≤ y`, `x ≤ Σ*`, and `ε ≤ y` if `y` is nullable;
//! - a union lies below `y` if each of its members does, and `x` below a union if it lies below
//!   some member; an intersection lies below `y` if some member does, and `x` below an
//!   intersection if it lies below each member;
//! - `¬x ≤ ¬y` if `y ≤ x`;
//! - `x_1⋯x_n ≤ y_1⋯y_n` if `x_i ≤ y_i` for each `i`, and `x ≤ Σ*·y` and `x ≤ y·Σ*` if `x ≤ y`;
//! - `x* ≤ y*` and `x ≤ y*` if `x ≤ y`;
//! - between one-event tests, `φ ≤ ψ` if `φ = ψ`, `ψ` is `⊤`, `φ` is `⊥`, a disjunction `φ` has
//!   each disjunct below `ψ`, `φ` lies below each conjunct of a conjunction `ψ`, a conjunction `φ`
//!   has some conjunct below `ψ`, or `φ` lies below some disjunct of a disjunction `ψ`.
//!
//! Each rule is the monotonicity or antitonicity of an operator, or an inclusion that holds under
//! every valuation of the candidate, so `x ≤ y` implies that the language of `x` is included in
//! that of `y`. Every premise relates a pair of smaller nodes, so recursion on pairs, memoised,
//! decides the relation. It need not be transitive.

use history_store::native::NativeMap;
#[cfg(verus_keep_ghost)]
verus! { broadcast use junco_core::spec::hypotheses::internal_keys::group_internal_key_laws; }
#[cfg(verus_keep_ghost)]
use crate::verify::simulation_exec::*;
use history_semantics::SymbolicLanguage;
#[cfg(verus_keep_ghost)]
use history_semantics::symbolic_language_verify as facade;
#[cfg(verus_keep_ghost)]
use history_semantics::verify::refinement::pruning as paper;
#[cfg(verus_keep_ghost)]
use history_store::native::representatives;
use junco_core::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, RegexKindView, RegexView, TestId, TestView};
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
use smallvec::SmallVec;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec};

verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;

/// The simulation between the residuals of one language, memoised per pair.
pub(crate) struct Simulation {
    pub(crate) known: NativeMap<(RegexId, RegexId), bool>,
    pub(crate) known_tests: NativeMap<(TestId, TestId), bool>,
}

/// A residual's node, with its children copied out of the graph.
pub(crate) enum Node {
    Empty, All, Epsilon, Test(TestId), Union(SmallVec<[RegexId; 4]>),
    Concat(SmallVec<[RegexId; 4]>), Star(RegexId), Intersect(SmallVec<[RegexId; 4]>), Not(RegexId),
}

/// A test's node, with the children of a conjunction or disjunction copied out of the graph.
pub(crate) enum TestNode {
    True, False, Atom, And(SmallVec<[TestId; 4]>), Or(SmallVec<[TestId; 4]>),
}

impl Simulation {
    pub(crate) fn new() -> (s: Self)
        ensures forall|l: SymbolicLanguage| memo_wf(s, l),
            representatives(s.known) == Seq::empty(),
            representatives(s.known_tests) == Seq::empty(),
    {
        Self { known: NativeMap::new(), known_tests: NativeMap::new() }
    }

    /// Whether every member of `xs` lies below some member of `ys`, in increasing order.
    pub(crate) fn covered(&mut self, language: &mut SymbolicLanguage,
        xs: &[RegexId], ys: &[RegexId]) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            ids_valid(*old(language), xs@), ids_valid(*old(language), ys@),
            model::strictly_increasing(model::regex_ids(ys@)),
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), 2 * facade::graph(*old(language)).regexes.len()),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| #![trigger xs@[i]] 0 <= i < xs@.len()
                ==> index_range(xs@.len(), i) && (exists|j: int| 0 <= j < ys@.len()
                    && #[trigger] regex_le(*final(language), xs@[i], ys@[j])),
        decreases 1nat, 2 * facade::graph(*old(language)).regexes.len(), 3nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let ghost bound = 2 * facade::graph(*language).regexes.len();
        let ghost mut witnesses = Seq::<int>::empty();
        let mut index = 0;
        while index < xs.len()
            invariant index <= xs@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                bound == 2 * facade::graph(initial).regexes.len(),
                facade::language_wf(*language), memo_wf(*self, *language),
                ids_valid(*language, xs@), ids_valid(*language, ys@),
                model::strictly_increasing(model::regex_ids(ys@)),
                memo_grows(entry, *self, bound),
                witnesses.len() == index,
                forall|i: int| #![trigger witnesses[i]] #![trigger index_range(index as nat, i)]
                    0 <= i < index
                    ==> 0 <= witnesses[i] < ys@.len()
                        && regex_le(*language, xs@[i], ys@[witnesses[i]]),
            decreases xs@.len() - index,
        {
            let x = xs[index];
            let ghost mut witness = 0int;
            assert forall|i: int, j: int| 0 <= i < j < ys@.len() implies
                ys@[i].cmp_spec(&ys@[j]) is Less by {
                assert(model::regex_ids(ys@)[i] == ys@[i]@);
                assert(model::regex_ids(ys@)[j] == ys@[j]@);
            }
            proof { RegexId::lemma_obeys_cmp(); }
            let found = ys.binary_search(&x);
            if found.is_err() {
                let ghost before = *self;
                let covered = self.below_some(language, x, ys, Ghost(bound));
                proof { lemma_growth_trans(entry, before, *self, bound, bound); }
                if !covered? { return Ok(false); }
                proof {
                    witness = choose|j: int| 0 <= j < ys@.len()
                        && regex_le(*language, x, ys@[j]);
                }
            } else {
                let ghost j = found->Ok_0;
                assert(x@ == ys@[j as int]@);
                assert(regex_le(*language, x, ys@[j as int]));
                proof { witness = j as int; }
            }
            proof { witnesses = witnesses.push(witness); }
            index += 1;
        }
        assert forall|i: int| #![trigger xs@[i]] 0 <= i < xs@.len() implies
            index_range(xs@.len(), i) && (exists|j: int| 0 <= j < ys@.len()
                && #[trigger] regex_le(*language, xs@[i], ys@[j])) by {
            assert(index_range(index as nat, i));
            let j = witnesses[i];
            assert(0 <= j < ys@.len() && regex_le(*language, xs@[i], ys@[j]));
        }
        Ok(true)
    }

    /// Whether `x` ≤ `y`.
    pub(crate) fn le(&mut self, language: &mut SymbolicLanguage, x: RegexId, y: RegexId)
        -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            x@ < facade::graph(*old(language)).regexes.len(),
            y@ < facade::graph(*old(language)).regexes.len(),
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), x@ + y@ + 1),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> regex_le(*final(language), x, y),
        decreases 1nat, x@ + y@, 4nat,
    {
        let ghost entry = *self;
        if x == y { return Ok(true); }
        if let Some(known) = self.known.lookup(&(x, y)) {
            proof {
                if known {
                    let i = choose|i: int| 0 <= i < representatives(self.known).len()
                        && representatives(self.known)[i].1
                        && (x, y).eq_spec(&representatives(self.known)[i].0);
                    assert(regex_le(*language, x, y));
                }
            }
            return Ok(known);
        }
        let (left, _) = node(language, x)?;
        let (right, nullable) = node(language, y)?;
        let derived = self.derive(language, x, &left, &right, y, nullable)?;
        proof { lemma_regex_absent(entry, *self, x, y); }
        self.known.insert_fresh((x, y), derived);
        Ok(derived)
    }

    fn derive(&mut self, language: &mut SymbolicLanguage, x: RegexId, left: &Node,
        right: &Node, y: RegexId, nullable: bool) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            node_wf(*old(language), x, *left),
            node_wf(*old(language), y, *right),
            nullable == junco_core::verify::history_specs::nullable(facade::abs(*old(language), y)),
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), x@ + y@),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> regex_le(*final(language), x, y),
        decreases 1nat, x@ + y@, 3nat,
    {
        let ghost entry = *self;
        let ghost bound = x@ + y@;
        if matches!(left, Node::Empty) || matches!(right, Node::All)
            || matches!(left, Node::Epsilon) && nullable
        {
            proof { lemma_rule(*language, x, y); }
            return Ok(true);
        }
        if let Node::Union(members) = left {
            proof { lemma_lifts(*language, members.view()); }
            proof { lemma_regex_rank(members.view(), x@); }
            assert forall|i: int| 0 <= i < members.view().len() implies
                members.view()[i]@ + y@ < bound by { assert(members.view()[i]@ < x@); }
            let ghost before = *self;
            let checked = self.each_below(language, members, y, Ghost(bound));
            proof { lemma_growth_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof { lemma_rule(*language, x, y); }
                return Ok(true);
            }
        }
        if let Node::Intersect(members) = right {
            proof { lemma_lifts(*language, members.view()); }
            proof { lemma_regex_rank(members.view(), y@); }
            assert forall|i: int| 0 <= i < members.view().len() implies
                x@ + members.view()[i]@ < bound by { assert(members.view()[i]@ < y@); }
            let ghost before = *self;
            let checked = self.below_each(language, x, members, Ghost(bound));
            proof { lemma_growth_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof { lemma_rule(*language, x, y); }
                return Ok(true);
            }
        }
        if let Node::Union(members) = right {
            proof { lemma_lifts(*language, members.view()); }
            proof { lemma_regex_rank(members.view(), y@); }
            assert forall|i: int| 0 <= i < members.view().len() implies
                x@ + members.view()[i]@ < bound by { assert(members.view()[i]@ < y@); }
            let ghost before = *self;
            let checked = self.below_some(language, x, members, Ghost(bound));
            proof { lemma_growth_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof {
                    let i = choose|i: int| 0 <= i < members.view().len()
                        && regex_le(*language, x, members.view()[i]);
                    assert(facade::abs(*language, y) ==
                        junco_core::verify::history_specs::Regex::Union(lifts(*language, members.view())));
                    assert(paper::lang_le(facade::abs(*language, x),
                        lifts(*language, members.view())[i]));
                    lemma_regex_some(semantic_le(), semantic_tle(),
                        facade::abs(*language, x), facade::abs(*language, y),
                        lifts(*language, members.view()), i);
                    lemma_rule(*language, x, y);
                }
                return Ok(true);
            }
        }
        if let Node::Intersect(members) = left {
            proof { lemma_lifts(*language, members.view()); }
            proof { lemma_regex_rank(members.view(), x@); }
            assert forall|i: int| 0 <= i < members.view().len() implies
                members.view()[i]@ + y@ < bound by { assert(members.view()[i]@ < x@); }
            let ghost before = *self;
            let checked = self.some_below(language, members, y, Ghost(bound));
            proof { lemma_growth_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof {
                    let i = choose|i: int| 0 <= i < members.view().len()
                        && regex_le(*language, members.view()[i], y);
                    assert(facade::abs(*language, x) ==
                        junco_core::verify::history_specs::Regex::Intersect(lifts(*language, members.view())));
                    assert(paper::lang_le(lifts(*language, members.view())[i],
                        facade::abs(*language, y)));
                    lemma_regex_some(semantic_le(), semantic_tle(),
                        facade::abs(*language, x), facade::abs(*language, y),
                        lifts(*language, members.view()), i);
                    lemma_rule(*language, x, y);
                }
                return Ok(true);
            }
        }
        let checked = match (left, right) {
            (Node::Not(inner), Node::Not(outer)) => {
                let ghost before = *self;
                let checked = self.le(language, *outer, *inner);
                proof { lemma_growth_trans(entry, before, *self, (outer@ + inner@ + 1) as nat, bound); }
                checked?
            },
            (Node::Test(phi), Node::Test(psi)) => {
                let ghost before = *self;
                let checked = self.test_le(language, *phi, *psi);
                assert(memo_grows(before, *self, bound));
                proof { lemma_growth_trans(entry, before, *self, bound, bound); }
                checked?
            },
            (Node::Star(inner), Node::Star(outer)) => {
                let ghost before = *self;
                let checked = self.le(language, *inner, *outer);
                proof { lemma_growth_trans(entry, before, *self, (inner@ + outer@ + 1) as nat, bound); }
                if checked? { true } else {
                    let ghost before = *self;
                    let checked = self.le(language, x, *outer);
                    proof { lemma_growth_trans(entry, before, *self, (x@ + outer@ + 1) as nat, bound); }
                    checked?
                }
            },
            (_, Node::Star(outer)) => {
                let ghost before = *self;
                let checked = self.le(language, x, *outer);
                proof { lemma_growth_trans(entry, before, *self, (x@ + outer@ + 1) as nat, bound); }
                checked?
            },
            (_, Node::Concat(factors)) => {
                proof { lemma_lifts(*language, factors.view()); }
                proof { lemma_regex_rank(factors.view(), y@); }
                assert forall|i: int| 0 <= i < factors.view().len() implies
                    x@ + factors.view()[i]@ < bound by { assert(factors.view()[i]@ < y@); }
                let ghost before = *self;
                let checked = self.factors_le(language, x, left, factors, Ghost(bound));
                proof { lemma_growth_trans(entry, before, *self, bound, bound); }
                checked?
            },
            _ => false,
        };
        proof { if checked { lemma_rule(*language, x, y); } }
        Ok(checked)
    }

    /// Matches factors after dropping only universal padding at the ends.
    fn factors_le(&mut self, language: &mut SymbolicLanguage, x: RegexId, left: &Node,
        ys: &[RegexId], Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            node_wf(*old(language), x, *left),
            ids_valid(*old(language), ys@),
            forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> paper::cat_padded(semantic_le(),
                facade::abs(*final(language), x), lifts(*final(language), ys@)),
            result matches Ok(true) ==> paper::lang_le(facade::abs(*final(language), x),
                junco_core::verify::history_specs::Regex::Concat(lifts(*final(language), ys@))),
        decreases 1nat, bound, 2nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let single = [x];
        let xs: &[RegexId] = match left { Node::Concat(factors) => factors, _ => &single };
        proof { if let Node::Concat(factors) = left { lemma_lifts(*language, factors.view()); } }
        assert forall|i: int| 0 <= i < xs@.len() implies xs@[i]@ <= x@ by {
            match left {
                Node::Concat(factors) => {
                    assert(xs@ == factors.view());
                    lemma_regex_rank(factors.view(), x@);
                    assert(factors.view()[i]@ < x@);
                },
                _ => { assert(xs@[i] == x); },
            }
        }
        let Some(extra) = ys.len().checked_sub(xs.len()) else { return Ok(false); };
        let mut leading = 0;
        while leading < extra && is_all(language, ys[leading])?
            invariant leading <= extra, extra + xs@.len() == ys@.len(), *language == initial,
                entry == *old(self), initial == *old(language), *self == entry,
                memo_wf(*self, *language), memo_grows(entry, *self, bound),
                node_wf(*language, x, *left), ids_valid(*language, xs@),
                ids_valid(*language, ys@),
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ <= x@,
                forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
                lifts(*language, xs@) == match facade::abs(*language, x) {
                    junco_core::verify::history_specs::Regex::Concat(cs) => cs,
                    _ => seq![facade::abs(*language, x)],
                },
                facade::language_wf(*language),
                forall|i: int| 0 <= i < leading ==> lifts(*language, ys@)[i] is All,
            decreases extra - leading,
        { leading += 1; }
        let mut trailing = 0;
        while trailing < extra && is_all(language, ys[ys.len() - 1 - trailing])?
            invariant trailing <= extra, extra + xs@.len() == ys@.len(), *language == initial,
                entry == *old(self), initial == *old(language), *self == entry,
                memo_wf(*self, *language), memo_grows(entry, *self, bound),
                node_wf(*language, x, *left), ids_valid(*language, xs@),
                ids_valid(*language, ys@), leading <= extra,
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ <= x@,
                forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
                forall|i: int| 0 <= i < leading ==> lifts(*language, ys@)[i] is All,
                lifts(*language, xs@) == match facade::abs(*language, x) {
                    junco_core::verify::history_specs::Regex::Concat(cs) => cs,
                    _ => seq![facade::abs(*language, x)],
                },
                facade::language_wf(*language),
                forall|i: int| ys@.len() - trailing <= i < ys@.len()
                    ==> lifts(*language, ys@)[i] is All,
            decreases extra - trailing,
        { trailing += 1; }
        let mut front = 0;
        loop
            invariant front <= leading, leading <= extra, trailing <= extra,
                entry == *old(self), initial == *old(language),
                extra + xs@.len() == ys@.len(), *language == initial,
                facade::language_wf(*language), memo_wf(*self, *language),
                node_wf(*language, x, *left), ids_valid(*language, xs@), ids_valid(*language, ys@),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ <= x@,
                forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
                forall|i: int| 0 <= i < leading ==> lifts(*language, ys@)[i] is All,
                forall|i: int| ys@.len() - trailing <= i < ys@.len()
                    ==> lifts(*language, ys@)[i] is All,
                lifts(*language, xs@) == match facade::abs(*language, x) {
                    junco_core::verify::history_specs::Regex::Concat(cs) => cs,
                    _ => seq![facade::abs(*language, x)],
                },
            decreases leading - front,
        {
            let back = extra - front;
            if back <= trailing {
                let middle = &ys[front..ys.len() - back];
                let ghost before = *self;
                let checked = self.pointwise(language, xs, middle, Ghost(bound));
                proof { lemma_growth_trans(entry, before, *self, bound, bound); }
                if checked? {
                    assert(paper::padding_ok(lifts(*language, ys@), front as nat,
                        back as nat, xs@.len()));
                    assert forall|i: int| #![trigger lifts(*language, ys@)[front + i]]
                        0 <= i < xs@.len() implies
                        paper::lang_le(lifts(*language, xs@)[i],
                            lifts(*language, ys@)[front + i]) by {
                        assert(middle@[i] == ys@[front + i]);
                    }
                    proof { lemma_padding(semantic_le(), facade::abs(*language, x), lifts(*language, xs@),
                        lifts(*language, ys@), front as nat, back as nat); }
                    return Ok(true);
                }
            }
            if front == leading { break; }
            front += 1;
        }
        Ok(false)
    }

    fn pointwise(&mut self, language: &mut SymbolicLanguage, xs: &[RegexId], ys: &[RegexId],
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            ids_valid(*old(language), xs@), ids_valid(*old(language), ys@), xs@.len() == ys@.len(),
            forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + ys@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| 0 <= i < xs@.len() ==> regex_le(*final(language), xs@[i], ys@[i]),
        decreases 1nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < xs.len()
            invariant index <= xs@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                ids_valid(*language, xs@), ids_valid(*language, ys@), xs@.len() == ys@.len(),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + ys@[i]@ < bound,
                forall|i: int| 0 <= i < index ==> regex_le(*language, xs@[i], ys@[i]),
            decreases xs@.len() - index,
        {
            let a = xs[index];
            let b = ys[index];
            let ghost before = *self;
            let checked = self.le(language, a, b);
            proof { lemma_growth_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if !checked? { return Ok(false); }
            index += 1;
        }
        Ok(true)
    }

    fn each_below(&mut self, language: &mut SymbolicLanguage, xs: &[RegexId], y: RegexId,
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            ids_valid(*old(language), xs@), y@ < facade::graph(*old(language)).regexes.len(),
            forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + y@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| 0 <= i < xs@.len() ==> regex_le(*final(language), xs@[i], y),
        decreases 1nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < xs.len()
            invariant index <= xs@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                ids_valid(*language, xs@), y@ < facade::graph(*language).regexes.len(),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + y@ < bound,
                forall|i: int| 0 <= i < index ==> regex_le(*language, xs@[i], y),
            decreases xs@.len() - index,
        {
            let a = xs[index];
            let b = y;
            let ghost before = *self;
            let checked = self.le(language, a, b);
            proof { lemma_growth_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if !checked? { return Ok(false); }
            index += 1;
        }
        Ok(true)
    }

    fn below_each(&mut self, language: &mut SymbolicLanguage, x: RegexId, ys: &[RegexId],
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            x@ < facade::graph(*old(language)).regexes.len(), ids_valid(*old(language), ys@),
            forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| 0 <= i < ys@.len() ==> regex_le(*final(language), x, ys@[i]),
        decreases 1nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < ys.len()
            invariant index <= ys@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                x@ < facade::graph(*language).regexes.len(), ids_valid(*language, ys@),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
                forall|i: int| 0 <= i < index ==> regex_le(*language, x, ys@[i]),
            decreases ys@.len() - index,
        {
            let a = x;
            let b = ys[index];
            let ghost before = *self;
            let checked = self.le(language, a, b);
            proof { lemma_growth_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if !checked? { return Ok(false); }
            index += 1;
        }
        Ok(true)
    }

    fn some_below(&mut self, language: &mut SymbolicLanguage, xs: &[RegexId], y: RegexId,
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            ids_valid(*old(language), xs@), y@ < facade::graph(*old(language)).regexes.len(),
            forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + y@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> exists|i: int| 0 <= i < xs@.len() && regex_le(*final(language), xs@[i], y),
        decreases 1nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < xs.len()
            invariant index <= xs@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                ids_valid(*language, xs@), y@ < facade::graph(*language).regexes.len(),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < xs@.len() ==> xs@[i]@ + y@ < bound,

            decreases xs@.len() - index,
        {
            let a = xs[index];
            let b = y;
            let ghost before = *self;
            let checked = self.le(language, a, b);
            proof { lemma_growth_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if checked? { return Ok(true); }
            index += 1;
        }
        Ok(false)
    }

    fn below_some(&mut self, language: &mut SymbolicLanguage, x: RegexId, ys: &[RegexId],
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            x@ < facade::graph(*old(language)).regexes.len(), ids_valid(*old(language), ys@),
            forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        memo_grows(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> exists|i: int| 0 <= i < ys@.len() && regex_le(*final(language), x, ys@[i]),
        decreases 1nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < ys.len()
            invariant index <= ys@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                x@ < facade::graph(*language).regexes.len(), ids_valid(*language, ys@),
                memo_grows(entry, *self, bound),
                forall|i: int| 0 <= i < ys@.len() ==> x@ + ys@[i]@ < bound,

            decreases ys@.len() - index,
        {
            let a = x;
            let b = ys[index];
            let ghost before = *self;
            let checked = self.le(language, a, b);
            proof { lemma_growth_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if checked? { return Ok(true); }
            index += 1;
        }
        Ok(false)
    }

    /// Whether the one-event test implication is established by the syntactic rules.
    fn test_le(&mut self, language: &mut SymbolicLanguage, phi: TestId, psi: TestId)
        -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            phi@ < facade::graph(*old(language)).tests.len(),
            psi@ < facade::graph(*old(language)).tests.len(),
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), phi@ + psi@ + 1),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> test_le(*final(language), phi, psi),
        decreases 0nat, phi@ + psi@, 4nat,
    {
        let ghost entry = *self;
        if phi == psi { return Ok(true); }
        if let Some(known) = self.known_tests.lookup(&(phi, psi)) {
            proof {
                if known {
                    let i = choose|i: int| 0 <= i < representatives(self.known_tests).len()
                        && representatives(self.known_tests)[i].1
                        && (phi, psi).eq_spec(&representatives(self.known_tests)[i].0);
                    assert(test_le(*language, phi, psi));
                }
            }
            return Ok(known);
        }
        let left = test_node(language, phi)?;
        let right = test_node(language, psi)?;
        let checked = self.derive_test(language, phi, &left, &right, psi)?;
        proof { lemma_test_absent(entry, *self, phi, psi); }
        self.known_tests.insert_fresh((phi, psi), checked);
        Ok(checked)
    }

    fn derive_test(&mut self, language: &mut SymbolicLanguage, phi: TestId, left: &TestNode,
        right: &TestNode, psi: TestId) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            test_node_wf(*old(language), phi, *left),
            test_node_wf(*old(language), psi, *right),
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), phi@ + psi@),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> test_le(*final(language), phi, psi),
        decreases 0nat, phi@ + psi@, 3nat,
    {
        let ghost entry = *self;
        let ghost bound = phi@ + psi@;
        if matches!(right, TestNode::True) || matches!(left, TestNode::False) {
            proof { lemma_test_rule(*language, phi, psi); }
            return Ok(true);
        }
        if let TestNode::Or(children) = left {
            proof { lemma_test_rank(children.view(), phi@); }
            assert forall|i: int| 0 <= i < children.view().len() implies
                children.view()[i]@ + psi@ < bound by { assert(children.view()[i]@ < phi@); }
            let ghost before = *self;
            let checked = self.each_test_below(language, children, psi, Ghost(bound));
            proof { lemma_tests_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof { lemma_test_rule(*language, phi, psi); }
                return Ok(true);
            }
        }
        if let TestNode::And(children) = right {
            proof { lemma_test_rank(children.view(), psi@); }
            assert forall|i: int| 0 <= i < children.view().len() implies
                phi@ + children.view()[i]@ < bound by { assert(children.view()[i]@ < psi@); }
            let ghost before = *self;
            let checked = self.below_each_test(language, phi, children, Ghost(bound));
            proof { lemma_tests_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof { lemma_test_rule(*language, phi, psi); }
                return Ok(true);
            }
        }
        if let TestNode::And(children) = left {
            proof { lemma_test_rank(children.view(), phi@); }
            assert forall|i: int| 0 <= i < children.view().len() implies
                children.view()[i]@ + psi@ < bound by { assert(children.view()[i]@ < phi@); }
            let ghost before = *self;
            let checked = self.some_test_below(language, children, psi, Ghost(bound));
            proof { lemma_tests_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof {
                    let i = choose|i: int| 0 <= i < children.view().len()
                        && test_le(*language, children.view()[i], psi);
                    assert(model::lift_test(facade::graph(*language), phi@)
                        == model::Test::And(test_lifts(*language, children.view())));
                    assert(paper::test_le_sem(test_lifts(*language, children.view())[i],
                        model::lift_test(facade::graph(*language), psi@)));
                    lemma_test_some(semantic_tle(), model::lift_test(facade::graph(*language), phi@),
                        model::lift_test(facade::graph(*language), psi@),
                        test_lifts(*language, children.view()), i);
                    lemma_test_rule(*language, phi, psi);
                }
                return Ok(true);
            }
        }
        if let TestNode::Or(children) = right {
            proof { lemma_test_rank(children.view(), psi@); }
            assert forall|i: int| 0 <= i < children.view().len() implies
                phi@ + children.view()[i]@ < bound by { assert(children.view()[i]@ < psi@); }
            let ghost before = *self;
            let checked = self.below_some_test(language, phi, children, Ghost(bound));
            proof { lemma_tests_trans(entry, before, *self, bound, bound); }
            if checked? {
                proof {
                    let i = choose|i: int| 0 <= i < children.view().len()
                        && test_le(*language, phi, children.view()[i]);
                    assert(model::lift_test(facade::graph(*language), psi@)
                        == model::Test::Or(test_lifts(*language, children.view())));
                    assert(paper::test_le_sem(model::lift_test(facade::graph(*language), phi@),
                        test_lifts(*language, children.view())[i]));
                    lemma_test_some(semantic_tle(), model::lift_test(facade::graph(*language), phi@),
                        model::lift_test(facade::graph(*language), psi@),
                        test_lifts(*language, children.view()), i);
                    lemma_test_rule(*language, phi, psi);
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn each_test_below(&mut self, language: &mut SymbolicLanguage, phis: &[TestId], psi: TestId,
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            test_ids_valid(*old(language), phis@), psi@ < facade::graph(*old(language)).tests.len(),
            forall|i: int| 0 <= i < phis@.len() ==> phis@[i]@ + psi@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| 0 <= i < phis@.len() ==> test_le(*final(language), phis@[i], psi),
        decreases 0nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < phis.len()
            invariant index <= phis@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                test_ids_valid(*language, phis@), psi@ < facade::graph(*language).tests.len(), tests_grow(entry, *self, bound),
                forall|i: int| 0 <= i < phis@.len() ==> phis@[i]@ + psi@ < bound,
                forall|i: int| 0 <= i < index ==> test_le(*language, phis@[i], psi),
            decreases phis@.len() - index,
        {
            let a = phis[index];
            let b = psi;
            let ghost before = *self;
            let checked = self.test_le(language, a, b);
            proof { lemma_tests_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if !checked? { return Ok(false); }
            index += 1;
        }
        Ok(true)
    }

    fn below_each_test(&mut self, language: &mut SymbolicLanguage, phi: TestId, psis: &[TestId],
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            phi@ < facade::graph(*old(language)).tests.len(), test_ids_valid(*old(language), psis@),
            forall|i: int| 0 <= i < psis@.len() ==> phi@ + psis@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> forall|i: int| 0 <= i < psis@.len() ==> test_le(*final(language), phi, psis@[i]),
        decreases 0nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < psis.len()
            invariant index <= psis@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                phi@ < facade::graph(*language).tests.len(), test_ids_valid(*language, psis@), tests_grow(entry, *self, bound),
                forall|i: int| 0 <= i < psis@.len() ==> phi@ + psis@[i]@ < bound,
                forall|i: int| 0 <= i < index ==> test_le(*language, phi, psis@[i]),
            decreases psis@.len() - index,
        {
            let a = phi;
            let b = psis[index];
            let ghost before = *self;
            let checked = self.test_le(language, a, b);
            proof { lemma_tests_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if !checked? { return Ok(false); }
            index += 1;
        }
        Ok(true)
    }

    fn some_test_below(&mut self, language: &mut SymbolicLanguage, phis: &[TestId], psi: TestId,
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            test_ids_valid(*old(language), phis@), psi@ < facade::graph(*old(language)).tests.len(),
            forall|i: int| 0 <= i < phis@.len() ==> phis@[i]@ + psi@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> exists|i: int| 0 <= i < phis@.len() && test_le(*final(language), phis@[i], psi),
        decreases 0nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < phis.len()
            invariant index <= phis@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                test_ids_valid(*language, phis@), psi@ < facade::graph(*language).tests.len(), tests_grow(entry, *self, bound),
                forall|i: int| 0 <= i < phis@.len() ==> phis@[i]@ + psi@ < bound,

            decreases phis@.len() - index,
        {
            let a = phis[index];
            let b = psi;
            let ghost before = *self;
            let checked = self.test_le(language, a, b);
            proof { lemma_tests_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if checked? { return Ok(true); }
            index += 1;
        }
        Ok(false)
    }

    fn below_some_test(&mut self, language: &mut SymbolicLanguage, phi: TestId, psis: &[TestId],
        Ghost(bound): Ghost<nat>) -> (result: Result<bool, HistoryError>)
        requires facade::language_wf(*old(language)), memo_wf(*old(self), *old(language)),
            phi@ < facade::graph(*old(language)).tests.len(), test_ids_valid(*old(language), psis@),
            forall|i: int| 0 <= i < psis@.len() ==> phi@ + psis@[i]@ < bound,
        ensures
        *final(language) == *old(language), memo_wf(*final(self), *final(language)),
        tests_grow(*old(self), *final(self), bound),
        junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Ok(true) ==> exists|i: int| 0 <= i < psis@.len() && test_le(*final(language), phi, psis@[i]),
        decreases 0nat, bound, 1nat,
    {
        let ghost entry = *self;
        let ghost initial = *language;
        let mut index = 0;
        while index < psis.len()
            invariant index <= psis@.len(), *language == initial,
                entry == *old(self), initial == *old(language),
                facade::language_wf(*language), memo_wf(*self, *language),
                phi@ < facade::graph(*language).tests.len(), test_ids_valid(*language, psis@), tests_grow(entry, *self, bound),
                forall|i: int| 0 <= i < psis@.len() ==> phi@ + psis@[i]@ < bound,

            decreases psis@.len() - index,
        {
            let a = phi;
            let b = psis[index];
            let ghost before = *self;
            let checked = self.test_le(language, a, b);
            proof { lemma_tests_trans(entry, before, *self, (a@ + b@ + 1) as nat, bound); }
            if checked? { return Ok(true); }
            index += 1;
        }
        Ok(false)
    }
}

fn copy_regex_ids(ids: &[RegexId]) -> (copied: SmallVec<[RegexId; 4]>)
    ensures copied.view() == ids@,
{
    let mut copied = SmallVec::new();
    copied.extend_from_slice(ids);
    copied
}

fn copy_test_ids(ids: &[TestId]) -> (copied: SmallVec<[TestId; 4]>)
    ensures copied.view() == ids@,
{
    let mut copied = SmallVec::new();
    copied.extend_from_slice(ids);
    copied
}

fn node(language: &mut SymbolicLanguage, id: RegexId) -> (result: Result<(Node, bool), HistoryError>)
    requires facade::language_wf(*old(language)),
    ensures *final(language) == *old(language),
        id@ < facade::graph(*final(language)).regexes.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Ok((n, nullable)) ==> node_wf(*final(language), id, n)
            && nullable == junco_core::verify::history_specs::nullable(facade::abs(*final(language), id)),
{
    let result = language.read_regex(id, |view: RegexView<'_>| -> (copied: (Node, bool))
        ensures copied.0@ == view.kind@, copied.1 == view.nullable,
    {
        let n = match view.kind {
            RegexKindView::Empty => Node::Empty,
            RegexKindView::All => Node::All,
            RegexKindView::Epsilon => Node::Epsilon,
            RegexKindView::Test(t) => Node::Test(t),
            RegexKindView::Union(cs) => Node::Union(copy_regex_ids(cs)),
            RegexKindView::Concat(cs) => Node::Concat(copy_regex_ids(cs)),
            RegexKindView::Star(r) => Node::Star(r),
            RegexKindView::Intersect(cs) => Node::Intersect(copy_regex_ids(cs)),
            RegexKindView::Not(r) => Node::Not(r),
        };
        (n, view.nullable)
    });
    proof { if let Ok((n, _)) = &result { lemma_node(*language, id, *n); } }
    result
}

fn is_all(language: &mut SymbolicLanguage, id: RegexId) -> (result: Result<bool, HistoryError>)
    requires facade::language_wf(*old(language)),
    ensures *final(language) == *old(language),
        id@ < facade::graph(*final(language)).regexes.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Ok(true) ==> facade::abs(*final(language), id) is All,
{
    let result = language.read_regex(id, |view: RegexView<'_>| -> (all: bool)
        ensures all == (view.kind@ is All),
    { matches!(view.kind, RegexKindView::All) });
    proof {
        if let Ok(true) = result {
            facade::lemma_language_wf(*language);
            history_semantics::normalize_verify::regex_unfold(facade::graph(*language), id@);
        }
    }
    result
}

fn test_node(language: &mut SymbolicLanguage, id: TestId)
    -> (result: Result<TestNode, HistoryError>)
    requires facade::language_wf(*old(language)),
    ensures *final(language) == *old(language),
        id@ < facade::graph(*final(language)).tests.len()
            ==> junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Ok(n) ==> test_node_wf(*final(language), id, n),
{
    let result = language.read_test(id, |view: TestView<'_>| -> (n: TestNode)
        ensures test_matches(n, view@),
    {
        match view {
            TestView::True => TestNode::True,
            TestView::False => TestNode::False,
            TestView::Atom { .. } => TestNode::Atom,
            TestView::And(cs) => TestNode::And(copy_test_ids(cs)),
            TestView::Or(cs) => TestNode::Or(copy_test_ids(cs)),
        }
    });
    proof { if let Ok(n) = &result { lemma_test_node(*language, id, *n); } }
    result
}
}
