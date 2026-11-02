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
//! - between one-event tests, `φ ≤ ψ` if `ψ` is `⊤`, `φ` is `⊥`, every conjunct of `ψ` is one of
//!   `φ`, or every disjunct of `φ` is one of `ψ`.
//!
//! Each rule is the monotonicity or antitonicity of an operator, or an inclusion that holds under
//! every valuation of the candidate, so `x ≤ y` implies that the language of `x` is included in
//! that of `y`. Every premise relates a pair of smaller nodes, so recursion on pairs, memoised,
//! decides the relation. It need not be transitive.

use hashbrown::HashMap;
use history_semantics::SymbolicLanguage;
use junco_core::HistoryError;
use junco_core::kernel::{RegexId, RegexKindView, TestId, TestView};
use smallvec::{SmallVec, smallvec};

/// The simulation between the residuals of one language, memoised per pair.
#[derive(Default)]
pub(crate) struct Simulation {
    known: HashMap<(RegexId, RegexId), bool>,
}

/// A residual's node, with its children copied out of the graph.
enum Node {
    Empty,
    All,
    Epsilon,
    Test(TestId),
    Union(SmallVec<[RegexId; 4]>),
    Concat(SmallVec<[RegexId; 4]>),
    Star(RegexId),
    Intersect(SmallVec<[RegexId; 4]>),
    Not(RegexId),
}

/// A test's node, with the children of a conjunction or disjunction in increasing order.
enum TestNode {
    True,
    False,
    Atom,
    And(SmallVec<[TestId; 4]>),
    Or(SmallVec<[TestId; 4]>),
}

impl Simulation {
    /// Whether every member of `xs` lies below some member of `ys`, which is in increasing order.
    pub(crate) fn covered(
        &mut self,
        language: &mut SymbolicLanguage,
        xs: &[RegexId],
        ys: &[RegexId],
    ) -> Result<bool, HistoryError> {
        for &x in xs {
            if ys.binary_search(&x).is_err() && !self.below_some(language, x, ys)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Whether `x ≤ y`.
    pub(crate) fn le(
        &mut self,
        language: &mut SymbolicLanguage,
        x: RegexId,
        y: RegexId,
    ) -> Result<bool, HistoryError> {
        if x == y {
            return Ok(true);
        }
        if let Some(known) = self.known.get(&(x, y)) {
            return Ok(*known);
        }
        let (left, _) = node(language, x)?;
        let (right, nullable) = node(language, y)?;
        let result = self.derive(language, x, &left, &right, y, nullable)?;
        self.known.insert((x, y), result);
        Ok(result)
    }

    fn derive(
        &mut self,
        language: &mut SymbolicLanguage,
        x: RegexId,
        left: &Node,
        right: &Node,
        y: RegexId,
        nullable: bool,
    ) -> Result<bool, HistoryError> {
        if matches!(left, Node::Empty)
            || matches!(right, Node::All)
            || matches!(left, Node::Epsilon) && nullable
        {
            return Ok(true);
        }
        if let Node::Union(members) = left
            && self.each_below(language, members, y)?
        {
            return Ok(true);
        }
        if let Node::Intersect(members) = right
            && self.below_each(language, x, members)?
        {
            return Ok(true);
        }
        if let Node::Union(members) = right
            && self.below_some(language, x, members)?
        {
            return Ok(true);
        }
        if let Node::Intersect(members) = left
            && self.some_below(language, members, y)?
        {
            return Ok(true);
        }
        Ok(match (left, right) {
            (Node::Not(inner), Node::Not(outer)) => self.le(language, *outer, *inner)?,
            (Node::Test(phi), Node::Test(psi)) => test_le(language, *phi, *psi)?,
            (Node::Star(inner), Node::Star(outer)) => {
                self.le(language, *inner, *outer)? || self.le(language, x, *outer)?
            }
            (_, Node::Star(outer)) => self.le(language, x, *outer)?,
            (_, Node::Concat(factors)) => self.factors_le(language, x, left, factors)?,
            _ => false,
        })
    }

    /// Whether the factors of `x` lie below `ys` one by one, once `Σ*` factors are dropped from
    /// either end of `ys`.
    fn factors_le(
        &mut self,
        language: &mut SymbolicLanguage,
        x: RegexId,
        left: &Node,
        ys: &[RegexId],
    ) -> Result<bool, HistoryError> {
        let single = [x];
        let xs: &[RegexId] = match left {
            Node::Concat(factors) => factors,
            _ => &single,
        };
        let Some(extra) = ys.len().checked_sub(xs.len()) else {
            return Ok(false);
        };
        let mut leading = 0;
        while leading < extra && is_all(language, ys[leading])? {
            leading += 1;
        }
        let mut trailing = 0;
        while trailing < extra && is_all(language, ys[ys.len() - 1 - trailing])? {
            trailing += 1;
        }
        for front in 0..=leading {
            let back = extra - front;
            if back <= trailing && self.pointwise(language, xs, &ys[front..ys.len() - back])? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn pointwise(
        &mut self,
        language: &mut SymbolicLanguage,
        xs: &[RegexId],
        ys: &[RegexId],
    ) -> Result<bool, HistoryError> {
        for (x, y) in xs.iter().zip(ys) {
            if !self.le(language, *x, *y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn each_below(
        &mut self,
        language: &mut SymbolicLanguage,
        xs: &[RegexId],
        y: RegexId,
    ) -> Result<bool, HistoryError> {
        for &x in xs {
            if !self.le(language, x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn below_each(
        &mut self,
        language: &mut SymbolicLanguage,
        x: RegexId,
        ys: &[RegexId],
    ) -> Result<bool, HistoryError> {
        for &y in ys {
            if !self.le(language, x, y)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn some_below(
        &mut self,
        language: &mut SymbolicLanguage,
        xs: &[RegexId],
        y: RegexId,
    ) -> Result<bool, HistoryError> {
        for &x in xs {
            if self.le(language, x, y)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn below_some(
        &mut self,
        language: &mut SymbolicLanguage,
        x: RegexId,
        ys: &[RegexId],
    ) -> Result<bool, HistoryError> {
        for &y in ys {
            if self.le(language, x, y)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

fn node(language: &mut SymbolicLanguage, id: RegexId) -> Result<(Node, bool), HistoryError> {
    language.read_regex(id, |view| {
        let node = match view.kind {
            RegexKindView::Empty => Node::Empty,
            RegexKindView::All => Node::All,
            RegexKindView::Epsilon => Node::Epsilon,
            RegexKindView::Test(test) => Node::Test(test),
            RegexKindView::Union(members) => Node::Union(SmallVec::from_slice(members)),
            RegexKindView::Concat(factors) => Node::Concat(SmallVec::from_slice(factors)),
            RegexKindView::Star(inner) => Node::Star(inner),
            RegexKindView::Intersect(members) => Node::Intersect(SmallVec::from_slice(members)),
            RegexKindView::Not(inner) => Node::Not(inner),
        };
        (node, view.nullable)
    })
}

fn is_all(language: &mut SymbolicLanguage, id: RegexId) -> Result<bool, HistoryError> {
    language.read_regex(id, |view| matches!(view.kind, RegexKindView::All))
}

fn test_node(language: &mut SymbolicLanguage, id: TestId) -> Result<TestNode, HistoryError> {
    language.read_test(id, |view| match view {
        TestView::True => TestNode::True,
        TestView::False => TestNode::False,
        TestView::Atom { .. } => TestNode::Atom,
        TestView::And(conjuncts) => TestNode::And(SmallVec::from_slice(conjuncts)),
        TestView::Or(disjuncts) => TestNode::Or(SmallVec::from_slice(disjuncts)),
    })
}

/// Whether every event that satisfies `phi` satisfies `psi`, by the rule for tests.
fn test_le(
    language: &mut SymbolicLanguage,
    phi: TestId,
    psi: TestId,
) -> Result<bool, HistoryError> {
    if phi == psi {
        return Ok(true);
    }
    let (left, right) = (test_node(language, phi)?, test_node(language, psi)?);
    if matches!(right, TestNode::True) || matches!(left, TestNode::False) {
        return Ok(true);
    }
    let conjuncts = |id: TestId, node: &TestNode| match node {
        TestNode::And(conjuncts) => conjuncts.clone(),
        _ => smallvec![id],
    };
    let disjuncts = |id: TestId, node: &TestNode| match node {
        TestNode::Or(disjuncts) => disjuncts.clone(),
        _ => smallvec![id],
    };
    let included = |small: &[TestId], large: &[TestId]| {
        small.iter().all(|test| large.binary_search(test).is_ok())
    };
    Ok(included(&conjuncts(psi, &right), &conjuncts(phi, &left))
        || included(&disjuncts(phi, &left), &disjuncts(psi, &right)))
}
