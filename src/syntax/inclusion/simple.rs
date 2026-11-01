//! The simple strategy: breadth-first exploration of the Brzozowski derivatives of `left ∩ ¬right`.
//!
//! Residuals are extended regexes in a syntax of their own, built only by the smart constructors
//! below. These make just local simplifications: unions and intersections are flat, sorted and
//! duplicate-free, lose their unit, and collapse to their absorber when it, or a child beside its
//! complement, occurs; `¬∅ = Σ*`, `¬Σ* = ∅` and `¬¬x = x`; concatenation is binary and drops `ε`
//! factors, or collapses to `∅` with an `∅` factor; `∅* = ε* = ε` and `(Σ*)* = Σ*`. With exactly
//! these rules every expression has finitely many iterated derivatives, whatever the letters, so the
//! search terminates. junco's normaliser applies further identities that this argument does not
//! cover, so it only builds the two sides. Tests remain junco's compiled tests: leaves evaluated
//! against each letter.
//!
//! One derivative equation per operator applies at every depth, so intersection and complement
//! need no special treatment under concatenation or star. A search state pairs a constraint with a
//! residual, and states are compared by identity only, so breadth-first order finds a shortest
//! counterexample.

use std::hash::BuildHasher;
use std::rc::Rc;

use hashbrown::{DefaultHashBuilder, HashMap, HashSet, HashTable};
use smallbitvec::SmallBitVec;
use smallvec::SmallVec;

use super::super::node::{RegexId, RegexKind, TestId};
use super::super::symbolic::eval_test_assignment;
use super::constraint::{Constraint, ConstraintId, ConstraintTable, Letter, steps};
use super::search::{Refutation, SearchOutcome};
use super::term::{Atoms, distinct, test_atoms};
use super::{SearchOptions, SearchStats};

/// Identity of an interned expression; ids order expressions by interning time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExprId(u32);

impl ExprId {
    const EMPTY: Self = Self(0);
    const EPSILON: Self = Self(1);
    const ALL: Self = Self(2);

    const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Normalised expression.
///
/// A union or intersection has at least two children, sorted and distinct, none of which is the
/// connective's unit or absorber or a node of the same connective, and no child occurs beside its
/// complement. A complement's operand is not `∅`, `Σ*` or a complement. Neither factor of a
/// concatenation is `∅` or `ε`. A star's operand is not `∅`, `ε` or `Σ*`.
#[derive(Clone, Debug)]
enum Expr<'arena> {
    Empty,
    Epsilon,
    All,
    Test(TestId<'arena>),
    Union(Rc<[ExprId]>),
    Intersect(Rc<[ExprId]>),
    Not(ExprId),
    Concat(ExprId, ExprId),
    Star(ExprId),
}

/// Borrowed form of an [`Expr`], by which nodes are hashed and compared, so that finding an
/// existing union or intersection does not allocate its children.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum View<'children, 'arena> {
    Empty,
    Epsilon,
    All,
    Test(TestId<'arena>),
    Union(&'children [ExprId]),
    Intersect(&'children [ExprId]),
    Not(ExprId),
    Concat(ExprId, ExprId),
    Star(ExprId),
}

impl<'arena> Expr<'arena> {
    fn view(&self) -> View<'_, 'arena> {
        match self {
            Self::Empty => View::Empty,
            Self::Epsilon => View::Epsilon,
            Self::All => View::All,
            Self::Test(test) => View::Test(*test),
            Self::Union(children) => View::Union(children),
            Self::Intersect(children) => View::Intersect(children),
            Self::Not(inner) => View::Not(*inner),
            Self::Concat(head, tail) => View::Concat(*head, *tail),
            Self::Star(inner) => View::Star(*inner),
        }
    }
}

impl<'arena> View<'_, 'arena> {
    fn expr(self) -> Expr<'arena> {
        match self {
            Self::Empty => Expr::Empty,
            Self::Epsilon => Expr::Epsilon,
            Self::All => Expr::All,
            Self::Test(test) => Expr::Test(test),
            Self::Union(children) => Expr::Union(Rc::from(children)),
            Self::Intersect(children) => Expr::Intersect(Rc::from(children)),
            Self::Not(inner) => Expr::Not(inner),
            Self::Concat(head, tail) => Expr::Concat(head, tail),
            Self::Star(inner) => Expr::Star(inner),
        }
    }
}

/// Union or intersection, which share one smart constructor.
#[derive(Clone, Copy)]
enum Connective {
    Union,
    Intersect,
}

impl Connective {
    /// The identity element, dropped from the children.
    const fn unit(self) -> ExprId {
        match self {
            Self::Union => ExprId::EMPTY,
            Self::Intersect => ExprId::ALL,
        }
    }

    /// The absorbing element, which is also the result when a child occurs beside its complement.
    const fn absorber(self) -> ExprId {
        match self {
            Self::Union => ExprId::ALL,
            Self::Intersect => ExprId::EMPTY,
        }
    }

    /// The children of `expr` if it is a node of this connective, for flattening.
    fn children<'expr>(self, expr: &'expr Expr<'_>) -> Option<&'expr [ExprId]> {
        match (self, expr) {
            (Self::Union, Expr::Union(children)) | (Self::Intersect, Expr::Intersect(children)) => {
                Some(children)
            }
            _ => None,
        }
    }

    fn view<'children, 'arena>(self, children: &'children [ExprId]) -> View<'children, 'arena> {
        match self {
            Self::Union => View::Union(children),
            Self::Intersect => View::Intersect(children),
        }
    }
}

/// Interned expression with its nullability and first atoms.
struct Node<'arena> {
    expr: Expr<'arena>,
    /// `ν`: whether the expression accepts the empty history.
    nullable: bool,
    /// `fst`: every atom its derivatives evaluate.
    first: Atoms<'arena>,
}

/// Interned expressions and their derivatives, reused across the searches over one store.
pub(super) struct Expressions<'arena> {
    nodes: Vec<Node<'arena>>,
    /// Ids of `nodes`, hashed by view.
    table: HashTable<ExprId>,
    hasher: DefaultHashBuilder,
    /// The shared empty atom list.
    no_atoms: Atoms<'arena>,
    /// Expressions of the junco regexes searched so far.
    imported: HashMap<RegexId<'arena>, ExprId>,
    /// `D_ℓ x`, keyed by `x` and the truth of `fst(x)` under `ℓ`: letters that agree there have the
    /// same derivative, whatever constraint they were built for.
    derivatives: HashMap<(ExprId, SmallBitVec), ExprId>,
}

impl Default for Expressions<'_> {
    fn default() -> Self {
        let mut expressions = Self {
            nodes: Vec::new(),
            table: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
            no_atoms: Rc::from([]),
            imported: HashMap::new(),
            derivatives: HashMap::new(),
        };
        let constants =
            [View::Empty, View::Epsilon, View::All].map(|view| expressions.intern(view));
        debug_assert_eq!(constants, [ExprId::EMPTY, ExprId::EPSILON, ExprId::ALL]);
        expressions
    }
}

impl<'arena> Expressions<'arena> {
    /// Decides `left ⊑_constraint right` by breadth-first search from `left ∩ ¬right`.
    pub(super) fn includes(
        &mut self,
        constraint: Constraint<'arena>,
        left: RegexId<'arena>,
        right: RegexId<'arena>,
        options: SearchOptions,
        stats: &mut SearchStats,
    ) -> SearchOutcome<'arena> {
        let left = self.import(left);
        let right = self.import(right);
        let excluded = self.not(right);
        let difference = self.intersect([left, excluded]);
        let mut search = Search {
            expressions: self,
            options,
            stats,
            constraints: ConstraintTable::default(),
            items: Vec::new(),
            seen: HashSet::new(),
        };
        let constraint = search.constraints.intern(constraint);
        search.insert(constraint, difference, None);
        search.run()
    }

    fn node(&self, expr: ExprId) -> &Node<'arena> {
        &self.nodes[expr.index()]
    }

    fn nullable(&self, expr: ExprId) -> bool {
        self.node(expr).nullable
    }

    fn first(&self, expr: ExprId) -> &Atoms<'arena> {
        &self.node(expr).first
    }

    /// The node for `view`, interned on first use.
    fn intern(&mut self, view: View<'_, 'arena>) -> ExprId {
        let hash = self.hasher.hash_one(view);
        let nodes = &self.nodes;
        if let Some(expr) = self
            .table
            .find(hash, |expr| nodes[expr.index()].expr.view() == view)
        {
            return *expr;
        }
        let (nullable, first) = self.properties(view);
        let expr = ExprId(u32::try_from(self.nodes.len()).expect("expression ids fit in u32"));
        self.nodes.push(Node {
            expr: view.expr(),
            nullable,
            first,
        });
        let (nodes, hasher) = (&self.nodes, &self.hasher);
        self.table.insert_unique(hash, expr, |expr| {
            hasher.hash_one(nodes[expr.index()].expr.view())
        });
        expr
    }

    /// `ν` and `fst` of a node, from those of its children.
    fn properties(&self, view: View<'_, 'arena>) -> (bool, Atoms<'arena>) {
        match view {
            View::Empty => (false, self.no_atoms.clone()),
            View::Epsilon | View::All => (true, self.no_atoms.clone()),
            View::Test(test) => {
                let mut atoms = Vec::new();
                test_atoms(test, &mut atoms);
                (false, distinct(atoms))
            }
            View::Union(children) => (
                children.iter().any(|child| self.nullable(*child)),
                self.first_of(children),
            ),
            View::Intersect(children) => (
                children.iter().all(|child| self.nullable(*child)),
                self.first_of(children),
            ),
            View::Not(inner) => (!self.nullable(inner), self.first(inner).clone()),
            View::Concat(head, tail) if self.nullable(head) => {
                (self.nullable(tail), self.first_of(&[head, tail]))
            }
            View::Concat(head, _) => (false, self.first(head).clone()),
            View::Star(inner) => (true, self.first(inner).clone()),
        }
    }

    /// The union of the first atoms of `children`, sharing the list when only one child has any.
    fn first_of(&self, children: &[ExprId]) -> Atoms<'arena> {
        let mut lists = children
            .iter()
            .map(|child| self.first(*child))
            .filter(|atoms| !atoms.is_empty());
        match (lists.next(), lists.next()) {
            (None, _) => self.no_atoms.clone(),
            (Some(only), None) => only.clone(),
            (Some(one), Some(two)) => {
                let mut atoms = one.to_vec();
                atoms.extend_from_slice(two);
                for more in lists {
                    atoms.extend_from_slice(more);
                }
                distinct(atoms)
            }
        }
    }

    fn test(&mut self, test: TestId<'arena>) -> ExprId {
        self.intern(View::Test(test))
    }

    fn union(&mut self, children: impl IntoIterator<Item = ExprId>) -> ExprId {
        self.boolean(Connective::Union, children)
    }

    fn intersect(&mut self, children: impl IntoIterator<Item = ExprId>) -> ExprId {
        self.boolean(Connective::Intersect, children)
    }

    /// Union or intersection of normalised `children`.
    fn boolean(
        &mut self,
        connective: Connective,
        children: impl IntoIterator<Item = ExprId>,
    ) -> ExprId {
        let (unit, absorber) = (connective.unit(), connective.absorber());
        let mut flat = SmallVec::<[ExprId; 8]>::new();
        for child in children {
            if child == absorber {
                return absorber;
            }
            if child != unit {
                match connective.children(&self.node(child).expr) {
                    Some(nested) => flat.extend_from_slice(nested),
                    None => flat.push(child),
                }
            }
        }
        flat.sort_unstable();
        flat.dedup();
        let nodes = &self.nodes;
        let complementary = flat.iter().any(|child| {
            matches!(nodes[child.index()].expr, Expr::Not(inner) if flat.binary_search(&inner).is_ok())
        });
        if complementary {
            return absorber;
        }
        match *flat.as_slice() {
            [] => unit,
            [only] => only,
            _ => self.intern(connective.view(&flat)),
        }
    }

    /// Complement, without pushing it into the operand.
    fn not(&mut self, inner: ExprId) -> ExprId {
        match self.node(inner).expr {
            Expr::Empty => ExprId::ALL,
            Expr::All => ExprId::EMPTY,
            Expr::Not(operand) => operand,
            _ => self.intern(View::Not(inner)),
        }
    }

    /// Ordered binary concatenation, neither distributed nor reassociated.
    fn concat(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        if head == ExprId::EMPTY || tail == ExprId::EMPTY {
            ExprId::EMPTY
        } else if head == ExprId::EPSILON {
            tail
        } else if tail == ExprId::EPSILON {
            head
        } else {
            self.intern(View::Concat(head, tail))
        }
    }

    /// Star, without unfolding it.
    fn star(&mut self, inner: ExprId) -> ExprId {
        if inner == ExprId::EMPTY || inner == ExprId::EPSILON {
            ExprId::EPSILON
        } else if inner == ExprId::ALL {
            ExprId::ALL
        } else {
            self.intern(View::Star(inner))
        }
    }

    /// The expression for a compiled junco regex, normalised bottom-up.
    fn import(&mut self, regex: RegexId<'arena>) -> ExprId {
        if let Some(expr) = self.imported.get(&regex) {
            return *expr;
        }
        let expr = match regex.get().kind {
            RegexKind::Empty => ExprId::EMPTY,
            RegexKind::Epsilon => ExprId::EPSILON,
            RegexKind::All => ExprId::ALL,
            RegexKind::Test(test) => self.test(test),
            RegexKind::Union(children) => {
                let children = children
                    .iter()
                    .map(|child| self.import(*child))
                    .collect::<SmallVec<[ExprId; 8]>>();
                self.union(children)
            }
            RegexKind::Intersect(children) => {
                let children = children
                    .iter()
                    .map(|child| self.import(*child))
                    .collect::<SmallVec<[ExprId; 8]>>();
                self.intersect(children)
            }
            RegexKind::Not(inner) => {
                let inner = self.import(inner);
                self.not(inner)
            }
            // junco flattens concatenation; associate it to the right.
            RegexKind::Concat(factors) => {
                factors.iter().rev().fold(ExprId::EPSILON, |tail, factor| {
                    let head = self.import(*factor);
                    self.concat(head, tail)
                })
            }
            RegexKind::Star(inner) => {
                let inner = self.import(inner);
                self.star(inner)
            }
        };
        self.imported.insert(regex, expr);
        expr
    }

    /// `D_ℓ x`, for a letter built for a set of atoms that contains `fst(x)`.
    fn derive(&mut self, expr: ExprId, letter: &Letter<'arena>) -> ExprId {
        let node = self.node(expr);
        match node.expr {
            Expr::Empty | Expr::Epsilon => return ExprId::EMPTY,
            Expr::All => return ExprId::ALL,
            Expr::Test(test) => {
                return if eval_test_assignment(test, &mut |atom| letter.holds(atom)) {
                    ExprId::EPSILON
                } else {
                    ExprId::EMPTY
                };
            }
            _ => {}
        }
        let key = (
            expr,
            node.first
                .iter()
                .map(|atom| letter.holds(*atom))
                .collect::<SmallBitVec>(),
        );
        if let Some(derivative) = self.derivatives.get(&key) {
            return *derivative;
        }
        let derivative = match self.node(expr).expr.clone() {
            Expr::Union(children) => self.derive_boolean(Connective::Union, &children, letter),
            Expr::Intersect(children) => {
                self.derive_boolean(Connective::Intersect, &children, letter)
            }
            Expr::Not(inner) => {
                let derivative = self.derive(inner, letter);
                self.not(derivative)
            }
            // D(u·v) = D(u)·v, together with D(v) when u is nullable.
            Expr::Concat(head, tail) => {
                let in_head = self.derive(head, letter);
                let in_head = self.concat(in_head, tail);
                if self.nullable(head) {
                    let in_tail = self.derive(tail, letter);
                    self.union([in_head, in_tail])
                } else {
                    in_head
                }
            }
            // D(u*) = D(u)·u*.
            Expr::Star(inner) => {
                let derivative = self.derive(inner, letter);
                self.concat(derivative, expr)
            }
            Expr::Empty | Expr::Epsilon | Expr::All | Expr::Test(_) => {
                unreachable!("leaves are derived without the cache")
            }
        };
        self.derivatives.insert(key, derivative);
        derivative
    }

    /// The derivative of a union or intersection: its children's derivatives under the same
    /// connective, cut short by the first that is the connective's absorber.
    fn derive_boolean(
        &mut self,
        connective: Connective,
        children: &[ExprId],
        letter: &Letter<'arena>,
    ) -> ExprId {
        let absorber = connective.absorber();
        let mut derivatives = SmallVec::<[ExprId; 8]>::with_capacity(children.len());
        for child in children {
            let derivative = self.derive(*child, letter);
            if derivative == absorber {
                return absorber;
            }
            derivatives.push(derivative);
        }
        self.boolean(connective, derivatives)
    }
}

/// Inserted search state with its parent link, for counterexample reconstruction.
#[derive(Clone, Copy)]
struct Item<'arena> {
    constraint: ConstraintId,
    residual: ExprId,
    parent: Option<(usize, Letter<'arena>)>,
}

struct Search<'search, 'arena> {
    expressions: &'search mut Expressions<'arena>,
    options: SearchOptions,
    stats: &'search mut SearchStats,
    constraints: ConstraintTable<'arena>,
    /// Inserted states, in insertion order, which is also the order of expansion.
    items: Vec<Item<'arena>>,
    seen: HashSet<(ConstraintId, ExprId)>,
}

impl<'arena> Search<'_, 'arena> {
    fn run(&mut self) -> SearchOutcome<'arena> {
        let mut next = 0;
        while next < self.items.len() {
            if self.expressions.nullable(self.items[next].residual) {
                return self.counterexample(next);
            }
            if self
                .options
                .max_items
                .is_some_and(|budget| self.items.len() > budget)
            {
                return SearchOutcome::Exhausted;
            }
            self.expand(next);
            next += 1;
        }
        SearchOutcome::Holds
    }

    /// Inserts the derivative of the item by each step of its constraint and first atoms.
    fn expand(&mut self, index: usize) {
        self.stats.expanded += 1;
        let Item {
            constraint,
            residual,
            ..
        } = self.items[index];
        let atoms = self.expressions.first(residual);
        self.stats.assignments = self.stats.assignments.saturating_add(
            u32::try_from(atoms.len())
                .ok()
                .and_then(|width| 1_u64.checked_shl(width))
                .unwrap_or(u64::MAX),
        );
        let branches = steps(
            self.constraints.get(constraint),
            atoms,
            self.options.alphabet,
        );
        for (refined, letters) in branches {
            let refined = self.constraints.intern(refined);
            for letter in letters {
                self.stats.steps += 1;
                self.stats.generated += 1;
                let successor = self.expressions.derive(residual, &letter);
                self.insert(refined, successor, Some((index, letter)));
            }
        }
    }

    /// Queues a state unless its residual is `∅` or the same state was inserted before.
    fn insert(
        &mut self,
        constraint: ConstraintId,
        residual: ExprId,
        parent: Option<(usize, Letter<'arena>)>,
    ) {
        if residual == ExprId::EMPTY {
            self.stats.dead += 1;
            return;
        }
        if !self.seen.insert((constraint, residual)) {
            self.stats.repeated += 1;
            return;
        }
        self.items.push(Item {
            constraint,
            residual,
            parent,
        });
        self.stats.inserted += 1;
    }

    fn counterexample(&self, index: usize) -> SearchOutcome<'arena> {
        let constraint = self.constraints.get(self.items[index].constraint).clone();
        let mut letters = Vec::new();
        let mut current = index;
        while let Some((parent, letter)) = self.items[current].parent {
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
