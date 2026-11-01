//! Normal-form expressions: interned regexes over interned one-event tests, their smart
//! constructors, and their derivatives by letters.
//!
//! Expressions are built only by the smart constructors below. They make only local
//! simplifications: unions and intersections are flat, sorted and duplicate-free, lose their unit,
//! and collapse to their absorber when it, or a child beside its complement, occurs; `¬∅ = Σ*`,
//! `¬Σ* = ∅` and `¬¬x = x`; concatenation is binary and drops `ε` factors, or collapses to `∅` with
//! an `∅` factor; `∅* = ε* = ε` and `(Σ*)* = Σ*`. With exactly these rules every expression has
//! finitely many iterated derivatives, whatever the letters. Tests are leaves: they are interned
//! structurally and evaluated against each letter.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::hash::BuildHasher;
use hashbrown::{DefaultHashBuilder, HashMap, HashSet, HashTable};
use smallvec::SmallVec;

use crate::constraint::{Atom, Letter};

/// Atoms that the derivatives of an expression may evaluate, without duplicates.
pub(crate) type Atoms = Rc<[Atom]>;

/// Identity of an interned test.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TestId(u32);

/// One-event test.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Test {
    Bool(bool),
    Atom { atom: Atom, positive: bool },
    And(Rc<[TestId]>),
    Or(Rc<[TestId]>),
}

/// Interned test with its atoms.
struct TestNode {
    test: Test,
    atoms: Atoms,
}

/// Identity of an interned expression; ids order expressions by interning time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ExprId(u32);

impl ExprId {
    pub(crate) const EMPTY: Self = Self(0);
    pub(crate) const EPSILON: Self = Self(1);
    pub(crate) const ALL: Self = Self(2);

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
enum Expr {
    Empty,
    Epsilon,
    All,
    Test(TestId),
    Union(Rc<[ExprId]>),
    Intersect(Rc<[ExprId]>),
    Not(ExprId),
    Concat(ExprId, ExprId),
    Star(ExprId),
}

/// Borrowed form of an [`Expr`], by which nodes are hashed and compared, so that finding an
/// existing union or intersection does not allocate its children.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum View<'children> {
    Empty,
    Epsilon,
    All,
    Test(TestId),
    Union(&'children [ExprId]),
    Intersect(&'children [ExprId]),
    Not(ExprId),
    Concat(ExprId, ExprId),
    Star(ExprId),
}

impl Expr {
    fn view(&self) -> View<'_> {
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

impl View<'_> {
    fn expr(self) -> Expr {
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
    fn children(self, expr: &Expr) -> Option<&[ExprId]> {
        match (self, expr) {
            (Self::Union, Expr::Union(children)) | (Self::Intersect, Expr::Intersect(children)) => {
                Some(children)
            }
            _ => None,
        }
    }

    fn view(self, children: &[ExprId]) -> View<'_> {
        match self {
            Self::Union => View::Union(children),
            Self::Intersect => View::Intersect(children),
        }
    }
}

/// Interned expression with its nullability and first atoms.
struct Node {
    expr: Expr,
    /// `ν`: whether the expression accepts the empty history.
    nullable: bool,
    /// `fst`: every atom its derivatives evaluate.
    first: Atoms,
}

/// Interned tests and expressions with their derivatives, shared by the searches of one analyzer.
pub(crate) struct Expressions {
    tests: Vec<TestNode>,
    test_ids: HashMap<Test, TestId>,
    nodes: Vec<Node>,
    /// Ids of `nodes`, hashed by view.
    table: HashTable<ExprId>,
    hasher: DefaultHashBuilder,
    /// The shared empty atom list.
    no_atoms: Atoms,
    /// `D_ℓ x`, keyed by `x` and the truth of `fst(x)` under `ℓ`: letters that agree there have the
    /// same derivative, whatever constraint they were built for.
    derivatives: HashMap<(ExprId, SmallVec<[u64; 1]>), ExprId>,
}

impl Default for Expressions {
    fn default() -> Self {
        let mut expressions = Self {
            tests: Vec::new(),
            test_ids: HashMap::new(),
            nodes: Vec::new(),
            table: HashTable::new(),
            hasher: DefaultHashBuilder::default(),
            no_atoms: Rc::from([]),
            derivatives: HashMap::new(),
        };
        let constants =
            [View::Empty, View::Epsilon, View::All].map(|view| expressions.intern(view));
        debug_assert_eq!(constants, [ExprId::EMPTY, ExprId::EPSILON, ExprId::ALL]);
        expressions
    }
}

impl Expressions {
    fn node(&self, expr: ExprId) -> &Node {
        &self.nodes[expr.index()]
    }

    /// `ν`: whether `expr` accepts the empty history.
    pub(crate) fn nullable(&self, expr: ExprId) -> bool {
        self.node(expr).nullable
    }

    /// `fst`: every atom that a derivative of `expr` may evaluate.
    pub(crate) fn first(&self, expr: ExprId) -> &Atoms {
        &self.node(expr).first
    }

    /// The test that is always `value`.
    pub(crate) fn test_bool(&mut self, value: bool) -> TestId {
        self.intern_test(Test::Bool(value))
    }

    /// The test that `atom` holds, or fails if `positive` is false.
    pub(crate) fn test_atom(&mut self, atom: Atom, positive: bool) -> TestId {
        self.intern_test(Test::Atom { atom, positive })
    }

    /// The conjunction of `children`.
    pub(crate) fn test_and(&mut self, children: &[TestId]) -> TestId {
        self.intern_test(Test::And(Rc::from(children)))
    }

    /// The disjunction of `children`.
    pub(crate) fn test_or(&mut self, children: &[TestId]) -> TestId {
        self.intern_test(Test::Or(Rc::from(children)))
    }

    fn intern_test(&mut self, test: Test) -> TestId {
        if let Some(id) = self.test_ids.get(&test) {
            return *id;
        }
        let atoms = match &test {
            Test::Bool(_) => self.no_atoms.clone(),
            Test::Atom { atom, .. } => Rc::from([*atom]),
            Test::And(children) | Test::Or(children) => distinct(
                children
                    .iter()
                    .flat_map(|child| self.tests[child.0 as usize].atoms.iter().copied())
                    .collect(),
            ),
        };
        let id = TestId(u32::try_from(self.tests.len()).expect("test ids fit in u32"));
        self.tests.push(TestNode {
            test: test.clone(),
            atoms,
        });
        self.test_ids.insert(test, id);
        id
    }

    /// Whether the events of `letter` satisfy `test`; the letter must cover the test's atoms.
    fn test_holds(&self, test: TestId, letter: &Letter) -> bool {
        match &self.tests[test.0 as usize].test {
            Test::Bool(value) => *value,
            Test::Atom { atom, positive } => letter.holds(*atom) == *positive,
            Test::And(children) => children.iter().all(|child| self.test_holds(*child, letter)),
            Test::Or(children) => children.iter().any(|child| self.test_holds(*child, letter)),
        }
    }

    /// The node for `view`, interned on first use.
    fn intern(&mut self, view: View<'_>) -> ExprId {
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
    fn properties(&self, view: View<'_>) -> (bool, Atoms) {
        match view {
            View::Empty => (false, self.no_atoms.clone()),
            View::Epsilon | View::All => (true, self.no_atoms.clone()),
            View::Test(test) => (false, self.tests[test.0 as usize].atoms.clone()),
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
    fn first_of(&self, children: &[ExprId]) -> Atoms {
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

    /// The one-event language of `test`.
    pub(crate) fn test(&mut self, test: TestId) -> ExprId {
        self.intern(View::Test(test))
    }

    pub(crate) fn union(&mut self, children: impl IntoIterator<Item = ExprId>) -> ExprId {
        self.boolean(Connective::Union, children)
    }

    pub(crate) fn intersect(&mut self, children: impl IntoIterator<Item = ExprId>) -> ExprId {
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
    pub(crate) fn not(&mut self, inner: ExprId) -> ExprId {
        match self.node(inner).expr {
            Expr::Empty => ExprId::ALL,
            Expr::All => ExprId::EMPTY,
            Expr::Not(operand) => operand,
            _ => self.intern(View::Not(inner)),
        }
    }

    /// Ordered binary concatenation, neither distributed nor reassociated.
    pub(crate) fn concat(&mut self, head: ExprId, tail: ExprId) -> ExprId {
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
    pub(crate) fn star(&mut self, inner: ExprId) -> ExprId {
        if inner == ExprId::EMPTY || inner == ExprId::EPSILON {
            ExprId::EPSILON
        } else if inner == ExprId::ALL {
            ExprId::ALL
        } else {
            self.intern(View::Star(inner))
        }
    }

    /// `D_ℓ x`, for a letter built for a set of atoms that contains `fst(x)`.
    pub(crate) fn derive(&mut self, expr: ExprId, letter: &Letter) -> ExprId {
        let node = self.node(expr);
        match node.expr {
            Expr::Empty | Expr::Epsilon => return ExprId::EMPTY,
            Expr::All => return ExprId::ALL,
            Expr::Test(test) => {
                return if self.test_holds(test, letter) {
                    ExprId::EPSILON
                } else {
                    ExprId::EMPTY
                };
            }
            _ => {}
        }
        let key = (expr, truth(&node.first, letter));
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
        letter: &Letter,
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

/// The truth of `atoms` under `letter`, packed into words.
fn truth(atoms: &[Atom], letter: &Letter) -> SmallVec<[u64; 1]> {
    let mut words = SmallVec::from_elem(0, atoms.len().div_ceil(64));
    for (index, atom) in atoms.iter().enumerate() {
        if letter.holds(*atom) {
            words[index / 64] |= 1 << (index % 64);
        }
    }
    words
}

/// Removes repeated atoms, keeping first occurrences.
fn distinct(mut atoms: Vec<Atom>) -> Atoms {
    let mut seen = HashSet::new();
    atoms.retain(|atom| seen.insert(*atom));
    Rc::from(atoms)
}
