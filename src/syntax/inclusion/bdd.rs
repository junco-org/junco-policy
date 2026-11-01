//! Reduced ordered binary decision diagrams over residual-state variables.
//!
//! Formulas are canonical: two formulas are propositionally equivalent iff they are the same node.
//! Variables are numbered in discovery order, and smaller numbers lie nearer the root, so that
//! discovering a new variable never changes the relative order of existing ones.

use hashbrown::HashMap;

/// A node of the diagram; equal nodes denote equivalent formulas.
pub(super) type Formula = u32;

/// The constant false formula.
pub(super) const FALSE: Formula = 0;
/// The constant true formula.
pub(super) const TRUE: Formula = 1;

/// Variable index of the terminals, below every real variable.
const TERMINAL: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Node {
    variable: u32,
    low: Formula,
    high: Formula,
}

/// Unique table and operation cache.
pub(super) struct Bdd {
    nodes: Vec<Node>,
    unique: HashMap<Node, Formula>,
    ite: HashMap<(Formula, Formula, Formula), Formula>,
}

impl Default for Bdd {
    fn default() -> Self {
        let terminal = |value| Node {
            variable: TERMINAL,
            low: value,
            high: value,
        };
        Self {
            nodes: vec![terminal(FALSE), terminal(TRUE)],
            unique: HashMap::new(),
            ite: HashMap::new(),
        }
    }
}

impl Bdd {
    /// The formula consisting of one variable.
    pub(super) fn variable(&mut self, variable: u32) -> Formula {
        self.node(variable, FALSE, TRUE)
    }

    fn node(&mut self, variable: u32, low: Formula, high: Formula) -> Formula {
        if low == high {
            return low;
        }
        let node = Node {
            variable,
            low,
            high,
        };
        if let Some(existing) = self.unique.get(&node) {
            return *existing;
        }
        let formula = Formula::try_from(self.nodes.len()).expect("formula ids fit in u32");
        self.nodes.push(node);
        self.unique.insert(node, formula);
        formula
    }

    fn top(&self, formula: Formula) -> u32 {
        self.nodes[formula as usize].variable
    }

    /// Cofactors of `formula` for `variable`, which must not lie below the formula's root.
    fn cofactors(&self, formula: Formula, variable: u32) -> (Formula, Formula) {
        let node = self.nodes[formula as usize];
        if node.variable == variable {
            (node.low, node.high)
        } else {
            (formula, formula)
        }
    }

    /// `if condition then yes else no`.
    pub(super) fn ite(&mut self, condition: Formula, yes: Formula, no: Formula) -> Formula {
        if condition == TRUE || yes == no {
            return yes;
        }
        if condition == FALSE {
            return no;
        }
        if yes == TRUE && no == FALSE {
            return condition;
        }
        if let Some(result) = self.ite.get(&(condition, yes, no)) {
            return *result;
        }
        let variable = self.top(condition).min(self.top(yes)).min(self.top(no));
        let (condition_low, condition_high) = self.cofactors(condition, variable);
        let (yes_low, yes_high) = self.cofactors(yes, variable);
        let (no_low, no_high) = self.cofactors(no, variable);
        let low = self.ite(condition_low, yes_low, no_low);
        let high = self.ite(condition_high, yes_high, no_high);
        let result = self.node(variable, low, high);
        self.ite.insert((condition, yes, no), result);
        result
    }

    pub(super) fn not(&mut self, formula: Formula) -> Formula {
        self.ite(formula, FALSE, TRUE)
    }

    pub(super) fn and(&mut self, left: Formula, right: Formula) -> Formula {
        self.ite(left, right, FALSE)
    }

    pub(super) fn or(&mut self, left: Formula, right: Formula) -> Formula {
        self.ite(left, TRUE, right)
    }

    /// Whether `left ⇒ right` is valid.
    pub(super) fn implies(&mut self, left: Formula, right: Formula) -> bool {
        let negation = self.not(right);
        self.and(left, negation) == FALSE
    }

    /// Variables the formula depends on, in increasing order.
    pub(super) fn support(&self, formula: Formula) -> Vec<u32> {
        let mut variables = Vec::new();
        let mut visited = hashbrown::HashSet::new();
        let mut pending = vec![formula];
        while let Some(formula) = pending.pop() {
            if formula <= TRUE || !visited.insert(formula) {
                continue;
            }
            let node = self.nodes[formula as usize];
            variables.push(node.variable);
            pending.push(node.low);
            pending.push(node.high);
        }
        variables.sort_unstable();
        variables.dedup();
        variables
    }

    /// Truth value of `formula` under an assignment to its variables.
    pub(super) fn evaluate(&self, mut formula: Formula, value: impl Fn(u32) -> bool) -> bool {
        while formula > TRUE {
            let node = self.nodes[formula as usize];
            formula = if value(node.variable) {
                node.high
            } else {
                node.low
            };
        }
        formula == TRUE
    }

    /// The paths from the root to `TRUE`, as cubes of `(variable, polarity)` literals ordered by
    /// variable. Their disjunction is `formula`; the cover depends only on the canonical formula.
    pub(super) fn cover(&self, formula: Formula) -> Vec<Box<[(u32, bool)]>> {
        let mut cubes = Vec::new();
        let mut path = Vec::new();
        self.paths(formula, &mut path, &mut cubes);
        cubes
    }

    fn paths(
        &self,
        formula: Formula,
        path: &mut Vec<(u32, bool)>,
        cubes: &mut Vec<Box<[(u32, bool)]>>,
    ) {
        match formula {
            FALSE => {}
            TRUE => cubes.push(path.as_slice().into()),
            _ => {
                let node = self.nodes[formula as usize];
                path.push((node.variable, false));
                self.paths(node.low, path, cubes);
                path.pop();
                path.push((node.variable, true));
                self.paths(node.high, path, cubes);
                path.pop();
            }
        }
    }

    /// Simultaneous substitution of `substitution[v]` for every variable `v` of `formula`.
    pub(super) fn compose(
        &mut self,
        formula: Formula,
        substitution: &HashMap<u32, Formula>,
    ) -> Formula {
        let mut memo = HashMap::new();
        self.compose_memo(formula, substitution, &mut memo)
    }

    fn compose_memo(
        &mut self,
        formula: Formula,
        substitution: &HashMap<u32, Formula>,
        memo: &mut HashMap<Formula, Formula>,
    ) -> Formula {
        if formula <= TRUE {
            return formula;
        }
        if let Some(result) = memo.get(&formula) {
            return *result;
        }
        let node = self.nodes[formula as usize];
        let low = self.compose_memo(node.low, substitution, memo);
        let high = self.compose_memo(node.high, substitution, memo);
        let replacement = substitution[&node.variable];
        let result = self.ite(replacement, high, low);
        memo.insert(formula, result);
        result
    }
}
