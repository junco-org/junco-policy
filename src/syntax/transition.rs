//! Normalized symbolic-transition smart constructors from `symbolic-matcher.tex`.

use super::node::{RegexId, RegexKind, TransitionId, TransitionNode};
use super::store::CanonicalStore;

impl<'arena> CanonicalStore<'arena> {
    /// Lifts one normalized regex state into a constant transition.
    pub(super) fn transition_const(&mut self, regex: RegexId<'arena>) -> TransitionId<'arena> {
        if regex == self.empty {
            self.transition_empty
        } else if regex == self.all {
            self.transition_all
        } else if regex == self.epsilon {
            self.transition_epsilon
        } else {
            self.transitions.mk(TransitionNode::Const(regex))
        }
    }

    fn intern_transition_if(
        &mut self,
        test: super::node::TestId<'arena>,
        then_transition: TransitionId<'arena>,
        else_transition: TransitionId<'arena>,
    ) -> TransitionId<'arena> {
        if test == self.test_true {
            then_transition
        } else if test == self.test_false {
            else_transition
        } else if then_transition == else_transition {
            then_transition
        } else {
            self.transitions.mk(TransitionNode::If {
                test,
                then_transition,
                else_transition,
            })
        }
    }

    fn clean_transition_path(
        &mut self,
        transition: TransitionId<'arena>,
        path: super::node::TestId<'arena>,
    ) -> TransitionId<'arena> {
        match *transition.get() {
            TransitionNode::Const(_) => transition,
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => self.clean_conditional_path(test, then_transition, else_transition, path),
            TransitionNode::Union(children) => {
                let children = children
                    .iter()
                    .map(|child| self.clean_transition_path(*child, path))
                    .collect();
                self.transition_union(children)
            }
            TransitionNode::Intersect(children) => {
                let children = children
                    .iter()
                    .map(|child| self.clean_transition_path(*child, path))
                    .collect();
                self.transition_intersect(children)
            }
            TransitionNode::Not(inner) => {
                let inner = self.clean_transition_path(inner, path);
                self.transition_not(inner)
            }
            TransitionNode::Append { transition, suffix } => {
                let transition = self.clean_transition_path(transition, path);
                self.transition_append(transition, suffix)
            }
        }
    }

    fn clean_conditional_path(
        &mut self,
        test: super::node::TestId<'arena>,
        then_transition: TransitionId<'arena>,
        else_transition: TransitionId<'arena>,
        path: super::node::TestId<'arena>,
    ) -> TransitionId<'arena> {
        if test == self.test_true {
            return self.clean_transition_path(then_transition, path);
        }
        if test == self.test_false {
            return self.clean_transition_path(else_transition, path);
        }
        if then_transition == else_transition {
            return self.clean_transition_path(then_transition, path);
        }

        let true_path = self.test_and(vec![path, test]);
        let complement = self.test_not(test);
        let false_path = self.test_and(vec![path, complement]);
        if true_path == self.test_false {
            return self.clean_transition_path(else_transition, false_path);
        }
        if false_path == self.test_false {
            return self.clean_transition_path(then_transition, true_path);
        }

        let then_transition = self.clean_transition_path(then_transition, true_path);
        let else_transition = self.clean_transition_path(else_transition, false_path);
        self.intern_transition_if(test, then_transition, else_transition)
    }

    /// Constructs a normalized conditional and removes path-infeasible nested branches.
    pub(super) fn transition_if(
        &mut self,
        test: super::node::TestId<'arena>,
        then_transition: TransitionId<'arena>,
        else_transition: TransitionId<'arena>,
    ) -> TransitionId<'arena> {
        self.clean_conditional_path(test, then_transition, else_transition, self.test_true)
    }

    /// Constructs flattened, ordered, deduplicated transition union.
    pub(super) fn transition_union(
        &mut self,
        children: Vec<TransitionId<'arena>>,
    ) -> TransitionId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TransitionNode::Const(regex) if regex == self.all => return self.transition_all,
                TransitionNode::Const(regex) if regex == self.empty => {}
                TransitionNode::Union(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        flat.sort_unstable();
        flat.dedup();
        if !flat.is_empty()
            && flat
                .iter()
                .all(|child| matches!(child.get(), TransitionNode::Const(_)))
        {
            let regexes = flat
                .iter()
                .map(|child| match *child.get() {
                    TransitionNode::Const(regex) => regex,
                    _ => unreachable!("all transition operands were checked as constants"),
                })
                .collect();
            let regex = self.regex_union(regexes);
            return self.transition_const(regex);
        }

        match flat.as_slice() {
            [] => self.transition_empty,
            [only] => *only,
            _ => {
                let values = self.transitions.arena().alloc_slice_copy(&flat);
                self.transitions.mk(TransitionNode::Union(values))
            }
        }
    }

    fn transition_intersect_pair(
        &mut self,
        left: TransitionId<'arena>,
        right: TransitionId<'arena>,
    ) -> TransitionId<'arena> {
        if left == right {
            return left;
        }
        match (*left.get(), *right.get()) {
            (TransitionNode::Const(regex), _) if regex == self.empty => {
                return self.transition_empty;
            }
            (_, TransitionNode::Const(regex)) if regex == self.empty => {
                return self.transition_empty;
            }
            (TransitionNode::Const(regex), _) if regex == self.all => return right,
            (_, TransitionNode::Const(regex)) if regex == self.all => return left,
            (TransitionNode::Const(left), TransitionNode::Const(right)) => {
                let regex = self.regex_intersect(vec![left, right]);
                return self.transition_const(regex);
            }
            (
                TransitionNode::If {
                    test: left_test,
                    then_transition: left_then,
                    else_transition: left_else,
                },
                TransitionNode::If {
                    test: right_test,
                    then_transition: right_then,
                    else_transition: right_else,
                },
            ) if left_else == self.transition_empty && right_else == self.transition_empty => {
                let guard = self.test_and(vec![left_test, right_test]);
                if guard == self.test_false {
                    return self.transition_empty;
                }
                let then_transition = self.transition_intersect(vec![left_then, right_then]);
                return self.transition_if(guard, then_transition, self.transition_empty);
            }
            (TransitionNode::Union(children), _) => {
                let intersections = children
                    .iter()
                    .map(|child| self.transition_intersect(vec![*child, right]))
                    .collect();
                return self.transition_union(intersections);
            }
            (_, TransitionNode::Union(children)) => {
                let intersections = children
                    .iter()
                    .map(|child| self.transition_intersect(vec![left, *child]))
                    .collect();
                return self.transition_union(intersections);
            }
            (
                TransitionNode::If {
                    test,
                    then_transition,
                    else_transition,
                },
                _,
            ) => {
                let then_transition = self.transition_intersect(vec![then_transition, right]);
                let else_transition = self.transition_intersect(vec![else_transition, right]);
                return self.transition_if(test, then_transition, else_transition);
            }
            (
                _,
                TransitionNode::If {
                    test,
                    then_transition,
                    else_transition,
                },
            ) => {
                let then_transition = self.transition_intersect(vec![left, then_transition]);
                let else_transition = self.transition_intersect(vec![left, else_transition]);
                return self.transition_if(test, then_transition, else_transition);
            }
            _ => {}
        }

        let mut children = vec![left, right];
        children.sort_unstable();
        let values = self.transitions.arena().alloc_slice_copy(&children);
        self.transitions.mk(TransitionNode::Intersect(values))
    }

    /// Constructs transition intersection in deterministic disjunctive normal form.
    pub(super) fn transition_intersect(
        &mut self,
        children: Vec<TransitionId<'arena>>,
    ) -> TransitionId<'arena> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TransitionNode::Const(regex) if regex == self.empty => {
                    return self.transition_empty;
                }
                TransitionNode::Const(regex) if regex == self.all => {}
                TransitionNode::Intersect(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }

        flat.sort_unstable();
        flat.dedup();
        let mut children = flat.into_iter();
        let Some(first) = children.next() else {
            return self.transition_all;
        };
        children.fold(first, |result, child| {
            self.transition_intersect_pair(result, child)
        })
    }

    /// Pushes transition complement through Boolean structure and conditionals to regex leaves.
    pub(super) fn transition_not(
        &mut self,
        transition: TransitionId<'arena>,
    ) -> TransitionId<'arena> {
        match *transition.get() {
            TransitionNode::Const(regex) => {
                let regex = self.regex_not(regex);
                self.transition_const(regex)
            }
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } if then_transition == self.transition_all
                && else_transition == self.transition_empty =>
            {
                let test = self.test_not(test);
                self.transition_if(test, self.transition_all, self.transition_empty)
            }
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => {
                let then_transition = self.transition_not(then_transition);
                let else_transition = self.transition_not(else_transition);
                self.transition_if(test, then_transition, else_transition)
            }
            TransitionNode::Union(children) => {
                let complements = children
                    .iter()
                    .map(|child| self.transition_not(*child))
                    .collect();
                self.transition_intersect(complements)
            }
            TransitionNode::Intersect(children) => {
                let complements = children
                    .iter()
                    .map(|child| self.transition_not(*child))
                    .collect();
                self.transition_union(complements)
            }
            TransitionNode::Not(inner) => inner,
            TransitionNode::Append { .. } => self.transitions.mk(TransitionNode::Not(transition)),
        }
    }

    /// Appends a fixed normalized regex suffix, distributing to transition leaves.
    pub(super) fn transition_append(
        &mut self,
        transition: TransitionId<'arena>,
        suffix: &[RegexId<'arena>],
    ) -> TransitionId<'arena> {
        if suffix.is_empty() {
            return transition;
        }
        let normalized = self.regex_concat(suffix.to_vec());
        if normalized == self.epsilon {
            return transition;
        }
        if normalized == self.empty {
            return self.transition_empty;
        }
        let suffix = match normalized.get().kind {
            RegexKind::Concat(factors) => factors.to_vec(),
            _ => vec![normalized],
        };

        match *transition.get() {
            TransitionNode::Const(regex) => {
                let mut factors = Vec::with_capacity(1 + suffix.len());
                factors.push(regex);
                factors.extend_from_slice(&suffix);
                let regex = self.regex_concat(factors);
                self.transition_const(regex)
            }
            TransitionNode::Union(children) => {
                let appended = children
                    .iter()
                    .map(|child| self.transition_append(*child, &suffix))
                    .collect();
                self.transition_union(appended)
            }
            TransitionNode::If {
                test,
                then_transition,
                else_transition,
            } => {
                let then_transition = self.transition_append(then_transition, &suffix);
                let else_transition = self.transition_append(else_transition, &suffix);
                self.transition_if(test, then_transition, else_transition)
            }
            TransitionNode::Append {
                transition,
                suffix: existing,
            } => {
                let mut combined = Vec::with_capacity(existing.len() + suffix.len());
                combined.extend_from_slice(existing);
                combined.extend_from_slice(&suffix);
                self.transition_append(transition, &combined)
            }
            TransitionNode::Intersect(_) | TransitionNode::Not(_) => {
                let values = self.transitions.arena().alloc_slice_copy(&suffix);
                self.transitions.mk(TransitionNode::Append {
                    transition,
                    suffix: values,
                })
            }
        }
    }
}
