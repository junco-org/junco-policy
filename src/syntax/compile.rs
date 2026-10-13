//! Source-rule compilation into canonical runtime representations.
//!
//! Every function receives the canonical store and rule-local variable environment explicitly.
//! Source expressions remain context-free; runtime nodes contain only copied component constants,
//! interned variable symbols, and child references. Errors are relative to the one source rule
//! passed to [`compile_rule`].

use crate::history::History;
use crate::model::Event;
use crate::validator::CompileError;

use super::component::{CompiledAtomPattern, CompiledPattern};
use super::environment::{CompiledHead, ResolveError, VariableEnvironment};
use super::node::{RegexId, TestId, TestNode};
use super::progress::ProgressCache;
use super::source::{
    AtomPattern, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use super::store::CanonicalStore;
use super::symbolic::{SymbolicDerivativeCache, SymbolicMatcher};

/// Runtime rule with an event-independent derivative cache and bounded evaluated-history progress
/// retained across evaluations.
pub(crate) struct RuntimeRule<'arena, E: Event + 'arena> {
    pub(crate) mode: RuleMode,
    pub(crate) head: CompiledHead<E>,
    pub(crate) tail: RegexId<'arena, E>,
    derivatives: SymbolicDerivativeCache<'arena, E>,
    progress: ProgressCache<'arena, E>,
}

impl<'arena, E: Event + 'arena> RuntimeRule<'arena, E> {
    /// Matches the candidate head and evaluates committed history, resuming retained progress.
    ///
    /// Returns `None` when the head does not match `candidate`.
    pub(crate) fn accepts_history(
        &mut self,
        store: &mut CanonicalStore<'arena, E>,
        history: &History<E>,
        candidate: &E,
    ) -> Option<bool> {
        let substitution = self.head.match_candidate(candidate)?;
        Some(self.progress.accepts(
            store,
            &mut self.derivatives,
            self.tail,
            history,
            &substitution,
        ))
    }

    /// Number of event-independent symbolic derivatives retained by this rule.
    #[cfg(test)]
    pub(crate) fn derivative_count(&self) -> usize {
        self.derivatives.len()
    }

    /// Number of dense minterm transitions prepared before the first event is evaluated.
    #[cfg(test)]
    pub(crate) fn precompiled_transition_count(&self) -> usize {
        self.derivatives.precompiled_len()
    }
}

/// Compiles and validates one complete source rule.
pub(crate) fn compile_rule<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    source: &Rule<E>,
) -> Result<RuntimeRule<'arena, E>, CompileError> {
    let (head, variables) = compile_head(store, &source.head)?;
    let tail = compile_regex(store, &variables, &source.tail)?;
    let mut derivatives = SymbolicDerivativeCache::new();
    SymbolicMatcher::new(store, &mut derivatives).precompile(tail);
    Ok(RuntimeRule {
        mode: source.mode,
        head,
        tail,
        derivatives,
        progress: ProgressCache::new(),
    })
}

/// Compiles one head coordinate occupying `component` and records variable declarations.
fn compile_head_pattern<'arena, E: Event + 'arena, T: Copy>(
    store: &mut CanonicalStore<'arena, E>,
    pattern: &ComponentPattern<T>,
    component: Component,
    variables: &mut VariableEnvironment,
) -> Result<CompiledPattern<T>, CompileError> {
    Ok(match pattern {
        ComponentPattern::Constant(value) => ComponentPattern::Constant(*value),
        ComponentPattern::Variable(name) => {
            let variable = store.intern_variable(name);
            variables.bind(variable, component).map_err(|_| {
                CompileError::VariableComponentConflict {
                    name: name.to_owned(),
                }
            })?;
            ComponentPattern::Variable(variable)
        }
    })
}

/// Compiles the fixed capability-product head and its variable environment.
fn compile_head<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    head: &Head<E>,
) -> Result<(CompiledHead<E>, VariableEnvironment), CompileError> {
    let mut variables = VariableEnvironment::default();
    let principal =
        compile_head_pattern(store, &head.principal, Component::Principal, &mut variables)?;
    let action = compile_head_pattern(store, &head.action, Component::Action, &mut variables)?;
    let resource =
        compile_head_pattern(store, &head.resource, Component::Resource, &mut variables)?;
    Ok((
        CompiledHead {
            principal,
            action,
            resource,
        },
        variables,
    ))
}

/// Compiles one tail pattern occupying `component` after resolving its source variable.
fn compile_pattern<'arena, E: Event + 'arena, T: Copy>(
    store: &mut CanonicalStore<'arena, E>,
    pattern: &ComponentPattern<T>,
    component: Component,
    variables: &VariableEnvironment,
) -> Result<CompiledPattern<T>, CompileError> {
    Ok(match pattern {
        ComponentPattern::Constant(value) => ComponentPattern::Constant(*value),
        ComponentPattern::Variable(name) => {
            let variable = store.intern_variable(name);
            variables
                .resolve(variable, component)
                .map_err(|error| match error {
                    ResolveError::Unbound => CompileError::UnboundVariable {
                        name: name.to_owned(),
                    },
                    ResolveError::ComponentConflict => CompileError::VariableComponentConflict {
                        name: name.to_owned(),
                    },
                })?;
            ComponentPattern::Variable(variable)
        }
    })
}

/// Compiles the atom representation retained by hashconsed test nodes.
fn compile_atom_pattern<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    pattern: &AtomPattern<E>,
    variables: &VariableEnvironment,
) -> Result<CompiledAtomPattern<E>, CompileError> {
    let component = pattern.component();
    Ok(match pattern {
        AtomPattern::Principal(pattern) => {
            CompiledAtomPattern::Principal(compile_pattern(store, pattern, component, variables)?)
        }
        AtomPattern::Action(pattern) => {
            CompiledAtomPattern::Action(compile_pattern(store, pattern, component, variables)?)
        }
        AtomPattern::Resource(pattern) => {
            CompiledAtomPattern::Resource(compile_pattern(store, pattern, component, variables)?)
        }
    })
}

/// Recursively compiles one owned boolean expression.
fn compile_test<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    variables: &VariableEnvironment,
    source: &TestExpr<E>,
) -> Result<TestId<'arena, E>, CompileError> {
    match source {
        TestExpr::True => Ok(store.test_true),
        TestExpr::False => Ok(store.test_false),
        TestExpr::Atom {
            comparison,
            pattern,
        } => {
            let pattern = compile_atom_pattern(store, pattern, variables)?;
            Ok(store.tests.mk(TestNode::Atom {
                comparison: *comparison,
                pattern,
            }))
        }
        TestExpr::And(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_test(store, variables, child)?);
            }
            Ok(store.test_and(compiled))
        }
        TestExpr::Or(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_test(store, variables, child)?);
            }
            Ok(store.test_or(compiled))
        }
    }
}

/// Recursively compiles one owned regex expression through canonical smart constructors.
fn compile_regex<'arena, E: Event + 'arena>(
    store: &mut CanonicalStore<'arena, E>,
    variables: &VariableEnvironment,
    source: &RegexExpr<E>,
) -> Result<RegexId<'arena, E>, CompileError> {
    match source {
        RegexExpr::Empty => Ok(store.empty),
        RegexExpr::All => Ok(store.all),
        RegexExpr::Epsilon => Ok(store.epsilon),
        RegexExpr::Test(test) => {
            let test = compile_test(store, variables, test)?;
            Ok(store.regex_test(test))
        }
        RegexExpr::Union(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, variables, child)?);
            }
            Ok(store.regex_union(compiled))
        }
        RegexExpr::Concat(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, variables, child)?);
            }
            Ok(store.regex_concat(compiled))
        }
        RegexExpr::Star(inner) => {
            let inner = compile_regex(store, variables, inner)?;
            Ok(store.regex_star(inner))
        }
        RegexExpr::Intersect(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, variables, child)?);
            }
            Ok(store.regex_intersect(compiled))
        }
        RegexExpr::Not(inner) => {
            let inner = compile_regex(store, variables, inner)?;
            Ok(store.regex_not(inner))
        }
    }
}
