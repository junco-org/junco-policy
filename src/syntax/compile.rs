//! Source-rule compilation into canonical arena-backed nodes.
//!
//! Every function receives the canonical store and rule-local variable environment explicitly.
//! Source expressions remain context-free; compiled nodes contain only immutable values and child
//! references. The variable environment is created from the head and dropped after the tail is
//! compiled.

use crate::model::{Action, Principal, Resource};
use crate::validator::{CompileError, RuleIndex};

use super::component::{CompiledAtomPattern, CompiledPattern, ComponentDomain};
use super::environment::{CompiledHead, ResolveError, VariableEnvironment};
use super::node::{RegexId, TestId, TestNode};
use super::source::{AtomPattern, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr};
use super::store::CanonicalStore;

/// Minimal executable representation retained after a source rule is compiled.
#[derive(Clone, Copy)]
pub(crate) struct CompiledRule<'arena> {
    pub(crate) mode: RuleMode,
    pub(crate) head: CompiledHead<'arena>,
    pub(crate) tail: RegexId<'arena>,
}

/// Compiles and validates one complete source rule.
pub(crate) fn compile_rule<'arena>(
    store: &mut CanonicalStore<'arena>,
    rule_index: RuleIndex,
    source: &Rule,
) -> Result<CompiledRule<'arena>, CompileError> {
    let (head, variables) = compile_head(store, rule_index, &source.head)?;
    let tail = compile_regex(store, rule_index, &variables, &source.tail)?;
    Ok(CompiledRule {
        mode: source.mode,
        head,
        tail,
    })
}

/// Compiles one head coordinate and records variable declarations.
fn compile_head_pattern<'arena, ComponentType: ComponentDomain<'arena>>(
    store: &mut CanonicalStore<'arena>,
    rule: RuleIndex,
    pattern: &ComponentPattern<ComponentType>,
    variables: &mut VariableEnvironment,
) -> Result<CompiledPattern<'arena, ComponentType>, CompileError> {
    Ok(CompiledPattern::new(match pattern {
        ComponentPattern::Constant(value) => {
            ComponentPattern::Constant(ComponentType::compile(store.arena(), value))
        }
        ComponentPattern::Variable(name) => {
            let symbol = store.variables.get_or_intern(name);
            variables
                .bind(symbol, ComponentType::COMPONENT)
                .map_err(|_| CompileError::VariableComponentConflict {
                    rule,
                    name: name.to_owned(),
                })?;
            ComponentPattern::Variable(symbol)
        }
    }))
}

/// Compiles the fixed capability-product head and its variable type environment.
fn compile_head<'arena>(
    store: &mut CanonicalStore<'arena>,
    rule: RuleIndex,
    head: &Head,
) -> Result<(CompiledHead<'arena>, VariableEnvironment), CompileError> {
    let mut variables = VariableEnvironment::default();
    let principal =
        compile_head_pattern::<Principal>(store, rule, &head.principal, &mut variables)?;
    let action = compile_head_pattern::<Action>(store, rule, &head.action, &mut variables)?;
    let resource = compile_head_pattern::<Resource>(store, rule, &head.resource, &mut variables)?;
    Ok((
        CompiledHead {
            principal,
            action,
            resource,
        },
        variables,
    ))
}

/// Compiles one tail component pattern after resolving its source variable.
fn compile_pattern<'arena, ComponentType: ComponentDomain<'arena>>(
    store: &CanonicalStore<'arena>,
    rule: RuleIndex,
    pattern: &ComponentPattern<ComponentType>,
    variables: &VariableEnvironment,
) -> Result<CompiledPattern<'arena, ComponentType>, CompileError> {
    Ok(CompiledPattern::new(match pattern {
        ComponentPattern::Constant(value) => {
            ComponentPattern::Constant(ComponentType::compile(store.arena(), value))
        }
        ComponentPattern::Variable(name) => {
            let Some(symbol) = store.variables.get(name) else {
                return Err(CompileError::UnboundVariable {
                    rule,
                    name: name.to_owned(),
                });
            };
            variables
                .resolve(symbol, ComponentType::COMPONENT)
                .map_err(|error| match error {
                    ResolveError::Unbound => CompileError::UnboundVariable {
                        rule,
                        name: name.to_owned(),
                    },
                    ResolveError::ComponentConflict => CompileError::VariableComponentConflict {
                        rule,
                        name: name.to_owned(),
                    },
                })?;
            ComponentPattern::Variable(symbol)
        }
    }))
}

/// Compiles the concrete atom enum retained by hashconsed test nodes.
fn compile_atom_pattern<'arena>(
    store: &CanonicalStore<'arena>,
    rule: RuleIndex,
    pattern: &AtomPattern,
    variables: &VariableEnvironment,
) -> Result<CompiledAtomPattern<'arena>, CompileError> {
    Ok(match pattern {
        AtomPattern::Principal(pattern) => AtomPattern::Principal(
            compile_pattern::<Principal>(store, rule, pattern, variables)?.into_inner(),
        ),
        AtomPattern::Action(pattern) => AtomPattern::Action(
            compile_pattern::<Action>(store, rule, pattern, variables)?.into_inner(),
        ),
        AtomPattern::Resource(pattern) => AtomPattern::Resource(
            compile_pattern::<Resource>(store, rule, pattern, variables)?.into_inner(),
        ),
    })
}

/// Recursively compiles one owned boolean expression.
fn compile_test<'arena>(
    store: &mut CanonicalStore<'arena>,
    rule: RuleIndex,
    variables: &VariableEnvironment,
    source: &TestExpr,
) -> Result<TestId<'arena>, CompileError> {
    match source {
        TestExpr::True => Ok(store.test_true),
        TestExpr::False => Ok(store.test_false),
        TestExpr::Atom {
            comparison,
            pattern,
        } => {
            let pattern = compile_atom_pattern(store, rule, pattern, variables)?;
            Ok(store.tests.mk(TestNode::Atom {
                comparison: *comparison,
                pattern,
            }))
        }
        TestExpr::And(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_test(store, rule, variables, child)?);
            }
            Ok(store.test_and(compiled))
        }
        TestExpr::Or(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_test(store, rule, variables, child)?);
            }
            Ok(store.test_or(compiled))
        }
    }
}

/// Recursively compiles one owned regex expression through canonical smart constructors.
fn compile_regex<'arena>(
    store: &mut CanonicalStore<'arena>,
    rule: RuleIndex,
    variables: &VariableEnvironment,
    source: &RegexExpr,
) -> Result<RegexId<'arena>, CompileError> {
    match source {
        RegexExpr::Empty => Ok(store.empty),
        RegexExpr::All => Ok(store.all),
        RegexExpr::Epsilon => Ok(store.epsilon),
        RegexExpr::Test(test) => {
            let test = compile_test(store, rule, variables, test)?;
            Ok(store.regex_test(test))
        }
        RegexExpr::Union(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, rule, variables, child)?);
            }
            Ok(store.regex_union(compiled))
        }
        RegexExpr::Concat(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, rule, variables, child)?);
            }
            Ok(store.regex_concat(compiled))
        }
        RegexExpr::Star(inner) => {
            let inner = compile_regex(store, rule, variables, inner)?;
            Ok(store.regex_star(inner))
        }
        RegexExpr::Intersect(children) => {
            let mut compiled = Vec::with_capacity(children.len());
            for child in children {
                compiled.push(compile_regex(store, rule, variables, child)?);
            }
            Ok(store.regex_intersect(compiled))
        }
        RegexExpr::Not(inner) => {
            let inner = compile_regex(store, rule, variables, inner)?;
            Ok(store.regex_not(inner))
        }
    }
}
