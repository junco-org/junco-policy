use std::hash::Hash;

use string_interner::DefaultSymbol;

use crate::model::{Action, Principal, Resource};
use crate::validator::CompileError;

use super::node::CompiledAction;
use super::pattern::{AtomPattern, Component, ComponentPattern, Head};
use super::scope::{CompiledHead, Scope};
use super::storage::SyntaxContext;

trait ArenaComponent<'a>: Sized {
    const COMPONENT: Component;
    type Compiled: Clone + Copy + std::fmt::Debug + PartialEq + Eq + Hash;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> Self::Compiled;
}

impl<'a> ArenaComponent<'a> for Principal {
    const COMPONENT: Component = Component::Principal;
    type Compiled = &'a str;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> Self::Compiled {
        context.alloc_principal(value)
    }
}

impl<'a> ArenaComponent<'a> for Action {
    const COMPONENT: Component = Component::Action;
    type Compiled = CompiledAction<'a>;

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> Self::Compiled {
        CompiledAction::from_action(context.arena(), value)
    }
}

impl<'a> ArenaComponent<'a> for Resource {
    const COMPONENT: Component = Component::Resource;
    type Compiled = &'a [&'a str];

    fn intern(context: &SyntaxContext<'a>, value: &Self) -> Self::Compiled {
        context.alloc_resource(value)
    }
}

impl<'a> SyntaxContext<'a> {
    fn compile_head_pattern<T: ArenaComponent<'a>>(
        &mut self,
        rule: usize,
        pattern: &ComponentPattern<T>,
        scope: &mut Scope,
    ) -> Result<ComponentPattern<T::Compiled, DefaultSymbol>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => ComponentPattern::Constant(T::intern(self, value)),
            ComponentPattern::Variable(name) => {
                let symbol = self.variables.get_or_intern(name);
                scope.bind(rule, name, symbol, T::COMPONENT)?;
                ComponentPattern::Variable(symbol)
            }
        })
    }

    fn compile_pattern<T: ArenaComponent<'a>>(
        &self,
        rule: usize,
        pattern: &ComponentPattern<T>,
        scope: &Scope,
    ) -> Result<ComponentPattern<T::Compiled, DefaultSymbol>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => ComponentPattern::Constant(T::intern(self, value)),
            ComponentPattern::Variable(name) => {
                let Some(symbol) = self.variables.get(name) else {
                    return Err(CompileError::UnboundVariable {
                        rule,
                        name: name.to_owned(),
                    });
                };
                scope.resolve(rule, name, symbol, T::COMPONENT)?;
                ComponentPattern::Variable(symbol)
            }
        })
    }

    pub(super) fn compile_atom_pattern(
        &self,
        rule: usize,
        pattern: &AtomPattern,
        scope: &Scope,
    ) -> Result<AtomPattern<&'a str, CompiledAction<'a>, &'a [&'a str], DefaultSymbol>, CompileError>
    {
        Ok(match pattern {
            AtomPattern::Principal(pattern) => {
                AtomPattern::Principal(self.compile_pattern(rule, pattern, scope)?)
            }
            AtomPattern::Action(pattern) => {
                AtomPattern::Action(self.compile_pattern(rule, pattern, scope)?)
            }
            AtomPattern::Resource(pattern) => {
                AtomPattern::Resource(self.compile_pattern(rule, pattern, scope)?)
            }
        })
    }

    pub(super) fn compile_head(
        &mut self,
        rule: usize,
        head: &Head,
    ) -> Result<(CompiledHead<'a>, Scope), CompileError> {
        let mut scope = Scope::default();
        let principal = self.compile_head_pattern(rule, &head.principal, &mut scope)?;
        let action = self.compile_head_pattern(rule, &head.action, &mut scope)?;
        let resource = self.compile_head_pattern(rule, &head.resource, &mut scope)?;
        Ok((
            CompiledHead {
                principal,
                action,
                resource,
            },
            scope,
        ))
    }
}
