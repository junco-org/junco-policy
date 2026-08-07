//! Source-to-arena compilation for heads and atom patterns.
//!
//! Compilation performs two related jobs. Constants are copied into immutable arena-backed forms
//! selected by [`Match`], and variable names are interned and checked against the rule's typed head
//! scope. Head compilation binds variables; tail compilation may only resolve those bindings.

use string_interner::DefaultSymbol;

use crate::model::{Action, Principal, Resource};
use crate::validator::{CompileError, RuleIndex};

use super::component::{CompiledAtomPattern, Match};
use super::pattern::{AtomPattern, ComponentPattern, Head};
use super::scope::{CompiledHead, Scope};
use super::storage::SyntaxContext;

impl<'arena> SyntaxContext<'arena> {
    /// Compiles one head coordinate, adding variable occurrences to `scope`.
    fn compile_head_pattern<ComponentType: Match<'arena>>(
        &mut self,
        rule: RuleIndex,
        pattern: &ComponentPattern<ComponentType>,
        scope: &mut Scope,
    ) -> Result<ComponentPattern<ComponentType::Compiled, DefaultSymbol>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => {
                ComponentPattern::Constant(ComponentType::compile(self.arena(), value))
            }
            ComponentPattern::Variable(name) => {
                let symbol = self.variables.get_or_intern(name);
                scope.bind(rule, name, symbol, ComponentType::COMPONENT)?;
                ComponentPattern::Variable(symbol)
            }
        })
    }

    /// Compiles one tail coordinate, requiring every variable to be present in `scope` with the
    /// same component type used by the head.
    fn compile_pattern<ComponentType: Match<'arena>>(
        &self,
        rule: RuleIndex,
        pattern: &ComponentPattern<ComponentType>,
        scope: &Scope,
    ) -> Result<ComponentPattern<ComponentType::Compiled, DefaultSymbol>, CompileError> {
        Ok(match pattern {
            ComponentPattern::Constant(value) => {
                ComponentPattern::Constant(ComponentType::compile(self.arena(), value))
            }
            ComponentPattern::Variable(name) => {
                let Some(symbol) = self.variables.get(name) else {
                    return Err(CompileError::UnboundVariable {
                        rule,
                        name: name.to_owned(),
                    });
                };
                scope.resolve(rule, name, symbol, ComponentType::COMPONENT)?;
                ComponentPattern::Variable(symbol)
            }
        })
    }

    /// Compiles one typed source atom into the concrete hashable atom enum stored by `TestNode`.
    pub(super) fn compile_atom_pattern(
        &self,
        rule: RuleIndex,
        pattern: &AtomPattern,
        scope: &Scope,
    ) -> Result<CompiledAtomPattern<'arena>, CompileError> {
        Ok(match pattern {
            AtomPattern::Principal(pattern) => {
                AtomPattern::Principal(self.compile_pattern::<Principal>(rule, pattern, scope)?)
            }
            AtomPattern::Action(pattern) => {
                AtomPattern::Action(self.compile_pattern::<Action>(rule, pattern, scope)?)
            }
            AtomPattern::Resource(pattern) => {
                AtomPattern::Resource(self.compile_pattern::<Resource>(rule, pattern, scope)?)
            }
        })
    }

    /// Compiles the fixed capability-product head and returns its validated variable scope.
    pub(super) fn compile_head(
        &mut self,
        rule: RuleIndex,
        head: &Head,
    ) -> Result<(CompiledHead<'arena>, Scope), CompileError> {
        let mut scope = Scope::default();
        let principal =
            self.compile_head_pattern::<Principal>(rule, &head.principal, &mut scope)?;
        let action = self.compile_head_pattern::<Action>(rule, &head.action, &mut scope)?;
        let resource = self.compile_head_pattern::<Resource>(rule, &head.resource, &mut scope)?;
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
