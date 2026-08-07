//! Compilation and execution of the capability-product past-regex language.
//!
//! Source patterns are typed by product component. Rule construction compiles owned constants
//! into arena-backed values, interns variable names, checks variable scope, and normalizes tests
//! and regexes into hashconsed DAGs. Runtime evaluation binds a candidate head and folds exact
//! Brzozowski derivatives over the committed pre-candidate history.

mod builder;
mod compile;
mod component;
mod derive;
mod identity;
mod node;
mod normalize;
mod pattern;
mod scope;
mod storage;

pub use builder::RuleSyntax;
pub use node::{Regex, Test};
pub use pattern::{AtomPattern, Comparison, Component, ComponentPattern, Head, RuleMode};

pub(crate) use identity::ContextId;
pub(crate) use node::RegexId;
pub(crate) use scope::CompiledHead;
pub(crate) use storage::SyntaxContext;

#[cfg(test)]
mod tests;
