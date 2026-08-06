mod builder;
mod compile;
mod derive;
mod node;
mod normalize;
mod pattern;
mod scope;
mod storage;

pub use builder::RuleSyntax;
pub use node::{Regex, Test};
pub use pattern::{AtomPattern, Comparison, Component, ComponentPattern, Head, RuleMode};

pub(crate) use node::RegexId;
pub(crate) use scope::CompiledHead;
pub(crate) use storage::SyntaxContext;

#[cfg(test)]
mod tests;
