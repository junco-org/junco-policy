//! Arena-backed variable names used directly as map keys and compiled pattern payloads.

use std::borrow::Borrow;
use std::fmt;

/// Interned variable spelling represented by a stable arena reference rather than a table index.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct VariableName<'arena>(&'arena str);

impl<'arena> VariableName<'arena> {
    /// Wraps a spelling already owned by the validator arena.
    pub(super) const fn new(name: &'arena str) -> Self {
        Self(name)
    }
}

impl Borrow<str> for VariableName<'_> {
    fn borrow(&self) -> &str {
        self.0
    }
}

impl fmt::Debug for VariableName<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}
