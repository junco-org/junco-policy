//! Typed variable symbols produced by the black-box string interner.

use string_interner::DefaultSymbol;

/// Interned variable spelling, distinct from symbols used as component values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct VariableSymbol(DefaultSymbol);

impl VariableSymbol {
    /// Wraps a symbol returned by the canonical store's string interner.
    pub(super) const fn new(symbol: DefaultSymbol) -> Self {
        Self(symbol)
    }
}
