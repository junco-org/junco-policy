//! Pruning of search states by antichains.
//!
//! A residual of `left ∩ ¬right` in normal form keeps the shape of a pair of a state of `left` and
//! a macrostate of `right`: it intersects the parts it requires with the complements of unions of
//! the pieces it avoids, and its language is the parts' languages intersected, minus the pieces'
//! languages. Two kinds of state need no expansion:
//!
//! - a *dead* state has a part all of whose pieces it avoids, so its language is empty;
//! - a *subsumed* state entails the constraint of an inserted state, requires every part and
//!   avoids every piece of it, so each of its counterexamples is one of the inserted state. This is
//!   the antichain order on pairs of a state and a macrostate, extended to constraints.
//!
//! Residuals are canonical, so parts and pieces are compared by identity. Inserted states are
//! never removed: a subsumed state's counterexamples belong to a state inserted no later, so
//! breadth-first order still reports a shortest counterexample.

use alloc::boxed::Box;
use alloc::vec::Vec;

use hashbrown::HashMap;
use history_semantics::SymbolicLanguage;
use junco_core::HistoryError;
use junco_core::kernel::{RegexId, RegexKindView};
use smallvec::SmallVec;

use crate::constraint::{ConstraintId, ConstraintTable};

/// Number of parts up to which a subsumption check looks up every subset of a state's parts.
/// Beyond it, only states with the same parts are compared, which loses pruning, not soundness.
const ENUMERATED_PARTS: usize = 4;

/// The parts a residual requires and the pieces it avoids.
pub(crate) struct Decomposition {
    /// In increasing identifier order.
    parts: SmallVec<[RegexId; 4]>,
    /// In increasing identifier order, without duplicates.
    pieces: SmallVec<[RegexId; 8]>,
}

impl Decomposition {
    /// An intersection requires its children that are not complements and avoids the pieces of
    /// the complemented ones; a complement avoids the pieces of its child; any other residual
    /// requires itself. The pieces of a union are its children, and of anything else itself.
    pub(crate) fn of(
        language: &mut SymbolicLanguage,
        residual: RegexId,
    ) -> Result<Self, HistoryError> {
        enum Root {
            Intersect(SmallVec<[RegexId; 4]>),
            Not(RegexId),
            Other,
        }
        let mut parts = SmallVec::new();
        let mut pieces = SmallVec::new();
        let root = language.read_regex(residual, |node| match node.kind {
            RegexKindView::Intersect(children) => Root::Intersect(SmallVec::from_slice(children)),
            RegexKindView::Not(child) => Root::Not(child),
            _ => Root::Other,
        })?;
        match root {
            Root::Intersect(children) => {
                for child in children {
                    let complemented = language.read_regex(child, |node| match node.kind {
                        RegexKindView::Not(inner) => Some(inner),
                        _ => None,
                    })?;
                    match complemented {
                        Some(inner) => push_pieces(language, inner, &mut pieces)?,
                        None => parts.push(child),
                    }
                }
            }
            Root::Not(child) => push_pieces(language, child, &mut pieces)?,
            Root::Other => parts.push(residual),
        }
        pieces.sort_unstable();
        pieces.dedup();
        Ok(Self { parts, pieces })
    }

    /// Whether some part has all of its pieces among the avoided ones, so that the residual has no
    /// histories.
    pub(crate) fn dead(&self, language: &mut SymbolicLanguage) -> Result<bool, HistoryError> {
        if self.pieces.is_empty() {
            return Ok(false);
        }
        for &part in &self.parts {
            let covered = language.read_regex(part, |node| match node.kind {
                RegexKindView::Union(children) => children.iter().all(|piece| self.avoids(*piece)),
                _ => self.avoids(part),
            })?;
            if covered {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn avoids(&self, piece: RegexId) -> bool {
        self.pieces.binary_search(&piece).is_ok()
    }
}

/// Appends the pieces of `residual`.
fn push_pieces(
    language: &mut SymbolicLanguage,
    residual: RegexId,
    pieces: &mut SmallVec<[RegexId; 8]>,
) -> Result<(), HistoryError> {
    language.read_regex(residual, |node| match node.kind {
        RegexKindView::Union(children) => pieces.extend_from_slice(children),
        _ => pieces.push(residual),
    })
}

/// Inserted states, grouped by their parts.
#[derive(Default)]
pub(crate) struct Antichain {
    groups: HashMap<SmallVec<[RegexId; 4]>, Vec<Entry>>,
}

struct Entry {
    constraint: ConstraintId,
    pieces: Box<[RegexId]>,
    /// One hashed bit per piece, so that the signature of a subset is contained in the set's.
    signature: u64,
}

impl Antichain {
    /// Whether an inserted state subsumes the state of `constraint` and `state`.
    pub(crate) fn subsumes(
        &self,
        constraints: &ConstraintTable,
        constraint: ConstraintId,
        state: &Decomposition,
    ) -> bool {
        let signature = signature(&state.pieces);
        let constraint = constraints.get(constraint);
        let covers = |entries: &Vec<Entry>| {
            entries.iter().any(|entry| {
                entry.signature & !signature == 0
                    && subset(&entry.pieces, &state.pieces)
                    && constraint.entails(constraints.get(entry.constraint))
            })
        };
        let parts = &state.parts;
        if parts.len() > ENUMERATED_PARTS {
            return self.groups.get(parts).is_some_and(covers);
        }
        (0..1_usize << parts.len()).any(|mask| {
            let subset = parts
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask & 1 << bit != 0)
                .map(|(_, part)| *part)
                .collect::<SmallVec<[RegexId; 4]>>();
            self.groups.get(&subset).is_some_and(covers)
        })
    }

    /// Records an inserted state.
    pub(crate) fn insert(&mut self, constraint: ConstraintId, state: Decomposition) {
        let signature = signature(&state.pieces);
        self.groups.entry(state.parts).or_default().push(Entry {
            constraint,
            pieces: state.pieces.into_iter().collect(),
            signature,
        });
    }
}

fn signature(pieces: &[RegexId]) -> u64 {
    pieces.iter().fold(0, |signature, piece| {
        signature | 1 << (u64::from(piece.get()).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 58)
    })
}

/// Whether every member of `small` is in `large`; both are in increasing order.
fn subset(small: &[RegexId], large: &[RegexId]) -> bool {
    let mut large = large.iter();
    small.iter().all(|piece| {
        large
            .by_ref()
            .find(|other| *other >= piece)
            .is_some_and(|other| other == piece)
    })
}
