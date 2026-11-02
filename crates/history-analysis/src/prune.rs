//! Pruning of search states by antichains, up to simulation.
//!
//! A residual of `left ∩ ¬right` in normal form keeps the shape of a pair of a state of `left` and
//! a macrostate of `right`: it intersects the parts it requires with the complements of unions of
//! the pieces it avoids, and its language is the parts' languages intersected, minus the pieces'
//! languages. Two kinds of state need no expansion:
//!
//! - a *dead* state has a part whose pieces each lie below a piece it avoids, so its language is
//!   empty;
//! - a *subsumed* state entails the constraint of an inserted state, requires every part of it,
//!   and avoids a piece above each of its pieces, so each of its counterexamples is one of the
//!   inserted state. This is the antichain order on pairs of a state and a macrostate, extended to
//!   constraints and relaxed to simulation.
//!
//! Pieces are compared by the syntactic simulation of [`crate::simulation`], which contains
//! identity. Parts are compared by identity, so that inserted states can be indexed by their parts.
//! Inserted states are never removed: a subsumed state's counterexamples belong to a state inserted
//! no later, so breadth-first order still reports a shortest counterexample.

use alloc::boxed::Box;
use alloc::vec::Vec;

use hashbrown::HashMap;
use history_semantics::SymbolicLanguage;
use junco_core::HistoryError;
use junco_core::kernel::{RegexId, RegexKindView};
use smallvec::{SmallVec, smallvec};

use crate::constraint::{Constraint, ConstraintId, ConstraintTable};
use crate::simulation::Simulation;

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

    /// Whether some part has each of its pieces below an avoided piece, so that the residual has no
    /// histories.
    pub(crate) fn dead(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
    ) -> Result<bool, HistoryError> {
        if self.pieces.is_empty() {
            return Ok(false);
        }
        for &part in &self.parts {
            let members = language.read_regex(part, |node| match node.kind {
                RegexKindView::Union(children) => SmallVec::<[RegexId; 8]>::from_slice(children),
                _ => smallvec![part],
            })?;
            if simulation.covered(language, &members, &self.pieces)? {
                return Ok(true);
            }
        }
        Ok(false)
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
}

impl Antichain {
    /// Whether an inserted state subsumes the state of `constraint` and `state`.
    pub(crate) fn subsumes(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
        constraints: &ConstraintTable,
        constraint: ConstraintId,
        state: &Decomposition,
    ) -> Result<bool, HistoryError> {
        let constraint = constraints.get(constraint);
        let parts = &state.parts;
        if parts.len() > ENUMERATED_PARTS {
            return self.group_subsumes(
                language,
                simulation,
                constraints,
                constraint,
                parts,
                state,
            );
        }
        for mask in 0_usize..1 << parts.len() {
            let subset = parts
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask & 1 << bit != 0)
                .map(|(_, part)| *part)
                .collect::<SmallVec<[RegexId; 4]>>();
            if self.group_subsumes(
                language,
                simulation,
                constraints,
                constraint,
                &subset,
                state,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether an inserted state with exactly `parts` subsumes the state.
    fn group_subsumes(
        &self,
        language: &mut SymbolicLanguage,
        simulation: &mut Simulation,
        constraints: &ConstraintTable,
        constraint: &Constraint,
        parts: &[RegexId],
        state: &Decomposition,
    ) -> Result<bool, HistoryError> {
        let Some(entries) = self.groups.get(parts) else {
            return Ok(false);
        };
        for entry in entries {
            if constraint.entails(constraints.get(entry.constraint))
                && simulation.covered(language, &entry.pieces, &state.pieces)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Records an inserted state.
    pub(crate) fn insert(&mut self, constraint: ConstraintId, state: Decomposition) {
        self.groups.entry(state.parts).or_default().push(Entry {
            constraint,
            pieces: state.pieces.into_iter().collect(),
        });
    }
}
