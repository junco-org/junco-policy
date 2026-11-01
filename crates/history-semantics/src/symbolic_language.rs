//! A compiled tail stepped by classes of events instead of events.
//!
//! The runtime steps a residual by one event in three parts: it derives the residual
//! symbolically, evaluates the derivative's atoms on the event under the rule's bindings, and
//! interprets the derivative under those truth values. [`SymbolicLanguage`] exposes the first and
//! last parts, so a caller that knows only which atoms hold, such as a static analysis over
//! classes of events, follows exactly the runtime's derivatives and successors.
//!
//! This is a native facade. Graph construction, derivatives, atom collection and successor
//! interpretation are the verified runtime operations; the facade keeps their shared
//! precondition, a well-formed compiled pair, by owning the pair and rejecting identifiers that
//! do not belong to its graph.

use alloc::vec::Vec;
use history_store::cache::EventClass;
use history_store::graph::RuntimeKernel;
use junco_core::error::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::kernel::{KernelStore, Primitive, RegexId, TestView, TransitionId};
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
use smallvec::SmallVec;

use crate::progress::CompiledPair;
use crate::symbolic::RegexDerivative;

/// A compiled tail whose residuals are stepped by classes of events.
///
/// A class is given by the truth values of the positive atoms that a residual's derivative
/// tests: every event with those truth values has the same successor, under any bindings that
/// realize them. Residuals are canonical within one language, so equal identifiers denote equal
/// normal forms.
///
/// The graph has the runtime's fixed budget; an operation that would exceed it fails with
/// [`HistoryError::GraphLimit`].
#[derive(Debug)]
pub struct SymbolicLanguage {
    pair: CompiledPair,
}

impl SymbolicLanguage {
    /// Compiles a numeric tail into a fresh graph, as the runtime does.
    pub fn compile(template: &FlatPair<u64>) -> Result<Self, HistoryError> {
        let pair = CompiledPair::compile(template, &mut Unmetered, &mut ObservationWorld)?;
        Ok(Self { pair })
    }

    /// The residual of the empty history: the tail itself.
    pub fn root(&self) -> RegexId {
        self.pair.root
    }

    /// Whether `residual` is the canonical empty language. A residual whose language is empty
    /// need not be.
    pub fn is_empty(&self, residual: RegexId) -> bool {
        residual == self.pair.store.constants().empty
    }

    /// Whether `residual` accepts the empty history.
    pub fn nullable(&mut self, residual: RegexId) -> Result<bool, HistoryError> {
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        let kernel = RuntimeKernel {
            store: &mut self.pair.store,
            limits: &mut limits,
            world: &mut world,
        };
        Ok(kernel.regex(residual)?.nullable)
    }

    /// The derivative of `residual`, with the primitives of the positive atoms it tests in the
    /// order of the truth bits that [`SymbolicLanguage::successor`] takes.
    pub fn derive(
        &mut self,
        residual: RegexId,
    ) -> Result<(TransitionId, Vec<Primitive>), HistoryError> {
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        let transition = {
            let mut kernel = RuntimeKernel {
                store: &mut self.pair.store,
                limits: &mut limits,
                world: &mut world,
            };
            kernel.regex(residual)?;
            RegexId::derivative(residual, &mut kernel, &mut self.pair.caches.derivatives)?
        };
        self.pair
            .ensure_atoms(transition, &mut limits, &mut world)?;
        let atoms = CompiledPair::cached_atoms(self.pair.caches.atoms.as_slice(), transition)?;
        let kernel = RuntimeKernel {
            store: &mut self.pair.store,
            limits: &mut limits,
            world: &mut world,
        };
        let mut primitives = Vec::with_capacity(atoms.ids().len());
        for id in atoms.ids() {
            match kernel.test(*id)? {
                TestView::Atom {
                    primitive,
                    positive: true,
                } => primitives.push(primitive),
                _ => return Err(HistoryError::invalid_atom_set()),
            }
        }
        Ok((transition, primitives))
    }

    /// The residual after one event of the class whose atom truths are `truth`: bit `i % 64` of
    /// word `i / 64` is the truth of atom `i` of [`SymbolicLanguage::derive`]'s list.
    pub fn successor(
        &mut self,
        transition: TransitionId,
        truth: &[u64],
    ) -> Result<RegexId, HistoryError> {
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        {
            let kernel = RuntimeKernel {
                store: &mut self.pair.store,
                limits: &mut limits,
                world: &mut world,
            };
            kernel.transition(transition)?;
        }
        self.pair
            .ensure_atoms(transition, &mut limits, &mut world)?;
        let key = EventClass {
            transition,
            words: SmallVec::from_slice(truth),
        };
        self.pair.successor(key, &mut limits, &mut world)
    }
}
