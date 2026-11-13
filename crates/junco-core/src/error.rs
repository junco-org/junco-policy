// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use crate::limits::LimitError;
use alloc::borrow::ToOwned;
use alloc::string::String;
use vstd::prelude::*;

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryError {
    #[error("invalid history policy at {path}: {message}")]
    InvalidPolicy { path: String, message: &'static str },
    #[error("history variable {name:?} is not bound by request pattern")]
    UnboundVariable { name: String },
    /// An actual graph charge would exceed its byte budget.
    #[error("history symbolic graph budget exceeded: {0}")]
    GraphBudget(BudgetExceeded),
    /// A graph index, payload-size calculation, or case product is not representable.
    #[error("history graph index or product overflow")]
    IndexOverflow,
    #[error("history allocation failed")]
    AllocationFailed,
    #[error("history arena exhausted")]
    ArenaExhausted,
    #[error("history invariant violated: {message}")]
    Invariant { message: &'static str },
    #[error("history {domain} identity exhausted")]
    IdExhausted { domain: &'static str },
    #[error("unknown history {domain} identity {id}")]
    UnknownId { domain: &'static str, id: u64 },
    #[error("history belongs to another store")]
    WrongHistoryOwner,
    #[error("checkpoint does not belong to this history")]
    WrongCheckpointOwner,
    #[error("checkpoint is beyond the current history")]
    CheckpointBeyondHistory,
    #[error("history revision exhausted")]
    RevisionExhausted,
    #[error("history changed from revision {expected} to {actual}")]
    HistoryChanged { expected: u64, actual: u64 },
    #[error(transparent)]
    Limit(LimitError),
}

/// Exact accounting for a failed graph charge, kept valid across error propagation.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("{charged} charged + {requested} requested exceeds {limit} bytes")]
pub struct BudgetExceeded {
    limit: usize,
    charged: usize,
    requested: usize,
}

#[verus_verify]
impl BudgetExceeded {
    #[cfg(verus_keep_ghost)]
    verus! {
        /// The recorded limit, prior charge, and failed request, respectively.
        pub closed spec fn view(&self) -> (nat, nat, nat) {
            (self.limit as nat, self.charged as nat, self.requested as nat)
        }

        #[verifier::type_invariant]
        spec fn exceeded(&self) -> bool {
            self.charged as nat + self.requested as nat > self.limit as nat
        }
    }

    /// Records the inputs of a charge that cannot fit the given budget.
    #[verus_spec(result =>
        requires charged as nat + requested as nat > limit as nat,
        ensures result.view() == (limit as nat, charged as nat, requested as nat),
    )]
    pub const fn new(limit: usize, charged: usize, requested: usize) -> Self {
        Self { limit, charged, requested }
    }

    /// Byte limit of the graph whose charge failed.
    #[verus_spec(result => ensures result as nat == self.view().0)]
    pub const fn limit(&self) -> usize {
        self.limit
    }

    /// Byte charge immediately before the failed request.
    #[verus_spec(result => ensures result as nat == self.view().1)]
    pub const fn charged(&self) -> usize {
        self.charged
    }

    /// Additional bytes requested by the failed charge.
    #[verus_spec(result => ensures result as nat == self.view().2)]
    pub const fn requested(&self) -> usize {
        self.requested
    }

    /// Returns the exact limit, prior charge, and failed request.
    #[verus_spec(result => ensures
        (result.0 as nat, result.1 as nat, result.2 as nat) == self.view(),
        result.1 as nat + result.2 as nat > result.0 as nat,
    )]
    pub const fn evidence(&self) -> (usize, usize, usize) {
        proof! { use_type_invariant(self); }
        (self.limit, self.charged, self.requested)
    }
}

/// Preserves a result while exposing the invariant of any propagated budget error.
#[verus_verify]
#[inline]
#[verus_spec(output => ensures output == result, match output {
    Err(HistoryError::GraphBudget(evidence)) =>
        evidence.view().1 + evidence.view().2 > evidence.view().0,
    _ => true,
})]
pub fn graph_budget_result<T>(result: Result<T, HistoryError>) -> Result<T, HistoryError> {
    if let Err(HistoryError::GraphBudget(_evidence)) = &result {
        proof! { use_type_invariant(_evidence); }
    }
    result
}

#[verus_verify]
impl From<LimitError> for HistoryError {
    #[verus_spec(result => ensures result == Self::Limit(error))]
    fn from(error: LimitError) -> Self {
        Self::Limit(error)
    }
}

#[verus_verify]
impl HistoryError {
    #[verus_verify]
    #[verus_spec(result => ensures match result {
        Self::InvalidPolicy { path: owned, message: actual } => owned@ == path@ && actual == message,
        _ => false,
    })]
    pub fn invalid_policy(path: &str, message: &'static str) -> Self {
        Self::InvalidPolicy {
            path: path.to_owned(),
            message,
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result == (HistoryError::Invariant { message }))]
    pub const fn invariant(message: &'static str) -> HistoryError {
        HistoryError::Invariant { message }
    }

    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn normalization_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid normalization work stack",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn symbolic_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid symbolic work stack",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn invalid_truth_assignment() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid truth assignment",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn graph_id_overflow() -> HistoryError {
        HistoryError::Invariant {
            message: "graph ID does not fit usize",
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result is IndexOverflow)]
    #[inline]
    pub const fn graph_index_overflow() -> HistoryError {
        HistoryError::IndexOverflow
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn invalid_atom_set() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid primitive atom set",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn missing_transition_atom() -> HistoryError {
        HistoryError::Invariant {
            message: "transition primitive missing from atom set",
        }
    }
}

/// Rule-compilation failure detected before a validator can execute.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CompileError {
    /// The head must have exactly the event type's number of coordinates.
    #[error("head has {found} slots but the event type has {expected}")]
    HeadArity { expected: usize, found: usize },
    /// Tagged constants may only be used in their own coordinate.
    #[error("constant of coordinate {coordinate} used in coordinate {component}")]
    ComponentCoordinate { component: usize, coordinate: usize },
    /// One variable name occurs in different product components in the same rule.
    #[error("variable {name:?} occurs in different product components")]
    VariableComponentConflict { name: String },
    /// A tail references a variable that its head does not bind.
    #[error("tail variable {name:?} is not bound by the head")]
    UnboundVariable { name: String },
    #[error(transparent)]
    Runtime(HistoryError),
}

#[verus_verify]
impl From<HistoryError> for CompileError {
    #[verus_spec(result => ensures result == Self::Runtime(error))]
    fn from(error: HistoryError) -> Self {
        Self::Runtime(error)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl vstd::std_specs::convert::FromSpecImpl<LimitError> for HistoryError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: LimitError) -> Self { Self::Limit(error) }
}

impl vstd::std_specs::convert::FromSpecImpl<HistoryError> for CompileError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: HistoryError) -> Self { Self::Runtime(error) }
}

}
