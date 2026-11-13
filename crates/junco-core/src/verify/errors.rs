//! Error guarantees shared by verified executable contracts.

use vstd::prelude::*;

verus! {
/// Resource failures and policy rejection remain distinct from impossible internal failures.
pub open spec fn no_invariant_failure<T>(result: Result<T, crate::error::HistoryError>) -> bool {
    !(result matches Err(crate::error::HistoryError::Invariant { .. }))
}

pub open spec fn no_internal_compile_error<T>(result: Result<T, crate::error::CompileError>) -> bool {
    !(result matches Err(crate::error::CompileError::Runtime(crate::error::HistoryError::Invariant { .. })))
}

}
