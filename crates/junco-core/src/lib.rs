#![no_std]
// Verus generates erased unsafe scaffolding for native specifications.
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod compile;
pub mod error;
pub mod event;
pub mod flat;
pub mod flatten;
pub mod limits;
pub mod observation;
pub mod syntax;

#[cfg(feature = "runtime")]
pub(crate) mod graph;
#[cfg(feature = "runtime")]
pub(crate) mod kernel;
#[cfg(feature = "runtime")]
pub(crate) mod normalize;
#[cfg(feature = "runtime")]
pub(crate) mod progress;
#[cfg(feature = "runtime")]
pub(crate) mod symbolic;

#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod history;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod policy;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod runtime;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod store;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod typed;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod validator;

#[cfg(feature = "runtime")]
pub(crate) type WorkVec<T> = smallvec::SmallVec<[T; 4]>;

#[cfg(verus_keep_ghost)]
pub mod verify;

pub use compile::{FlatEncoder, lower_flat};
#[cfg(feature = "runtime")]
pub use error::PolicyError;
pub use error::{CompileError, HistoryError};
pub use event::{Event, Grant, Request};
pub use flatten::{ComponentValue, flatten_rule};
pub use frunk_core::Coprod;
pub use frunk_core::coproduct::{CNil, Coproduct};
#[cfg(feature = "runtime")]
pub use history::{Checkpoint, History};
#[cfg(feature = "runtime")]
pub use policy::{PolicyDecision, TraceDiagnostic, TracePolicy, TraceRule};
pub use syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
#[cfg(feature = "runtime")]
pub use typed::{CompiledRule, Store};
#[cfg(feature = "runtime")]
pub use validator::{Decision, Denial, Validator, ValidatorBuilder};
