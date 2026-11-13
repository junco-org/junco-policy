//! Specification hierarchy for the correctness of policy-refinement analysis.
//!
//! Each layer holds definitions, the theorem statements (`stmt_*` spec functions returning the
//! proposition), and their proofs (`theorem_*`, each with `ensures stmt_*(...)`). Every `stmt_*`
//! is proved. The mapping to the paper's results is the index `crate::verify::paper`.
//!
//! Layers, top-down:
//! - [`analyzer`]: what each analyzer query's verdict means, against [`semantics`].
//! - [`semantics`]: rules, statuses, policies, refinement over typed component values.
//! - [`policy_removal`]: arbitrary-id-list redundancy as preservation of deny/permit decisions.
//! - [`encoding`]: typed rules as numeric rules, through the existing verified front end
//!   (`flatten_rule`, `lower_flat`, `compile`), plus renaming invariance for fresh values.
//! - [`inclusion`]: constraints, `Split`, constrained inclusion, and the policy reduction.
//! - [`search`]: items, witnesses, successor cases, and the breadth-first search.
//! - [`pruning`]: state decomposition, dead items, domination, syntactic simulation.
//! - [`finiteness`]: finitely many reachable states, via the abstract model of `finite_states`.
//! - [`implementation`]: graph ids, interned constraints and letters as abstract objects.
pub mod analyzer;
pub mod encoding;
pub mod finiteness;
pub mod implementation;
pub mod inclusion;
pub mod policy_removal;
pub mod pruning;
pub mod search;
pub mod semantics;
