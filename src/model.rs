//! Compact, statically dispatched capability-product events.
//!
//! An [`Event`] is any caller-defined `Copy` value projecting the three policy coordinates:
//! principal, action, and resource. Events carry compact caller identities such as small enums or
//! numeric IDs; human-readable labels live outside the evaluator. A finite Frunk [`Coproduct`] of
//! event payloads whose projections share component types is itself an event, dispatched by pattern
//! matching without trait objects. [`LockEvent`] is the built-in event of [`crate::LockPolicy`].

use std::fmt::{self, Debug};
use std::hash::Hash;

use frunk_core::coproduct::{CNil, Coproduct};

/// Capability-product event matched by heads and tail atoms.
///
/// Equality and hashing must be the event's full identity: the variant and every payload field.
/// Projections are immutable value functions. An event's equality, hash, and projected components
/// must stay stable for as long as the value lives in a policy or history; equal component values
/// must denote the same caller value in constants, history, and candidates.
pub trait Event: Copy + Debug + Eq + Hash {
    /// Identity of the actor requesting a capability.
    type Principal: Copy + Debug + Eq + Hash;
    /// Requested operation.
    type Action: Copy + Debug + Eq + Hash;
    /// Protected resource.
    type Resource: Copy + Debug + Eq + Hash;

    /// Returns the actor requesting the capability.
    fn principal(self) -> Self::Principal;
    /// Returns the requested operation.
    fn action(self) -> Self::Action;
    /// Returns the protected resource.
    fn resource(self) -> Self::Resource;
}

/// Final variant of a Frunk event union.
impl<H: Event> Event for Coproduct<H, CNil> {
    type Principal = H::Principal;
    type Action = H::Action;
    type Resource = H::Resource;

    fn principal(self) -> Self::Principal {
        match self {
            Coproduct::Inl(head) => head.principal(),
            Coproduct::Inr(nil) => match nil {},
        }
    }

    fn action(self) -> Self::Action {
        match self {
            Coproduct::Inl(head) => head.action(),
            Coproduct::Inr(nil) => match nil {},
        }
    }

    fn resource(self) -> Self::Resource {
        match self {
            Coproduct::Inl(head) => head.resource(),
            Coproduct::Inr(nil) => match nil {},
        }
    }
}

/// Head variant of a Frunk event union whose tail projects the same component types.
impl<H, T, Rest> Event for Coproduct<H, Coproduct<T, Rest>>
where
    H: Event,
    Coproduct<T, Rest>: Event<Principal = H::Principal, Action = H::Action, Resource = H::Resource>,
{
    type Principal = H::Principal;
    type Action = H::Action;
    type Resource = H::Resource;

    fn principal(self) -> Self::Principal {
        match self {
            Coproduct::Inl(head) => head.principal(),
            Coproduct::Inr(tail) => tail.principal(),
        }
    }

    fn action(self) -> Self::Action {
        match self {
            Coproduct::Inl(head) => head.action(),
            Coproduct::Inr(tail) => tail.action(),
        }
    }

    fn resource(self) -> Self::Resource {
        match self {
            Coproduct::Inl(head) => head.resource(),
            Coproduct::Inr(tail) => tail.resource(),
        }
    }
}

/// Ownership-lock capability action.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Action {
    /// Observe resource contents; takes the resource's read claim.
    Read,
    /// Modify resource contents; acquires ownership of the resource.
    Edit,
    /// Relinquish ownership of the resource; the read claim is untouched.
    Release,
    /// An observed successful removal of the resource's name; clears ownership and read claim.
    Remove,
}

impl Action {
    /// Returns `true` for [`Action::Read`], the one action that changes no ownership.
    ///
    /// This classifies the capability itself. It inspects no command line, appends no event and
    /// moves no claim; whether a read is recorded in a history is the caller's decision.
    pub fn is_read(&self) -> bool {
        matches!(self, Self::Read)
    }

    /// Returns `true` for actions that mutate a resource's policy state — its ownership or
    /// presence — even when no byte changes, as for [`Action::Release`].
    pub fn is_write(&self) -> bool {
        matches!(self, Self::Edit | Self::Release | Self::Remove)
    }
}

impl fmt::Display for Action {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Read => "read",
            Self::Edit => "edit",
            Self::Release => "release",
            Self::Remove => "remove",
        })
    }
}

/// Built-in compact ownership-lock event.
///
/// Principals and resources are caller-owned compact identities; the caller renders their labels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LockEvent<P, R> {
    /// Actor requesting the capability.
    pub principal: P,
    /// Requested operation.
    pub action: Action,
    /// Protected resource.
    pub resource: R,
}

impl<P, R> LockEvent<P, R> {
    /// Creates a lock event.
    pub fn new(principal: P, action: Action, resource: R) -> Self {
        Self {
            principal,
            action,
            resource,
        }
    }
}

impl<P, R> Event for LockEvent<P, R>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    type Principal = P;
    type Action = Action;
    type Resource = R;

    fn principal(self) -> P {
        self.principal
    }

    fn action(self) -> Action {
        self.action
    }

    fn resource(self) -> R {
        self.resource
    }
}

/// Capability request with opaque caller metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request<E: Event, M> {
    /// Product event evaluated by the policy.
    pub event: E,
    /// Opaque value passed through unchanged on grant.
    pub metadata: M,
}

impl<E: Event, M> Request<E, M> {
    /// Creates a request from an event and opaque metadata.
    pub fn new(event: E, metadata: M) -> Self {
        Self { event, metadata }
    }
}

/// Accepted request echoed at the authorization boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant<E: Event, M> {
    /// Accepted event, also appended to committed history.
    pub event: E,
    /// Original request metadata, preserved unchanged.
    pub metadata: M,
}
