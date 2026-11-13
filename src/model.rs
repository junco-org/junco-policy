//! Compact ownership-lock events for the shared [`Event`](history_syntax::Event) interface.

use core::fmt::{self, Debug};
use core::hash::Hash;

use history_syntax::{Event, N3};

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

/// Tagged coordinate of a [`LockEvent`], ordered as principal, action, resource.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LockComponent<P, R> {
    /// Actor at coordinate zero.
    Principal(P),
    /// Requested operation at coordinate one.
    Action(Action),
    /// Protected resource at coordinate two.
    Resource(R),
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

// Hypothesis (D4): this crate is not verified, so `event_laws::<LockEvent<P, R>>` (R1) is assumed,
// not proved: arity 3; `coordinate(component(e, i)) == i`; every tuple tagged 0, 1, 2 is the view
// of `LockEvent::new(p, a, r)`. Converting to the verified tuple `(P, Action, R)` would drop the
// named `LockComponent` variants from the public API, so the impl stays hand-written.
impl<P, R> Event for LockEvent<P, R>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    type Component = LockComponent<P, R>;
    type Arity = N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => LockComponent::Principal(self.principal),
            1 => LockComponent::Action(self.action),
            _ => LockComponent::Resource(self.resource),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            LockComponent::Principal(_) => 0,
            LockComponent::Action(_) => 1,
            LockComponent::Resource(_) => 2,
        }
    }
}
