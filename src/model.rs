//! Compact ownership-lock events for the shared [`Event`](history_syntax::Event) interface.

use core::fmt::{self, Debug};
use core::hash::Hash;

use history_syntax::Event;

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
