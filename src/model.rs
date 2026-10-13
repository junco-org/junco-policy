//! Compact, statically dispatched capability-product events.
//!
//! An [`Event`] is any caller-defined `Copy` value projecting the three policy coordinates:
//! principal, action, and resource. Events carry compact caller identities such as small enums or
//! numeric IDs; human-readable labels live outside the evaluator. A finite Frunk [`Coproduct`] of
//! event payloads whose projections share component types is itself an event, dispatched by pattern
//! matching without trait objects. [`GitEvent`] is the built-in Git representation.

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

/// Caller-assigned identity of one commit message.
///
/// The message text lives outside the evaluator. Equal IDs must denote the same message wherever
/// they occur; a commit without a message is distinct from every ID, including one the caller
/// assigns to an empty message.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MessageId(pub u64);

impl fmt::Display for MessageId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

/// Git-like capability action.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Action {
    /// Observe resource contents.
    Read,
    /// Modify resource contents.
    Edit,
    /// Stage a resource.
    Stage,
    /// Remove a resource from the staging area.
    Unstage,
    /// Commit a staged resource, optionally with an exact message identity.
    Commit {
        /// Commit message identity. `None` is distinct from every present message.
        message: Option<MessageId>,
    },
    /// Restore a resource from the repository.
    Checkout,
    /// Stash local resource changes.
    Stash,
    /// Remove a resource from the working tree and stage the removal.
    Delete,
    /// Discard untracked working-tree content at a resource.
    Clean,
    /// Observe resource differences.
    Diff,
    /// Observe resource history.
    History,
}

impl Action {
    /// Creates a commit action with a present message.
    pub fn commit(message: MessageId) -> Self {
        Self::Commit {
            message: Some(message),
        }
    }

    /// Creates a commit action with no message field.
    pub fn commit_without_message() -> Self {
        Self::Commit { message: None }
    }

    /// Returns `true` for actions that observe a resource without changing its policy state:
    /// [`Action::Read`], [`Action::Diff`] and [`Action::History`].
    ///
    /// This classifies the capability itself. It inspects no command line, appends no event and
    /// moves no claim; whether a read is recorded in a history is the caller's decision.
    pub fn is_read(&self) -> bool {
        matches!(self, Self::Read | Self::Diff | Self::History)
    }

    /// Returns `true` for actions that change a resource's policy state: its contents, its
    /// staging, its committed history, or its presence in the working tree.
    ///
    /// Index and history transitions count even when no working-tree byte changes, because the
    /// policy's ownership rows hinge on them. Like [`Action::is_read`], this classifies the
    /// capability only and changes no history or rule.
    pub fn is_write(&self) -> bool {
        matches!(
            self,
            Self::Edit
                | Self::Stage
                | Self::Unstage
                | Self::Commit { .. }
                | Self::Checkout
                | Self::Stash
                | Self::Delete
                | Self::Clean
        )
    }
}

impl fmt::Display for Action {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read => formatter.write_str("read"),
            Self::Edit => formatter.write_str("edit"),
            Self::Stage => formatter.write_str("stage"),
            Self::Unstage => formatter.write_str("unstage"),
            Self::Commit {
                message: Some(message),
            } => write!(formatter, "commit({message})"),
            Self::Commit { message: None } => formatter.write_str("commit(<missing message>)"),
            Self::Checkout => formatter.write_str("checkout"),
            Self::Stash => formatter.write_str("stash"),
            Self::Delete => formatter.write_str("delete"),
            Self::Clean => formatter.write_str("clean"),
            Self::Diff => formatter.write_str("diff"),
            Self::History => formatter.write_str("history"),
        }
    }
}

/// Non-commit Git operation payload of a [`GitEvent`]; created only by [`git_event`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GitOperation<P, R> {
    principal: P,
    action: Action,
    resource: R,
}

impl<P, R> Event for GitOperation<P, R>
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

/// Commit payload of a [`GitEvent`]; created only by [`git_event`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GitCommit<P, R> {
    principal: P,
    message: Option<MessageId>,
    resource: R,
}

impl<P, R> Event for GitCommit<P, R>
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
        Action::Commit {
            message: self.message,
        }
    }

    fn resource(self) -> R {
        self.resource
    }
}

/// Built-in compact Git event: a Frunk union of [`GitOperation`] and [`GitCommit`].
///
/// Principals and resources are caller-owned compact identities; the caller renders their labels.
/// Values are created only by [`git_event`], so a commit is never stored as a plain operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// Spelled out because built-in derives reject type macros such as `Coprod!` in field types; this
// is exactly `Coprod!(GitOperation<P, R>, GitCommit<P, R>)`.
pub struct GitEvent<P, R>(Coproduct<GitOperation<P, R>, Coproduct<GitCommit<P, R>, CNil>>);

impl<P, R> Event for GitEvent<P, R>
where
    P: Copy + Debug + Eq + Hash,
    R: Copy + Debug + Eq + Hash,
{
    type Principal = P;
    type Action = Action;
    type Resource = R;

    fn principal(self) -> P {
        self.0.principal()
    }

    fn action(self) -> Action {
        self.0.action()
    }

    fn resource(self) -> R {
        self.0.resource()
    }
}

/// Creates a Git event, selecting [`GitCommit`] for commit actions and [`GitOperation`] otherwise.
pub fn git_event<P, R>(principal: P, action: Action, resource: R) -> GitEvent<P, R> {
    GitEvent(match action {
        Action::Commit { message } => Coproduct::inject(GitCommit {
            principal,
            message,
            resource,
        }),
        action => Coproduct::inject(GitOperation {
            principal,
            action,
            resource,
        }),
    })
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

#[cfg(test)]
mod tests {
    use frunk_core::coproduct::Coproduct;

    use super::{Action, Event, GitEvent, MessageId, git_event};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Actor(u32);

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Path(u32);

    #[test]
    fn action_predicates_classify_reads_and_state_changes() {
        let cases = [
            (Action::Read, true, false),
            (Action::Diff, true, false),
            (Action::History, true, false),
            (Action::Edit, false, true),
            (Action::Stage, false, true),
            (Action::Unstage, false, true),
            (Action::commit_without_message(), false, true),
            (Action::commit(MessageId(1)), false, true),
            (Action::Checkout, false, true),
            (Action::Stash, false, true),
            (Action::Delete, false, true),
            (Action::Clean, false, true),
        ];
        for (action, read, write) in cases {
            assert_eq!(action.is_read(), read, "{action} is_read");
            assert_eq!(action.is_write(), write, "{action} is_write");
        }
    }

    #[test]
    fn git_event_keeps_full_identity_and_selects_payload_by_action() {
        let commit = |action| -> GitEvent<Actor, Path> { git_event(Actor(1), action, Path(7)) };
        let first = commit(Action::commit(MessageId(1)));
        let second = commit(Action::commit(MessageId(2)));
        let missing = commit(Action::commit_without_message());
        assert_ne!(first, second);
        assert_ne!(first, missing);
        assert_ne!(second, missing);
        assert_eq!(first.action(), Action::commit(MessageId(1)));
        assert_eq!(missing.action(), Action::commit_without_message());
        for event in [first, second, missing] {
            assert!(matches!(event.0, Coproduct::Inr(Coproduct::Inl(_))));
        }

        let alice_edit = git_event(Actor(1), Action::Edit, Path(7));
        let bob_edit = git_event(Actor(2), Action::Edit, Path(7));
        assert_ne!(alice_edit, bob_edit);
        assert!(matches!(alice_edit.0, Coproduct::Inl(_)));
        assert_eq!(
            (
                alice_edit.principal(),
                alice_edit.action(),
                alice_edit.resource()
            ),
            (Actor(1), Action::Edit, Path(7))
        );
        assert_eq!(bob_edit.principal(), Actor(2));
    }
}
