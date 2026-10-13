//! Tracked committed-history owners.
//!
//! A [`History`] owns its events and a private process-unique identity plus truncation revision.
//! Appending preserves both, so evaluators may resume retained progress over only the appended
//! suffix. Every shortening increments the revision before events change, and clones receive a
//! fresh identity, so retained progress can never be applied to a sequence it did not observe.
//! No mutable slice escapes: replacement is truncate-and-append or a new owner.

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::model::Event;

/// Next unallocated history identity. Zero is never issued.
static NEXT_HISTORY_ID: AtomicU64 = AtomicU64::new(1);

/// Process-unique identity of one [`History`] owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct HistoryId(u64);

impl HistoryId {
    /// Allocates a fresh identity, panicking rather than wrapping on exhaustion.
    fn fresh() -> Self {
        let id = NEXT_HISTORY_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
                next.checked_add(1)
            })
            .expect("history identity space exhausted");
        Self(id)
    }
}

/// Number of length-reducing truncations applied to one [`History`] owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Revision(u64);

impl Revision {
    /// Returns the next revision, panicking rather than wrapping on exhaustion.
    fn next(self) -> Self {
        Self(
            self.0
                .checked_add(1)
                .expect("history revision space exhausted"),
        )
    }
}

/// Opaque owner-specific committed-history length marker.
///
/// A checkpoint is produced only by [`History::checkpoint`] and is accepted only by
/// [`History::rollback`] on the same owner. It records a length, not a saved branch, and remains
/// reusable after later appends or rollbacks on that owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Checkpoint {
    owner: HistoryId,
    len: usize,
}

/// Committed event sequence with a tracked identity for exact incremental evaluation.
///
/// Equality and `Debug` observe only the event sequence. Cloning copies the events into a new
/// owner with a fresh identity, so cached progress of the original never applies to the clone.
pub struct History<E: Event> {
    events: Vec<E>,
    id: HistoryId,
    revision: Revision,
}

impl<E: Event> History<E> {
    /// Creates an empty history owner.
    pub fn new() -> Self {
        Self::from_events([])
    }

    /// Creates a history owner containing `events` in order.
    pub fn from_events(events: impl IntoIterator<Item = E>) -> Self {
        Self {
            events: events.into_iter().collect(),
            id: HistoryId::fresh(),
            revision: Revision(0),
        }
    }

    /// Appends one committed event.
    pub fn push(&mut self, event: E) {
        self.events.push(event);
    }

    /// Shortens the history to `len` events; does nothing when `len` is at least the current
    /// length.
    ///
    /// # Panics
    /// Panics if the truncation revision space is exhausted. The history is unchanged then.
    pub fn truncate(&mut self, len: usize) {
        if len >= self.events.len() {
            return;
        }
        self.revision = self.revision.next();
        self.events.truncate(len);
    }

    /// Returns the committed events in order.
    pub fn as_slice(&self) -> &[E] {
        &self.events
    }

    /// Iterates the committed events in order.
    pub fn iter(&self) -> std::slice::Iter<'_, E> {
        self.events.iter()
    }

    /// Returns the number of committed events.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Returns `true` when no event has been committed.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Captures the current length of this owner in constant time.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            owner: self.id,
            len: self.events.len(),
        }
    }

    /// Restores this owner to a previously captured length.
    ///
    /// # Panics
    /// Panics before any mutation if `checkpoint` was captured from another owner or lies beyond
    /// the current length.
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        assert!(
            checkpoint.owner == self.id,
            "checkpoint does not belong to this history"
        );
        assert!(
            checkpoint.len <= self.events.len(),
            "checkpoint is beyond the current history"
        );
        self.truncate(checkpoint.len);
    }

    /// Process-unique identity of this owner.
    pub(crate) fn id(&self) -> HistoryId {
        self.id
    }

    /// Current truncation revision of this owner.
    pub(crate) fn revision(&self) -> Revision {
        self.revision
    }
}

impl<E: Event> Default for History<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Event> FromIterator<E> for History<E> {
    fn from_iter<I: IntoIterator<Item = E>>(events: I) -> Self {
        Self::from_events(events)
    }
}

impl<E: Event> Clone for History<E> {
    /// Copies the events into a new owner with a fresh identity and revision zero.
    fn clone(&self) -> Self {
        Self {
            events: self.events.clone(),
            id: HistoryId::fresh(),
            revision: Revision(0),
        }
    }
}

impl<E: Event> fmt::Debug for History<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("History")
            .field(&self.events)
            .finish()
    }
}

impl<E: Event> PartialEq for History<E> {
    fn eq(&self, other: &Self) -> bool {
        self.events == other.events
    }
}

impl<E: Event> Eq for History<E> {}

#[cfg(test)]
mod tests {
    use super::{History, Revision};
    use crate::model::{Action, LockEvent};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Actor(u32);

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Path(u32);

    fn read(actor: Actor) -> LockEvent<Actor, Path> {
        LockEvent::new(actor, Action::Read, Path(0))
    }

    #[test]
    fn clone_is_an_equal_new_owner_at_revision_zero() {
        let mut original = History::from_events([read(Actor(1)), read(Actor(2)), read(Actor(3))]);
        original.truncate(2);
        assert_eq!(original.revision(), Revision(1));

        let clone = original.clone();
        assert_eq!(clone, original);
        assert_ne!(clone.id(), original.id());
        assert_eq!(clone.revision(), Revision(0));
    }

    #[test]
    fn only_real_shortening_advances_the_revision() {
        let mut history = History::new();
        let empty = history.checkpoint();
        history.push(read(Actor(1)));
        history.push(read(Actor(2)));
        assert_eq!(history.revision(), Revision(0));

        history.truncate(2);
        history.truncate(5);
        history.rollback(history.checkpoint());
        assert_eq!(history.revision(), Revision(0));

        history.truncate(1);
        assert_eq!(history.revision(), Revision(1));
        assert_eq!(history.as_slice(), [read(Actor(1))]);

        history.push(read(Actor(3)));
        assert_eq!(history.revision(), Revision(1));
        history.rollback(empty);
        assert_eq!(history.revision(), Revision(2));
        assert!(history.is_empty());
    }

    #[test]
    fn every_constructor_allocates_a_distinct_identity() {
        let ids = [
            History::<LockEvent<Actor, Path>>::new().id(),
            History::<LockEvent<Actor, Path>>::new().id(),
            History::<LockEvent<Actor, Path>>::default().id(),
            [read(Actor(1))].into_iter().collect::<History<_>>().id(),
        ];
        for (index, id) in ids.iter().enumerate() {
            assert!(!ids[index + 1..].contains(id));
        }
    }
}
