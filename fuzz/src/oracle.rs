//! The no-surprise oracle: a simulated repository that decides, from modelled content, whether a
//! validated trace ever made one principal's knowledge of a resource wrong behind its back.
//!
//! Real git is this harness's ground truth for legality — `tests/git_oracle.rs` replays every
//! granted operation through libgit2 and asserts it is accepted — but it cannot decide surprise: it
//! has no notion of agents or of what an agent has seen. This module supplies that ground truth
//! instead. A content change is `worktree_after != worktree_before`, derived from the simulation
//! rather than from a list of which actions "are writes", which is what keeps the oracle
//! independent of the policy it checks.

use std::collections::BTreeMap;
use std::fmt;

use junco_policy::{Action, Event, GitEvent};

use crate::{Agent, PooledPath};

/// A working-tree blob. `0` is the seed commit's content and every `edit` at history index `i`
/// stamps `i + 1`, so no write can reproduce an earlier blob.
type Version = u64;

/// Modelled repository state for one resource. The index is not modelled: no transition reads it,
/// so it cannot change what a principal would observe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FileState {
    worktree: Option<Version>,
    head: Option<Version>,
}

impl FileState {
    /// The seed commit, in which every pooled path exists and is committed.
    const SEEDED: Self = Self {
        worktree: Some(0),
        head: Some(0),
    };

    /// Applies the event at `index` and returns the state after it.
    fn apply(self, action: Action, index: usize) -> Self {
        match action {
            Action::Edit => Self {
                worktree: Some(index as Version + 1),
                ..self
            },
            Action::Delete => Self {
                worktree: None,
                ..self
            },
            Action::Commit { .. } => Self {
                head: self.worktree,
                ..self
            },
            Action::Checkout | Action::Stash => Self {
                worktree: self.head,
                ..self
            },
            Action::Stage
            | Action::Unstage
            | Action::Clean
            | Action::Read
            | Action::Diff
            | Action::History => self,
        }
    }
}

/// A no-surprise violation: `principal` rewrote `resource`'s working-tree content and made another
/// principal's knowledge of it wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Surprise {
    /// Index in the granted history of the content-changing event.
    pub index: usize,
    /// Principal that changed the content.
    pub principal: String,
    /// The content-changing action, rendered by `Action`'s `Display`.
    pub action: String,
    /// Resource path, rendered by [`PooledPath`]'s `Display`.
    pub resource: String,
    /// Principal whose remembered content the change falsified.
    pub surprised: String,
    /// Index at which that principal last learned the content.
    pub learned_at: usize,
}

impl fmt::Display for Surprise {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "step {}: {} {} {}, which {} had last seen at step {}",
            self.index, self.principal, self.action, self.resource, self.surprised, self.learned_at,
        )
    }
}

/// Replays `history` through the modelled repository. Returns the first violation and how many
/// events acted on a resource another principal held an outstanding view of. Both answers come from
/// one fold so the two public entry points can never drift apart.
///
/// `BTreeMap`, not `HashMap`: with several surprised principals the reported one must be
/// deterministic.
fn replay(history: &[GitEvent<Agent, PooledPath>]) -> (Option<Surprise>, usize) {
    let mut files: BTreeMap<PooledPath, FileState> = BTreeMap::new();
    let mut views: BTreeMap<(Agent, PooledPath), (Option<Version>, usize)> = BTreeMap::new();
    let mut first: Option<Surprise> = None;
    let mut contended = 0usize;

    for (index, event) in history.iter().enumerate() {
        let (principal, action, resource) = (event.principal(), event.action(), event.resource());
        let before = *files.get(&resource).unwrap_or(&FileState::SEEDED);
        let after = before.apply(action, index);

        if views
            .keys()
            .any(|&(viewer, viewed)| viewed == resource && viewer != principal)
        {
            contended += 1;
        }

        if after.worktree != before.worktree && first.is_none() {
            for (&(viewer, viewed), &(remembered, learned_at)) in &views {
                if viewed == resource && viewer != principal && remembered == before.worktree {
                    first = Some(Surprise {
                        index,
                        principal: principal.to_string(),
                        action: action.to_string(),
                        resource: resource.to_string(),
                        surprised: viewer.to_string(),
                        learned_at,
                    });
                    break;
                }
            }
        }

        // A read hands the resource over: every other principal's view of it is superseded.
        if action == Action::Read {
            views.retain(|&(_, viewed), _| viewed != resource);
        }
        match action {
            Action::Read | Action::Edit => {
                views.insert((principal, resource), (after.worktree, index));
            }
            Action::Stage
            | Action::Delete
            | Action::Commit { .. }
            | Action::Checkout
            | Action::Stash => {
                views.remove(&(principal, resource));
            }
            Action::Unstage | Action::Diff | Action::History | Action::Clean => {}
        }
        files.insert(resource, after);
    }
    (first, contended)
}

/// The first no-surprise violation in `history`, or `None` when the trace has the property.
pub fn no_surprise_violation(history: &[GitEvent<Agent, PooledPath>]) -> Option<Surprise> {
    replay(history).0
}

/// How many events in `history` acted on a resource another principal held an outstanding view of —
/// the interleavings the property is about. A deterministic sweep whose total is zero would pass
/// [`no_surprise_violation`] vacuously.
pub fn contended_events(history: &[GitEvent<Agent, PooledPath>]) -> usize {
    replay(history).1
}

#[cfg(test)]
mod tests {
    use junco_policy::{History, MessageId, git_event};

    use super::*;
    use crate::{
        BYTES_PER_EVENT, BYTES_PER_TRACE, DETERMINISTIC_SEED, SEEDED_TRACE_COUNT, entropy,
        granted_history, validate_trace,
    };

    /// The first two simulated agents every hand-written trace below uses.
    const A: Agent = Agent(0);
    const B: Agent = Agent(1);

    /// One event on the pooled path every hand-written trace below acts on.
    fn event(agent: Agent, action: Action) -> GitEvent<Agent, PooledPath> {
        git_event(agent, action, PooledPath(0))
    }

    /// Every trace the fixed seeded stream produces, each paired with the source name a failure
    /// message names. The randomized set the replay oracle adds is not replayed here: this test
    /// must fail identically on every machine and every run.
    fn deterministic_traces() -> Vec<(String, History<GitEvent<Agent, PooledPath>>)> {
        let seeded = entropy(DETERMINISTIC_SEED, SEEDED_TRACE_COUNT * BYTES_PER_TRACE);
        seeded
            .chunks(BYTES_PER_TRACE)
            .enumerate()
            .map(|(index, bytes)| (format!("seed/{index}"), validate_trace(bytes).history))
            .collect()
    }

    #[test]
    fn every_deterministic_trace_has_the_no_surprise_property() {
        let traces = deterministic_traces();
        let mut contended = 0usize;
        for (source, history) in &traces {
            assert_eq!(
                no_surprise_violation(history.as_slice()),
                None,
                "{source} surprised a principal",
            );
            contended += contended_events(history.as_slice());
        }
        assert!(
            contended > 0,
            "no deterministic trace ever contended a resource, so the sweep proves nothing",
        );
    }

    #[test]
    fn the_oracle_reports_a_destroyed_view() {
        let history = [
            event(A, Action::Edit),
            event(B, Action::Read),
            event(A, Action::Checkout),
        ];
        assert_eq!(
            no_surprise_violation(&history),
            Some(Surprise {
                index: 2,
                principal: "agent0".to_string(),
                action: "checkout".to_string(),
                resource: "src/file0.txt".to_string(),
                surprised: "agent1".to_string(),
                learned_at: 1,
            }),
        );
    }

    #[test]
    fn a_checkout_of_a_pristine_resource_changes_nothing() {
        let history = [
            event(B, Action::Read),
            event(A, Action::Checkout),
            event(A, Action::Edit),
        ];
        // The checkout at index 1 restores content identical to the working tree, which the oracle
        // derives rather than assumes; only the edit at index 2 changes anything.
        assert_eq!(
            no_surprise_violation(&history).map(|surprise| surprise.index),
            Some(2),
        );
    }

    #[test]
    fn a_read_takes_the_resource_over() {
        let history = [
            event(A, Action::Read),
            event(B, Action::Read),
            event(B, Action::Edit),
        ];
        assert_eq!(no_surprise_violation(&history), None);
    }

    #[test]
    fn a_principal_is_never_surprised_by_its_own_change() {
        let history = [
            event(A, Action::Read),
            event(A, Action::Edit),
            event(A, Action::Stage),
            event(A, Action::commit(MessageId(1))),
        ];
        assert_eq!(no_surprise_violation(&history), None);
    }

    /// Lengths the criterion benchmark measures, so the property is proven exactly where the
    /// scaling numbers are reported. Seed counts fall as length rises because generation cost per
    /// trace grows with the history it re-checks at every step.
    const SWEEP: [(usize, u64); 6] = [
        (0, 256),
        (4, 256),
        (16, 256),
        (64, 128),
        (256, 32),
        (1024, 8),
    ];

    #[test]
    fn no_surprise_holds_at_benchmark_trace_lengths() {
        let mut contended = 0usize;
        for (length, seeds) in SWEEP {
            for seed in 0..seeds {
                let data = entropy(
                    seed.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    length * BYTES_PER_EVENT + 1,
                );
                let history = granted_history(&data, length);
                assert_eq!(
                    no_surprise_violation(history.as_slice()),
                    None,
                    "length {length} seed {seed} surprised a principal",
                );
                contended += contended_events(history.as_slice());
            }
        }
        assert!(contended > 0, "the sweep never contended a resource");
    }
}
