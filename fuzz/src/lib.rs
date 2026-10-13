#![deny(missing_docs)]
//! Trace-level generation and policy validation for the ownership-lock trace policy.
//!
//! A trace is generated from fuzzer-chosen bytes and every candidate event is fed through the
//! checker exactly as a retained validator does: appended to the history on grant, dropped on deny.
//! Nothing in this crate touches the filesystem. [`validate_trace`] returns the granted history,
//! which the no-surprise oracle ([`no_surprise_violation`]) judges from modelled content.
//!
//! Generation is constrained so that the *filesystem* preconditions always hold independently of
//! the policy: a path is only created when it is currently absent, and only modified, removed or
//! read when it is present. Every content mutation embeds the monotonically increasing step index,
//! so a write can never coincidentally reproduce an earlier blob.
//!
//! [`TraceGenerator`] is the only entropy-to-candidate implementation, so the oracle tests, the
//! criterion benchmark (through [`granted_history`]) and the libFuzzer target all drive identical
//! generation and can never diverge.

use std::fmt;

use arbitrary::Unstructured;
use junco_policy::{Action, Bump, History, LockEvent, LockPolicy, PolicyDecision};

mod oracle;

pub use oracle::{Surprise, contended_events, no_surprise_violation};

/// Upper bound on generated trace length.
pub const MAX_TRACE_LENGTH: usize = 32;
/// Number of simulated agents; principals are `agent0 … agent{MAX_AGENT_NUMBER-1}`.
pub const MAX_AGENT_NUMBER: usize = 3;
/// Number of pooled paths `src/file{0..}.txt`.
pub const MAX_FILE_NUMBER: usize = 4;
/// Seed of the deterministic byte stream the fixed traces are chunked out of.
pub const DETERMINISTIC_SEED: u64 = 0x5eed_cafe_f00d_beef;
/// Number of fixed traces replayed from the seeded stream.
pub const SEEDED_TRACE_COUNT: usize = 32;
/// Fuzzer input bytes handed to each fixed trace.
pub const BYTES_PER_TRACE: usize = 256;
/// Entropy budget per requested granted event, for callers of [`granted_history`]: generation
/// spends ~3 bytes per step and denies a fraction of them, and this value is proven sufficient at
/// length 1024 by both the criterion benchmark and the oracle's length sweep.
pub const BYTES_PER_EVENT: usize = 32;

/// Principal identity of a simulated agent: its index in `0..MAX_AGENT_NUMBER`.
///
/// Displays as `agent{index}`, the label diagnostics and oracle reports use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Agent(pub usize);

impl fmt::Display for Agent {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "agent{}", self.0)
    }
}

/// Resource identity of a pooled path: its index in `0..MAX_FILE_NUMBER`.
///
/// Displays as `src/file{index}.txt`, the label diagnostics and oracle reports use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PooledPath(pub usize);

impl fmt::Display for PooledPath {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "src/file{}.txt", self.0)
    }
}

/// Runs one candidate through a retained lock policy; `true` means grant.
///
/// This is the single operation the benchmark times and the trace validator gates history on.
pub fn check(
    policy: &mut LockPolicy<'_, Agent, PooledPath>,
    history: &History<LockEvent<Agent, PooledPath>>,
    candidate: &LockEvent<Agent, PooledPath>,
) -> bool {
    matches!(policy.decide(history, candidate), PolicyDecision::Grant)
}

/// Deterministic pseudo-random bytes: the entropy source wherever libFuzzer is not driving
/// generation. Identical `seed` and `length` always yield identical bytes.
pub fn entropy(seed: u64, length: usize) -> Vec<u8> {
    let mut state = seed;
    (0..length)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) as u8
        })
        .collect()
}

/// Generates a policy-legal history of exactly `length` granted events from `data`, touching no
/// filesystem. Every prefix of the result is itself a legal history, so
/// `&history.as_slice()[..n]` is a valid trace of length `n`.
///
/// # Panics
///
/// Panics if `data` is exhausted before `length` events are granted; supply more bytes.
pub fn granted_history(data: &[u8], length: usize) -> History<LockEvent<Agent, PooledPath>> {
    let mut generator = TraceGenerator::new(data);
    let arena = Bump::new();
    let mut policy = LockPolicy::new(&arena);
    let mut history = History::new();
    while history.len() < length {
        let Some(candidate) = generator.next_candidate() else {
            panic!(
                "entropy exhausted after {} of {length} granted events",
                history.len()
            );
        };
        if check(&mut policy, &history, &candidate.event) {
            generator.record_grant(&candidate);
            history.push(candidate.event);
        }
    }
    history
}

/// One probe candidate per [`Action`] variant, each by `agent0` on the first pooled path
/// `src/file0.txt`, paired with the lowercase action name used as the benchmark's function name.
pub fn probe_candidates() -> [(&'static str, LockEvent<Agent, PooledPath>); 4] {
    let probe = |action: Action| LockEvent::new(Agent(0), action, PooledPath(0));
    [
        ("read", probe(Action::Read)),
        ("edit", probe(Action::Edit)),
        ("release", probe(Action::Release)),
        ("remove", probe(Action::Remove)),
    ]
}

/// Generates one trace from `data` and reduces it to the events the policy granted.
///
/// Empty or exhausted input yields a [`ValidatedTrace::default`]. Denied candidates are recorded
/// only as denials: they leave the history and working-tree model untouched.
pub fn validate_trace(data: &[u8]) -> ValidatedTrace {
    let mut generator = TraceGenerator::new(data);
    let arena = Bump::new();
    let mut policy = LockPolicy::new(&arena);
    let mut trace = ValidatedTrace::default();
    for _ in 0..generator.step_budget() {
        let Some(candidate) = generator.next_candidate() else {
            break;
        };
        match policy.decide(&trace.history, &candidate.event) {
            PolicyDecision::Grant => {
                generator.record_grant(&candidate);
                trace.history.push(candidate.event);
            }
            PolicyDecision::Deny {
                failed_precondition,
                ..
            } => trace.denials.push(DeniedCandidate {
                granted_prefix_len: trace.history.len(),
                event: candidate.event,
                failed_precondition,
            }),
        }
    }
    trace
}

/// One concrete generated operation; edit-like filesystem effects stay distinct for the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GeneratedOperation {
    /// Write a currently absent pooled path ([`Action::Edit`]).
    Create,
    /// Rewrite a present pooled path ([`Action::Edit`]).
    Modify,
    /// Remove a present pooled path ([`Action::Remove`]).
    Delete,
    /// Read a present pooled path.
    Read,
    /// Relinquish ownership of any pooled path.
    Release,
}

/// Every generated operation, in a fixed order so generation is deterministic.
const OPS: [GeneratedOperation; 5] = [
    GeneratedOperation::Create,
    GeneratedOperation::Modify,
    GeneratedOperation::Delete,
    GeneratedOperation::Read,
    GeneratedOperation::Release,
];

impl GeneratedOperation {
    /// What an agent that just ran this operation on a path would naturally do next to it: a
    /// write is followed by its release. `None` for every operation that ends a unit of work.
    const fn follow_up(self) -> Option<Self> {
        match self {
            Self::Create | Self::Modify => Some(Self::Release),
            Self::Delete | Self::Read | Self::Release => None,
        }
    }

    /// The policy action this operation requests.
    fn action(self) -> Action {
        match self {
            Self::Create | Self::Modify => Action::Edit,
            Self::Delete => Action::Remove,
            Self::Read => Action::Read,
            Self::Release => Action::Release,
        }
    }
}

/// One candidate the policy denied, kept so a trace can be asked what a denial cost.
///
/// Named `DeniedCandidate`, not `Denial`: `junco_policy::Denial` is a different, exported type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeniedCandidate {
    /// Length of the granted history when the denial happened; the prefix that produced it is
    /// `&trace.history.as_slice()[..granted_prefix_len]`, because a denial never mutates history.
    pub granted_prefix_len: usize,
    /// The event the policy refused.
    pub event: LockEvent<Agent, PooledPath>,
    /// The denial's `failed_precondition` string, verbatim.
    pub failed_precondition: String,
}

/// A generated trace reduced to its policy-granted history plus every denial.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ValidatedTrace {
    /// The granted events in order, for trace-level property checks such as
    /// [`no_surprise_violation`].
    pub history: History<LockEvent<Agent, PooledPath>>,
    /// Every denied candidate in generation order, for strictness analysis.
    pub denials: Vec<DeniedCandidate>,
}

/// One generated candidate operation; its event's resource is the path the model applies it to.
#[derive(Clone, Debug)]
struct Candidate {
    operation: GeneratedOperation,
    event: LockEvent<Agent, PooledPath>,
}

/// The previous step's unit of work: one principal, one path, and what it last did to it.
#[derive(Clone, Copy, Debug)]
struct Burst {
    agent: Agent,
    operation: GeneratedOperation,
    file: PooledPath,
}

/// Pure trace generation: entropy in, candidate operations out.
struct TraceGenerator<'data> {
    unstructured: Unstructured<'data>,
    /// Presence per pooled path. An array, not a set, so iteration order (which feeds generation)
    /// is deterministic.
    exists: [bool; MAX_FILE_NUMBER],
    /// What the previous candidate did, so a principal can keep working on one path across steps.
    /// Recorded for denied candidates too: generation must not depend on what the policy decided.
    burst: Option<Burst>,
}

impl<'data> TraceGenerator<'data> {
    /// Starts generation over `data` with every pooled path present.
    fn new(data: &'data [u8]) -> Self {
        Self {
            unstructured: Unstructured::new(data),
            exists: [true; MAX_FILE_NUMBER],
            burst: None,
        }
    }

    /// Consumes the fuzzer-chosen step budget in `0..=MAX_TRACE_LENGTH` from the front of the
    /// input. Call at most once, before any candidate.
    fn step_budget(&mut self) -> usize {
        // `arbitrary` returns the range start rather than an error once input is exhausted, so
        // trace length is bounded by `is_empty` in `next_candidate`, never by an `Err`.
        self.unstructured
            .int_in_range(0..=MAX_TRACE_LENGTH)
            .unwrap_or(0)
    }

    /// Next candidate, or `None` once the entropy is spent.
    ///
    /// Draws an `(agent, operation, file)` triple, restricted to operations whose filesystem
    /// precondition currently holds; `Release` accepts every path, so a step is never wasted.
    /// Steps come in bursts — one principal working one path, often write-then-release — because
    /// independent draws would almost never release a principal's own write.
    fn next_candidate(&mut self) -> Option<Candidate> {
        if self.unstructured.is_empty() {
            return None;
        }

        // How the previous burst continues: `0` ends it and redraws the principal and the path,
        // `1` and `2` follow the pipeline on, `3` and `4` keep both but draw the operation freely.
        let continuation = match self.burst {
            Some(_) => self.unstructured.int_in_range(0u8..=4).ok()?,
            None => 0,
        };
        let burst = self.burst.filter(|_| continuation > 0);

        let agent = match burst {
            Some(burst) => burst.agent,
            None => Agent(
                self.unstructured
                    .int_in_range(0..=MAX_AGENT_NUMBER - 1)
                    .ok()?,
            ),
        };

        let pipelined = burst
            .filter(|_| continuation <= 2)
            .and_then(|burst| Some((burst.operation.follow_up()?, burst.file)))
            .filter(|&(operation, file)| self.eligible(operation).contains(&file));

        let (operation, file) = match pipelined {
            Some(step) => step,
            None => {
                let ops: Vec<GeneratedOperation> = OPS
                    .iter()
                    .copied()
                    .filter(|operation| !self.eligible(*operation).is_empty())
                    .collect();
                let operation = *self.unstructured.choose(&ops).ok()?;
                let files = self.eligible(operation);
                let file = match burst.filter(|burst| files.contains(&burst.file)) {
                    Some(burst) => burst.file,
                    None => *self.unstructured.choose(&files).ok()?,
                };
                (operation, file)
            }
        };
        self.burst = Some(Burst {
            agent,
            operation,
            file,
        });

        let event = LockEvent::new(agent, operation.action(), file);
        Some(Candidate { operation, event })
    }

    /// Applies the presence effect of a *granted* candidate.
    fn record_grant(&mut self, candidate: &Candidate) {
        let file = candidate.event.resource.0;
        match candidate.operation {
            GeneratedOperation::Create => self.exists[file] = true,
            GeneratedOperation::Delete => self.exists[file] = false,
            GeneratedOperation::Modify | GeneratedOperation::Read | GeneratedOperation::Release => {
            }
        }
    }

    /// Pooled paths, ascending, on which `operation` can be executed.
    fn eligible(&self, operation: GeneratedOperation) -> Vec<PooledPath> {
        (0..MAX_FILE_NUMBER)
            .map(PooledPath)
            .filter(|&PooledPath(file)| match operation {
                GeneratedOperation::Create => !self.exists[file],
                GeneratedOperation::Modify
                | GeneratedOperation::Delete
                | GeneratedOperation::Read => self.exists[file],
                GeneratedOperation::Release => true,
            })
            .collect()
    }
}
