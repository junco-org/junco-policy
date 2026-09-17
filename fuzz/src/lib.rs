#![deny(missing_docs)]
//! Trace-level generation and policy validation for the git trace policy.
//!
//! A trace is generated from fuzzer-chosen bytes and every candidate event is fed through the
//! checker exactly as a retained validator does: appended to the history on grant, dropped on deny.
//! Nothing in this crate touches git or the filesystem. [`validate_trace`] returns the granted
//! operations as plain data, and an external ground-truth executor — the git2 replay oracle in
//! `tests/git_oracle.rs` — replays them against a real repository.
//!
//! Generation is constrained so that the *filesystem* preconditions always hold independently of
//! the policy: a path is only created when it is currently absent, and only edited, deleted,
//! committed, or read when it is present. Every path lives in the seed commit and is never removed
//! from `HEAD`, so pathspec matching always succeeds and `checkout`/`stash` always have a source to
//! restore from. `Commit` requires working-tree presence, so a staged deletion — the state a
//! granted `Remove` (`git rm`) leaves behind — can never be committed and the path therefore never
//! leaves `HEAD`. The generator also tracks index membership, because `git rm` and a `git add` of
//! an absent path drop the index entry, and `Create` requires a tracked path: working-tree presence
//! therefore implies trackedness, so `stash`'s pathspec never misses and `git clean` is provably a
//! no-op on every pooled path — which is why `Clean` has no model effect. Every content mutation
//! embeds the monotonically increasing step index, so a write can never coincidentally reproduce
//! the committed blob.
//!
//! [`TraceGenerator`] is the only entropy-to-candidate implementation, so the replay oracle, the
//! criterion benchmark (through [`granted_history`]) and the libFuzzer target all drive identical
//! generation and can never diverge.

use std::env;
use std::time::{SystemTime, UNIX_EPOCH};

use arbitrary::Unstructured;
use rust_validator::{Action, Bump, Event, GitPolicy, PolicyDecision, Resource};

mod oracle;

pub use oracle::{Surprise, contended_events, no_surprise_violation};

/// Upper bound on generated trace length.
pub const MAX_TRACE_LENGTH: usize = 32;
/// Number of simulated agents; principals are `agent0 … agent{MAX_AGENT_NUMBER-1}`.
pub const MAX_AGENT_NUMBER: usize = 3;
/// Number of pooled repository paths `src/file{0..}.txt`.
pub const MAX_FILE_NUMBER: usize = 4;
/// Seed of the deterministic byte stream the fixed traces are chunked out of.
pub const DETERMINISTIC_SEED: u64 = 0x5eed_cafe_f00d_beef;
/// Number of fixed traces replayed from the seeded stream.
pub const SEEDED_TRACE_COUNT: usize = 32;
/// Number of freshly seeded traces the replay oracle adds to every run.
pub const RANDOM_TRACE_COUNT: usize = 16;
/// Environment variable that pins [`random_seed`], so a reported failure replays exactly.
pub const SEED_VARIABLE: &str = "JUNCO_FUZZ_SEED";
/// Fuzzer input bytes handed to each fixed trace.
pub const BYTES_PER_TRACE: usize = 256;
/// Entropy budget per requested granted event, for callers of [`granted_history`]: generation
/// spends ~3 bytes per step and denies a large fraction of them, and this value is proven
/// sufficient at length 1024 by both the criterion benchmark and the oracle's length sweep.
pub const BYTES_PER_EVENT: usize = 32;

/// Seed for the randomized trace set: [`SEED_VARIABLE`] when it is set, otherwise the wall clock,
/// so every run explores traces no previous run has replayed.
///
/// The replay oracle prints the seed it used on failure, which is what makes an exploratory run
/// reproducible: rerun with `JUNCO_FUZZ_SEED=0x…` to get the identical traces back.
///
/// # Panics
///
/// Panics if [`SEED_VARIABLE`] is set to something other than a decimal or `0x`-prefixed
/// hexadecimal `u64`, rather than silently exploring a different trace set than was asked for.
pub fn random_seed() -> u64 {
    let Ok(raw) = env::var(SEED_VARIABLE) else {
        return SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock is at or after the unix epoch")
            .as_nanos() as u64;
    };

    let text = raw.trim();
    let parsed = match text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        Some(hexadecimal) => u64::from_str_radix(hexadecimal, 16),
        None => text.parse(),
    };
    parsed.unwrap_or_else(|error| panic!("{SEED_VARIABLE}={raw} is not a u64 seed: {error}"))
}

/// Counters describing one generated and validated trace.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TraceSummary {
    /// Operations the policy granted, and which the replay oracle executes.
    pub granted: usize,
    /// Operations the policy denied, which are dropped without being replayed.
    pub denied: usize,
    /// Granted operations that were commits.
    pub commits: usize,
}

/// Runs one candidate through a retained Git policy; `true` means grant.
///
/// This is the single operation the benchmark times and the trace validator gates replay on.
pub fn check(policy: &mut GitPolicy<'_>, history: &[Event], candidate: &Event) -> bool {
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

/// Generates a policy-legal history of exactly `length` granted events from `data`, touching
/// neither git nor the filesystem. Every prefix of the result is itself a legal history, so
/// `&history[..n]` is a valid trace of length `n`.
///
/// # Panics
///
/// Panics if `data` is exhausted before `length` events are granted; supply more bytes.
pub fn granted_history(data: &[u8], length: usize) -> Vec<Event> {
    let mut generator = TraceGenerator::new(data);
    let arena = Bump::new();
    let mut policy = GitPolicy::new(&arena);
    let mut history = Vec::with_capacity(length);
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
/// Order is fixed: `read`, `edit`, `stage`, `unstage`, `commit`, `checkout`, `stash`, `diff`,
/// `history`, `delete`, `clean`.
pub fn probe_candidates() -> [(&'static str, Event); 11] {
    let probe = |action: Action| {
        Event::new(
            "agent0".to_string(),
            action,
            Resource::from(vec!["src".to_string(), "file0.txt".to_string()]),
        )
    };
    [
        ("read", probe(Action::Read)),
        ("edit", probe(Action::Edit)),
        ("stage", probe(Action::Stage)),
        ("unstage", probe(Action::Unstage)),
        ("commit", probe(Action::commit("probe"))),
        ("checkout", probe(Action::Checkout)),
        ("stash", probe(Action::Stash)),
        ("diff", probe(Action::Diff)),
        ("history", probe(Action::History)),
        ("delete", probe(Action::Delete)),
        ("clean", probe(Action::Clean)),
    ]
}

/// Generates one trace from `data` and reduces it to the operations the policy granted.
///
/// Empty or exhausted input yields a [`ValidatedTrace::default`]. Denied candidates advance the
/// counters only: they are replayed nowhere and leave the history and working-tree model untouched.
pub fn validate_trace(data: &[u8]) -> ValidatedTrace {
    let mut generator = TraceGenerator::new(data);
    let arena = Bump::new();
    let mut policy = GitPolicy::new(&arena);
    let budget = generator.step_budget();
    if budget == 0 {
        return ValidatedTrace::default();
    }

    let mut trace = ValidatedTrace::default();
    let mut history = Vec::new();
    for _ in 0..budget {
        let Some(candidate) = generator.next_candidate() else {
            break;
        };
        match policy.decide(&history, &candidate.event) {
            PolicyDecision::Grant => {
                generator.record_grant(&candidate);
                trace.summary.granted += 1;
                if candidate.operation == GeneratedOperation::Commit {
                    trace.summary.commits += 1;
                }
                trace.operations.push(ValidatedOperation {
                    agent: candidate.agent,
                    operation: candidate.operation,
                    file: candidate.file,
                    step: candidate.step,
                });
                history.push(candidate.event);
            }
            PolicyDecision::Deny {
                failed_precondition,
                ..
            } => {
                trace.summary.denied += 1;
                trace.denials.push(DeniedCandidate {
                    granted_prefix_len: history.len(),
                    event: candidate.event,
                    failed_precondition,
                });
            }
        }
    }

    trace.history = history;
    trace
}

/// One concrete generated operation; edit-like filesystem effects stay distinct for replay.
///
/// `Create`/`Modify`/`Delete` are distinct working-tree effects that all map onto the model's
/// single mutation action, [`Action::Edit`]; `Remove` is the one that maps to [`Action::Delete`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GeneratedOperation {
    /// Write a currently absent pooled path.
    Create,
    /// Append to a present pooled path.
    Modify,
    /// Remove a present pooled path from the working tree.
    Delete,
    /// `git add -- <path>`.
    Stage,
    /// `git restore --staged -- <path>`.
    Unstage,
    /// `git commit -m "step <n>" -- <path>`.
    Commit,
    /// `git checkout HEAD -- <path>`.
    Checkout,
    /// `git stash push -- <path>`.
    Stash,
    /// Read a present pooled path.
    Read,
    /// `git diff -- <path>`.
    Diff,
    /// `git log -- <path>`.
    History,
    /// `git rm -- <path>`.
    Remove,
    /// `git clean --force -- <path>`.
    Clean,
}

/// Every generated operation, in a fixed order so generation is deterministic.
const OPS: [GeneratedOperation; 13] = [
    GeneratedOperation::Create,
    GeneratedOperation::Modify,
    GeneratedOperation::Delete,
    GeneratedOperation::Stage,
    GeneratedOperation::Unstage,
    GeneratedOperation::Commit,
    GeneratedOperation::Checkout,
    GeneratedOperation::Stash,
    GeneratedOperation::Read,
    GeneratedOperation::Diff,
    GeneratedOperation::History,
    GeneratedOperation::Remove,
    GeneratedOperation::Clean,
];

impl GeneratedOperation {
    /// Lowercase name the replay oracle uses when it renders an operation in a failure report.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Create => "create",
            Self::Modify => "modify",
            Self::Delete => "delete",
            Self::Stage => "stage",
            Self::Unstage => "unstage",
            Self::Commit => "commit",
            Self::Checkout => "checkout",
            Self::Stash => "stash",
            Self::Read => "read",
            Self::Diff => "diff",
            Self::History => "history",
            Self::Remove => "remove",
            Self::Clean => "clean",
        }
    }

    /// The policy action this operation requests. Commit messages are per-step so distinct commits
    /// stay distinguishable in a rendered trace.
    fn action(self, step: usize) -> Action {
        match self {
            Self::Create | Self::Modify | Self::Delete => Action::Edit,
            Self::Stage => Action::Stage,
            Self::Unstage => Action::Unstage,
            Self::Commit => Action::commit(format!("step {step}")),
            Self::Checkout => Action::Checkout,
            Self::Stash => Action::Stash,
            Self::Read => Action::Read,
            Self::Diff => Action::Diff,
            Self::History => Action::History,
            Self::Remove => Action::Delete,
            Self::Clean => Action::Clean,
        }
    }
}

/// One policy-granted concrete operation ready for an external ground-truth executor.
///
/// Indices rather than rendered strings: the replay oracle formats `agent{agent}` and
/// `src/file{file}.txt` when it acts on them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedOperation {
    /// Agent index in `0..MAX_AGENT_NUMBER`; principal `agent{agent}`.
    pub agent: usize,
    /// The concrete operation to execute.
    pub operation: GeneratedOperation,
    /// Pooled path index in `0..MAX_FILE_NUMBER`; path `src/file{file}.txt`.
    pub file: usize,
    /// Zero-based generation step, also the commit message suffix for [`GeneratedOperation::Commit`].
    pub step: usize,
}

/// One candidate the policy denied, kept so a trace can be asked what a denial cost.
///
/// Named `DeniedCandidate`, not `Denial`: `rust_validator::Denial` is a different, exported type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeniedCandidate {
    /// Length of the granted history when the denial happened; the prefix that produced it is
    /// `&trace.history[..granted_prefix_len]`, because a denial never mutates history.
    pub granted_prefix_len: usize,
    /// The event the policy refused.
    pub event: Event,
    /// The denial's `failed_precondition` string, verbatim.
    pub failed_precondition: String,
}

/// A generated trace reduced to policy-granted operations plus grant/deny counters.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ValidatedTrace {
    /// Granted operations in generation order; replaying them in order is the property under test.
    pub operations: Vec<ValidatedOperation>,
    /// The granted events in order — the same values fed to the policy, for trace-level property
    /// checks such as [`no_surprise_violation`].
    pub history: Vec<Event>,
    /// Counters for the whole trace, including the denied candidates that were never replayed.
    pub summary: TraceSummary,
    /// Every denied candidate in generation order, for strictness analysis.
    pub denials: Vec<DeniedCandidate>,
}

/// One generated candidate operation, with the indices an executor needs to act on it.
#[derive(Clone, Debug)]
struct Candidate {
    agent: usize,
    operation: GeneratedOperation,
    file: usize,
    step: usize,
    event: Event,
}

/// Pure trace generation: entropy in, candidate operations out. Touches neither git nor the
/// filesystem, so the replay oracle and the benchmark can drive the identical generator.
struct TraceGenerator<'data> {
    unstructured: Unstructured<'data>,
    /// Working-tree presence per pooled path. An array, not a set, so iteration order (which feeds
    /// generation) is deterministic.
    exists: [bool; MAX_FILE_NUMBER],
    /// Index-entry presence per pooled path. A path leaves the index only via `git rm` or a
    /// `git add` of an already-absent path, and an untracked path is what would make
    /// `stash`'s pathspec fail and `clean` destructive, so `Create` is gated on it.
    tracked: [bool; MAX_FILE_NUMBER],
    step: usize,
}

impl<'data> TraceGenerator<'data> {
    /// Starts generation over `data` with every pooled path present and tracked, matching the seed
    /// commit.
    fn new(data: &'data [u8]) -> Self {
        Self {
            unstructured: Unstructured::new(data),
            exists: [true; MAX_FILE_NUMBER],
            tracked: [true; MAX_FILE_NUMBER],
            step: 0,
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
    /// precondition currently holds. Never wastes a step: the operation is chosen from those with
    /// at least one eligible path, and that set is never empty because `Stage`, `Unstage`,
    /// `Checkout`, `Stash`, `Diff`, `History`, and `Clean` accept every path.
    fn next_candidate(&mut self) -> Option<Candidate> {
        if self.unstructured.is_empty() {
            return None;
        }
        let agent = self
            .unstructured
            .int_in_range(0..=MAX_AGENT_NUMBER - 1)
            .ok()?;
        let ops: Vec<GeneratedOperation> = OPS
            .iter()
            .copied()
            .filter(|operation| !self.eligible(*operation).is_empty())
            .collect();
        let operation = *self.unstructured.choose(&ops).ok()?;
        let files = self.eligible(operation);
        let file = *self.unstructured.choose(&files).ok()?;

        let step = self.step;
        let event = Event::new(
            format!("agent{agent}"),
            operation.action(step),
            Resource::from(vec!["src".to_string(), format!("file{file}.txt")]),
        );
        self.step += 1;
        Some(Candidate {
            agent,
            operation,
            file,
            step,
            event,
        })
    }

    /// Applies the working-tree and index effect of a *granted* candidate.
    fn record_grant(&mut self, candidate: &Candidate) {
        let file = candidate.file;
        match candidate.operation {
            GeneratedOperation::Create => self.exists[file] = true,
            GeneratedOperation::Delete => self.exists[file] = false,
            // `git rm` drops the working-tree file *and* its index entry.
            GeneratedOperation::Remove => {
                self.exists[file] = false;
                self.tracked[file] = false;
            }
            // `git add -- p` stages whatever the working tree says: content when `p` is present,
            // its removal — which drops the index entry — when it is absent.
            GeneratedOperation::Stage => self.tracked[file] = self.exists[file],
            // `git restore --staged -- p` rewrites the index entry from `HEAD` without touching
            // the working tree, so it re-tracks a `git rm`-ed path.
            GeneratedOperation::Unstage => self.tracked[file] = true,
            // `git checkout HEAD -- p` and `git stash push -- p` both restore `p` from `HEAD` in
            // the working tree and in the index.
            GeneratedOperation::Checkout | GeneratedOperation::Stash => {
                self.exists[file] = true;
                self.tracked[file] = true;
            }
            GeneratedOperation::Commit
            | GeneratedOperation::Modify
            | GeneratedOperation::Read
            | GeneratedOperation::Diff
            | GeneratedOperation::History
            | GeneratedOperation::Clean => {}
        }
    }

    /// Pooled path indices, ascending, on which `operation` can be executed given working-tree
    /// presence and index trackedness.
    fn eligible(&self, operation: GeneratedOperation) -> Vec<usize> {
        (0..MAX_FILE_NUMBER)
            .filter(|&file| match operation {
                // Gating on `tracked` is what keeps `exists` implying `tracked`: recreating an
                // untracked path is the one way a pooled path could become untracked *content*.
                GeneratedOperation::Create => !self.exists[file] && self.tracked[file],
                GeneratedOperation::Modify
                | GeneratedOperation::Delete
                | GeneratedOperation::Remove
                | GeneratedOperation::Commit
                | GeneratedOperation::Read => self.exists[file],
                GeneratedOperation::Stage
                | GeneratedOperation::Unstage
                | GeneratedOperation::Checkout
                | GeneratedOperation::Stash
                | GeneratedOperation::Diff
                | GeneratedOperation::History
                | GeneratedOperation::Clean => true,
            })
            .collect()
    }
}
