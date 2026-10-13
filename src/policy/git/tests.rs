//! The table this module encodes, checked against an independent literal oracle.

use std::fmt;

use super::languages::{clean_lang, staged_lang, unstaged_other_lang, unstaged_self_lang};
use super::{GitPolicy, git_decision};
use crate::policy::PolicyDecision;
use crate::syntax::{CanonicalStore, compile_rule};
use crate::{
    Action, Bump, ComponentPattern, GitEvent, Head, History, MessageId, Rule, RuleMode, git_event,
};

/// The two principals the literal oracle names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Who {
    Me,
    Other,
}

impl fmt::Display for Who {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Me => "self",
            Self::Other => "other",
        })
    }
}

/// The one resource every oracle row acts on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SrcX;

impl fmt::Display for SrcX {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("src/x")
    }
}

fn event(who: Who, action: Action) -> GitEvent<Who, SrcX> {
    git_event(who, action, SrcX)
}

/// History whose fold lands the resource in the named row (candidate principal is "self").
fn history_for(row: &str) -> History<GitEvent<Who, SrcX>> {
    History::from_events(match row {
        "clean" => vec![],
        "staged" => vec![event(Who::Me, Action::Edit), event(Who::Me, Action::Stage)],
        "unstaged-self" => vec![event(Who::Me, Action::Edit)],
        "unstaged-other" => vec![event(Who::Other, Action::Edit)],
        other => panic!("unknown row {other}"),
    })
}

fn grant() -> PolicyDecision {
    PolicyDecision::Grant
}

fn denial(precondition: &str, fixes: &[&str]) -> PolicyDecision {
    PolicyDecision::Deny {
        failed_precondition: precondition.to_string(),
        allowed_fixes: fixes.iter().map(|f| f.to_string()).collect(),
    }
}

fn opf() -> Vec<String> {
    vec![
        "other stage src/x".to_string(),
        "other checkout src/x".to_string(),
        "other stash src/x".to_string(),
        "self only reads, diffs, or histories src/x".to_string(),
    ]
}

/// Independent oracle: the reduced default table for candidate principal "self", resource
/// "src/x", foreign owner "other". Strings are literal to pin the Rust translation. The commit
/// branch is message-agnostic: `commit(MessageId(1))` and `commit_without_message()` yield the
/// same per-row result.
fn oracle(row: &str, action: &Action) -> PolicyDecision {
    match action {
        Action::Read | Action::Diff | Action::History => grant(),
        Action::Delete => match row {
            "clean" => grant(),
            "staged" => denial(
                "delete requires a resource with no staged or unstaged changes",
                &["self commit src/x before deleting", "self checkout src/x before deleting"],
            ),
            "unstaged-self" => denial(
                "delete requires a resource with no staged or unstaged changes",
                &["self checkout src/x before deleting", "self stash src/x before deleting"],
            ),
            _ => PolicyDecision::Deny {
                failed_precondition:
                    "src/x is unstaged by other; delete would discard other's dirty resource"
                        .to_string(),
                allowed_fixes: opf(),
            },
        },
        Action::Clean => match row {
            "unstaged-other" => PolicyDecision::Deny {
                failed_precondition:
                    "src/x is unstaged by other; clean would discard other's dirty resource"
                        .to_string(),
                allowed_fixes: opf(),
            },
            _ => grant(),
        },
        Action::Edit => match row {
            "unstaged-other" => PolicyDecision::Deny {
                failed_precondition:
                    "src/x is unstaged by other; self may read, diff, or history it but may not edit it"
                        .to_string(),
                allowed_fixes: opf(),
            },
            _ => grant(),
        },
        Action::Checkout => match row {
            "unstaged-other" => PolicyDecision::Deny {
                failed_precondition:
                    "src/x is unstaged by other; checkout would discard or replace other's dirty resource"
                        .to_string(),
                allowed_fixes: opf(),
            },
            _ => grant(),
        },
        Action::Stage => match row {
            "unstaged-self" => grant(),
            "clean" => denial(
                "stage requires an unstaged resource owned by the acting principal",
                &["self edit src/x before staging"],
            ),
            "staged" => denial(
                "stage requires an unstaged resource owned by the acting principal",
                &["self unstage src/x before staging again"],
            ),
            _ => PolicyDecision::Deny {
                failed_precondition: "src/x is unstaged by other; only other may stage it"
                    .to_string(),
                allowed_fixes: opf(),
            },
        },
        Action::Stash => match row {
            "unstaged-self" => grant(),
            "clean" => denial(
                "stash requires an unstaged resource owned by the acting principal",
                &["self edit src/x before stashing"],
            ),
            "staged" => denial(
                "stash requires an unstaged resource owned by the acting principal",
                &["self unstage src/x before stashing"],
            ),
            _ => PolicyDecision::Deny {
                failed_precondition: "src/x is unstaged by other; only other may stash it"
                    .to_string(),
                allowed_fixes: opf(),
            },
        },
        Action::Unstage => match row {
            "staged" => grant(),
            "unstaged-other" => PolicyDecision::Deny {
                failed_precondition: "unstage requires a staged resource".to_string(),
                allowed_fixes: opf(),
            },
            _ => denial(
                "unstage requires a staged resource",
                &["self stage src/x before unstaging"],
            ),
        },
        Action::Commit { .. } => match row {
            "staged" => grant(),
            "clean" => denial(
                "commit requires a staged resource",
                &["self edit src/x", "self stage src/x before committing"],
            ),
            "unstaged-self" => denial(
                "commit requires a staged resource",
                &["self stage src/x before committing"],
            ),
            _ => PolicyDecision::Deny {
                failed_precondition: "commit requires a staged resource".to_string(),
                allowed_fixes: opf(),
            },
        },
    }
}

#[test]
fn git_decision_matches_the_reduced_table_exhaustively() {
    let rows = ["clean", "staged", "unstaged-self", "unstaged-other"];
    let actions = [
        Action::Read,
        Action::Edit,
        Action::Stage,
        Action::Unstage,
        Action::commit(MessageId(1)),
        Action::commit_without_message(),
        Action::Checkout,
        Action::Stash,
        Action::Delete,
        Action::Clean,
        Action::Diff,
        Action::History,
    ];
    for row in rows {
        let history = history_for(row);
        for action in actions {
            let got = git_decision(&history, &event(Who::Me, action));
            let expected = oracle(row, &action);
            assert_eq!(got, expected, "row={row} action={action:?}");
        }
    }
}

#[test]
fn row_languages_match_the_four_canonical_states() {
    let languages = [
        ("clean", clean_lang()),
        ("staged", staged_lang()),
        ("unstaged-self", unstaged_self_lang()),
        ("unstaged-other", unstaged_other_lang()),
    ];
    let histories = [
        ("clean", history_for("clean")),
        ("staged", history_for("staged")),
        ("unstaged-self", history_for("unstaged-self")),
        ("unstaged-other", history_for("unstaged-other")),
        // History commits clean the resource whether or not they carry a message.
        (
            "clean",
            History::from_events([
                event(Who::Me, Action::Edit),
                event(Who::Me, Action::Stage),
                event(Who::Me, Action::commit(MessageId(1))),
            ]),
        ),
        (
            "clean",
            History::from_events([
                event(Who::Me, Action::Edit),
                event(Who::Me, Action::Stage),
                event(Who::Me, Action::commit_without_message()),
            ]),
        ),
    ];
    let candidate = event(Who::Me, Action::Read);

    for (lang_name, lang) in &languages {
        for (history_name, history) in &histories {
            let arena = Bump::new();
            let mut store = CanonicalStore::new(&arena);
            // Bind-all classifier head: matches any candidate, binds `p`/`r`; the unused `a`
            // binding is legal — only tail variables absent from the head would error.
            let rule = Rule::new(
                RuleMode::Forbid,
                Head::new(
                    ComponentPattern::variable("p"),
                    ComponentPattern::variable("a"),
                    ComponentPattern::variable("r"),
                ),
                lang.clone(),
            );
            let mut rt = compile_rule(&mut store, &rule).expect("row language compiles");
            let inside = rt
                .accepts_history(&mut store, history, &candidate)
                .expect("bind-all head matches candidate");
            assert_eq!(
                inside,
                lang_name == history_name,
                "lang={lang_name} history={history_name} {history:?}",
            );
        }
    }
}

#[test]
fn a_read_claim_moves_only_when_another_principal_reads() {
    let candidate = event(Who::Me, Action::Edit);

    // A foreign read claims the resource.
    let history = History::from_events([event(Who::Other, Action::Read)]);
    assert_eq!(
        git_decision(&history, &candidate),
        denial(
            "src/x was last read by other; self must read it before editing it",
            &["self read src/x"],
        ),
    );

    // Reading it takes the claim over: last reader wins.
    let history = History::from_events([
        event(Who::Other, Action::Read),
        event(Who::Me, Action::Read),
    ]);
    assert_eq!(git_decision(&history, &candidate), PolicyDecision::Grant);

    // Settling does not move the claim. `other` has relinquished, but `self` still has to look
    // before it writes -- otherwise it would clobber content it has never seen.
    let mut history = History::from_events([
        event(Who::Other, Action::Read),
        event(Who::Other, Action::Edit),
        event(Who::Other, Action::Stage),
    ]);
    assert_eq!(
        git_decision(&history, &candidate),
        denial(
            "src/x was last read by other; self must read it before editing it",
            &["self read src/x"],
        ),
    );

    // Taking it over is always available: `read` has no cell in any row or claim state.
    history.push(event(Who::Me, Action::Read));
    assert_eq!(git_decision(&history, &candidate), PolicyDecision::Grant);

    // A foreign owner row and a foreign read claim at once: the row denial wins.
    let history = History::from_events([
        event(Who::Other, Action::Read),
        event(Who::Other, Action::Edit),
    ]);
    assert_eq!(
        git_decision(&history, &candidate),
        oracle("unstaged-other", &Action::Edit),
    );
}

#[test]
fn a_read_claim_blocks_foreign_content_changes() {
    // Staged row: cell 2 covers only unstaged-other, so the claim is all that stands in the way.
    let staged = History::from_events([
        event(Who::Other, Action::Edit),
        event(Who::Other, Action::Stage),
        event(Who::Me, Action::Read),
    ]);
    assert_eq!(
        git_decision(&staged, &event(Who::Other, Action::Checkout)),
        denial(
            "src/x was last read by self; other must read it before checking it out",
            &["other read src/x"],
        ),
    );

    // Unstaged-self row for `other`: cells 6-8 cover the other three rows.
    let unstaged = History::from_events([
        event(Who::Other, Action::Edit),
        event(Who::Me, Action::Read),
    ]);
    assert_eq!(
        git_decision(&unstaged, &event(Who::Other, Action::Stash)),
        denial(
            "src/x was last read by self; other must read it before stashing it",
            &["other read src/x"],
        ),
    );

    // Clean row: no row cell forbids delete or clean, so only the claim denies them.
    for (action, precondition) in [
        (
            Action::Delete,
            "src/x was last read by other; self must read it before deleting it",
        ),
        (
            Action::Clean,
            "src/x was last read by other; self must read it before cleaning it",
        ),
    ] {
        let mut claimed = History::from_events([event(Who::Other, Action::Read)]);
        assert_eq!(
            git_decision(&claimed, &event(Who::Me, action)),
            denial(precondition, &["self read src/x"]),
        );
        claimed.push(event(Who::Me, Action::Read));
        assert_eq!(git_decision(&claimed, &event(Who::Me, action)), grant());
    }
}

#[test]
fn delete_settles_the_resource_into_the_staged_row() {
    let history = History::from_events([event(Who::Me, Action::Delete)]);
    assert_eq!(
        git_decision(&history, &event(Who::Me, Action::Stage)),
        denial(
            "stage requires an unstaged resource owned by the acting principal",
            &["self unstage src/x before staging again"],
        ),
    );
    assert_eq!(
        git_decision(&history, &event(Who::Me, Action::commit(MessageId(1)))),
        PolicyDecision::Grant,
    );
}

/// Agent identity for the retained-policy walk; wide enough to evict progress cursors.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Agent(u32);

impl fmt::Display for Agent {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "agent{}", self.0)
    }
}

/// Pooled file identity for the retained-policy walk.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct File(u32);

impl fmt::Display for File {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "src/file{}.txt", self.0)
    }
}

/// Decides `candidate` with the retained policy and asserts it equals a fresh one-shot decision,
/// denial diagnostics (and therefore first-violated-rule order) included.
fn retained_decision(
    policy: &mut GitPolicy<'_, Agent, File>,
    history: &History<GitEvent<Agent, File>>,
    candidate: GitEvent<Agent, File>,
) -> PolicyDecision {
    let expected = git_decision(history, &candidate);
    let actual = policy.decide(history, &candidate);
    assert_eq!(actual, expected, "{candidate:?} over {history:?}");
    actual
}

/// Probes row and claim cells for two agents on one file, twice, so the second pass runs on warm
/// progress cursors.
fn probe_all(policy: &mut GitPolicy<'_, Agent, File>, history: &History<GitEvent<Agent, File>>) {
    let probes = [
        (Agent(0), Action::Edit),
        (Agent(0), Action::Stage),
        (Agent(0), Action::Unstage),
        (Agent(0), Action::commit(MessageId(7))),
        (Agent(1), Action::Edit),
        (Agent(1), Action::Checkout),
        (Agent(1), Action::Stash),
        (Agent(1), Action::Delete),
    ];
    for _ in 0..2 {
        for (agent, action) in probes {
            retained_decision(policy, history, git_event(agent, action, File(0)));
        }
    }
}

#[test]
fn retained_policy_matches_one_shot_decisions_across_history_updates() {
    let arena = Bump::new();
    let mut policy = GitPolicy::new(&arena);
    let (me, other, file) = (Agent(0), Agent(1), File(0));

    // Append: grants extend the owner, denials leave it unchanged.
    let mut history = History::new();
    for candidate in [
        git_event(me, Action::Edit, file),
        git_event(me, Action::Stage, file),
        git_event(me, Action::commit(MessageId(1)), file),
        git_event(other, Action::Edit, file),
        git_event(other, Action::Read, file),
        git_event(me, Action::Edit, file),
    ] {
        if retained_decision(&mut policy, &history, candidate) == PolicyDecision::Grant {
            history.push(candidate);
        }
        probe_all(&mut policy, &history);
    }

    // Truncate and reappend a different branch of the same total length.
    let length = history.len();
    history.truncate(1);
    history.push(git_event(other, Action::Read, file));
    while history.len() < length {
        history.push(git_event(other, Action::Diff, File(1)));
    }
    probe_all(&mut policy, &history);

    // Cloned owners diverge by append only; a rebuilt owner replays the same events afresh.
    let mut left = history.clone();
    let mut right = history.clone();
    left.push(git_event(me, Action::Read, file));
    right.push(git_event(other, Action::Edit, file));
    probe_all(&mut policy, &left);
    probe_all(&mut policy, &right);
    probe_all(&mut policy, &left);
    probe_all(&mut policy, &History::from_events(right.iter().copied()));

    // More distinct (principal, resource) bindings than a rule retains cursors for.
    for agent in 2..40 {
        retained_decision(
            &mut policy,
            &left,
            git_event(Agent(agent), Action::Edit, file),
        );
    }
    probe_all(&mut policy, &left);
}

/// Asserts agent0's literal file0 outcomes for the history built by
/// `other_resource_changes_preserve_row_and_claim`: an unstaged-self row and agent1's read claim.
/// Runs twice so the second pass decides on warm progress cursors.
fn assert_file0_row_and_claim(
    policy: &mut GitPolicy<'_, Agent, File>,
    history: &History<GitEvent<Agent, File>>,
) {
    for _ in 0..2 {
        assert_eq!(
            policy.decide(history, &git_event(Agent(0), Action::Stage, File(0))),
            grant(),
            "{history:?}",
        );
        assert_eq!(
            policy.decide(history, &git_event(Agent(0), Action::Edit, File(0))),
            denial(
                "src/file0.txt was last read by agent1; agent0 must read it before editing it",
                &["agent0 read src/file0.txt"],
            ),
            "{history:?}",
        );
    }
}

#[test]
fn other_resource_changes_preserve_row_and_claim() {
    let arena = Bump::new();
    let mut policy = GitPolicy::new(&arena);
    let (me, other, target, elsewhere) = (Agent(0), Agent(1), File(0), File(1));
    let mut history = History::from_events([
        git_event(me, Action::Edit, target),
        git_event(other, Action::Read, target),
    ]);
    assert_file0_row_and_claim(&mut policy, &history);

    for candidate in [
        git_event(me, Action::Read, elsewhere),
        git_event(other, Action::Read, elsewhere),
        git_event(other, Action::Edit, elsewhere),
        git_event(other, Action::Stage, elsewhere),
        git_event(other, Action::commit(MessageId(9)), elsewhere),
    ] {
        assert_eq!(
            policy.decide(&history, &candidate),
            grant(),
            "{candidate:?} over {history:?}",
        );
        history.push(candidate);
        assert_file0_row_and_claim(&mut policy, &history);
    }
}
