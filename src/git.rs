//! Git legality expressed as native trace policies.
//!
//! The git authorization table is re-expressed as declarative [`Rule`] values whose tails are
//! past-regexes over committed history. Each deny cell of the table is one `Forbid` rule paired
//! with a diagnostic closure carrying the exact precondition/fix strings the consumer boundary
//! surfaces. Grant/deny is entirely trace-policy driven; the commit-message payload is omitted
//! from policy checking (the candidate commit is normalized to a canonical payload-less form).
//!
//! This runs its own `match_candidate` + `accepts` loop (mirroring `validator.rs::check`) rather
//! than building a [`crate::Validator`], because `Validator::check` returns a single opaque
//! denial message that cannot carry the per-cell diagnostic, and its arena invariance forbids a
//! persistent compiled form across napi calls.

use crate::{
    Action, AtomPattern, Bump, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule,
    RuleMode, TestExpr,
};
use crate::syntax::{accepts, compile_rule, CanonicalStore};

// -- Decision ---------------------------------------------------------------

/// The reduced git verdict: grant, or a single collapsed soft-error carrying the exact git
/// precondition text and fix list the consumer boundary surfaces.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum GitDecision {
    /// Request is legal.
    Grant,
    /// Request is denied with the precondition it violated and the fixes that would unblock it.
    Deny {
        /// Human-readable git precondition the request failed.
        failed_precondition: String,
        /// Ordered list of state-changing fixes that would make the request legal.
        allowed_fixes: Vec<String>,
    },
}

// -- One-event TestExpr building blocks -------------------------------------
//
// Head variables are the string names `"p"` (principal) and `"r"` (resource).

/// An event on the head-bound resource `r`.
fn on_r() -> TestExpr {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::variable("r")),
    )
}

/// An event whose action compares (`Eq`/`Neq`) against the constant `a`.
fn is(a: Action, cmp: Comparison) -> TestExpr {
    TestExpr::atom(cmp, AtomPattern::Action(ComponentPattern::constant(a)))
}

/// An event by the head-bound principal `p`.
fn by_p() -> TestExpr {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("p")),
    )
}

/// An event by a principal other than the head-bound `p`.
fn by_other() -> TestExpr {
    TestExpr::atom(
        Comparison::Neq,
        AtomPattern::Principal(ComponentPattern::variable("p")),
    )
}

/// An event that does not change `r`'s state: off-`r`, or a pure observation of `r`.
fn not_state_mut_on_r() -> TestExpr {
    TestExpr::or([
        TestExpr::atom(
            Comparison::Neq,
            AtomPattern::Resource(ComponentPattern::variable("r")),
        ),
        is(Action::Read, Comparison::Eq),
        is(Action::Diff, Comparison::Eq),
        is(Action::History, Comparison::Eq),
    ])
}

/// An on-`r` `stage` event.
fn stage_setter() -> TestExpr {
    TestExpr::and([on_r(), is(Action::Stage, Comparison::Eq)])
}

/// An on-`r` `edit`/`unstage` event by the acting principal `p`.
fn edit_unstage_by_p() -> TestExpr {
    TestExpr::and([
        on_r(),
        TestExpr::or([
            is(Action::Edit, Comparison::Eq),
            is(Action::Unstage, Comparison::Eq),
        ]),
        by_p(),
    ])
}

/// An on-`r` `edit`/`unstage` event by a principal other than `p`.
fn edit_unstage_by_other() -> TestExpr {
    TestExpr::and([
        on_r(),
        TestExpr::or([
            is(Action::Edit, Comparison::Eq),
            is(Action::Unstage, Comparison::Eq),
        ]),
        by_other(),
    ])
}

/// An on-`r` event that is none of the six enumerated actions, i.e. exactly
/// `{commit(any message), checkout, stash}`. The `Neq`-enumeration is message-agnostic by
/// construction, so it matches a commit regardless of its message payload.
fn clean_setter() -> TestExpr {
    TestExpr::and([
        on_r(),
        is(Action::Read, Comparison::Neq),
        is(Action::Diff, Comparison::Neq),
        is(Action::History, Comparison::Neq),
        is(Action::Edit, Comparison::Neq),
        is(Action::Stage, Comparison::Neq),
        is(Action::Unstage, Comparison::Neq),
    ])
}

// -- Regular row-languages --------------------------------------------------
//
// `Concat[All, T(setter), Star(not_state_mut_on_r)]` pins `setter` to the LAST state-mutating
// event on `r`: `accepts` explores all split points, and the trailing `Star` forbids any later
// state change to `r`.

/// A trailing run of events that do not change `r`'s state.
fn observations_tail() -> RegexExpr {
    RegexExpr::star(RegexExpr::test(not_state_mut_on_r()))
}

/// Never any state-mutating `r` event, OR the last such event is commit/checkout/stash.
fn clean_lang() -> RegexExpr {
    RegexExpr::union([
        RegexExpr::star(RegexExpr::test(not_state_mut_on_r())),
        RegexExpr::concat([
            RegexExpr::all(),
            RegexExpr::test(clean_setter()),
            observations_tail(),
        ]),
    ])
}

/// The last state-mutating `r` event is a stage.
fn staged_lang() -> RegexExpr {
    RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(stage_setter()),
        observations_tail(),
    ])
}

/// The last state-mutating `r` event is an edit/unstage by the acting principal.
fn unstaged_self_lang() -> RegexExpr {
    RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(edit_unstage_by_p()),
        observations_tail(),
    ])
}

/// The last state-mutating `r` event is an edit/unstage by another principal.
fn unstaged_other_lang() -> RegexExpr {
    RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(edit_unstage_by_other()),
        observations_tail(),
    ])
}

// -- Diagnostics ------------------------------------------------------------

/// Extracts the current owner of `resource` for diagnostics only — grant/deny is entirely
/// trace-policy driven and never consults this value. Folds to the principal of the most-recent
/// `edit`/`unstage` (reset by `stage`/`commit`/`checkout`/`stash`), or `"another principal"`.
fn current_owner(history: &[Event], resource: &crate::Resource) -> String {
    let mut owner: Option<String> = None;
    for event in history.iter().filter(|event| &event.resource == resource) {
        match &event.action {
            Action::Edit | Action::Unstage => owner = Some(event.principal.as_str().to_string()),
            Action::Stage | Action::Commit { .. } | Action::Checkout | Action::Stash => {
                owner = None;
            }
            Action::Read | Action::Diff | Action::History => {}
        }
    }
    owner.unwrap_or_else(|| "another principal".to_string())
}

/// Owner-protection fixes shared by every foreign-owner contention cell.
fn opf(p: &str, r: &str, q: &str) -> Vec<String> {
    vec![
        format!("{q} stage {r}"),
        format!("{q} checkout {r}"),
        format!("{q} stash {r}"),
        format!("{p} only reads, diffs, or histories {r}"),
    ]
}

/// Renders a cell's `(failed_precondition, allowed_fixes)` from `(p, r, q)`.
type Diagnostic = Box<dyn Fn(&str, &str, &str) -> (String, Vec<String>)>;

/// One trace-policy rule paired with the diagnostic its violation surfaces.
struct GitRule {
    rule: Rule,
    diagnostic: Diagnostic,
}

/// Builds a `Forbid` rule with an action-constant head over the acting principal and resource.
fn forbid(action: Action, tail: RegexExpr, diagnostic: Diagnostic) -> GitRule {
    GitRule {
        rule: Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable("p"),
                ComponentPattern::constant(action),
                ComponentPattern::variable("r"),
            ),
            tail,
        ),
        diagnostic,
    }
}

/// The 14-rule git legality table. Within one action the row-languages are mutually exclusive
/// (at most one rule fires); across actions heads pin distinct action constants, so rule order
/// is irrelevant. Read/Diff/History and every staged-row commit have no rule and thus grant.
fn git_rules() -> Vec<GitRule> {
    vec![
        // 1. edit on a resource unstaged by another principal.
        forbid(
            Action::Edit,
            unstaged_other_lang(),
            Box::new(|p, r, q| {
                (
                    format!(
                        "{r} is unstaged by {q}; {p} may read, diff, or history it but may not edit it"
                    ),
                    opf(p, r, q),
                )
            }),
        ),
        // 2. checkout of a resource unstaged by another principal.
        forbid(
            Action::Checkout,
            unstaged_other_lang(),
            Box::new(|p, r, q| {
                (
                    format!(
                        "{r} is unstaged by {q}; checkout would discard or replace {q}'s dirty resource"
                    ),
                    opf(p, r, q),
                )
            }),
        ),
        // 3. stage of a clean resource.
        forbid(
            Action::Stage,
            clean_lang(),
            Box::new(|p, r, _q| {
                (
                    "stage requires an unstaged resource owned by the acting principal".to_string(),
                    vec![format!("{p} edit {r} before staging")],
                )
            }),
        ),
        // 4. stage of an already-staged resource.
        forbid(
            Action::Stage,
            staged_lang(),
            Box::new(|p, r, _q| {
                (
                    "stage requires an unstaged resource owned by the acting principal".to_string(),
                    vec![format!("{p} unstage {r} before staging again")],
                )
            }),
        ),
        // 5. stage of a resource unstaged by another principal.
        forbid(
            Action::Stage,
            unstaged_other_lang(),
            Box::new(|p, r, q| {
                (
                    format!("{r} is unstaged by {q}; only {q} may stage it"),
                    opf(p, r, q),
                )
            }),
        ),
        // 6. stash of a clean resource.
        forbid(
            Action::Stash,
            clean_lang(),
            Box::new(|p, r, _q| {
                (
                    "stash requires an unstaged resource owned by the acting principal".to_string(),
                    vec![format!("{p} edit {r} before stashing")],
                )
            }),
        ),
        // 7. stash of an already-staged resource.
        forbid(
            Action::Stash,
            staged_lang(),
            Box::new(|p, r, _q| {
                (
                    "stash requires an unstaged resource owned by the acting principal".to_string(),
                    vec![format!("{p} unstage {r} before stashing")],
                )
            }),
        ),
        // 8. stash of a resource unstaged by another principal.
        forbid(
            Action::Stash,
            unstaged_other_lang(),
            Box::new(|p, r, q| {
                (
                    format!("{r} is unstaged by {q}; only {q} may stash it"),
                    opf(p, r, q),
                )
            }),
        ),
        // 9. unstage of a resource unstaged by another principal.
        forbid(
            Action::Unstage,
            unstaged_other_lang(),
            Box::new(|p, r, q| ("unstage requires a staged resource".to_string(), opf(p, r, q))),
        ),
        // 10. unstage of a clean resource.
        forbid(
            Action::Unstage,
            clean_lang(),
            Box::new(|p, r, _q| {
                (
                    "unstage requires a staged resource".to_string(),
                    vec![format!("{p} stage {r} before unstaging")],
                )
            }),
        ),
        // 11. unstage of a resource unstaged by the acting principal.
        forbid(
            Action::Unstage,
            unstaged_self_lang(),
            Box::new(|p, r, _q| {
                (
                    "unstage requires a staged resource".to_string(),
                    vec![format!("{p} stage {r} before unstaging")],
                )
            }),
        ),
        // 12. commit of a clean resource.
        forbid(
            Action::commit_without_message(),
            clean_lang(),
            Box::new(|p, r, _q| {
                (
                    "commit requires a staged resource".to_string(),
                    vec![
                        format!("{p} edit {r}"),
                        format!("{p} stage {r} before committing"),
                    ],
                )
            }),
        ),
        // 13. commit of a resource unstaged by the acting principal.
        forbid(
            Action::commit_without_message(),
            unstaged_self_lang(),
            Box::new(|p, r, _q| {
                (
                    "commit requires a staged resource".to_string(),
                    vec![format!("{p} stage {r} before committing")],
                )
            }),
        ),
        // 14. commit of a resource unstaged by another principal.
        forbid(
            Action::commit_without_message(),
            unstaged_other_lang(),
            Box::new(|p, r, q| ("commit requires a staged resource".to_string(), opf(p, r, q))),
        ),
    ]
}

// -- Evaluator --------------------------------------------------------------

/// Decides one candidate against the resource's committed history via the trace-policy table.
///
/// The commit message is omitted from policy checking: any commit candidate is normalized to the
/// canonical payload-less form so the `Constant(commit_without_message)` head fires on every
/// commit. History is passed unnormalized — row-languages classify commits by the message-agnostic
/// `clean_setter` enumeration, so history commit messages never affect the outcome.
pub(crate) fn git_decision(history: &[Event], candidate: &Event) -> GitDecision {
    let arena = Bump::new();
    let mut store = CanonicalStore::new(&arena);

    let mut probe = candidate.clone();
    if let Action::Commit { .. } = probe.action {
        probe.action = Action::commit_without_message();
    }

    let p = candidate.principal.as_str();
    let r = candidate.resource.segments().join("/");

    for grule in git_rules() {
        let rt = compile_rule(&mut store, &grule.rule).expect("static git rules compile");
        let Some(subst) = rt.head.match_candidate(&mut store, &probe) else {
            continue;
        };
        let inside = accepts(&mut store, rt.tail, history.iter(), &subst);
        let violated = match rt.mode {
            RuleMode::Forbid => inside,
            RuleMode::Require => !inside,
        };
        if violated {
            let q = current_owner(history, &candidate.resource);
            let (failed_precondition, allowed_fixes) = (grule.diagnostic)(p, &r, &q);
            return GitDecision::Deny {
                failed_precondition,
                allowed_fixes,
            };
        }
    }
    GitDecision::Grant
}

#[cfg(test)]
mod tests {
    use super::*;

    fn resource() -> [&'static str; 2] {
        ["src", "x"]
    }

    /// History whose fold lands the resource in the named row (candidate principal is "self").
    fn history_for(row: &str) -> Vec<Event> {
        let r = resource();
        match row {
            "clean" => vec![],
            "staged" => vec![
                Event::new("self", Action::Edit, r),
                Event::new("self", Action::Stage, r),
            ],
            "unstaged-self" => vec![Event::new("self", Action::Edit, r)],
            "unstaged-other" => vec![Event::new("other", Action::Edit, r)],
            other => panic!("unknown row {other}"),
        }
    }

    fn grant() -> GitDecision {
        GitDecision::Grant
    }

    fn denial(precondition: &str, fixes: &[&str]) -> GitDecision {
        GitDecision::Deny {
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
    /// branch is message-agnostic: `commit("m")` and `commit_without_message()` yield the same
    /// per-row result.
    fn oracle(row: &str, action: &Action) -> GitDecision {
        match action {
            Action::Read | Action::Diff | Action::History => grant(),
            Action::Edit => match row {
                "unstaged-other" => GitDecision::Deny {
                    failed_precondition:
                        "src/x is unstaged by other; self may read, diff, or history it but may not edit it"
                            .to_string(),
                    allowed_fixes: opf(),
                },
                _ => grant(),
            },
            Action::Checkout => match row {
                "unstaged-other" => GitDecision::Deny {
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
                _ => GitDecision::Deny {
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
                _ => GitDecision::Deny {
                    failed_precondition: "src/x is unstaged by other; only other may stash it"
                        .to_string(),
                    allowed_fixes: opf(),
                },
            },
            Action::Unstage => match row {
                "staged" => grant(),
                "unstaged-other" => GitDecision::Deny {
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
                _ => GitDecision::Deny {
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
            Action::commit("m"),
            Action::commit_without_message(),
            Action::Checkout,
            Action::Stash,
            Action::Diff,
            Action::History,
        ];
        for row in rows {
            let history = history_for(row);
            for action in &actions {
                let candidate = Event::new("self", action.clone(), resource());
                let got = git_decision(&history, &candidate);
                let expected = oracle(row, action);
                assert_eq!(got, expected, "row={row} action={action:?}");
            }
        }
    }

    #[test]
    fn row_languages_match_the_four_canonical_states() {
        let languages: [(&str, fn() -> RegexExpr); 4] = [
            ("clean", clean_lang),
            ("staged", staged_lang),
            ("unstaged-self", unstaged_self_lang),
            ("unstaged-other", unstaged_other_lang),
        ];
        let histories = [
            ("clean", history_for("clean")),
            ("staged", history_for("staged")),
            ("unstaged-self", history_for("unstaged-self")),
            ("unstaged-other", history_for("unstaged-other")),
        ];
        let candidate = Event::new("self", Action::Read, resource());

        for (lang_name, lang) in languages {
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
                    lang(),
                );
                let rt = compile_rule(&mut store, &rule).expect("row language compiles");
                let subst = rt
                    .head
                    .match_candidate(&mut store, &candidate)
                    .expect("bind-all head matches candidate");
                let inside = accepts(&mut store, rt.tail, history.iter(), &subst);
                assert_eq!(
                    inside,
                    lang_name == *history_name,
                    "lang={lang_name} history={history_name}",
                );
            }
        }
    }
}
