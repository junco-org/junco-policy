//! A miniature non-lock policy, assembled only from kernel pieces.
//!
//! The lock table is not the contract under test here: this file exists to pin that [`super::atoms`],
//! [`super::language`], [`super::rule`] and [`super::evaluate`] carry no lock assumptions, by
//! building a policy over a different vocabulary and running it through the same loop.

use std::fmt;

use super::atoms::{action_is, principal_is, resource_is};
use super::decision::PolicyDecision;
use super::evaluate::decide;
use super::language::last_state_change;
use super::rule::{PolicyRule, forbid};
use crate::{Comparison, Event, History, TestExpr};

/// Principals of the miniature policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Editor {
    Alice,
    Bob,
}

impl fmt::Display for Editor {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Alice => "alice",
            Self::Bob => "bob",
        })
    }
}

/// The one resource the miniature policy guards.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SrcX;

impl fmt::Display for SrcX {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("src/x")
    }
}

/// Operations of the miniature policy; deliberately not the built-in lock [`crate::Action`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DocAction {
    Read,
    Edit,
}

/// One event of the miniature policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DocEvent {
    principal: Editor,
    action: DocAction,
    resource: SrcX,
}

impl Event for DocEvent {
    type Principal = Editor;
    type Action = DocAction;
    type Resource = SrcX;

    fn principal(self) -> Editor {
        self.principal
    }

    fn action(self) -> DocAction {
        self.action
    }

    fn resource(self) -> SrcX {
        self.resource
    }
}

/// Context of the miniature policy: the resource and who last edited it.
struct LastEditor {
    resource: String,
    editor: String,
}

/// The whole table: reading a resource whose last state change was a foreign edit is forbidden.
fn rules() -> Vec<PolicyRule<DocEvent, LastEditor>> {
    let setter = TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(DocAction::Edit, Comparison::Eq),
        principal_is(Comparison::Neq),
    ]);
    let stable = TestExpr::or([
        resource_is(Comparison::Neq),
        action_is(DocAction::Read, Comparison::Eq),
    ]);
    vec![forbid(
        DocAction::Read,
        last_state_change(setter, stable),
        Box::new(|context| {
            let LastEditor { resource, editor } = context;
            (
                format!("{resource} was last edited by {editor}"),
                vec![format!("{editor} release {resource}")],
            )
        }),
    )]
}

/// Builds the context for `candidate`: the last principal to edit its resource, or `"nobody"`.
fn context(history: &[DocEvent], candidate: &DocEvent) -> LastEditor {
    let editor = history
        .iter()
        .rfind(|event| event.resource == candidate.resource && event.action == DocAction::Edit)
        .map_or_else(|| "nobody".to_string(), |event| event.principal.to_string());
    LastEditor {
        resource: candidate.resource.to_string(),
        editor,
    }
}

#[test]
fn a_non_lock_policy_reuses_the_kernel_loop() {
    let candidate = DocEvent {
        principal: Editor::Bob,
        action: DocAction::Read,
        resource: SrcX,
    };

    let history = History::new();
    assert_eq!(
        decide(rules(), &history, &candidate, || context(
            history.as_slice(),
            &candidate
        )),
        PolicyDecision::Grant,
    );

    let history = History::from_events([DocEvent {
        principal: Editor::Alice,
        action: DocAction::Edit,
        resource: SrcX,
    }]);
    assert_eq!(
        decide(rules(), &history, &candidate, || context(
            history.as_slice(),
            &candidate
        )),
        PolicyDecision::Deny {
            failed_precondition: "src/x was last edited by alice".to_string(),
            allowed_fixes: vec!["alice release src/x".to_string()],
        },
    );
}
