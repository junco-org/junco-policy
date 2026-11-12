use std::sync::Arc;

use history_store::{History, Store};
use history_syntax::RegexExpr;

use super::*;

type Observation = FlowEvent<&'static str, &'static str, &'static str>;
type Policy = FlowPolicy<&'static str, &'static str, &'static str>;

fn event(
    principal: &'static str,
    handle: &'static str,
    action: FlowAction,
    label: &'static str,
) -> Observation {
    FlowEvent {
        principal,
        handle,
        action,
        label,
    }
}

fn history(events: &[Observation]) -> History<Observation> {
    let store = Arc::new(Store::new().unwrap());
    History::from_events(store, events.iter().copied()).unwrap()
}

fn policy() -> Policy {
    FlowPolicy::new().rule(FlowRule::no_contact_after_read("untrusted", &["sink"]))
}

fn paper_history() -> History<Observation> {
    history(&[
        event("A", "$1", FlowAction::Read, "untrusted"),
        event("A", "$2", FlowAction::Receive, "untrusted"),
        event("B", "$2", FlowAction::Receive, "untrusted"),
    ])
}

#[test]
fn paper_trace_denies_tainted_contact() {
    let mut history = paper_history();
    let candidate = event("B", "$2", FlowAction::Contact, "sink");
    let denials = policy()
        .check(&mut history, &[candidate], |_, _| {})
        .unwrap_err();
    assert_eq!(
        denials,
        [FlowDenial {
            event: candidate,
            failed_precondition: "B passed $2 to a sink sink after receiving untrusted data".into(),
            allowed_fixes: vec![
                "declassify untrusted for B's copy of $2, or pass a value not derived from untrusted data".into(),
            ],
        }]
    );
    assert_eq!(history.as_slice().len(), 3);
}

#[test]
fn untainted_handle_is_granted() {
    let mut history = paper_history();
    let candidate = event("B", "$3", FlowAction::Contact, "sink");
    policy()
        .check(&mut history, &[candidate], |_, _| {})
        .unwrap();
    assert_eq!(history.as_slice().last(), Some(&candidate));
}

#[test]
fn matching_declassification_grants_contact() {
    let mut history = paper_history();
    history
        .push(event("B", "$2", FlowAction::Declassify, "untrusted"))
        .unwrap();
    let candidate = event("B", "$2", FlowAction::Contact, "sink");
    assert_eq!(policy().decide(&history, &candidate), None);
}

#[test]
fn trusted_reads_and_receives_do_not_taint() {
    let history = history(&[
        event("B", "$2", FlowAction::Read, "trusted"),
        event("B", "$2", FlowAction::Receive, "trusted"),
    ]);
    let candidate = event("B", "$2", FlowAction::Contact, "sink");
    assert_eq!(policy().decide(&history, &candidate), None);
}

#[test]
fn one_principals_read_does_not_taint_another_copy_of_the_same_handle() {
    let history = history(&[event("A", "$2", FlowAction::Read, "untrusted")]);
    let policy = policy();
    let other_copy = event("B", "$2", FlowAction::Contact, "sink");
    assert_eq!(policy.decide(&history, &other_copy), None);
    let tainted_copy = event("A", "$2", FlowAction::Contact, "sink");
    let denial = policy.decide(&history, &tainted_copy).unwrap();
    assert_eq!(
        denial.failed_precondition,
        "A passed $2 to a sink sink after receiving untrusted data"
    );
}

#[test]
fn declassifying_one_principals_copy_does_not_clear_another_copy() {
    let history = history(&[
        event("A", "$2", FlowAction::Receive, "untrusted"),
        event("B", "$2", FlowAction::Receive, "untrusted"),
        event("A", "$2", FlowAction::Declassify, "untrusted"),
    ]);
    let policy = policy();
    let declassified_copy = event("A", "$2", FlowAction::Contact, "sink");
    assert_eq!(policy.decide(&history, &declassified_copy), None);
    let other_copy = event("B", "$2", FlowAction::Contact, "sink");
    let denial = policy.decide(&history, &other_copy).unwrap();
    assert_eq!(
        denial.failed_precondition,
        "B passed $2 to a sink sink after receiving untrusted data"
    );
}

#[test]
fn declassification_must_match_both_handle_and_label() {
    let history = history(&[
        event("B", "$2", FlowAction::Read, "untrusted"),
        event("B", "$3", FlowAction::Declassify, "untrusted"),
        event("B", "$2", FlowAction::Declassify, "private"),
    ]);
    let candidate = event("B", "$2", FlowAction::Contact, "sink");
    let denial = policy().decide(&history, &candidate).unwrap();
    assert_eq!(
        denial.failed_precondition,
        "B passed $2 to a sink sink after receiving untrusted data"
    );
}

#[test]
fn receiving_tainted_data_again_restores_taint_for_each_sink() {
    let history = history(&[
        event("B", "$2", FlowAction::Read, "untrusted"),
        event("B", "$2", FlowAction::Declassify, "untrusted"),
        event("B", "$2", FlowAction::Receive, "untrusted"),
    ]);
    let policy = FlowPolicy::new().rule(FlowRule::no_contact_after_read(
        "untrusted",
        &["sink", "peer"],
    ));
    for sink in ["sink", "peer"] {
        let candidate = event("B", "$2", FlowAction::Contact, sink);
        let denial = policy.decide(&history, &candidate).unwrap();
        assert_eq!(
            denial.failed_precondition,
            format!("B passed $2 to a {sink} sink after receiving untrusted data")
        );
    }
    let candidate = event("B", "$2", FlowAction::Contact, "local");
    assert_eq!(policy.decide(&history, &candidate), None);
}

#[test]
fn custom_rules_convert_into_a_flow_policy() {
    let rule = FlowRule::custom(TraceRule::new(
        Rule::new(
            RuleMode::Forbid,
            Head::new([
                ComponentPattern::variable("p"),
                ComponentPattern::variable("v"),
                ComponentPattern::constant(FlowComponent::Action(FlowAction::Contact)),
                ComponentPattern::constant(FlowComponent::Label("sink")),
            ]),
            RegexExpr::all(),
        ),
        |event: &Observation| {
            (
                format!("{} cannot contact this sink", event.principal),
                vec![],
            )
        },
    ));
    let policy = FlowPolicy::new().rule(rule);
    let history = history(&[]);
    let candidate = event("B", "$2", FlowAction::Contact, "sink");
    let denial = policy.decide(&history, &candidate).unwrap();
    assert_eq!(denial.event, candidate);
    assert_eq!(denial.failed_precondition, "B cannot contact this sink");
    assert_eq!(
        policy.decide(&history, &event("B", "$2", FlowAction::Read, "sink")),
        None
    );
}
