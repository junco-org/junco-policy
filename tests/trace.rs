use std::sync::Arc;

use junco_core::{
    AtomPattern, Comparison, ComponentPattern, Head, History, PolicyDecision, RegexExpr, Rule,
    RuleMode, Store, TestExpr, TracePolicy, TraceRule,
};
use junco_policy::{Action, LockEvent};

type Event = LockEvent<&'static str, &'static str>;

/// Editing anything after the same principal read `secret` is forbidden.
fn taint() -> TraceRule<Event> {
    let read_secret = TestExpr::and([
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("p")),
        ),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Action(ComponentPattern::constant(Action::Read)),
        ),
        TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::constant("secret")),
        ),
    ]);
    TraceRule::new(
        Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable("p"),
                ComponentPattern::constant(Action::Edit),
                ComponentPattern::variable("r"),
            ),
            RegexExpr::concat([
                RegexExpr::all(),
                RegexExpr::test(read_secret),
                RegexExpr::all(),
            ]),
        ),
        |event: &Event| (format!("{} read a secret", event.principal), Vec::new()),
    )
}

#[test]
fn decides_against_external_history_without_appending() {
    let store = Arc::new(Store::new().unwrap());
    let mut policy = TracePolicy::new(Arc::clone(&store), [taint()]).unwrap();
    let edit = LockEvent::new("a", Action::Edit, "out");
    let empty = History::new(Arc::clone(&store)).unwrap();
    assert_eq!(policy.decide(&empty, &edit).unwrap(), PolicyDecision::Grant);
    let other = History::from_events(
        Arc::clone(&store),
        [LockEvent::new("b", Action::Read, "secret")],
    )
    .unwrap();
    assert_eq!(policy.decide(&other, &edit).unwrap(), PolicyDecision::Grant);
    let mut history =
        History::from_events(store, [LockEvent::new("a", Action::Read, "secret")]).unwrap();
    history
        .push(LockEvent::new("a", Action::Read, "other"))
        .unwrap();
    assert_eq!(
        policy.decide(&history, &edit).unwrap(),
        PolicyDecision::Deny {
            failed_precondition: "a read a secret".into(),
            allowed_fixes: Vec::new(),
        }
    );
    assert_eq!(history.len(), 2);
}
