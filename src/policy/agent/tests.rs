use super::*;

type Event = AgentEvent<&'static str, &'static str>;

fn event(principal: &'static str, action: AgentAction, class: &'static str) -> Event {
    AgentEvent::new(principal, action, class)
}
fn read(principal: &'static str, class: &'static str) -> Event {
    event(principal, AgentAction::Read, class)
}
fn edit(principal: &'static str, class: &'static str) -> Event {
    event(principal, AgentAction::Edit, class)
}
fn contact(principal: &'static str, class: &'static str) -> Event {
    event(principal, AgentAction::Contact, class)
}
fn approve(label: &'static str) -> Event {
    event("operator", AgentAction::Approve, label)
}

/// A coding-agent policy over the classes `secret`, `ci`, `src`, `tests` and `lockfile`.
fn coding() -> AgentPolicy<&'static str, &'static str> {
    AgentPolicy::new()
        .rule(AgentRule::no_contact_after_read(
            "secret",
            &["external", "unknown"],
        ))
        .rule(AgentRule::requires_approval("ci"))
        .rule(AgentRule::locked_after("src", "tests"))
        .rule(AgentRule::tainted_by_run(
            &["curl", "wget"],
            &["ci", "lockfile"],
        ))
}

/// Decides `batch` after `history`, returning the first denial's precondition.
fn verdict(
    policy: &AgentPolicy<&'static str, &'static str>,
    history: &[Event],
    batch: &[Event],
) -> Option<String> {
    policy
        .check(history.iter().copied(), batch, |_, _| {})
        .err()
        .map(|denials| denials[0].failed_precondition.clone())
}

#[test]
fn contact_is_denied_only_after_the_same_principal_reads_the_secret() {
    let policy = coding();
    let secret = read("a", "secret");
    assert_eq!(verdict(&policy, &[], &[contact("a", "external")]), None);
    assert_eq!(
        verdict(&policy, &[secret], &[contact("b", "external")]),
        None
    );
    assert_eq!(
        verdict(&policy, &[secret], &[contact("a", "loopback")]),
        None
    );
    assert_eq!(
        verdict(&policy, &[secret], &[contact("a", "external")]).unwrap(),
        "a contacted an external peer after reading secret data"
    );
    assert!(verdict(&policy, &[], &[secret, contact("a", "unknown")]).is_some());
}

#[test]
fn approval_gates_protected_classes() {
    let policy = coding();
    let change = edit("a", "ci");
    let create = event("a", AgentAction::Create, "ci");
    assert!(verdict(&policy, &[], &[change]).is_some());
    assert!(verdict(&policy, &[], &[create]).is_some());
    assert!(verdict(&policy, &[approve("tests")], &[change]).is_some());
    assert_eq!(verdict(&policy, &[approve("ci")], &[change, create]), None);
}

#[test]
fn tests_lock_once_source_changes_until_approved() {
    let policy = coding();
    let (src, tests) = (edit("a", "src"), edit("a", "tests"));
    assert_eq!(verdict(&policy, &[], &[tests, src]), None);
    assert!(verdict(&policy, &[], &[src, tests]).is_some());
    assert_eq!(verdict(&policy, &[src], &[edit("b", "tests")]), None);
    assert_eq!(verdict(&policy, &[src, approve("tests")], &[tests]), None);
    assert!(verdict(&policy, &[src, approve("tests"), src], &[tests]).is_some());
    let removal = event("a", AgentAction::Remove, "src");
    assert!(verdict(&policy, &[removal], &[tests]).is_some());
}

#[test]
fn running_a_downloader_locks_supply_chain_classes() {
    let policy = coding();
    let lock = edit("a", "lockfile");
    let run = |program| event("a", AgentAction::Run, program);
    assert_eq!(verdict(&policy, &[run("cargo")], &[lock]), None);
    assert_eq!(
        verdict(&policy, &[run("wget")], &[lock]).unwrap(),
        "a ran curl, wget and may not then change lockfile resources"
    );
    assert_eq!(
        verdict(&policy, &[run("curl"), approve("lockfile")], &[lock]),
        None
    );
}

#[test]
fn removals_are_budgeted_between_approvals() {
    let policy = AgentPolicy::new().rule(AgentRule::deletion_budget(2, "delete"));
    let remove = |principal, class| event(principal, AgentAction::Remove, class);
    let (x, y, z) = (remove("a", "x"), remove("a", "y"), remove("a", "z"));
    assert_eq!(verdict(&policy, &[], &[x, y]), None);
    assert!(verdict(&policy, &[x, y], &[z]).is_some());
    assert_eq!(verdict(&policy, &[x, y, approve("delete")], &[z]), None);
    assert_eq!(verdict(&policy, &[x, y], &[remove("b", "z")]), None);
}

#[test]
fn append_only_classes_accept_only_creation() {
    let policy = AgentPolicy::new().rule(AgentRule::append_only("migrations"));
    let create = event("a", AgentAction::Create, "migrations");
    assert_eq!(verdict(&policy, &[], &[create]), None);
    assert!(verdict(&policy, &[], &[edit("a", "migrations")]).is_some());
    let remove = event("a", AgentAction::Remove, "migrations");
    assert!(verdict(&policy, &[], &[remove]).is_some());
}

#[test]
fn peer_classes_can_be_forbidden_outright() {
    let policy = AgentPolicy::new().rule(AgentRule::no_network("external"));
    assert!(verdict(&policy, &[], &[contact("a", "external")]).is_some());
    assert_eq!(verdict(&policy, &[], &[contact("a", "internal")]), None);
}

#[test]
fn a_denied_batch_reports_every_denial_and_grants_build_on_each_other() {
    let policy = coding();
    let denials = policy
        .check(
            [],
            &[edit("a", "ci"), edit("a", "src"), edit("a", "tests")],
            |_, _| {},
        )
        .unwrap_err();
    let refused: Vec<_> = denials.iter().map(|denial| denial.event).collect();
    assert_eq!(refused, [edit("a", "ci"), edit("a", "tests")]);
}

#[test]
fn audit_reports_would_be_denials_without_enforcing_them() {
    let mut reported = Vec::new();
    let policy = coding().audit();
    let batch = [
        read("a", "secret"),
        contact("a", "external"),
        edit("a", "ci"),
    ];
    let checked = policy.check([], &batch, |event, decision| {
        if !matches!(decision, PolicyDecision::Grant) {
            reported.push(*event);
        }
    });
    assert!(checked.is_ok());
    assert_eq!(reported, [contact("a", "external"), edit("a", "ci")]);
    assert!(
        policy
            .decide([read("a", "secret")], &contact("a", "external"))
            .is_some()
    );
}

/// A custom rule whose tail names a variable its head does not bind.
fn uncompilable() -> AgentRule<&'static str, &'static str> {
    let head = Head::new(
        ComponentPattern::variable(PRINCIPAL_VAR),
        ComponentPattern::constant(AgentAction::Contact),
        ComponentPattern::constant("external"),
    );
    let tail = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("unbound")),
    ));
    AgentRule::custom(TraceRule::new(
        Rule::new(RuleMode::Forbid, head, tail),
        |_| (String::new(), Vec::new()),
    ))
}

#[test]
fn an_uncompilable_rule_denies_only_what_it_could_judge() {
    let policy = AgentPolicy::new().rule(uncompilable());
    let batch = [contact("a", "external"), edit("a", "src")];
    let denials = policy.check([], &batch, |_, _| {}).unwrap_err();
    assert_eq!(denials.len(), 1);
    assert_eq!(denials[0].event, batch[0]);
    assert!(denials[0].failed_precondition.contains("does not compile"));
    assert!(policy.decide([], &batch[0]).is_some());
    assert!(policy.decide([], &batch[1]).is_none());
    assert!(policy.audit().check([], &batch, |_, _| {}).is_ok());
}

#[test]
fn deciding_judges_only_the_candidate() {
    let policy = coding();
    assert!(policy.judges(&contact("a", "external")));
    assert!(!policy.judges(&contact("a", "loopback")));
    // An unapproved ci change earlier in the history is the batch's to refuse, not the contact's.
    assert_eq!(
        policy.decide([edit("a", "ci")], &contact("a", "external")),
        None
    );
    let denial = policy
        .decide(
            [edit("a", "ci"), read("a", "secret")],
            &contact("a", "external"),
        )
        .unwrap();
    assert_eq!(denial.event, contact("a", "external"));
    assert_eq!(
        denial.to_string(),
        "a contact external: a contacted an external peer after reading secret data\n    \
         fix: contact external peers only from a principal that has not read secret"
    );
    assert_eq!(
        policy.decide([read("a", "secret")], &contact("b", "external")),
        None
    );
}
