use rust_validator::{
    Action, Bump, CompileError, ComponentPattern, Decision, Event, Head, Regex, Request, Rule,
    RuleMode, Test, Validator,
};

fn event(principal: &str, action: Action, path: &[&str]) -> Event {
    Event::new(principal, action, path.to_vec())
}

fn request<M>(principal: &str, action: Action, path: &[&str], metadata: M) -> Request<M> {
    Request::new(event(principal, action, path), metadata)
}

fn same_actor_edit_before_stage() -> Rule {
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        Regex::concat([
            Regex::All,
            Regex::test(Test::and([
                Test::EqPrincipal(ComponentPattern::variable("actor")),
                Test::EqAction(ComponentPattern::constant(Action::Edit)),
                Test::EqResource(ComponentPattern::variable("target")),
            ])),
        ]),
    )
}

#[test]
fn require_rule_uses_only_committed_pre_candidate_history() {
    let arena = Bump::new();
    let mut validator = Validator::compile(&arena, [same_actor_edit_before_stage()]).unwrap();

    let denied = validator.check(request("alice", Action::Stage, &["src", "a.rs"], 1));
    assert!(matches!(denied, Decision::Denied(_)));
    assert!(validator.history().is_empty());

    let edit = validator.check(request("alice", Action::Edit, &["src", "a.rs"], 2));
    assert!(matches!(edit, Decision::Grant(grant) if grant.metadata == 2));

    let stage = validator.check(request("alice", Action::Stage, &["src", "a.rs"], 3));
    assert!(matches!(stage, Decision::Grant(grant) if grant.metadata == 3));
    assert_eq!(validator.history().len(), 2);
}

#[test]
fn forbid_rule_denies_duplicate_commit_without_mutating_history() {
    let arena = Bump::new();
    let matching_commit = Regex::test(Test::and([
        Test::EqAction(ComponentPattern::constant(Action::commit("ship"))),
        Test::EqResource(ComponentPattern::variable("target")),
    ]));
    let rule = Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::commit("ship")),
            ComponentPattern::variable("target"),
        ),
        Regex::concat([Regex::All, matching_commit, Regex::All]),
    );
    let mut validator = Validator::compile(&arena, [rule]).unwrap();

    assert!(
        validator
            .check(request("alice", Action::commit("ship"), &["a"], ()))
            .is_grant()
    );
    let checkpoint = validator.checkpoint();

    let denied = validator.check(request("alice", Action::commit("ship"), &["a"], ()));
    assert!(matches!(denied, Decision::Denied(denial) if denial.rule_index == 1));
    assert_eq!(validator.checkpoint(), checkpoint);

    assert!(
        validator
            .check(request("alice", Action::commit("ship"), &["b"], ()))
            .is_grant()
    );
}

#[test]
fn complement_is_exact_over_complete_history() {
    let arena = Bump::new();
    let no_edit = Regex::not(Regex::concat([
        Regex::All,
        Regex::test(Test::EqAction(ComponentPattern::constant(Action::Edit))),
        Regex::All,
    ]));
    let rule = Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        no_edit,
    );
    let mut validator = Validator::compile(&arena, [rule]).unwrap();

    assert!(
        validator
            .check(request("alice", Action::Stage, &["a"], ()))
            .is_grant()
    );
    assert!(
        validator
            .check(request("bob", Action::Edit, &["elsewhere"], ()))
            .is_grant()
    );
    assert!(matches!(
        validator.check(request("alice", Action::Stage, &["a"], ())),
        Decision::Denied(_)
    ));
}

#[test]
fn compile_rejects_unbound_and_cross_component_variables() {
    let arena = Bump::new();
    let missing = Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        Regex::test(Test::EqPrincipal(ComponentPattern::variable("missing"))),
    );
    assert!(matches!(
        Validator::compile(&arena, [missing]),
        Err(CompileError::UnboundVariable { rule: 1, .. })
    ));

    let conflict = Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::variable("same"),
            ComponentPattern::constant(["a"]),
        ),
        Regex::All,
    );
    assert!(matches!(
        Validator::compile(&arena, [conflict]),
        Err(CompileError::VariableComponentConflict { rule: 1, .. })
    ));
}

#[test]
fn checkpoint_restores_append_only_history() {
    let arena = Bump::new();
    let mut validator = Validator::compile(&arena, []).unwrap();
    assert!(
        validator
            .check(request("alice", Action::Read, &["a"], ()))
            .is_grant()
    );
    let checkpoint = validator.checkpoint();
    assert!(
        validator
            .check(request("bob", Action::Diff, &["b"], ()))
            .is_grant()
    );
    validator.rollback(checkpoint);
    assert_eq!(validator.history(), &[event("alice", Action::Read, &["a"])]);
}
