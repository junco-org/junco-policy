use rust_validator::{
    Action, AtomPattern, Bump, Comparison, CompileError, ComponentPattern, Decision, Event, Head,
    Request, RuleMode, Validator,
};

fn event(principal: &str, action: Action, path: &[&str]) -> Event {
    Event::new(principal, action, path.to_vec())
}

fn request<M>(principal: &str, action: Action, path: &[&str], metadata: M) -> Request<M> {
    Request::new(event(principal, action, path), metadata)
}

fn add_same_actor_edit_before_stage(validator: &mut rust_validator::ValidatorBuilder<'_>) {
    validator
        .add_rule(
            RuleMode::Require,
            Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Action::Stage),
                ComponentPattern::variable("target"),
            ),
            |syntax| {
                let principal = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Principal(ComponentPattern::variable("actor")),
                )?;
                let action = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
                )?;
                let resource = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Resource(ComponentPattern::variable("target")),
                )?;
                let predicate = syntax.and([principal, action, resource]);
                let event = syntax.test(predicate);
                let all = syntax.all();
                Ok(syntax.concat([all, event]))
            },
        )
        .unwrap();
}

#[test]
fn require_rule_uses_only_committed_pre_candidate_history() {
    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    add_same_actor_edit_before_stage(&mut builder);
    let mut validator = builder.finish();

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
    let mut builder = Validator::builder(&arena);
    builder
        .add_rule(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Action::commit("ship")),
                ComponentPattern::variable("target"),
            ),
            |syntax| {
                let action = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Action(ComponentPattern::constant(Action::commit("ship"))),
                )?;
                let resource = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Resource(ComponentPattern::variable("target")),
                )?;
                let matching_commit = syntax.and([action, resource]);
                let matching_commit = syntax.test(matching_commit);
                let prefix = syntax.all();
                let suffix = syntax.all();
                Ok(syntax.concat([prefix, matching_commit, suffix]))
            },
        )
        .unwrap();
    let mut validator = builder.finish();

    assert!(
        validator
            .check(request("alice", Action::commit("ship"), &["a"], ()))
            .is_grant()
    );
    let checkpoint = validator.checkpoint();

    let denied = validator.check(request("alice", Action::commit("ship"), &["a"], ()));
    assert!(matches!(denied, Decision::Denied(denial) if denial.rule_index.get() == 1));
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
    let mut builder = Validator::builder(&arena);
    builder
        .add_rule(
            RuleMode::Require,
            Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Action::Stage),
                ComponentPattern::variable("target"),
            ),
            |syntax| {
                let edit = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
                )?;
                let edit = syntax.test(edit);
                let prefix = syntax.all();
                let suffix = syntax.all();
                let contains_edit = syntax.concat([prefix, edit, suffix]);
                Ok(syntax.not(contains_edit))
            },
        )
        .unwrap();
    let mut validator = builder.finish();

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
fn construction_rejects_unbound_and_cross_component_variables() {
    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    let missing = builder.add_rule(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        |syntax| {
            let test = syntax.atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("missing")),
            )?;
            Ok(syntax.test(test))
        },
    );
    assert!(matches!(
        missing,
        Err(CompileError::UnboundVariable { rule, .. }) if rule.get() == 1
    ));

    let mut builder = Validator::builder(&arena);
    let conflict = builder.add_rule(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::variable("same"),
            ComponentPattern::constant(["a"]),
        ),
        |syntax| Ok(syntax.all()),
    );
    assert!(matches!(
        conflict,
        Err(CompileError::VariableComponentConflict { rule, .. }) if rule.get() == 1
    ));
}

#[test]
fn hashconsed_handles_cannot_cross_rule_scopes() {
    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    let mut leaked = None;
    builder
        .add_rule(
            RuleMode::Require,
            Head::new(
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Action::Stage),
                ComponentPattern::constant(["a"]),
            ),
            |syntax| {
                let actor = syntax.atom(
                    Comparison::Eq,
                    AtomPattern::Principal(ComponentPattern::variable("actor")),
                )?;
                let actor = syntax.test(actor);
                leaked = Some(actor);
                Ok(actor)
            },
        )
        .unwrap();

    let result = builder.add_rule(
        RuleMode::Require,
        Head::new(
            ComponentPattern::constant("bob"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::constant(["b"]),
        ),
        |_| Ok(leaked.unwrap()),
    );
    assert!(matches!(
        result,
        Err(CompileError::ForeignRuleHandle { rule }) if rule.get() == 2
    ));
}

#[test]
fn checkpoint_restores_append_only_history() {
    let arena = Bump::new();
    let mut validator = Validator::builder(&arena).finish();
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

#[test]
fn rule_indexes_are_nonzero_and_one_based() {
    assert!(rust_validator::RuleIndex::new(0).is_none());
    assert_eq!(rust_validator::RuleIndex::new(1).unwrap().get(), 1);
}

#[test]
#[should_panic(expected = "checkpoint belongs to another validator")]
fn checkpoints_cannot_cross_validator_contexts() {
    let arena = Bump::new();
    let first = Validator::builder(&arena).finish();
    let checkpoint = first.checkpoint();
    let mut second = Validator::builder(&arena).finish();
    second.rollback(checkpoint);
}
