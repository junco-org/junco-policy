use junco_policy::{
    Action, AtomPattern, Bump, Comparison, CompileError, ComponentPattern, Decision, GitEvent,
    Head, MessageId, RegexExpr, Request, Rule, RuleMode, TestExpr, Validator, git_event,
};

/// Caller-owned principal identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Actor {
    Alice,
    Bob,
}

/// Caller-owned resource identities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Path {
    SrcA,
    A,
    B,
    Elsewhere,
}

/// Commit message identity the duplicate-commit rule forbids repeating.
const SHIP: MessageId = MessageId(1);

fn request<M>(
    actor: Actor,
    action: Action,
    path: Path,
    metadata: M,
) -> Request<GitEvent<Actor, Path>, M> {
    Request::new(git_event(actor, action, path), metadata)
}

fn same_actor_edit_before_stage() -> Rule<GitEvent<Actor, Path>> {
    let principal = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("actor")),
    );
    let action = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
    );
    let resource = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::variable("target")),
    );
    let event = RegexExpr::test(TestExpr::and([principal, action, resource]));
    let tail = RegexExpr::concat([RegexExpr::all(), event]);
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        tail,
    )
}

#[test]
fn require_rule_uses_only_committed_pre_candidate_history() {
    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    builder.add_rule(same_actor_edit_before_stage()).unwrap();
    let mut validator = builder.finish();

    let denied = validator.check(request(Actor::Alice, Action::Stage, Path::SrcA, 1));
    assert!(matches!(denied, Decision::Denied(_)));
    assert!(validator.history().is_empty());

    let edit = validator.check(request(Actor::Alice, Action::Edit, Path::SrcA, 2));
    assert!(matches!(edit, Decision::Grant(grant) if grant.metadata == 2));

    let stage = validator.check(request(Actor::Alice, Action::Stage, Path::SrcA, 3));
    assert!(matches!(stage, Decision::Grant(grant) if grant.metadata == 3));
    assert_eq!(validator.history().len(), 2);
}

#[test]
fn forbid_rule_denies_duplicate_commit_without_mutating_history() {
    let action = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::commit(SHIP))),
    );
    let resource = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::variable("target")),
    );
    let matching_commit = RegexExpr::test(TestExpr::and([action, resource]));
    let tail = RegexExpr::concat([RegexExpr::all(), matching_commit, RegexExpr::all()]);
    let rule = Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::commit(SHIP)),
            ComponentPattern::variable("target"),
        ),
        tail,
    );

    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    builder.add_rule(rule).unwrap();
    let mut validator = builder.finish();

    assert!(
        validator
            .check(request(Actor::Alice, Action::commit(SHIP), Path::A, ()))
            .is_grant()
    );
    let history = validator.history().to_vec();

    let denied = validator.check(request(Actor::Alice, Action::commit(SHIP), Path::A, ()));
    assert!(matches!(denied, Decision::Denied(denial) if denial.mode == RuleMode::Forbid));
    assert_eq!(validator.history(), history.as_slice());

    assert!(
        validator
            .check(request(Actor::Alice, Action::commit(SHIP), Path::B, ()))
            .is_grant()
    );
}

#[test]
fn complement_is_exact_over_complete_history() {
    let edit = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Edit)),
    ));
    let contains_edit = RegexExpr::concat([RegexExpr::all(), edit, RegexExpr::all()]);
    let rule = Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::complement(contains_edit),
    );

    let arena = Bump::new();
    let mut builder = Validator::builder(&arena);
    builder.add_rule(rule).unwrap();
    let mut validator = builder.finish();

    assert!(
        validator
            .check(request(Actor::Alice, Action::Stage, Path::A, ()))
            .is_grant()
    );
    assert!(
        validator
            .check(request(Actor::Bob, Action::Edit, Path::Elsewhere, ()))
            .is_grant()
    );
    assert!(matches!(
        validator.check(request(Actor::Alice, Action::Stage, Path::A, ())),
        Decision::Denied(_)
    ));
}

#[test]
fn construction_rejects_unbound_and_cross_component_variables() {
    let arena = Bump::new();
    let mut builder = Validator::<GitEvent<Actor, Path>>::builder(&arena);
    let missing = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("missing")),
        )),
    ));
    assert!(matches!(
        missing,
        Err(CompileError::UnboundVariable { name }) if name == "missing"
    ));

    let mut builder = Validator::<GitEvent<Actor, Path>>::builder(&arena);
    let conflict = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::variable("same"),
            ComponentPattern::constant(Path::A),
        ),
        RegexExpr::all(),
    ));
    assert!(matches!(
        conflict,
        Err(CompileError::VariableComponentConflict { name }) if name == "same"
    ));

    // Principal and resource share one Rust type; coordinates must still stay distinct.
    let mut builder = Validator::<GitEvent<Actor, Actor>>::builder(&arena);
    let head_conflict = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::variable("same"),
        ),
        RegexExpr::all(),
    ));
    assert!(matches!(
        head_conflict,
        Err(CompileError::VariableComponentConflict { name }) if name == "same"
    ));

    let mut builder = Validator::<GitEvent<Actor, Actor>>::builder(&arena);
    let tail_conflict = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::constant(Action::Stage),
            ComponentPattern::constant(Actor::Bob),
        ),
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::variable("same")),
        )),
    ));
    assert!(matches!(
        tail_conflict,
        Err(CompileError::VariableComponentConflict { name }) if name == "same"
    ));
}

#[test]
fn checkpoint_restores_append_only_history() {
    let arena = Bump::new();
    let mut validator = Validator::builder(&arena).finish();
    assert!(
        validator
            .check(request(Actor::Alice, Action::Read, Path::A, ()))
            .is_grant()
    );
    let checkpoint = validator.checkpoint();
    assert!(
        validator
            .check(request(Actor::Bob, Action::Diff, Path::B, ()))
            .is_grant()
    );
    validator.rollback(checkpoint);
    assert_eq!(
        validator.history(),
        &[git_event(Actor::Alice, Action::Read, Path::A)]
    );
}
