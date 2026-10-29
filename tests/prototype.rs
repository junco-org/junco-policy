use junco_core::{
    AtomPattern, Comparison, CompileError, ComponentPattern, Decision, Head, RegexExpr, Request,
    Rule, RuleMode, Store, TestExpr, Validator,
};
use junco_policy::{Action, LockEvent};
use std::sync::Arc;

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

fn request<M>(
    actor: Actor,
    action: Action,
    path: Path,
    metadata: M,
) -> Request<LockEvent<Actor, Path>, M> {
    Request::new(LockEvent::new(actor, action, path), metadata)
}

fn same_actor_edit_before_release() -> Rule<LockEvent<Actor, Path>> {
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
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        tail,
    )
}

#[test]
fn require_rule_uses_only_committed_pre_candidate_history() {
    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder.add_rule(same_actor_edit_before_release()).unwrap();
    let mut validator = builder.finish().unwrap();

    let denied = validator
        .check(request(Actor::Alice, Action::Release, Path::SrcA, 1))
        .unwrap();
    assert!(matches!(denied, Decision::Denied(_)));
    assert!(validator.history().is_empty());

    let edit = validator
        .check(request(Actor::Alice, Action::Edit, Path::SrcA, 2))
        .unwrap();
    assert!(matches!(edit, Decision::Grant(grant) if grant.metadata == 2));

    let release = validator
        .check(request(Actor::Alice, Action::Release, Path::SrcA, 3))
        .unwrap();
    assert!(matches!(release, Decision::Grant(grant) if grant.metadata == 3));
    assert_eq!(validator.history().len(), 2);
}

#[test]
fn forbid_rule_denies_duplicate_remove_without_mutating_history() {
    let action = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(Action::Remove)),
    );
    let resource = TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::variable("target")),
    );
    let matching_remove = RegexExpr::test(TestExpr::and([action, resource]));
    let tail = RegexExpr::concat([RegexExpr::all(), matching_remove, RegexExpr::all()]);
    let rule = Rule::new(
        RuleMode::Forbid,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Remove),
            ComponentPattern::variable("target"),
        ),
        tail,
    );

    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder.add_rule(rule).unwrap();
    let mut validator = builder.finish().unwrap();

    assert!(
        validator
            .check(request(Actor::Alice, Action::Remove, Path::A, ()))
            .unwrap()
            .is_grant()
    );
    let history = validator.history().to_vec();

    let denied = validator
        .check(request(Actor::Alice, Action::Remove, Path::A, ()))
        .unwrap();
    assert!(matches!(denied, Decision::Denied(denial) if denial.mode == RuleMode::Forbid));
    assert_eq!(validator.history(), history.as_slice());

    assert!(
        validator
            .check(request(Actor::Alice, Action::Remove, Path::B, ()))
            .unwrap()
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
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("target"),
        ),
        RegexExpr::complement(contains_edit),
    );

    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::builder(Arc::clone(&store));
    builder.add_rule(rule).unwrap();
    let mut validator = builder.finish().unwrap();

    assert!(
        validator
            .check(request(Actor::Alice, Action::Release, Path::A, ()))
            .unwrap()
            .is_grant()
    );
    assert!(
        validator
            .check(request(Actor::Bob, Action::Edit, Path::Elsewhere, ()))
            .unwrap()
            .is_grant()
    );
    assert!(matches!(
        validator
            .check(request(Actor::Alice, Action::Release, Path::A, ()))
            .unwrap(),
        Decision::Denied(_)
    ));
}

#[test]
fn construction_rejects_unbound_and_cross_component_variables() {
    let store = Arc::new(Store::new().unwrap());
    let mut builder = Validator::<LockEvent<Actor, Path>>::builder(Arc::clone(&store));
    let missing = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Action::Release),
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

    let mut builder = Validator::<LockEvent<Actor, Path>>::builder(Arc::clone(&store));
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
    let mut builder =
        Validator::<LockEvent<Actor, Actor>>::builder(Arc::new(Store::new().unwrap()));
    let head_conflict = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::constant(Action::Release),
            ComponentPattern::variable("same"),
        ),
        RegexExpr::all(),
    ));
    assert!(matches!(
        head_conflict,
        Err(CompileError::VariableComponentConflict { name }) if name == "same"
    ));

    let mut builder =
        Validator::<LockEvent<Actor, Actor>>::builder(Arc::new(Store::new().unwrap()));
    let tail_conflict = builder.add_rule(Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::constant(Action::Release),
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
    let store = Arc::new(Store::new().unwrap());
    let mut validator = Validator::builder(Arc::clone(&store)).finish().unwrap();
    assert!(
        validator
            .check(request(Actor::Alice, Action::Read, Path::A, ()))
            .unwrap()
            .is_grant()
    );
    let checkpoint = validator.checkpoint();
    assert!(
        validator
            .check(request(Actor::Bob, Action::Remove, Path::B, ()))
            .unwrap()
            .is_grant()
    );
    validator.rollback(checkpoint).unwrap();
    assert_eq!(
        validator.history(),
        &[LockEvent::new(Actor::Alice, Action::Read, Path::A)]
    );
}
