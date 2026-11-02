//! Fallible, iterative lowering of the owned DSL into the canonical portable tables.

use crate::error::{CompileError, HistoryError};
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use alloc::vec::Vec;
use history_syntax::Event;
use history_syntax::syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, TestExpr,
};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::flatten::*;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs::{no_internal_compile_error, no_internal_error};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

#[cfg(verus_keep_ghost)]
verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
}

/// A concrete component value tagged with its coordinate, even when component Rust types coincide.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub enum ComponentValue<E: Event> {
    Principal(E::Principal),
    Action(E::Action),
    Resource(E::Resource),
}

#[verus_verify]
impl<E: Event> PartialEq for ComponentValue<E> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Principal(left), Self::Principal(right)) => left == right,
            (Self::Action(left), Self::Action(right)) => left == right,
            (Self::Resource(left), Self::Resource(right)) => left == right,
            _ => false,
        }
    }
}

impl<E: Event> Eq for ComponentValue<E> {}

impl<E: Event> core::hash::Hash for ComponentValue<E> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        core::hash::Hash::hash(&core::mem::discriminant(self), state);
        match self {
            Self::Principal(value) => core::hash::Hash::hash(value, state),
            Self::Action(value) => core::hash::Hash::hash(value, state),
            Self::Resource(value) => core::hash::Hash::hash(value, state),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl<E: Event> PartialEqSpecImpl for ComponentValue<E> {
    open spec fn obeys_eq_spec() -> bool {
        E::Principal::obeys_eq_spec() && E::Action::obeys_eq_spec() && E::Resource::obeys_eq_spec()
    }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Principal(left), Self::Principal(right)) => left.eq_spec(right),
            (Self::Action(left), Self::Action(right)) => left.eq_spec(right),
            (Self::Resource(left), Self::Resource(right)) => left.eq_spec(right),
            _ => false,
        }
    }
}
}

// Only borrowed source nodes enter the work stack: every failure leaves caller-owned trees intact.
#[verus_verify]
pub(crate) enum Work<'a, E: Event> {
    Regex(&'a RegexExpr<E>),
    Test(&'a TestExpr<E>),
    FinishRegex(&'a RegexExpr<E>, usize),
    FinishTest(&'a TestExpr<E>, usize),
}

#[verus_verify]
#[verus_spec(result => ensures
    result is Ok ==> final(values)@ == old(values)@.push(value),
    result is Err ==> final(values)@ == old(values)@,
    no_internal_error(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
)]
fn push<T, L: Limits>(
    values: &mut Vec<T>,
    value: T,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    match world.try_reserve_vec(values, 1) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    values.push(value);
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures
    start <= old(values)@.len() ==> no_internal_error(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    match result {
        Ok(children) => start <= old(values)@.len()
            && children@ == old(values)@.subrange(start as int, old(values)@.len() as int)
            && final(values)@ == old(values)@.subrange(0, start as int),
        Err(_) => final(values)@ == old(values)@,
    },
)]
fn take_children<L: Limits>(
    values: &mut Vec<u32>,
    start: usize,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<u32>, HistoryError> {
    if start > values.len() {
        return Err(HistoryError::invariant("invalid source operand range"));
    }
    let count = values.len() - start;
    let mut children = Vec::new();
    match world.try_reserve_vec_exact(&mut children, count) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    let mut index = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= index <= values@.len(),
            children@ == values@.subrange(start as int, index as int),
        decreases values@.len() - index,
    ))]
    while index < values.len() {
        limits.checkpoint()?;
        children.push(values[index]);
        index += 1;
    }
    values.truncate(start);
    Ok(children)
}

#[verus_verify]
#[verus_spec(result => requires
    old(scope).name_spec(Component::Principal) is None,
    old(scope).name_spec(Component::Action) is None,
    old(scope).name_spec(Component::Resource) is None,
    ensures result matches Ok(flat) ==>
        head_represents::<E>(flat@, head@) && crate::verify::dsl::head_scoped(head@)
        && scope_matches::<E>(*final(scope), head@),
    result is Ok <==> crate::verify::dsl::head_scoped(head@),
    no_internal_compile_error(result),
    !(result matches Err(CompileError::Runtime(_))),
)]
fn flatten_head<'a, E: Event>(
    head: &'a Head<E>,
    scope: &mut VariableScope<'a>,
) -> Result<[FlatHead<ComponentValue<E>>; 3], CompileError> {
    let principal = match &head.principal {
        ComponentPattern::Constant(value) => FlatHead::Constant(ComponentValue::Principal(*value)),
        ComponentPattern::Variable(name) => {
            scope.bind(Component::Principal, name.as_str())?;
            FlatHead::Bind
        }
    };
    let action = match &head.action {
        ComponentPattern::Constant(value) => FlatHead::Constant(ComponentValue::Action(*value)),
        ComponentPattern::Variable(name) => {
            scope.bind(Component::Action, name.as_str())?;
            FlatHead::Bind
        }
    };
    let resource = match &head.resource {
        ComponentPattern::Constant(value) => FlatHead::Constant(ComponentValue::Resource(*value)),
        ComponentPattern::Variable(name) => {
            scope.bind(Component::Resource, name.as_str())?;
            FlatHead::Bind
        }
    };
    Ok([principal, action, resource])
}

#[verus_verify]
#[verus_spec(result => ensures result matches Ok((field, term)) ==>
    forall|head| scope_matches::<E>(*scope, head) ==> atom_term_represents::<E>(field, term, atom@, head),
    no_internal_compile_error(result),
    !(result matches Err(CompileError::Runtime(_))),
    forall|head| scope_matches::<E>(*scope, head)
        && crate::verify::dsl::atom_scoped(atom@, head) ==> result is Ok,
)]
fn flatten_atom<E: Event>(
    atom: &AtomPattern<E>,
    scope: &VariableScope<'_>,
) -> Result<(Component, FlatTerm<ComponentValue<E>>), CompileError> {
    match atom {
        AtomPattern::Principal(pattern) => Ok((
            Component::Principal,
            match pattern {
                ComponentPattern::Constant(value) => {
                    FlatTerm::Constant(ComponentValue::Principal(*value))
                }
                ComponentPattern::Variable(name) => {
                    FlatTerm::Variable(scope.resolve(Component::Principal, name.as_str())?)
                }
            },
        )),
        AtomPattern::Action(pattern) => Ok((
            Component::Action,
            match pattern {
                ComponentPattern::Constant(value) => {
                    FlatTerm::Constant(ComponentValue::Action(*value))
                }
                ComponentPattern::Variable(name) => {
                    FlatTerm::Variable(scope.resolve(Component::Action, name.as_str())?)
                }
            },
        )),
        AtomPattern::Resource(pattern) => Ok((
            Component::Resource,
            match pattern {
                ComponentPattern::Constant(value) => {
                    FlatTerm::Constant(ComponentValue::Resource(*value))
                }
                ComponentPattern::Variable(name) => {
                    FlatTerm::Variable(scope.resolve(Component::Resource, name.as_str())?)
                }
            },
        )),
    }
}

#[verus_verify]
#[verus_spec(result => ensures result is Ok ==> forall|ts, rs|
    run_work::<E>(final(work)@, ts, rs) == run_work::<E>(old(work)@, ts,
        rs + regex_views::<E>(children@)),
    result is Ok ==> work_cost::<E>(final(work)@) == work_cost::<E>(old(work)@)
        + regex_forest_cost::<E>(regex_views::<E>(children@)),
    no_internal_error(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result is Ok ==> forall|head| work_scoped::<E>(old(work)@, head)
        && (forall|i: int| 0 <= i < children@.len()
            ==> crate::verify::dsl::regex_scoped(children@[i]@, head))
        ==> work_scoped::<E>(final(work)@, head),
)]
fn schedule_regexes<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [RegexExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    proof_decl! { let ghost before = work@; }
    let mut index = children.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= children@.len(),
            forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts, rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int))),
            work_cost::<E>(work@) == work_cost::<E>(before)
                + regex_forest_cost::<E>(regex_views::<E>(children@.subrange(index as int, children@.len() as int))),
            forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::verify::dsl::regex_scoped(children@[i]@, head))
                ==> work_scoped::<E>(work@, head),
        decreases index,
    ))]
    while index > 0 {
        limits.checkpoint()?;
        proof_decl! { let ghost previous = work@; }
        index -= 1;
        push(work, Work::Regex(&children[index]), limits, world)?;
        proof! {
            assert(work@.drop_last() =~= previous);
            assert forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::verify::dsl::regex_scoped(children@[i]@, head))
                implies work_scoped::<E>(work@, head) by {
                lemma_work_scoped_push::<E>(previous, Work::Regex(&children[index as int]), head);
            }
            assert(match work@.last() { Work::Regex(source) => source@ == children@[index as int]@, _ => false });
            reveal_with_fuel(regex_forest_cost, 2);
            let suffix = regex_views::<E>(children@.subrange(index as int + 1, children@.len() as int));
            assert(regex_views::<E>(children@.subrange(index as int, children@.len() as int))
                =~= seq![children@[index as int]@] + suffix);
            lemma_regex_forest_cost_append::<E>(seq![children@[index as int]@], suffix);
            reveal_with_fuel(run_work, 2);
            reveal_with_fuel(work_cost, 2);
            assert forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts, rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int))) by {
                assert(run_work::<E>(work@, ts, rs)
                    == run_work::<E>(previous, ts, rs.push(children@[index as int]@)));
                assert(rs.push(children@[index as int]@) + suffix
                    =~= rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int)));
            }
            assert(work_cost::<E>(work@) == work_cost::<E>(previous) + regex_cost::<E>(children@[index as int]@));
        }
    }
    proof! { assert(children@.subrange(0, children@.len() as int) =~= children@); }
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures result is Ok ==> forall|ts, rs|
    run_work::<E>(final(work)@, ts, rs) == run_work::<E>(old(work)@,
        ts + test_views::<E>(children@), rs),
    result is Ok ==> work_cost::<E>(final(work)@) == work_cost::<E>(old(work)@)
        + test_forest_cost::<E>(test_views::<E>(children@)),
    no_internal_error(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result is Ok ==> forall|head| work_scoped::<E>(old(work)@, head)
        && (forall|i: int| 0 <= i < children@.len()
            ==> crate::verify::dsl::test_scoped(children@[i]@, head))
        ==> work_scoped::<E>(final(work)@, head),
)]
fn schedule_tests<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [TestExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    proof_decl! { let ghost before = work@; }
    let mut index = children.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= children@.len(),
            forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)), rs),
            work_cost::<E>(work@) == work_cost::<E>(before)
                + test_forest_cost::<E>(test_views::<E>(children@.subrange(index as int, children@.len() as int))),
            forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::verify::dsl::test_scoped(children@[i]@, head))
                ==> work_scoped::<E>(work@, head),
        decreases index,
    ))]
    while index > 0 {
        limits.checkpoint()?;
        proof_decl! { let ghost previous = work@; }
        index -= 1;
        push(work, Work::Test(&children[index]), limits, world)?;
        proof! {
            assert(work@.drop_last() =~= previous);
            assert forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::verify::dsl::test_scoped(children@[i]@, head))
                implies work_scoped::<E>(work@, head) by {
                lemma_work_scoped_push::<E>(previous, Work::Test(&children[index as int]), head);
            }
            assert(match work@.last() { Work::Test(source) => source@ == children@[index as int]@, _ => false });
            reveal_with_fuel(test_forest_cost, 2);
            let suffix = test_views::<E>(children@.subrange(index as int + 1, children@.len() as int));
            assert(test_views::<E>(children@.subrange(index as int, children@.len() as int))
                =~= seq![children@[index as int]@] + suffix);
            lemma_test_forest_cost_append::<E>(seq![children@[index as int]@], suffix);
            reveal_with_fuel(run_work, 2);
            reveal_with_fuel(work_cost, 2);
            assert forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)), rs) by {
                assert(run_work::<E>(work@, ts, rs)
                    == run_work::<E>(previous, ts.push(children@[index as int]@), rs));
                assert(ts.push(children@[index as int]@) + suffix
                    =~= ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)));
            }
            assert(work_cost::<E>(work@) == work_cost::<E>(previous) + test_cost::<E>(children@[index as int]@));
        }
    }
    proof! { assert(children@.subrange(0, children@.len() as int) =~= children@); }
    Ok(())
}

/// Lowers borrowed syntax in source order without constructing an executable graph.
/// Resource failures propagate; well-scoped inputs cannot produce scope diagnostics.
/// The continuation invariant excludes internal stack and operand-guard failures.
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
#[verus_spec(result => ensures
    no_internal_compile_error(result),
    !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
    crate::verify::dsl::head_scoped(rule.head@)
        && crate::verify::dsl::regex_scoped(rule.tail@, rule.head@)
        ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
            && !(result matches Err(CompileError::UnboundVariable { .. })),
    result matches Ok(flat) ==> flattened::<E>(*rule, flat)
        && crate::verify::encoding::constants_in_domain(flat.source, component_domain::<E>()),
)]
pub fn flatten_rule<E: Event, L: Limits>(
    rule: &Rule<E>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRule<ComponentValue<E>>, CompileError> {
    limits.checkpoint().map_err(HistoryError::from)?;
    let mut scope = VariableScope::new();
    let head = flatten_head(&rule.head, &mut scope)?;
    let mut builder = FlatBuilder::new(head);
    let mut work = Vec::new();
    let mut tests: Vec<u32> = Vec::new();
    let mut regexes: Vec<u32> = Vec::new();
    proof_decl! {
        let ghost mut test_sources = Seq::empty();
        let ghost mut regex_sources = Seq::empty();
    }
    push(&mut work, Work::Regex(&rule.tail), limits, world)?;
    proof! {
        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@]))) by {
            reveal_with_fuel(run_work, 2);
        }
        if crate::verify::dsl::regex_scoped(rule.tail@, rule.head@) {
            assert(work_scoped::<E>(work@, rule.head@)) by { reveal(work_scoped); }
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant builder.wf(),
            head_represents::<E>(builder.head_view(), rule.head@),
            crate::verify::dsl::head_scoped(rule.head@),
            scope_matches::<E>(scope, rule.head@),
            crate::verify::dsl::regex_scoped(rule.tail@, rule.head@)
                ==> work_scoped::<E>(work@, rule.head@),
            forall|i: int| 0 <= i < 3 ==> crate::verify::encoding::head_in_domain(
                builder.head_view()[i], crate::verify::encoding::field_at(i), component_domain::<E>()),
            forall|i: int| 0 <= i < builder.tests_view().len()
                ==> crate::verify::encoding::test_in_domain(builder.tests_view()[i], component_domain::<E>()),
            result_stacks::<E>(builder.tests_view(), builder.regexes_view(), tests@, regexes@,
                test_sources, regex_sources, rule.head@),
            run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])),
        decreases work_cost::<E>(work@),
    ))]
    while !work.is_empty() {
        limits.checkpoint().map_err(HistoryError::from)?;
        proof_decl! {
            let ghost old_tests = builder.tests_view();
            let ghost old_regexes = builder.regexes_view();
            let ghost old_work = work@;
            let ghost old_test_ids = tests@;
            let ghost old_regex_ids = regexes@;
            let ghost old_test_sources = test_sources;
            let ghost old_regex_sources = regex_sources;
        }
        let task = match work.pop() {
            Some(task) => task,
            None => return Err(HistoryError::invariant("missing source work").into()),
        };
        proof! {
            assert(old_work =~= work@.push(task));
            assert(old_work.drop_last() =~= work@);
            lemma_run_work_step::<E>(old_work, test_sources, regex_sources);
            if crate::verify::dsl::regex_scoped(rule.tail@, rule.head@) {
                lemma_work_scoped_pop::<E>(old_work, rule.head@);
                assert(work_scoped::<E>(work@, rule.head@));
            }
            reveal_with_fuel(work_cost, 2);
            reveal_with_fuel(history_syntax::verify::dsl::regex_view, 2);
            reveal_with_fuel(history_syntax::verify::dsl::test_view, 2);
            reveal(regex_cost);
            reveal(test_cost);
        }
        match task {
            Work::Regex(regex) => match regex {
                RegexExpr::Empty | RegexExpr::All | RegexExpr::Epsilon => {
                    let node = match regex {
                        RegexExpr::Empty => FlatRegex::Empty,
                        RegexExpr::All => FlatRegex::All,
                        _ => FlatRegex::Epsilon,
                    };
                    let id = builder.regex(node, limits, world)?;
                    proof! {
                        assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                        assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                        lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                            old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), id as nat, regex@, rule.head@));
                    }
                    push(&mut regexes, id, limits, world)?;
                    proof! { regex_sources = regex_sources.push(regex@); }
                }
                RegexExpr::Test(test) => {
                    proof! {
                        lemma_visit_test_regex::<E>(work@, regex, test, tests.len(), test_sources, regex_sources, rule.head@);
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, tests.len()));
                        lemma_work_cost_push::<E>(work@.push(Work::FinishRegex(regex, tests.len())), Work::Test(test));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, tests.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Test(test), limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
                RegexExpr::Star(child) | RegexExpr::Not(child) => {
                    proof! {
                        lemma_visit_unary_regex::<E>(work@, regex, child, regexes.len(), test_sources, regex_sources, rule.head@);
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, regexes.len()));
                        lemma_work_cost_push::<E>(work@.push(Work::FinishRegex(regex, regexes.len())), Work::Regex(child));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Regex(child), limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
                RegexExpr::Concat(children)
                | RegexExpr::Union(children)
                | RegexExpr::Intersect(children) => {
                    proof! { match regex@ {
                        history_syntax::verify::dsl::RegexView::Concat(items) | history_syntax::verify::dsl::RegexView::Union(items)
                            | history_syntax::verify::dsl::RegexView::Intersect(items) => assert(items =~= regex_views::<E>(children@)),
                        _ => {},
                    } }
                    proof! {
                        lemma_finish_many_regex::<E>(work@, regex, regexes.len(), test_sources, regex_sources, regex_views::<E>(children@), rule.head@);
                        if crate::verify::dsl::regex_scoped(rule.tail@, rule.head@) {
                            assert forall|i: int| 0 <= i < children@.len() implies
                                crate::verify::dsl::regex_scoped(children@[i]@, rule.head@) by {
                                assert(regex_views::<E>(children@)[i] == children@[i]@);
                            }
                        }
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, regexes.len()));
                        assert(regex_cost::<E>(regex@) == 2 + regex_forest_cost::<E>(regex_views::<E>(children@)));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    schedule_regexes(&mut work, children, limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
            },
            Work::Test(test) => match test {
                TestExpr::True | TestExpr::False | TestExpr::Atom { .. } => {
                    let node = match test {
                        TestExpr::True => FlatTest::Bool(true),
                        TestExpr::False => FlatTest::Bool(false),
                        TestExpr::Atom {
                            comparison,
                            pattern,
                        } => {
                            proof! {
                                if crate::verify::dsl::regex_scoped(rule.tail@, rule.head@) {
                                    assert(crate::verify::dsl::atom_scoped(pattern@, rule.head@)) by {
                                        reveal_with_fuel(crate::verify::dsl::test_scoped, 1);
                                    }
                                }
                            }
                            let (field, term) = flatten_atom(pattern, &scope)?;
                            FlatTest::Atom {
                                field,
                                term,
                                positive: matches!(comparison, Comparison::Eq),
                            }
                        }
                        _ => return Err(HistoryError::invariant("invalid source test leaf").into()),
                    };
                    proof! {
                        assert(crate::flat::verify::test_wf(builder.head_view(), node, builder.tests_view().len()));
                        assert(crate::verify::encoding::test_in_domain(node, component_domain::<E>()));
                    }
                    let id = builder.test(node, limits, world)?;
                    proof! {
                        assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                        assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                        lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                            old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                        assert(test_represents::<E>(builder.tests_view(), id as nat, test@, rule.head@));
                    }
                    push(&mut tests, id, limits, world)?;
                    proof! { test_sources = test_sources.push(test@); }
                }
                TestExpr::And(children) | TestExpr::Or(children) => {
                    proof! { match test@ {
                        history_syntax::verify::dsl::TestView::And(items) | history_syntax::verify::dsl::TestView::Or(items) =>
                            assert(items =~= test_views::<E>(children@)),
                        _ => {},
                    } }
                    proof! {
                        assert(test@ == history_syntax::verify::dsl::TestView::And(test_views::<E>(children@))
                            || test@ == history_syntax::verify::dsl::TestView::Or(test_views::<E>(children@)));
                        lemma_finish_test::<E>(work@, test, tests.len(), test_sources, regex_sources, test_views::<E>(children@), rule.head@);
                        if crate::verify::dsl::regex_scoped(rule.tail@, rule.head@) {
                            assert forall|i: int| 0 <= i < children@.len() implies
                                crate::verify::dsl::test_scoped(children@[i]@, rule.head@) by {
                                assert(test_views::<E>(children@)[i] == children@[i]@);
                            }
                        }
                        assert(test_cost::<E>(test@) == 2 + test_forest_cost::<E>(test_views::<E>(children@)));
                    }
                    proof_decl! { let ghost prefix = work@; }
                    proof! { lemma_work_cost_push::<E>(prefix, Work::FinishTest(test, tests.len())); }
                    proof! { assert(work_cost::<E>(old_work) == work_cost::<E>(prefix) + test_cost::<E>(test@)); }
                    push(
                        &mut work,
                        Work::FinishTest(test, tests.len()),
                        limits,
                        world,
                    )?;
                    proof_decl! { let ghost finish = work@; }
                    proof! {
                        assert(finish.drop_last() =~= prefix);
                        assert(finish.last() is FinishTest);
                        assert(work_cost::<E>(finish) == work_cost::<E>(prefix) + 1);
                    }
                    schedule_tests(&mut work, children, limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) == work_cost::<E>(finish)
                            + test_forest_cost::<E>(test_views::<E>(children@)));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
            },
            Work::FinishTest(test, start) => {
                proof! {
                    assert(test@ is And || test@ is Or);
                    assert(start <= test_sources.len());
                    assert(start <= tests@.len());
                }
                let children = take_children(&mut tests, start, limits, world)?;
                proof_decl! { let ghost child_ids = children@; }
                let node = match test {
                    TestExpr::And(_) => FlatTest::And(children),
                    TestExpr::Or(_) => FlatTest::Or(children),
                    _ => return Err(HistoryError::invariant("invalid source test finish").into()),
                };
                proof! {
                    assert forall|i: int| 0 <= i < child_ids.len() implies
                        child_ids[i] < builder.tests_view().len() by {
                        assert(child_ids[i] == old_test_ids[start as int + i]);
                        assert(test_represents::<E>(builder.tests_view(), child_ids[i] as nat,
                            old_test_sources[start as int + i], rule.head@));
                    }
                    assert(crate::flat::verify::references_before(child_ids, builder.tests_view().len()));
                    assert(crate::flat::verify::test_wf(builder.head_view(), node, builder.tests_view().len()));
                }
                let id = builder.test(node, limits, world)?;
                proof! {
                    lemma_test_operands(builder.tests_view()[id as int]);
                    assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                    assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                    lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                        old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                    let sources = match test@ {
                        history_syntax::verify::dsl::TestView::And(items) | history_syntax::verify::dsl::TestView::Or(items) => items,
                        _ => arbitrary(),
                    };
                    assert(old_test_sources.subrange(start as int, old_test_sources.len() as int) == sources);
                    assert forall|i: int| 0 <= i < sources.len() implies
                        test_represents::<E>(builder.tests_view(), child_ids[i] as nat, sources[i], rule.head@) by {
                        assert(child_ids[i] == old_test_ids[start as int + i]);
                        assert(sources[i] == old_test_sources[start as int + i]);
                    }
                    assert forall|i: int| 0 <= i < sources.len() implies
                        crate::verify::dsl::test_scoped(sources[i], rule.head@) by {
                        assert(test_represents::<E>(builder.tests_view(), child_ids[i] as nat, sources[i], rule.head@));
                    }
                    reveal_with_fuel(crate::verify::dsl::test_scoped, 2);
                    assert(crate::verify::dsl::test_scoped(test@, rule.head@));
                    assert(child_ids.len() == sources.len());
                    assert(crate::flat::verify::references_before(child_ids, id as nat));
                    assert(test_represents::<E>(builder.tests_view(), id as nat, test@, rule.head@));
                }
                push(&mut tests, id, limits, world)?;
                proof! { test_sources = test_sources.subrange(0, start as int).push(test@); }
            }
            Work::FinishRegex(regex, start) => {
                proof! {
                    assert(match regex@ {
                        history_syntax::verify::dsl::RegexView::Test(_) => test_sources.len() == start + 1,
                        history_syntax::verify::dsl::RegexView::Star(_) | history_syntax::verify::dsl::RegexView::Not(_)
                            => regex_sources.len() == start + 1,
                        history_syntax::verify::dsl::RegexView::Concat(_) | history_syntax::verify::dsl::RegexView::Union(_)
                            | history_syntax::verify::dsl::RegexView::Intersect(_) => start <= regex_sources.len(),
                        _ => false,
                    });
                }
                let node = match regex {
                    RegexExpr::Test(_) => {
                        proof! { assert(tests@.len() == start + 1); }
                        let child = match tests.pop() {
                            Some(child) => child,
                            None => {
                                return Err(
                                    HistoryError::invariant("missing source test operand").into()
                                );
                            }
                        };
                        proof! { test_sources = test_sources.drop_last(); }
                        FlatRegex::Test(child)
                    }
                    RegexExpr::Star(_) | RegexExpr::Not(_) => {
                        proof! { assert(regexes@.len() == start + 1); }
                        let child = match regexes.pop() {
                            Some(child) => child,
                            None => {
                                return Err(HistoryError::invariant(
                                    "missing source regex operand",
                                )
                                .into());
                            }
                        };
                        proof! { regex_sources = regex_sources.drop_last(); }
                        match regex {
                            RegexExpr::Star(_) => FlatRegex::Star(child),
                            _ => FlatRegex::Complement(child),
                        }
                    }
                    RegexExpr::Concat(_) | RegexExpr::Union(_) | RegexExpr::Intersect(_) => {
                        proof! { assert(start <= regexes@.len()); }
                        let children = take_children(&mut regexes, start, limits, world)?;
                        proof! { regex_sources = regex_sources.subrange(0, start as int); }
                        match regex {
                            RegexExpr::Concat(_) => FlatRegex::Concat(children),
                            RegexExpr::Union(_) => FlatRegex::Union(children),
                            _ => FlatRegex::Intersect(children),
                        }
                    }
                    _ => return Err(HistoryError::invariant("invalid source regex finish").into()),
                };
                proof_decl! { let ghost finished = node; }
                proof! {
                    lemma_regex_operands(node);
                    match node {
                        FlatRegex::Test(child) => {
                            assert(child == old_test_ids.last());
                            assert(test_represents::<E>(builder.tests_view(), child as nat,
                                old_test_sources.last(), rule.head@));
                        },
                        FlatRegex::Star(child) | FlatRegex::Complement(child) => {
                            assert(child == old_regex_ids.last());
                            assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), child as nat,
                                old_regex_sources.last(), rule.head@));
                        },
                        FlatRegex::Concat(ref ids) | FlatRegex::Union(ref ids) | FlatRegex::Intersect(ref ids) => {
                            assert forall|i: int| 0 <= i < ids@.len() implies
                                ids@[i] < builder.regexes_view().len() by {
                                assert(ids@[i] == old_regex_ids[start as int + i]);
                                assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids@[i] as nat,
                                    old_regex_sources[start as int + i], rule.head@));
                            }
                        },
                        _ => {},
                    }
                    assert(crate::flat::verify::regex_wf(node, builder.regexes_view().len(), builder.tests_view().len()));
                }
                let id = builder.regex(node, limits, world)?;
                proof! {
                    lemma_regex_operands(builder.regexes_view()[id as int]);
                    assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                    assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                    lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                        old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                    match regex@ {
                        history_syntax::verify::dsl::RegexView::Test(source) => {
                            let child = match finished { FlatRegex::Test(id) => id, _ => arbitrary() };
                            assert(test_represents::<E>(builder.tests_view(), child as nat, source, rule.head@));
                        },
                        history_syntax::verify::dsl::RegexView::Star(source) | history_syntax::verify::dsl::RegexView::Not(source) => {
                            let child = match finished { FlatRegex::Star(id) | FlatRegex::Complement(id) => id, _ => arbitrary() };
                            assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), child as nat, *source, rule.head@));
                        },
                        history_syntax::verify::dsl::RegexView::Concat(sources) | history_syntax::verify::dsl::RegexView::Union(sources)
                            | history_syntax::verify::dsl::RegexView::Intersect(sources) => {
                            let ids = match finished {
                                FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@,
                                _ => arbitrary(),
                            };
                            assert(old_regex_sources.subrange(start as int, old_regex_sources.len() as int) == sources);
                            assert forall|i: int| 0 <= i < sources.len() implies
                                regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids[i] as nat, sources[i], rule.head@) by {
                                assert(ids[i] == old_regex_ids[start as int + i]);
                                assert(sources[i] == old_regex_sources[start as int + i]);
                            }
                            assert forall|i: int| 0 <= i < sources.len() implies
                                crate::verify::dsl::regex_scoped(sources[i], rule.head@) by {
                                assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids[i] as nat, sources[i], rule.head@));
                            }
                        },
                        _ => {},
                    }
                    reveal_with_fuel(crate::verify::dsl::regex_scoped, 2);
                    assert(crate::verify::dsl::regex_scoped(regex@, rule.head@));
                    assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), id as nat, regex@, rule.head@));
                }
                push(&mut regexes, id, limits, world)?;
                proof! { regex_sources = regex_sources.push(regex@); }
            }
        }
        proof! {
            reveal(result_stacks);
            reveal_with_fuel(work_cost, 2);
            assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
            assert forall|i: int| 0 <= i < builder.tests_view().len() implies
                crate::verify::encoding::test_in_domain(builder.tests_view()[i], component_domain::<E>()) by {
                if i < old_tests.len() { assert(builder.tests_view()[i] == old_tests[i]); }
            }
        }
    }
    proof! {
        reveal(result_stacks);
        reveal_with_fuel(run_work, 1);
        assert(test_sources =~= Seq::empty());
        assert(regex_sources =~= seq![rule.tail@]);
        assert(tests@.len() == 0);
        assert(regexes@.len() == 1);
    }
    if regexes.len() != 1 || !tests.is_empty() {
        return Err(HistoryError::invariant("invalid source result stack").into());
    }
    proof_decl! { let ghost result_ids = regexes@; }
    let root = match regexes.pop() {
        Some(root) => root,
        None => return Err(HistoryError::invariant("missing source root").into()),
    };
    proof! {
        assert(result_ids =~= seq![root]);
        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), result_ids[0] as nat, regex_sources[0], rule.head@));
        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), root as nat, rule.tail@, rule.head@));
    }
    limits.checkpoint().map_err(HistoryError::from)?;
    let source: FlatPair<ComponentValue<E>> = builder.finish(root)?;
    proof! {
        assert(head_represents::<E>(source.head@, rule.head@));
        assert(regex_represents::<E>(source.tests@, source.regexes@, source.root as nat, rule.tail@, rule.head@));
        assert(crate::verify::encoding::constants_in_domain(source, component_domain::<E>()));
    }
    Ok(FlatRule {
        mode: rule.mode,
        source,
    })
}
