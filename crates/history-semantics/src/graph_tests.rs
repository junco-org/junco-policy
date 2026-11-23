// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
#![allow(clippy::panic_in_result_fn)]
use crate::normalize::{RegexNormalize, TransitionNormalize};
use crate::progress::CompiledPair;
use crate::symbolic::{RegexDerivative, TransitionInterpret};
use alloc::vec::Vec;
use history_store::graph::{CanonicalStore, RuntimeKernel};
use junco_core::kernel::*;
use junco_core::observation::ObservationWorld;
#[test]
fn interned_nodes_keep_ids_bytes_and_derivative_semantics() -> KernelResult<()> {
    let mut world = ObservationWorld;
    let mut limits = junco_core::limits::Unmetered;
    let mut graph = CanonicalStore::new()?;
    let mut store = RuntimeKernel {
        store: &mut graph,
        limits: &mut limits,
        world: &mut world,
    };
    let node = TestView::Atom {
        primitive: Primitive::Eq {
            field: history_syntax::syntax::Component(0),
            term: Term::Constant(0),
        },
        positive: true,
    };
    let test = store.intern_test(node)?;
    let regex = store.intern_regex(RegexKindView::Test(test), false)?;
    let transition_node = TransitionView::If {
        test,
        then_transition: store.constants().transition_epsilon,
        else_transition: store.constants().transition_empty,
    };
    let transition = store.intern_transition(transition_node)?;
    let and = store.intern_test(TestView::And(&[test, store.constants().test_true]))?;
    let lists = store.store.table_counts().map(|counts| counts.0);
    let or = store.intern_test(TestView::Or(&[test, store.constants().test_true]))?;
    assert_ne!(and, or);
    assert_eq!(store.store.table_counts().map(|counts| counts.0), lists);
    assert_eq!(
        store.test(or)?,
        TestView::Or(&[test, store.constants().test_true])
    );
    let bytes = store.store.charged_bytes();
    let rows = store.store.table_counts().map(|counts| counts.1);
    assert_eq!(store.intern_test(node)?, test);
    assert_eq!(store.intern_regex(RegexKindView::Test(test), false)?, regex);
    assert_eq!(store.intern_transition(transition_node)?, transition);
    assert_eq!(
        store.intern_test(TestView::And(&[test, store.constants().test_true]),)?,
        and
    );
    assert_eq!(store.store.charged_bytes(), bytes);
    assert_eq!(store.store.table_counts().map(|counts| counts.1), rows);
    let mut kernel = store;
    let mut derivatives = Vec::new();
    assert_eq!(
        RegexId::derivative(regex, &mut kernel, &mut derivatives)?,
        transition
    );
    let atoms = CompiledPair::collect_atoms(&mut kernel, transition)?;
    let accepted = TransitionId::interpret(transition, &mut kernel, &atoms, &[1])?;
    assert!(RegexId::nullable(accepted, &kernel)?);
    Ok(())
}

#[test]
fn right_derivatives_preserve_chronological_concatenation() -> KernelResult<()> {
    fn atom(store: &mut impl KernelStore, code: u64) -> KernelResult<(TestId, RegexId)> {
        let test = store.intern_test(TestView::Atom {
            primitive: Primitive::Eq {
                field: history_syntax::syntax::Component(0),
                term: Term::Constant(code),
            },
            positive: true,
        })?;
        Ok((test, store.intern_regex(RegexKindView::Test(test), false)?))
    }

    fn step(
        store: &mut impl KernelStore,
        cache: &mut Vec<Option<TransitionId>>,
        residual: RegexId,
        event: TestId,
    ) -> KernelResult<RegexId> {
        let transition = RegexId::derivative(residual, store, cache)?;
        let atoms = CompiledPair::collect_atoms(store, transition)?;
        let word = atoms
            .ids()
            .iter()
            .position(|&id| id == event)
            .map_or(0, |i| 1 << i);
        let words = if atoms.ids().is_empty() {
            &[][..]
        } else {
            core::slice::from_ref(&word)
        };
        TransitionId::interpret(transition, store, &atoms, words)
    }

    fn accepts_steps(
        store: &mut impl KernelStore,
        cache: &mut Vec<Option<TransitionId>>,
        mut residual: RegexId,
        newest_first: &[TestId],
    ) -> KernelResult<bool> {
        for &event in newest_first {
            residual = step(store, cache, residual, event)?;
        }
        RegexId::nullable(residual, store)
    }

    let mut graph = CanonicalStore::new()?;
    let store = &mut RuntimeKernel {
        store: &mut graph,
        limits: &mut junco_core::limits::Unmetered,
        world: &mut ObservationWorld,
    };
    let cache = &mut Vec::new();
    let (a, ra) = atom(store, 1)?;
    let (b, rb) = atom(store, 2)?;
    let (c, rc) = atom(store, 3)?;
    let abc = RegexId::concat(store, &[ra, rb, rc])?;
    let after_c = step(store, cache, abc, c)?;
    assert!(accepts_steps(store, cache, after_c, &[b, a])?);
    assert!(!accepts_steps(store, cache, after_c, &[a, b])?);
    assert_eq!(step(store, cache, abc, a)?, store.constants().empty);
    assert!(accepts_steps(store, cache, abc, &[c, b, a])?);
    assert!(!accepts_steps(store, cache, abc, &[a, b, c])?);

    let bs = RegexId::star(rb, store)?;
    let abs = RegexId::concat(store, &[ra, bs])?;
    assert!(accepts_steps(store, cache, abs, &[a])?);
    assert!(accepts_steps(store, cache, abs, &[b, a])?);

    let ab = RegexId::concat(store, &[ra, rb])?;
    let star = RegexId::star(ab, store)?;
    let after_b = step(store, cache, star, b)?;
    assert!(accepts_steps(store, cache, after_b, &[a, b, a])?);
    assert!(!accepts_steps(store, cache, after_b, &[b, a, a])?);

    let inner = store.intern_transition(TransitionView::Prepend {
        transition: store.constants().transition_epsilon,
        prefix: &[rb],
    })?;
    let outer = TransitionId::prepend(inner, store, &[ra])?;
    let atoms = CompiledPair::collect_atoms(store, outer)?;
    let nested = TransitionId::interpret(outer, store, &atoms, &[])?;
    assert!(accepts_steps(store, cache, nested, &[b, a])?);
    assert!(!accepts_steps(store, cache, nested, &[a, b])?);
    Ok(())
}
