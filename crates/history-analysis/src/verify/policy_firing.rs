//! Exact head firing for the concrete split's structurally decided cases.
use super::*;
use history_semantics::verify::refinement::{encoding, implementation, inclusion};
use junco_core::verify::history_specs::Subst;
use vstd::prelude::*;

verus! {

/// The right side is an equality-only head, and every equality is structurally decided.
pub(crate) open spec fn head_firing_ready(case: implementation::ConstraintView,
    head: implementation::ConstraintView) -> bool {
    case.len() == head.len()
    && forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
        implementation::RegisterView::Equals(v) => case[i] is Equals || !register_sat(case[i], v),
        implementation::RegisterView::Differs(vs) => vs == Set::<nat>::empty(),
    }
}

/// A satisfiable structurally decided case entails a head exactly when the executable
/// register-by-register test does. This holds for arbitrary domains, including singletons.
pub(crate) proof fn lemma_head_firing_exact(d: encoding::NDomains,
    case: implementation::ConstraintView, head: implementation::ConstraintView)
    requires head_firing_ready(case, head), case.len() == d.len(),
        inclusion::satisfiable(d, implementation::constraint_of(case)),
    ensures inclusion::entails(d, implementation::constraint_of(case), implementation::constraint_of(head))
        == (forall|i: int| 0 <= i < case.len() ==> register_entails(case[i], head[i])),
{
    if forall|i: int| 0 <= i < case.len() ==> register_entails(case[i], head[i]) {
        lemma_constraint_entails(case, head);
    }
    if inclusion::entails(d, implementation::constraint_of(case), implementation::constraint_of(head)) {
        let theta = choose|theta: Subst| encoding::n_theta_ok(d, theta)
            && inclusion::sat_by(theta, implementation::constraint_of(case));
        lemma_constraint_sat(case, theta);
        lemma_constraint_sat(head, theta);
        assert forall|i: int| 0 <= i < case.len() implies
            register_entails(#[trigger] case[i], head[i]) by {
            match head[i] {
                implementation::RegisterView::Equals(v) => {
                    match case[i] {
                        implementation::RegisterView::Equals(_) => {},
                        implementation::RegisterView::Differs(_) => { assert(!register_sat(case[i], v)); },
                    }
                },
                implementation::RegisterView::Differs(_) => {},
            }
        }
    }
}

/// The executable split supplies the stronger structural decision required above.
pub(crate) proof fn lemma_split_head_firing_ready(g: Constraint, operands: Operands,
    universes: Universes, case: implementation::ConstraintView, head: implementation::ConstraintView)
    requires shape_wf(g, operands, universes), split_views(g, operands, universes).contains(case),
        head.len() == g@.len(),
        forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
            implementation::RegisterView::Equals(v) => operands.register[i]
                && codes(operands.constants[i].view()).contains(v),
            implementation::RegisterView::Differs(vs) => vs == Set::<nat>::empty(),
        },
    ensures head_firing_ready(case, head),
{
    lemma_refined_ready(g, operands, universes, case);
    assert forall|i: int| 0 <= i < head.len() implies match #[trigger] head[i] {
        implementation::RegisterView::Equals(v) => case[i] is Equals || !register_sat(case[i], v),
        implementation::RegisterView::Differs(vs) => vs == Set::<nat>::empty(),
    } by {
    }
}
/// A satisfiable case cannot entail an unsatisfiable head.
pub(crate) proof fn lemma_unsatisfiable_head_does_not_fire(
    d: encoding::NDomains, case: inclusion::Constraint, head: inclusion::Constraint)
    requires inclusion::satisfiable(d, case), !inclusion::satisfiable(d, head),
    ensures !inclusion::entails(d, case, head),
{
    let theta = choose|theta: Subst| encoding::n_theta_ok(d, theta)
        && inclusion::sat_by(theta, case);
    if inclusion::entails(d, case, head) {
        assert(inclusion::sat_by(theta, head));
        assert(inclusion::satisfiable(d, head));
    }
}

/// Restrict the concrete split's larger comparison set to a policy's head pairs.
pub(crate) proof fn lemma_policy_split(g: Constraint, operands: Operands, universes: Universes,
    atoms: Seq<Atom>, cases: Seq<Constraint>, policy: Seq<encoding::NRule>)
    requires shape_wf(g, operands, universes), operands_of(operands, atoms),
        split_contract(g, operands, universes, cases),
        inclusion::satisfiable(ndomains(universes), implementation::constraint_of(g@)),
        forall|p: (history_syntax::syntax::Component, nat)| #[trigger] inclusion::head_pairs(policy).contains(p)
            ==> p.0.0 < g@.len() && operands.register[p.0.0 as int]
                && codes(operands.constants[p.0.0 as int].view()).contains(p.1),
    ensures inclusion::split_ok(ndomains(universes), implementation::constraint_of(g@),
        inclusion::head_pairs(policy),
        constraint_views(cases).map(|v: implementation::ConstraintView| implementation::constraint_of(v))),
{
    lemma_operand_pairs(operands, atoms, universes);
    let all = search::domain_pairs(ndomains(universes), atom_set(atoms));
    let wanted = inclusion::head_pairs(policy);
    assert forall|p: (history_syntax::syntax::Component, nat)| wanted.contains(p)
        implies all.contains(p) by {}
}

/// Every code in a concrete split case comes from its input, compared constants,
/// or the corresponding declared finite universe.
pub(crate) proof fn lemma_split_case_codes(g: Constraint, operands: Operands, universes: Universes,
    case: implementation::ConstraintView)
    requires shape_wf(g, operands, universes), split_views(g, operands, universes).contains(case),
    ensures case.len() == g@.len(),
        forall|i: int, v: nat| 0 <= i < case.len()
            && #[trigger] register_codes(case[i]).contains(v)
            ==> register_codes(g@[i]).contains(v) || codes(operands.constants[i].view()).contains(v)
                || match domain_view(universes[i]) { Some(values) => values.contains(v), None => false },
{
    lemma_register_product_members(split_axes(g, operands, universes));
    assert forall|i: int, v: nat| 0 <= i < case.len()
        && #[trigger] register_codes(case[i]).contains(v)
        implies register_codes(g@[i]).contains(v) || codes(operands.constants[i].view()).contains(v)
            || match domain_view(universes[i]) { Some(values) => values.contains(v), None => false } by {
        lemma_register_options_members(g.0[i]@, operands.register[i],
            codes(operands.constants[i].view()), domain_view(universes[i]), case[i]);
        match g@[i] {
            implementation::RegisterView::Equals(_) => {},
            implementation::RegisterView::Differs(_) => {
                match domain_view(universes[i]) {
                    Some(_) => {},
                    None => { match case[i] {
                        implementation::RegisterView::Equals(_) => {},
                        implementation::RegisterView::Differs(_) => {},
                    } },
                }
            },
        }
    }
}


} // verus!
