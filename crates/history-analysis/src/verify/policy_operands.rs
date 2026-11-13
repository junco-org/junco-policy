//! Policy-head operand and split-case provenance for the executable query loop.
use super::*;
use super::{frontend::*, policy_firing, policy_queries as queries, reconstruction, verdict};
use crate::analyzer::{PolicyAnalyzer, RuleId};
use history_semantics::verify::refinement::{encoding, implementation, inclusion};
use history_syntax::spec::events::arity;
use history_syntax::{Event, syntax::Component};
use vstd::prelude::*;

verus! {
broadcast use {crate::verify::frontend::domain_view::lemma_analyzer_view,
    crate::verify::frontend::domain_view::lemma_rule_id_view};

/// Collected head atoms provide each policy comparison and contain only known codes.
pub(crate) proof fn lemma_policy_operands<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>,
    exclude: Option<RuleId>, atoms: Seq<Atom>, operands: Operands)
    requires analyzer_state_wf(a), valid_ids(a, ids), verdict::head_atoms_ok(a, ids, exclude, atoms),
        operands_of(operands, atoms), operands.register@.len() == arity::<E>(),
    ensures operands.register@.len() == arity::<E>(), operands.constants@.len() == arity::<E>(),
        forall|p: (Component, nat)| #[trigger] inclusion::head_pairs(queries::numeric_policy(a, ids, exclude)).contains(p)
            ==> p.0.0 < arity::<E>() && operands.register[p.0.0 as int]
                && codes(operands.constants[p.0.0 as int].view()).contains(p.1),
        forall|i: int, v: nat| 0 <= i < arity::<E>()
            && #[trigger] codes(operands.constants[i].view()).contains(v)
            ==> reconstruction::code_field(a.constants, Component(i as u8), v),
{
    let selected = queries::selected_ids(ids, exclude);
    let policy = queries::numeric_policy(a, ids, exclude);
    inclusion::lemma_head_pairs(policy);
    assert forall|i: int, v: nat| 0 <= i < arity::<E>()
        && #[trigger] codes(operands.constants[i].view()).contains(v)
        implies reconstruction::code_field(a.constants, Component(i as u8), v) by {
        lemma_codes(operands.constants[i].view());
        let x = choose|x: u32| operands.constants[i].view().contains(x) && x as nat == v;
        let j = choose|j: int| 0 <= j < atoms.len() && atoms[j].component == i
            && atoms[j].operand == Operand::Constant(x);
    }
    assert forall|p: (Component, nat)| #[trigger] inclusion::head_pairs(policy).contains(p)
        implies p.0.0 < arity::<E>() && operands.register[p.0.0 as int]
            && codes(operands.constants[p.0.0 as int].view()).contains(p.1) by {
        let j = choose|j: int| 0 <= j < policy.len()
            && encoding::n_head_field(policy[j].head, p.0) == Some(p.1);
        let id = selected[j];
        if let Some(excluded) = exclude {
            ids.lemma_filter_contains_rev(|id: RuleId| id.0 != excluded.0, id);
        }
        let pos = choose|pos: int| 0 <= pos < ids.len() && ids[pos] == id;
        let r = a.rules@[id.0 as int];
        let k = p.0.0 as int;
        assert(stored_rule_wf(a.constants, a.universes, r));
        assert(policy[j] == queries::stored_numeric(r));
        assert(policy[j].head == pins(r.numeric.head@));
        assert(head_view(r.constants@) == policy[j].head);
        let x = r.constants@[k]->Some_0;
        assert(atoms.contains(Atom { component: k as usize, operand: Operand::Constant(x) }));
        assert(atoms.contains(Atom { component: k as usize, operand: Operand::Register }));
        assert(operands.constants[k].view().contains(x));
        lemma_codes(operands.constants[k].view());
    }
}

/// Every split operand is an interned representative of a registered source-head literal.
pub(crate) proof fn lemma_policy_operands_known<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>,
    exclude: Option<RuleId>, atoms: Seq<Atom>, operands: Operands)
    requires analyzer_state_wf(a), junco_core::spec::hypotheses::analyzer_hypotheses::<E>(),
        valid_ids(a, ids), verdict::head_atoms_ok(a, ids, exclude, atoms),
        operands_of(operands, atoms), operands.register@.len() == arity::<E>(),
    ensures forall|k: int, code: nat| 0 <= k < arity::<E>()
        && codes(operands.constants[k].view()).contains(code)
        ==> super::typed_numeric::known_value::<E>(
            junco_core::spec::questions::knowable_constants::<E>(a@.domains, a@.rules),
            k, a.constants.values@[code as int - 1]),
{
    let known = junco_core::spec::questions::knowable_constants::<E>(a@.domains, a@.rules);
    assert forall|k: int, code: nat| 0 <= k < arity::<E>()
        && codes(operands.constants[k].view()).contains(code)
        implies super::typed_numeric::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
        lemma_codes(operands.constants[k].view());
        let value = choose|value: u32| operands.constants[k].view().contains(value) && value as nat == code;
        let j = choose|j: int| 0 <= j < atoms.len()
            && atoms[j].component == k && atoms[j].operand == Operand::Constant(value);
        let r = choose|r: int| 0 <= r < a.rules@.len() && a.rules@[r].constants@[k] == Some(value);
        let record = a.rules@[r];
        assert(stored_rule_wf(a.constants, a.universes, record));
        junco_core::spec::questions::lemma_knowable_rule::<E>(a@.domains, a@.rules, r);
        verdict::lemma_lowered_head_known(a.constants, record.original@, record.flat@, record.numeric, known);
        assert(head_view(record.constants@)[k] == pins(record.numeric.head@)[k]);
        assert(record.numeric.head@[k] == junco_core::flat::FlatHead::Constant(value as u64));
    }
}

/// Every code introduced by split is from the existing case, operands, or a declared universe.
pub(crate) proof fn lemma_known_split_case_codes<E: Event>(a: PolicyAnalyzer<E>, g: Constraint,
    operands: Operands, case: implementation::ConstraintView)
    requires analyzer_state_wf(a), shape_wf(g, operands, a.universes),
        verdict::constraint_codes_wf(a.constants, g@),
        split_views(g, operands, a.universes).contains(case),
        forall|i: int, v: nat| 0 <= i < arity::<E>()
            && #[trigger] codes(operands.constants[i].view()).contains(v)
            ==> reconstruction::code_field(a.constants, Component(i as u8), v),
    ensures verdict::constraint_codes_wf(a.constants, case),
{
    policy_firing::lemma_split_case_codes(g, operands, a.universes, case);
    assert forall|field: Component, v: nat| field.0 < case.len()
        && #[trigger] register_codes(implementation::register_of(case, field)).contains(v)
        implies reconstruction::code_field(a.constants, field, v) by {
        let i = field.0 as int;
        assert(implementation::register_of(case, field) == case[i]);
        assert(implementation::register_of(g@, field) == g@[i]);
        assert(field == Component(i as u8));
        assert(register_codes(g@[i]).contains(v)
            || codes(operands.constants[i].view()).contains(v)
            || match domain_view(a.universes[i]) { Some(values) => values.contains(v), None => false });
        if register_codes(g@[i]).contains(v) {
            assert(verdict::constraint_codes_wf(a.constants, g@));
        } else if codes(operands.constants[i].view()).contains(v) {
        } else {
            let ids = a.universes[i]->Some_0;
            lemma_codes((*ids)@);
            let j = choose|j: int| 0 <= j < (*ids)@.len() && (*ids)@[j] as nat == v;
            assert(value_field::<E>(a.constants.values@[v as int - 1]) == field);
        }
    }
}

/// The split preserves the query-local source/domain context, not the full native codebook.
pub(crate) proof fn lemma_split_case_known<E: Event>(a: PolicyAnalyzer<E>, g: Constraint,
    operands: Operands, case: implementation::ConstraintView, known: Seq<Set<E::Component>>)
    requires analyzer_state_wf(a), shape_wf(g, operands, a.universes),
        verdict::constraint_codes_known(a.constants, g@, known),
        split_views(g, operands, a.universes).contains(case),
        forall|k: int, code: nat| 0 <= k < arity::<E>()
            && (codes(operands.constants[k].view()).contains(code)
                || (domain_view(a.universes[k]) matches Some(values) && values.contains(code)))
            ==> super::typed_numeric::known_value::<E>(known, k, a.constants.values@[code as int - 1]),
    ensures verdict::constraint_codes_known(a.constants, case, known),
{
    policy_firing::lemma_split_case_codes(g, operands, a.universes, case);
    assert forall|k: int, code: nat| 0 <= k < case.len() && register_codes(case[k]).contains(code)
        implies super::typed_numeric::known_value::<E>(known, k, a.constants.values@[code as int - 1]) by {
        let field = Component(k as u8);
        assert(implementation::register_of(case, field) == case[k]);
        assert(implementation::register_of(g@, field) == g@[k]);
        assert(register_codes(g@[k]).contains(code)
            || codes(operands.constants[k].view()).contains(code)
            || (domain_view(a.universes[k]) matches Some(values) && values.contains(code)));
    }
}

/// A selected stored head is structurally decided by the policy split.
pub(crate) proof fn lemma_selected_head_ready<E: Event>(a: PolicyAnalyzer<E>, ids: Seq<RuleId>,
    exclude: Option<RuleId>, index: int, start: Constraint, operands: Operands,
    case: implementation::ConstraintView)
    requires analyzer_state_wf(a), valid_ids(a, ids), 0 <= index < ids.len(),
        !verdict::excluded_id(ids[index], exclude),
        shape_wf(start, operands, a.universes), split_views(start, operands, a.universes).contains(case),
        forall|p: (Component, nat)| #[trigger] inclusion::head_pairs(queries::numeric_policy(a, ids, exclude)).contains(p)
            ==> p.0.0 < arity::<E>() && operands.register[p.0.0 as int]
                && codes(operands.constants[p.0.0 as int].view()).contains(p.1),
    ensures match a.rules@[ids[index].0 as int].constraint {
        Some(head) => policy_firing::head_firing_ready(case, head@), None => true,
    },
{
    let id = ids[index];
    let r = a.rules@[id.0 as int];
    let selected = queries::selected_ids(ids, exclude);
    let policy = queries::numeric_policy(a, ids, exclude);
    assert(stored_rule_wf(a.constants, a.universes, r));
    if let Some(excluded) = exclude {
        ids.lemma_filter_contains(|x: RuleId| x.0 != excluded.0, index);
    }
    assert(selected.contains(id));
    let j = choose|j: int| 0 <= j < selected.len() && selected[j] == id;
    assert(policy[j] == queries::stored_numeric(r));
    assert(policy[j].head == head_view(r.constants@));
    inclusion::lemma_head_pairs(policy);
    if let Some(head) = r.constraint {
        assert(head@.len() == arity::<E>());
        assert forall|k: int| 0 <= k < head@.len() implies match #[trigger] head@[k] {
            implementation::RegisterView::Equals(v) => operands.register[k]
                && codes(operands.constants[k].view()).contains(v),
            implementation::RegisterView::Differs(vs) => vs == Set::<nat>::empty(),
        } by {
            match r.constants@[k] {
                Some(x) => {
                    let field = Component(k as u8);
                    assert(encoding::n_head_field(policy[j].head, field) == Some(x as nat));
                    assert(inclusion::head_pairs(policy).contains((field, x as nat)));
                },
                None => {},
            }
        }
        policy_firing::lemma_split_head_firing_ready(start, operands, a.universes, case, head@);
    }
}

} // verus!
