//! Layer 1: typed rules and pairs as numeric ones.
//!
//! The typed-to-numeric bridge is the existing verified front end, which the analyzer already
//! calls (`add_rule`, `analyzer.rs:301-312`): `flatten_rule` (`junco_core::verify::flatten`,
//! `flattened`, `flattening_preserves_semantics`), `lower_flat` with the analyzer's encoder
//! (`junco_core::verify::encoding`, `lowering`, `lemma_dsl_later_maps_preservation`), and the
//! graph compiler (`crate::compile`, `lemma_flat_regex`, the `compile` contract). This layer only
//! adds what those do not state: the numeric rule with its mode, the whole-candidate valuation
//! the analyzer uses (the runtime uses head bindings, with 0 at unbound components), and
//! renaming invariance for fresh values.
use super::semantics::*;
use history_syntax::Event;
use history_syntax::syntax::{Component, Rule, RuleMode};
use history_syntax::verify::dsl::RuleView;
use junco_core::ComponentValue;
use junco_core::flat::{FlatHead, FlatPair, FlatRule};
use junco_core::kernel::verify as model;
use junco_core::verify::dsl::EventView as TEvent;
use junco_core::verify::encoding as enc;
use junco_core::verify::flatten as fl;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use crate::compile::verify as numeric;
use vstd::prelude::*;

verus! {

/// Kernel test semantics under the whole-candidate valuation `θ`.
pub open spec fn n_lang(theta: Subst, r: Regex<model::Test>, w: Seq<EventView>) -> bool {
    language::lang(model::gsem(theta), r, w)
}

/// A numeric head: a code per constant component, `None` for a variable.
pub struct NHead { pub principal: Option<nat>, pub action: Option<nat>, pub resource: Option<nat> }

/// A numeric rule. Tail atoms compare component `i` with a code or with `Variable(i)`, which reads
/// the candidate's component `i`.
pub struct NRule { pub mode: RuleMode, pub head: NHead, pub tail: Regex<model::Test> }

pub open spec fn n_head_field(h: NHead, c: Component) -> Option<nat> {
    match c { Component::Principal => h.principal, Component::Action => h.action, Component::Resource => h.resource }
}

pub open spec fn n_head_matches(h: NHead, theta: Subst) -> bool {
    forall|c: Component| #[trigger] n_head_field(h, c) matches Some(v) ==> language::field_value(theta, c) == v
}

pub open spec fn n_rule_denies(rule: NRule, theta: Subst, w: Seq<EventView>) -> bool {
    n_head_matches(rule.head, theta) && violated_by(rule.mode, n_lang(theta, rule.tail, w))
}

pub open spec fn n_policy_denies(p: Seq<NRule>, theta: Subst, w: Seq<EventView>) -> bool {
    exists|i: int| 0 <= i < p.len() && #[trigger] n_rule_denies(p[i], theta, w)
}

/// Numeric domains: all of `nat` (`None`) or a finite set of codes (a declared finite domain).
pub struct NDomains { pub principal: Option<Set<nat>>, pub action: Option<Set<nat>>, pub resource: Option<Set<nat>> }

pub open spec fn n_domain(d: NDomains, c: Component) -> Option<Set<nat>> {
    match c { Component::Principal => d.principal, Component::Action => d.action, Component::Resource => d.resource }
}

pub open spec fn n_event_in(d: NDomains, e: EventView) -> bool {
    forall|c: Component| #[trigger] n_domain(d, c) matches Some(values) ==> values.contains(language::field_value(e, c))
}

pub open spec fn n_history_in(d: NDomains, w: Seq<EventView>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] n_event_in(d, w[i])
}

/// Valuations range over the domain and, as the kernel contracts require, over `u64` values.
pub open spec fn n_theta_ok(d: NDomains, theta: Subst) -> bool {
    language::event_wf(theta) && n_event_in(d, theta)
}

// ----- the verified front end -----

/// The view of an executable rule.
pub open spec fn rule_view<E: Event>(rule: Rule<E>) -> RuleView<E::Principal, E::Action, E::Resource> {
    RuleView { mode: rule.mode, head: rule.head@, tail: rule.tail@ }
}

/// What the analyzer's front end establishes for an added rule: the verified `flatten_rule`
/// (`flattening_client` gives `flattened`, hence `head_scoped` and `regex_scoped`) and
/// `lower_flat` (`lowering` and `constants_in_domain` for the encoder's books).
pub open spec fn front_end_ok<E: Event>(
    rule: Rule<E>, flat: FlatRule<ComponentValue<E>>, template: FlatPair<u64>,
    maps: enc::Codebook<ComponentValue<E>>, domain: enc::Domain<ComponentValue<E>>,
) -> bool {
    &&& fl::flattened::<E>(rule, flat)
    &&& enc::lowering(flat.source, template, maps, fl::component_equality::<E>())
    &&& enc::constants_in_domain(flat.source, domain)
}

pub open spec fn head_code(h: FlatHead<u64>) -> Option<nat> {
    match h { FlatHead::Constant(v) => Some(v as nat), _ => None }
}

/// The numeric rule `n` searched by the analyzer stands for the lowered template: same mode and
/// head constants, and a tail with the template's language (`numeric::source_regex`) under every
/// valuation. The `compile` contract gives the tail clause for the compiled graph root.
pub open spec fn represents(n: NRule, mode: RuleMode, template: FlatPair<u64>) -> bool {
    &&& n.mode == mode
    &&& template.head@.len() == 3
    &&& n.head.principal == head_code(template.head@[0])
    &&& n.head.action == head_code(template.head@[1])
    &&& n.head.resource == head_code(template.head@[2])
    &&& forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta)
        ==> #[trigger] n_lang(theta, n.tail, w) == numeric::source_regex(template, template.root as nat, theta, w)
}

/// Valuations that agree on the components the template's head binds.
pub open spec fn agrees_on_binds(template: FlatPair<u64>, a: Subst, b: Subst) -> bool {
    forall|c: Component| #[trigger] language::head_field(numeric::head_view(template), c) is Bind
        ==> language::field_value(a, c) == language::field_value(b, c)
}

/// New: `source_regex` reads the valuation only at bound components, because tail variables
/// refer only to bound components (`structural_wf`). This moves the existing results, stated for
/// the runtime's head bindings, to the analyzer's whole-candidate valuation.
pub open spec fn stmt_source_regex_local() -> bool {
    forall|template: FlatPair<u64>, a: Subst, b: Subst, w: Seq<EventView>|
        junco_core::flat::verify::structural_wf(template) && agrees_on_binds(template, a, b)
            ==> (#[trigger] numeric::source_regex(template, template.root as nat, a, w)
                == #[trigger] numeric::source_regex(template, template.root as nat, b, w))
}

/// Typed denial is numeric denial for a rule passed through the front end. Proof plan, from
/// existing results: `enc::lemma_dsl_later_maps_preservation` (typed head and language equal the
/// numeric flat ones), `numeric::lemma_flat_head` and `numeric::lemma_flat_regex` (flat language
/// equals `source_regex` under the head bindings), `stmt_source_regex_local`, and `represents`.
/// Like the runtime's typed guarantees, it is conditional on the encoder's books (`maps_wf`, which
/// requires nonzero codes) and on the pair being encoded. Tails (`tail_included`) are the case
/// `mode = Forbid`.
pub open spec fn stmt_front_end_denies<E: Event>() -> bool {
    forall|rule: Rule<E>, flat: FlatRule<ComponentValue<E>>, template: FlatPair<u64>,
        maps: enc::Codebook<ComponentValue<E>>, later: enc::Codebook<ComponentValue<E>>,
        domain: enc::Domain<ComponentValue<E>>, n: NRule,
        candidate: TEvent<E::Principal, E::Action, E::Resource>,
        history: Seq<TEvent<E::Principal, E::Action, E::Resource>>,
        request: Seq<u64>, word: Seq<Seq<u64>>, theta: Subst, w: Seq<EventView>|
        #![trigger front_end_ok(rule, flat, template, maps, domain), represents(n, rule.mode, template),
            enc::extends(maps, later, fl::component_equality::<E>()),
            enc::event_encoded(later, fl::component_equality::<E>(), domain, fl::event_values::<E>(candidate), request),
            enc::word_encoded(later, fl::component_equality::<E>(), domain, fl::word_values::<E>(history), word),
            enc::event_representation(request, theta), enc::word_representation(word, w)]
        front_end_ok(rule, flat, template, maps, domain) && represents(n, rule.mode, template)
            && enc::extends(maps, later, fl::component_equality::<E>())
            && enc::maps_wf(later, fl::component_equality::<E>(), domain)
            && enc::event_encoded(later, fl::component_equality::<E>(), domain, fl::event_values::<E>(candidate), request)
            && enc::word_encoded(later, fl::component_equality::<E>(), domain, fl::word_values::<E>(history), word)
            && enc::event_representation(request, theta) && enc::word_representation(word, w)
            ==> (rule_denies(rule_view(rule), candidate, history) == n_rule_denies(n, theta, w))
}

// ----- fresh values -----

/// Numeric genericity: renaming the values of a pair injectively, fixing the codes of the
/// rules' constants, preserves denial. Together with `stmt_front_end_denies` this transfers a
/// numeric verdict to every typed pair and every typed instantiation of fresh values.
pub open spec fn n_renaming_ok(f: spec_fn(nat) -> nat, fixed: ISet<nat>, values: ISet<nat>) -> bool {
    &&& forall|x: nat, y: nat| values.contains(x) && values.contains(y) ==> (#[trigger] f(x) == #[trigger] f(y) <==> x == y)
    &&& forall|x: nat| #[trigger] fixed.contains(x) ==> f(x) == x
    &&& forall|x: nat, k: nat| #![trigger values.contains(x), fixed.contains(k)]
        values.contains(x) && fixed.contains(k) ==> (f(x) == k <==> x == k)
}

pub open spec fn n_rename_event(f: spec_fn(nat) -> nat, e: EventView) -> EventView {
    EventView { principal: f(e.principal), action: f(e.action), resource: f(e.resource) }
}

pub open spec fn n_rename_history(f: spec_fn(nat) -> nat, w: Seq<EventView>) -> Seq<EventView> {
    w.map(|i: int, e: EventView| n_rename_event(f, e))
}

/// The rule's head or tail compares component `c` with the code `v`.
pub open spec fn rule_mentions(rule: NRule, c: Component, v: nat) -> bool {
    n_head_field(rule.head, c) == Some(v) || regex_mentions(rule.tail, c, v)
}

/// The codes occurring in a rule (head constants and tail atoms).
pub open spec fn n_rule_codes(rule: NRule) -> ISet<nat> {
    ISet::new(|v: nat| exists|c: Component| #[trigger] rule_mentions(rule, c, v))
}

/// Some atom of `r` compares component `c` with the code `v`.
pub open spec fn regex_mentions(r: Regex<model::Test>, c: Component, v: nat) -> bool
    decreases r,
{
    match r {
        Regex::Test(t) => test_mentions(t, c, v),
        Regex::Union(cs) | Regex::Concat(cs) | Regex::Intersect(cs) =>
            exists|i: int| 0 <= i < cs.len() && #[trigger] regex_mentions(cs[i], c, v),
        Regex::Star(b) | Regex::Not(b) => regex_mentions(*b, c, v),
        _ => false,
    }
}

pub open spec fn test_mentions(t: model::Test, c: Component, v: nat) -> bool
    decreases t,
{
    match t {
        model::Test::Atom(model::Primitive::Eq(field, model::GTerm::Constant(k)), _) => field == c && k == v,
        model::Test::And(cs) | model::Test::Or(cs) => exists|i: int| 0 <= i < cs.len() && #[trigger] test_mentions(cs[i], c, v),
        _ => false,
    }
}

pub open spec fn stmt_numeric_genericity() -> bool {
    forall|rule: NRule, theta: Subst, w: Seq<EventView>, f: spec_fn(nat) -> nat|
        n_renaming_ok(f, n_rule_codes(rule), n_pair_values(theta, w))
            ==> (n_rule_denies(rule, theta, w) == #[trigger] n_rule_denies(rule, n_rename_event(f, theta), n_rename_history(f, w)))
}

/// Every component value of a numeric pair.
pub open spec fn n_pair_values(theta: Subst, w: Seq<EventView>) -> ISet<nat> {
    ISet::new(|x: nat| x == theta.principal || x == theta.action || x == theta.resource
        || exists|i: int| 0 <= i < w.len() && ((#[trigger] w[i]).principal == x || w[i].action == x || w[i].resource == x))
}

} // verus!
