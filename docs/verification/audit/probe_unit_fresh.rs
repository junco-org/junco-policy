// AnalyzerClaims audit probe (private worktree only): the eval's event shape, Component3<(), u8, ()>
// with coordinate 1 declared, on a trivially failing inclusion `[a] ⊑ ∅`.
use history_analysis::{Domains, Inclusion, PolicyAnalyzer, Value};
use history_syntax::{
    AtomPattern, Comparison, Component, Component3, ComponentPattern, Event, Head, N3, RegexExpr,
    TestExpr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Char(pub u8);

impl Event for Char {
    type Component = Component3<(), u8, ()>;
    type Arity = N3;
    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component3::C0(()),
            1 => Component3::C1(self.0),
            _ => Component3::C2(()),
        }
    }
    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component3::C0(_) => 0,
            Component3::C1(_) => 1,
            Component3::C2(_) => 2,
        }
    }
}

#[test]
fn eval_shape_counterexample_uses_fresh_at_unit_coordinates() {
    let alphabet = [b'a', b'b'];
    let head = Head::<Char>::new([
        ComponentPattern::constant(Component3::C0(())),
        ComponentPattern::constant(Component3::C1(alphabet[0])),
        ComponentPattern::constant(Component3::C2(())),
    ]);
    let a = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::new(Component(1), ComponentPattern::constant(Component3::C1(b'a'))),
    ));
    let left = RegexExpr::concat([a.clone(), RegexExpr::star(a)]);
    let right = RegexExpr::epsilon();
    let mut analyzer = PolicyAnalyzer::new(
        Domains::<Char>::infinite().with_domain(Component(1), &alphabet.map(Component3::C1)).unwrap(),
    );
    let verdict = analyzer.tail_included(&head, &left, &right).unwrap();
    println!("{verdict:?}");
    match verdict {
        Inclusion::Counterexample(cex) => {
            let fresh_at_unit = cex.history.iter().any(|e| {
                matches!(e.values[0], Value::Fresh(_)) || matches!(e.values[2], Value::Fresh(_))
            });
            println!("fresh at a unit-typed coordinate: {fresh_at_unit}");
        }
        other => panic!("expected a counterexample, got {other:?}"),
    }
}
