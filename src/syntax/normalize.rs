use super::node::{RegexId, RegexNode, TestId, TestNode};
use super::storage::SyntaxContext;

fn has_complementary_tests(tests: &[TestId<'_>]) -> bool {
    tests.iter().enumerate().any(|(index, left)| {
        tests[index + 1..]
            .iter()
            .any(|right| complementary_test(*left, *right))
    })
}

fn complementary_test(left: TestId<'_>, right: TestId<'_>) -> bool {
    match (*left.get(), *right.get()) {
        (
            TestNode::Atom {
                comparison: left_comparison,
                pattern: left_pattern,
            },
            TestNode::Atom {
                comparison: right_comparison,
                pattern: right_pattern,
            },
        ) => left_comparison != right_comparison && left_pattern == right_pattern,
        _ => false,
    }
}

fn has_complementary_regexes(regexes: &[RegexId<'_>]) -> bool {
    regexes.iter().enumerate().any(|(index, left)| {
        regexes[index + 1..]
            .iter()
            .any(|right| complementary_regex(*left, *right))
    })
}

fn complementary_regex(left: RegexId<'_>, right: RegexId<'_>) -> bool {
    matches!(*left.get(), RegexNode::Not(inner) if inner == right)
        || matches!(*right.get(), RegexNode::Not(inner) if inner == left)
}

impl<'a> SyntaxContext<'a> {
    pub(super) fn test_and(&mut self, children: Vec<TestId<'a>>) -> TestId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TestNode::False => return self.test_false,
                TestNode::True => {}
                TestNode::And(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_tests(&flat) {
            return self.test_false;
        }
        match flat.as_slice() {
            [] => self.test_true,
            [only] => *only,
            _ => {
                let values = self.test_consign.arena().alloc_slice_copy(&flat);
                self.test_consign.mk(TestNode::And(values))
            }
        }
    }

    pub(super) fn test_or(&mut self, children: Vec<TestId<'a>>) -> TestId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                TestNode::True => return self.test_true,
                TestNode::False => {}
                TestNode::Or(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_tests(&flat) {
            return self.test_true;
        }
        match flat.as_slice() {
            [] => self.test_false,
            [only] => *only,
            _ => {
                let values = self.test_consign.arena().alloc_slice_copy(&flat);
                self.test_consign.mk(TestNode::Or(values))
            }
        }
    }

    fn intern_regex(&mut self, node: RegexNode<'a>, nullable: bool) -> RegexId<'a> {
        let (id, is_new) = self.regex_consign.mk_is_new(node);
        let index = id.uid() as usize;
        if is_new {
            assert_eq!(index, self.regex_nullable.len());
            self.regex_nullable.push(nullable);
        } else {
            assert_eq!(self.regex_nullable[index], nullable);
        }
        id
    }

    pub(super) fn regex_test(&mut self, test: TestId<'a>) -> RegexId<'a> {
        if test == self.test_false {
            self.empty
        } else {
            self.intern_regex(RegexNode::Test(test), false)
        }
    }

    pub(super) fn regex_union(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::All => return self.all,
                RegexNode::Empty => {}
                RegexNode::Union(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_regexes(&flat) {
            return self.all;
        }
        match flat.as_slice() {
            [] => self.empty,
            [only] => *only,
            _ => {
                let nullable = flat.iter().any(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Union(values), nullable)
            }
        }
    }

    pub(super) fn regex_intersect(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::Empty => return self.empty,
                RegexNode::All => {}
                RegexNode::Intersect(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        flat.sort_unstable_by_key(|child| child.uid());
        flat.dedup_by_key(|child| child.uid());
        if has_complementary_regexes(&flat) {
            return self.empty;
        }
        match flat.as_slice() {
            [] => self.all,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Intersect(values), nullable)
            }
        }
    }

    pub(super) fn regex_concat(&mut self, children: Vec<RegexId<'a>>) -> RegexId<'a> {
        let mut flat = Vec::with_capacity(children.len());
        for child in children {
            match *child.get() {
                RegexNode::Empty => return self.empty,
                RegexNode::Epsilon => {}
                RegexNode::Concat(nested) => flat.extend_from_slice(nested),
                _ => flat.push(child),
            }
        }
        match flat.as_slice() {
            [] => self.epsilon,
            [only] => *only,
            _ => {
                let nullable = flat.iter().all(|child| self.nullable(*child));
                let values = self.regex_consign.arena().alloc_slice_copy(&flat);
                self.intern_regex(RegexNode::Concat(values), nullable)
            }
        }
    }

    pub(super) fn regex_star(&mut self, inner: RegexId<'a>) -> RegexId<'a> {
        match *inner.get() {
            RegexNode::Empty | RegexNode::Epsilon => self.epsilon,
            RegexNode::All => self.all,
            RegexNode::Star(_) => inner,
            _ => self.intern_regex(RegexNode::Star(inner), true),
        }
    }

    pub(super) fn regex_not(&mut self, inner: RegexId<'a>) -> RegexId<'a> {
        match *inner.get() {
            RegexNode::Empty => self.all,
            RegexNode::All => self.empty,
            RegexNode::Not(value) => value,
            _ => self.intern_regex(RegexNode::Not(inner), !self.nullable(inner)),
        }
    }

    pub(super) fn nullable(&self, regex: RegexId<'a>) -> bool {
        self.regex_nullable[regex.uid() as usize]
    }
}
