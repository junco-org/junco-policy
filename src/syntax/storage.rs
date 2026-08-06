use std::sync::atomic::{AtomicU64, Ordering};

use bumpalo::Bump;
use hashconsing::BHConsign;
use string_interner::DefaultStringInterner;

use crate::model::{Principal, Resource};

use super::node::{RegexId, RegexNode, TestId, TestNode};

static NEXT_CONTEXT_ID: AtomicU64 = AtomicU64::new(1);

pub(crate) struct SyntaxContext<'a> {
    pub(super) context_id: u64,
    pub(super) variables: DefaultStringInterner,
    pub(super) test_consign: BHConsign<'a, TestNode<'a>>,
    pub(super) regex_consign: BHConsign<'a, RegexNode<'a>>,
    pub(super) regex_nullable: Vec<bool>,
    pub(super) test_true: TestId<'a>,
    pub(super) test_false: TestId<'a>,
    pub(super) empty: RegexId<'a>,
    pub(super) all: RegexId<'a>,
    pub(super) epsilon: RegexId<'a>,
}

impl<'a> SyntaxContext<'a> {
    pub(crate) fn new(arena: &'a Bump) -> Self {
        let context_id = NEXT_CONTEXT_ID.fetch_add(1, Ordering::Relaxed);
        assert_ne!(context_id, 0, "syntax context identifier space exhausted");
        let mut test_consign = BHConsign::with_capacity(arena, 128);
        let test_true = test_consign.mk(TestNode::True);
        let test_false = test_consign.mk(TestNode::False);

        let mut regex_consign = BHConsign::with_capacity(arena, 1024);
        let empty = regex_consign.mk(RegexNode::Empty);
        let all = regex_consign.mk(RegexNode::All);
        let epsilon = regex_consign.mk(RegexNode::Epsilon);
        let mut regex_nullable = Vec::with_capacity(1024);
        regex_nullable.push(false);
        regex_nullable.push(true);
        regex_nullable.push(true);

        Self {
            context_id,
            variables: DefaultStringInterner::with_capacity(64),
            test_consign,
            regex_consign,
            regex_nullable,
            test_true,
            test_false,
            empty,
            all,
            epsilon,
        }
    }

    pub(super) fn arena(&self) -> &'a Bump {
        self.test_consign.arena()
    }

    pub(super) fn alloc_principal(&self, principal: &Principal) -> &'a str {
        self.arena().alloc_str(principal.as_str())
    }

    pub(super) fn alloc_resource(&self, resource: &Resource) -> &'a [&'a str] {
        let segments: Vec<&'a str> = resource
            .segments()
            .iter()
            .map(|segment| self.arena().alloc_str(segment) as &str)
            .collect();
        self.arena().alloc_slice_copy(&segments)
    }

    #[cfg(test)]
    pub(crate) fn regex_node_count(&self) -> usize {
        self.regex_consign.len()
    }
}
