use crate::validator::CompileError;

use super::node::{Regex, RegexId, Test, TestId, TestNode};
use super::pattern::{AtomPattern, Comparison, Head};
use super::scope::{CompiledHead, Scope};
use super::storage::SyntaxContext;

pub struct RuleSyntax<'context, 'arena> {
    syntax: &'context mut SyntaxContext<'arena>,
    rule: usize,
    scope_id: u64,
    scope: Scope,
}

impl<'context, 'arena> RuleSyntax<'context, 'arena> {
    pub(crate) fn new(
        syntax: &'context mut SyntaxContext<'arena>,
        rule: usize,
        scope_id: u64,
        head: &Head,
    ) -> Result<(CompiledHead<'arena>, Self), CompileError> {
        let (head, scope) = syntax.compile_head(rule, head)?;
        Ok((
            head,
            Self {
                syntax,
                rule,
                scope_id,
                scope,
            },
        ))
    }

    fn wrap_test(&self, id: TestId<'arena>) -> Test<'arena> {
        Test {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    fn test_id(&self, test: Test<'arena>) -> TestId<'arena> {
        assert_eq!(
            test.context, self.syntax.context_id,
            "test belongs to another syntax context"
        );
        assert_eq!(
            test.scope, self.scope_id,
            "test belongs to another rule scope"
        );
        test.id
    }

    fn wrap_regex(&self, id: RegexId<'arena>) -> Regex<'arena> {
        Regex {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    pub(crate) fn regex_id(&self, regex: Regex<'arena>) -> RegexId<'arena> {
        assert_eq!(
            regex.context, self.syntax.context_id,
            "regex belongs to another syntax context"
        );
        assert_eq!(
            regex.scope, self.scope_id,
            "regex belongs to another rule scope"
        );
        regex.id
    }

    pub(crate) fn finish_regex(
        &self,
        regex: Regex<'arena>,
    ) -> Result<RegexId<'arena>, CompileError> {
        if regex.context != self.syntax.context_id || regex.scope != self.scope_id {
            return Err(CompileError::ForeignRuleHandle { rule: self.rule });
        }
        Ok(regex.id)
    }

    pub fn true_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_true)
    }

    pub fn false_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_false)
    }

    pub fn atom(
        &mut self,
        comparison: Comparison,
        pattern: AtomPattern,
    ) -> Result<Test<'arena>, CompileError> {
        let term = self
            .syntax
            .compile_atom_pattern(self.rule, &pattern, &self.scope)?;
        let id = self.syntax.test_consign.mk(TestNode::Atom {
            comparison,
            pattern: term,
        });
        Ok(self.wrap_test(id))
    }

    pub fn and(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_and(ids);
        self.wrap_test(id)
    }

    pub fn or(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_or(ids);
        self.wrap_test(id)
    }

    pub fn empty(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.empty)
    }

    pub fn all(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.all)
    }

    pub fn epsilon(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.epsilon)
    }

    pub fn test(&mut self, test: Test<'arena>) -> Regex<'arena> {
        let test = self.test_id(test);
        let id = self.syntax.regex_test(test);
        self.wrap_regex(id)
    }

    pub fn union(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_union(ids);
        self.wrap_regex(id)
    }

    pub fn concat(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_concat(ids);
        self.wrap_regex(id)
    }

    pub fn star(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_star(regex);
        self.wrap_regex(id)
    }

    pub fn intersect(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_intersect(ids);
        self.wrap_regex(id)
    }

    pub fn not(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_not(regex);
        self.wrap_regex(id)
    }

    pub fn nullable(&self, regex: Regex<'arena>) -> bool {
        self.syntax.nullable(self.regex_id(regex))
    }
}
