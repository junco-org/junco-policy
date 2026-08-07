//! Rule-local builder for typed tests and normalized past regular expressions.
//!
//! `RuleSyntax` owns an exclusive borrow of the validator's syntax context while one rule is being
//! built. Returned handles carry reference-backed context and scope identities. Combining a handle
//! from another rule is rejected, which prevents a tail from observing variables bound by a
//! different head.

use crate::validator::{CompileError, RuleIndex};

use super::identity::RuleScopeId;
use super::node::{Regex, RegexId, Test, TestId, TestNode};
use super::pattern::{AtomPattern, Comparison, Head};
use super::scope::{CompiledHead, Scope};
use super::storage::SyntaxContext;

/// Builder for the tests and regular expressions of one policy rule.
///
/// All constructors normalize and hashcons their results immediately. Handles are cheap `Copy`
/// values but remain valid only in this builder's syntax context and variable scope.
pub struct RuleSyntax<'context, 'arena> {
    syntax: &'context mut SyntaxContext<'arena>,
    rule: RuleIndex,
    scope_id: RuleScopeId<'arena>,
    scope: Scope,
}

impl<'context, 'arena> RuleSyntax<'context, 'arena> {
    /// Compiles the rule head and creates a builder tied to `scope_id`.
    pub(crate) fn new(
        syntax: &'context mut SyntaxContext<'arena>,
        rule: RuleIndex,
        scope_id: RuleScopeId<'arena>,
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

    /// Adds this builder's provenance identities to an internal canonical test handle.
    fn wrap_test(&self, id: TestId<'arena>) -> Test<'arena> {
        Test {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    /// Removes a public test wrapper after checking its context and rule scope.
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

    /// Adds this builder's provenance identities to an internal canonical regex handle.
    fn wrap_regex(&self, id: RegexId<'arena>) -> Regex<'arena> {
        Regex {
            context: self.syntax.context_id,
            scope: self.scope_id,
            id,
        }
    }

    /// Removes a public regex wrapper, panicking on programmer misuse inside a composition call.
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

    /// Validates the final callback result and reports foreign handles as a construction error.
    pub(crate) fn finish_regex(
        &self,
        regex: Regex<'arena>,
    ) -> Result<RegexId<'arena>, CompileError> {
        if regex.context != self.syntax.context_id || regex.scope != self.scope_id {
            return Err(CompileError::ForeignRuleHandle { rule: self.rule });
        }
        Ok(regex.id)
    }

    /// Returns the boolean test that accepts every single event.
    pub fn true_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_true)
    }

    /// Returns the boolean test that accepts no event.
    pub fn false_test(&self) -> Test<'arena> {
        self.wrap_test(self.syntax.test_false)
    }

    /// Compiles a component equality or disequality test.
    ///
    /// Variables must have been bound by this rule's head in the same component domain.
    pub fn atom(
        &mut self,
        comparison: Comparison,
        pattern: AtomPattern,
    ) -> Result<Test<'arena>, CompileError> {
        let pattern = self
            .syntax
            .compile_atom_pattern(self.rule, &pattern, &self.scope)?;
        let id = self.syntax.test_consign.mk(TestNode::Atom {
            comparison,
            pattern,
        });
        Ok(self.wrap_test(id))
    }

    /// Conjoins tests. Empty input is [`Self::true_test`].
    pub fn and(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_and(ids);
        self.wrap_test(id)
    }

    /// Disjoins tests. Empty input is [`Self::false_test`].
    pub fn or(&mut self, tests: impl IntoIterator<Item = Test<'arena>>) -> Test<'arena> {
        let ids = tests.into_iter().map(|test| self.test_id(test)).collect();
        let id = self.syntax.test_or(ids);
        self.wrap_test(id)
    }

    /// Returns the empty language, which accepts no history.
    pub fn empty(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.empty)
    }

    /// Returns the universal language, which accepts every complete history.
    pub fn all(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.all)
    }

    /// Returns the language containing only the empty history.
    pub fn epsilon(&self) -> Regex<'arena> {
        self.wrap_regex(self.syntax.epsilon)
    }

    /// Lifts a boolean test into the language of matching one-event histories.
    pub fn test(&mut self, test: Test<'arena>) -> Regex<'arena> {
        let test = self.test_id(test);
        let id = self.syntax.regex_test(test);
        self.wrap_regex(id)
    }

    /// Constructs set union. Empty input is [`Self::empty`].
    pub fn union(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_union(ids);
        self.wrap_regex(id)
    }

    /// Constructs ordered language concatenation. Empty input is [`Self::epsilon`].
    pub fn concat(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_concat(ids);
        self.wrap_regex(id)
    }

    /// Constructs Kleene star.
    pub fn star(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_star(regex);
        self.wrap_regex(id)
    }

    /// Constructs set intersection. Empty input is [`Self::all`].
    pub fn intersect(&mut self, regexes: impl IntoIterator<Item = Regex<'arena>>) -> Regex<'arena> {
        let ids = regexes
            .into_iter()
            .map(|regex| self.regex_id(regex))
            .collect();
        let id = self.syntax.regex_intersect(ids);
        self.wrap_regex(id)
    }

    /// Constructs whole-language complement.
    pub fn not(&mut self, regex: Regex<'arena>) -> Regex<'arena> {
        let regex = self.regex_id(regex);
        let id = self.syntax.regex_not(regex);
        self.wrap_regex(id)
    }

    /// Returns whether `regex` accepts the empty history.
    pub fn nullable(&self, regex: Regex<'arena>) -> bool {
        self.syntax.nullable(self.regex_id(regex))
    }
}
