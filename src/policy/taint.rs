//! Abstract taint tracking: which principals hold data of a propagated class, and which carriers
//! hold it for them.
//!
//! Agent rules follow the principal that read a class. That principal can hand the data to another
//! one through a carrier it writes (a file, a socket, a queue: any identity the caller keys with
//! `K`), so each shared log keeps one [`TaintState`]. A principal that reads a resource of a class
//! its [`AgentPolicy`] propagates holds that class; every carrier it then writes carries each class
//! it holds; a principal that reads a carrier acquires the carrier's classes. The caller logs each
//! acquisition as an [`AgentEvent`] with [`AgentAction::Receive`] ([`Taint::received_by`]), which
//! [`super::agent::AgentRule::no_contact_after_read`] treats like a read of the class itself.
//!
//! A principal can also receive data straight from another one's call, before the receiver itself
//! does anything observable: [`TaintState::hand`] records that at once, and the receiver's next
//! [`TaintState::observe`] returns it for its log.
//!
//! Taint is never rolled back by refusing what a principal did: what it read stays read. Only an
//! operator's declassification removes it: from a principal, which a later read taints again
//! ([`TaintState::declassify`]), or from a carrier ([`TaintState::declassify_carrier`]).

use std::collections::HashMap;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use super::agent::{AgentAction, AgentEvent, AgentPolicy, Label};

/// How a principal came to hold data of `class`: from `from`, through `via`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Taint<P, C, K> {
    /// The propagated class.
    pub class: C,
    /// The principal that read it, or wrote the carrier it came through.
    pub from: P,
    /// The resource it was read from, or the carrier it came through.
    pub via: K,
}

impl<P: Copy, C: Copy, K> Taint<P, C, K> {
    /// The log entry recording that `holder` received this taint.
    pub const fn received_by(&self, holder: P) -> AgentEvent<P, C> {
        AgentEvent::new(holder, AgentAction::Receive, self.class)
    }
}

impl<P: Display, C: Display, K: Debug> Display for Taint<P, C, K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} data from {} via {:?}",
            self.class, self.from, self.via
        )
    }
}

/// What one observed step of a principal read and wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Access<K, C> {
    /// Each carrier read, with the class of the resource read from it, if classified.
    pub reads: Vec<(K, Option<C>)>,
    /// Each carrier written.
    pub writes: Vec<K>,
}

impl<K, C> Default for Access<K, C> {
    fn default() -> Self {
        Self {
            reads: Vec::new(),
            writes: Vec::new(),
        }
    }
}

/// One shared log's live taint.
#[derive(Clone, Debug)]
pub struct TaintState<P, C, K> {
    /// The classes each principal holds, each with how it first came to hold it.
    tainted: HashMap<P, Vec<Taint<P, C, K>>>,
    /// The classes each carrier holds, each with the principal that wrote it.
    carriers: HashMap<K, Vec<Taint<P, C, K>>>,
    /// Taint handed to a principal by another one's step, not yet returned for its log.
    pending: HashMap<P, Vec<Taint<P, C, K>>>,
    /// Advances whenever any principal comes to hold, or stops holding, a class.
    revision: u64,
}

impl<P, C, K> Default for TaintState<P, C, K> {
    fn default() -> Self {
        Self {
            tainted: HashMap::new(),
            carriers: HashMap::new(),
            pending: HashMap::new(),
            revision: 0,
        }
    }
}

impl<P: Label, C: Label, K: Clone + Eq + Hash> TaintState<P, C, K> {
    /// An empty table: nobody holds anything.
    pub fn new() -> Self {
        Self::default()
    }

    /// Folds one observed step of `principal`, classified by `policy`, into the table. Returns
    /// the classes the step handed `principal` for the first time through a carrier, and those
    /// [handed](Self::hand) to it since its last step; its own read of a class is already in the
    /// log as that read.
    pub fn observe(
        &mut self,
        principal: P,
        policy: &AgentPolicy<P, C>,
        access: &Access<K, C>,
    ) -> Vec<Taint<P, C, K>> {
        let mut acquired = self.pending.remove(&principal).unwrap_or_default();
        for taint in own(principal, policy, access) {
            self.hold(principal, taint);
        }
        for taint in self.carried(access) {
            if self.hold(principal, taint.clone()) {
                acquired.push(taint);
            }
        }
        let Some(held) = self.tainted.get(&principal).filter(|held| !held.is_empty()) else {
            return acquired;
        };
        let held: Vec<C> = held.iter().map(|taint| taint.class).collect();
        for carrier in &access.writes {
            let classes = self.carriers.entry(carrier.clone()).or_default();
            for &class in &held {
                if !classes.iter().any(|taint| taint.class == class) {
                    classes.push(Taint {
                        class,
                        from: principal,
                        via: carrier.clone(),
                    });
                }
            }
        }
        acquired
    }

    /// The classes the carriers `access` reads hold, without recording that anyone read them.
    pub fn carried(&self, access: &Access<K, C>) -> Vec<Taint<P, C, K>> {
        access
            .reads
            .iter()
            .filter_map(|(carrier, _)| self.carriers.get(carrier))
            .flatten()
            .cloned()
            .collect()
    }

    /// Every class a step of `principal` sends: those it holds, and those it reads from
    /// `source` in the same step, before that read is observed.
    pub fn sending(
        &self,
        principal: P,
        policy: &AgentPolicy<P, C>,
        source: Option<&Access<K, C>>,
    ) -> Vec<Taint<P, C, K>> {
        let mut sent: Vec<Taint<P, C, K>> =
            self.tainted.get(&principal).cloned().unwrap_or_default();
        if let Some(source) = source {
            for taint in own(principal, policy, source).chain(self.carried(source)) {
                if !sent.iter().any(|held| held.class == taint.class) {
                    sent.push(taint);
                }
            }
        }
        sent
    }

    /// Hands `principal` the class of `taint` from another principal's step, before that step
    /// delivers anything to it. [`Self::observe`] returns it at `principal`'s next step.
    pub fn hand(&mut self, principal: P, taint: Taint<P, C, K>) {
        if self.hold(principal, taint.clone()) {
            self.pending.entry(principal).or_default().push(taint);
        }
    }

    /// Every class `principal` holds through another principal's carrier or step.
    pub fn received(&self, principal: P) -> Vec<Taint<P, C, K>> {
        self.tainted
            .get(&principal)
            .into_iter()
            .flatten()
            .filter(|taint| taint.from != principal)
            .cloned()
            .collect()
    }

    /// Advances whenever [`Self::received`] or [`Self::sending`] may have changed for some
    /// principal, so a caller can cache answers derived from them.
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Stops `principal` holding `class`, however it came to, including taint handed to it and
    /// not yet returned for its log. Carriers it wrote keep the class.
    pub fn declassify(&mut self, principal: P, class: C) {
        if let Some(held) = self.tainted.get_mut(&principal) {
            held.retain(|taint| taint.class != class);
        }
        if let Some(pending) = self.pending.get_mut(&principal) {
            pending.retain(|taint| taint.class != class);
        }
        self.revision += 1;
    }

    /// Stops `carrier` carrying `class`: a later read of it taints no one.
    pub fn declassify_carrier(&mut self, carrier: &K, class: C) {
        if let Some(classes) = self.carriers.get_mut(carrier) {
            classes.retain(|taint| taint.class != class);
        }
    }

    /// Records that `principal` holds `taint`'s class; true when it did not already.
    fn hold(&mut self, principal: P, taint: Taint<P, C, K>) -> bool {
        let held = self.tainted.entry(principal).or_default();
        if held.iter().any(|holding| holding.class == taint.class) {
            return false;
        }
        held.push(taint);
        self.revision += 1;
        true
    }
}

/// The propagated classes `principal` itself read in `access`.
fn own<'a, P: Label, C: Label, K: Clone>(
    principal: P,
    policy: &'a AgentPolicy<P, C>,
    access: &'a Access<K, C>,
) -> impl Iterator<Item = Taint<P, C, K>> + 'a {
    access
        .reads
        .iter()
        .filter_map(|(carrier, class)| class.map(|class| (carrier, class)))
        .filter(|&(_, class)| policy.propagates(class))
        .map(move |(carrier, class)| Taint {
            class,
            from: principal,
            via: carrier.clone(),
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AgentRule;

    type State = TaintState<&'static str, &'static str, &'static str>;

    fn policy() -> AgentPolicy<&'static str, &'static str> {
        AgentPolicy::new().rule(AgentRule::no_contact_after_read("secret", &["external"]))
    }
    fn reads(carrier: &'static str, class: &'static str) -> Access<&'static str, &'static str> {
        Access {
            reads: vec![(carrier, Some(class))],
            writes: Vec::new(),
        }
    }
    fn writes(carrier: &'static str) -> Access<&'static str, &'static str> {
        Access {
            reads: Vec::new(),
            writes: vec![carrier],
        }
    }

    #[test]
    fn a_carrier_written_after_a_secret_read_taints_its_reader() {
        let (policy, mut state) = (policy(), State::new());
        assert!(
            state
                .observe("a", &policy, &reads(".env", "secret"))
                .is_empty()
        );
        assert!(
            state
                .observe("a", &policy, &writes("/tmp/stage"))
                .is_empty()
        );
        let acquired = state.observe("b", &policy, &reads("/tmp/stage", "other"));
        assert_eq!(
            acquired,
            [Taint {
                class: "secret",
                from: "a",
                via: "/tmp/stage"
            }]
        );
        assert_eq!(
            acquired[0].received_by("b"),
            AgentEvent::new("b", AgentAction::Receive, "secret")
        );
        assert_eq!(state.received("b"), acquired);
        // Acquired once; a second read adds nothing new to the log.
        assert!(
            state
                .observe("b", &policy, &reads("/tmp/stage", "other"))
                .is_empty()
        );
        assert!(state.received("a").is_empty());
    }

    #[test]
    fn carriers_written_before_the_read_or_by_untainted_principals_carry_nothing() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &writes("/tmp/stage"));
        state.observe("a", &policy, &reads(".env", "secret"));
        assert!(
            state
                .observe("b", &policy, &reads("/tmp/stage", "other"))
                .is_empty()
        );
        assert!(
            state
                .observe("b", &policy, &reads("README.md", "src"))
                .is_empty()
        );
    }

    #[test]
    fn taint_passes_on_through_chains_naming_the_last_writer() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &reads(".env", "secret"));
        state.observe("a", &policy, &writes("notes.txt"));
        assert_eq!(
            state
                .observe("b", &policy, &reads("notes.txt", "src"))
                .len(),
            1
        );
        state.observe("b", &policy, &writes("/tmp/relay"));
        let acquired = state.observe("c", &policy, &reads("/tmp/relay", "other"));
        assert_eq!(acquired.len(), 1);
        assert_eq!(acquired[0].from, "b");
    }

    #[test]
    fn looking_up_carriers_records_nothing() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &reads(".env", "secret"));
        state.observe("a", &policy, &writes("/tmp/stage"));
        assert_eq!(state.carried(&reads("/tmp/stage", "other")).len(), 1);
        assert!(state.received("b").is_empty());
        assert_eq!(
            state
                .observe("b", &policy, &reads("/tmp/stage", "other"))
                .len(),
            1
        );
    }

    #[test]
    fn classes_no_rule_propagates_do_not_taint() {
        let mut state = State::new();
        let policy = AgentPolicy::new().rule(AgentRule::no_network("external"));
        state.observe("a", &policy, &reads(".env", "secret"));
        state.observe("a", &policy, &writes("/tmp/stage"));
        assert!(
            state
                .observe("b", &policy, &reads("/tmp/stage", "other"))
                .is_empty()
        );
    }

    #[test]
    fn a_step_sends_what_its_principal_holds_and_what_it_reads_on_the_way() {
        let (policy, mut state) = (policy(), State::new());
        assert!(state.sending("b", &policy, None).is_empty());
        // Copying the secret itself, or a carrier, sends the class before any read is observed.
        let direct = state.sending("b", &policy, Some(&reads(".env", "secret")));
        assert_eq!(direct[0].from, "b");
        state.observe("a", &policy, &reads(".env", "secret"));
        state.observe("a", &policy, &writes("/tmp/stage"));
        assert_eq!(state.sending("a", &policy, None).len(), 1);
        let sent = state.sending("b", &policy, Some(&reads("/tmp/stage", "other")));
        assert_eq!((sent.len(), sent[0].from), (1, "a"));
        assert!(state.received("b").is_empty());
    }

    #[test]
    fn handed_taint_is_held_at_once_and_logged_at_the_next_step() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &reads(".env", "secret"));
        let start = state.revision();
        let sent = state.sending("a", &policy, None);
        state.hand("b", sent[0].clone());
        assert!(state.revision() > start);
        assert_eq!(state.received("b").len(), 1);
        let logged = state.observe("b", &policy, &Access::default());
        assert_eq!(logged, sent);
        assert!(state.observe("b", &policy, &Access::default()).is_empty());
    }

    #[test]
    fn declassifying_clears_a_holder_until_it_reads_again() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &reads(".env", "secret"));
        state.hand("b", state.sending("a", &policy, None)[0].clone());
        let revision = state.revision();
        state.declassify("b", "secret");
        assert!(state.revision() > revision);
        assert!(state.received("b").is_empty());
        // Taint handed to b and not yet in its log is gone too.
        assert!(
            state
                .observe("b", &policy, &reads("README.md", "src"))
                .is_empty()
        );
        state.declassify("a", "secret");
        assert!(state.sending("a", &policy, None).is_empty());
        state.observe("a", &policy, &reads(".env", "secret"));
        assert_eq!(state.sending("a", &policy, None).len(), 1);
    }

    #[test]
    fn a_declassified_carrier_taints_no_later_reader() {
        let (policy, mut state) = (policy(), State::new());
        state.observe("a", &policy, &reads(".env", "secret"));
        state.observe("a", &policy, &writes("notes.txt"));
        state.declassify_carrier(&"notes.txt", "secret");
        assert!(
            state
                .observe("b", &policy, &reads("notes.txt", "src"))
                .is_empty()
        );
    }
}
