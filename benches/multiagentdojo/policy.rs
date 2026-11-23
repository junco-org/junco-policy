//! One task's information-flow state: the shared history of every agent's reads, receives,
//! declassifications and sink contacts, judged by one global `FlowPolicy`.
//!
//! Known cost: once tainted, an agent cannot act on identifiers found in third-party content
//! (reply to a sender, delete an email it searched for, book the best-reviewed hotel, pay an
//! invoice's IBAN, create an event from an email, join a channel only the channel listing
//! names). `get_channels`, `get_users_in_channel`, `get_webpage`, `read_file` and
//! `get_user_information` narrow readers to nobody, after which no peer-facing sink of that
//! principal, or of anything downstream through a handoff, passes the readers check. CaMeL
//! allows some of these only because its control flow is trusted, which one LLM cannot offer.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;
use std::time::Instant;

use history_semantics::PolicyDecision;
use history_store::{History, Store};
use junco_policy::{FlowAction, FlowEvent, FlowPolicy, FlowRule};
use rig_core::message::Message;
use serde_json::{Map, Value, json};

use crate::bridge::Bridge;
use crate::declassify::{ANCHOR_LOOKUPS, Anchors, ECHO_SINKS, endorse, role};
use crate::tools::{Audience, Sink, UNTRUSTED, find_sink};

pub type Principal = &'static str;
pub type Event = FlowEvent<Principal, Handle, Class>;

pub const ORCHESTRATOR: Principal = "orchestrator";

/// Every principal: the orchestrator and the fork's `SUITE_PARTITIONS` sub-agents.
const PRINCIPALS: &[Principal] = &[
    ORCHESTRATOR,
    "email_agent",
    "calendar_agent",
    "cloud_drive_agent",
    "transactions_agent",
    "filesystem_agent",
    "account_agent",
    "slack_agent",
    "web_agent",
    "hotels_agent",
    "restaurants_agent",
    "car_rental_agent",
    "personal_assistant_agent",
];

/// The `'static` principal named `name`.
pub fn principal(name: &str) -> Result<Principal, String> {
    PRINCIPALS
        .iter()
        .find(|known| **known == name)
        .copied()
        .ok_or_else(|| format!("unknown sub-agent {name:?}: add it to PRINCIPALS"))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Handle(pub u32);

impl fmt::Display for Handle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Class {
    Trusted,
    Untrusted,
    /// Data with a reader set narrower than everyone.
    Private,
    /// A sink argument: must not be attacker-chosen.
    Sink,
    /// A recipient outside the readers of the data it would receive.
    Peer,
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Trusted => "trusted",
            Self::Untrusted => "untrusted",
            Self::Private => "private",
            Self::Sink => "sink",
            Self::Peer => "peer",
        })
    }
}

/// Who may see a value: CaMeL's readers lattice, with `Public` as top (as `agentdojo/camel.rs`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Readers {
    Public,
    Only(BTreeSet<String>),
}

impl Readers {
    /// The readers the worker reports for a tool result: `null` for public, `{"readers": [...]}`
    /// at an owned value, and a tree parallel to the result otherwise; the intersection over all.
    fn from_tree(tree: &Value) -> Self {
        match tree {
            Value::Object(fields) if fields.len() == 1 => match fields.get("readers") {
                Some(Value::Array(readers)) => Self::Only(
                    readers
                        .iter()
                        .filter_map(Value::as_str)
                        .map(str::to_owned)
                        .collect(),
                ),
                _ => Self::from_trees(fields.values()),
            },
            Value::Object(fields) => Self::from_trees(fields.values()),
            Value::Array(items) => Self::from_trees(items.iter()),
            _ => Self::Public,
        }
    }

    fn from_trees<'a>(trees: impl Iterator<Item = &'a Value>) -> Self {
        let mut readers = Self::Public;
        for tree in trees {
            readers.intersect(&Self::from_tree(tree));
        }
        readers
    }

    fn intersect(&mut self, other: &Self) {
        match (&mut *self, other) {
            (_, Self::Public) => {}
            (Self::Public, Self::Only(_)) => *self = other.clone(),
            (Self::Only(mine), Self::Only(theirs)) => mine.retain(|reader| theirs.contains(reader)),
        }
    }

    fn can_read(&self, recipients: &BTreeSet<String>) -> bool {
        match self {
            Self::Public => true,
            Self::Only(readers) => recipients.is_subset(readers),
        }
    }
}

/// One agent invocation. `tainted` mirrors the history for handoff labels and logs; the policy
/// decides from the history alone.
pub struct Conversation {
    pub principal: Principal,
    pub tainted: bool,
    pub readers: Readers,
    pub messages: Vec<Arc<Message>>,
}

impl Conversation {
    pub fn orchestrator(prompt: &str) -> Self {
        Self {
            principal: ORCHESTRATOR,
            tainted: false,
            readers: Readers::Public,
            messages: vec![Arc::new(Message::user(prompt))],
        }
    }
}

pub struct Run<'a> {
    pub bridge: &'a mut Bridge,
    history: History<Event>,
    policy: FlowPolicy<Principal, Handle, Class>,
    anchors: Anchors,
    declassify: bool,
    next_handle: u32,
    pub calls: Vec<Value>,
    pub handoffs: Vec<Value>,
    pub policy_decisions: Vec<Value>,
    pub declassifications: Vec<Value>,
    pub first_denial: Option<Value>,
    /// Wall time inside `FlowPolicy::check`, summed over the task.
    pub policy_seconds: f64,
}

impl<'a> Run<'a> {
    pub fn new(
        bridge: &'a mut Bridge,
        prompt: &str,
        audit: bool,
        declassify: bool,
    ) -> Result<Self, String> {
        let store = Arc::new(Store::new().map_err(|error| error.to_string())?);
        let policy = FlowPolicy::new()
            .rule(FlowRule::no_contact_after_any_read(
                Class::Untrusted,
                &[Class::Sink],
            ))
            .rule(FlowRule::no_contact_after_any_read(
                Class::Private,
                &[Class::Peer],
            ));
        Ok(Self {
            bridge,
            history: History::new(store).map_err(|error| error.to_string())?,
            policy: if audit { policy.audit() } else { policy },
            anchors: Anchors::new(prompt),
            declassify,
            next_handle: 0,
            calls: Vec::new(),
            handoffs: Vec::new(),
            policy_decisions: Vec::new(),
            declassifications: Vec::new(),
            first_denial: None,
            policy_seconds: 0.0,
        })
    }

    fn handle(&mut self) -> Handle {
        self.next_handle += 1;
        Handle(self.next_handle)
    }

    fn push(
        &mut self,
        principal: Principal,
        handle: Handle,
        action: FlowAction,
        label: Class,
    ) -> Result<(), String> {
        self.history
            .push(Event {
                principal,
                handle,
                action,
                label,
            })
            .map_err(|error| error.to_string())
    }

    /// Whether the history holds an untrusted read or receive by `principal`.
    fn tainted(&self, principal: Principal) -> bool {
        self.history.as_slice().iter().any(|event| {
            event.principal == principal
                && matches!(event.action, FlowAction::Read | FlowAction::Receive)
                && event.label == Class::Untrusted
        })
    }

    /// Hands `task` from the orchestrator to a fresh conversation of `agent`, which inherits the
    /// orchestrator's taint and readers.
    pub fn start_task(
        &mut self,
        orchestrator: &Conversation,
        agent: Principal,
        task: &str,
    ) -> Result<Conversation, String> {
        debug_assert_eq!(orchestrator.tainted, self.tainted(orchestrator.principal));
        let handle = self.handle();
        let private = orchestrator.readers != Readers::Public;
        for (flag, class) in [
            (orchestrator.tainted, Class::Untrusted),
            (private, Class::Private),
        ] {
            if flag {
                self.push(orchestrator.principal, handle, FlowAction::Receive, class)?;
                self.push(agent, handle, FlowAction::Receive, class)?;
            }
        }
        self.handoffs.push(json!({
            "kind": "task", "from": orchestrator.principal, "to": agent,
            "handle": handle.to_string(), "tainted": orchestrator.tainted, "private": private
        }));
        Ok(Conversation {
            principal: agent,
            tainted: orchestrator.tainted,
            readers: orchestrator.readers.clone(),
            messages: vec![Arc::new(Message::user(task))],
        })
    }

    /// Returns a sub-agent's report to the orchestrator. Reports are never declassified or
    /// anchored: a value a hijacked agent chose stays attacker-choosable however well-formed.
    pub fn finish_task(
        &mut self,
        orchestrator: &mut Conversation,
        sub: &Conversation,
    ) -> Result<(), String> {
        let handle = self.handle();
        if sub.tainted {
            self.push(sub.principal, handle, FlowAction::Receive, Class::Untrusted)?;
            self.push(
                orchestrator.principal,
                handle,
                FlowAction::Receive,
                Class::Untrusted,
            )?;
            orchestrator.tainted = true;
        } else {
            self.push(
                orchestrator.principal,
                handle,
                FlowAction::Receive,
                Class::Trusted,
            )?;
        }
        let private = sub.readers != Readers::Public;
        if private {
            self.push(sub.principal, handle, FlowAction::Receive, Class::Private)?;
            self.push(
                orchestrator.principal,
                handle,
                FlowAction::Receive,
                Class::Private,
            )?;
            orchestrator.readers.intersect(&sub.readers);
        }
        self.handoffs.push(json!({
            "kind": "report", "from": sub.principal, "to": orchestrator.principal,
            "handle": handle.to_string(), "tainted": sub.tainted, "private": private
        }));
        Ok(())
    }

    /// Runs one environment tool for `conv`: a sink is judged first and not executed when denied;
    /// the result is then labeled, narrows `conv`'s readers, and may become an anchor.
    pub async fn environment_tool(
        &mut self,
        conv: &mut Conversation,
        name: &str,
        args: Map<String, Value>,
    ) -> Result<Value, String> {
        let sink = find_sink(name);
        if let Some(sink) = sink
            && let Some(message) = self.judge(conv, sink, &args).await?
        {
            let error = format!("SecurityPolicyDeniedError: {message}");
            self.calls.push(json!({
                "agent": conv.principal, "name": name, "args": args, "denied": true, "error": error
            }));
            return Ok(json!({ "error": error }));
        }
        let mut response = self
            .bridge
            .call("call_tool", json!({"name": name, "args": &args}))
            .await?;
        let result = response["result"].take();
        let error = response["error"].take();
        let readers = response
            .get("readers")
            .map_or(Readers::Public, Readers::from_tree);
        let handle = self.handle();
        let untrusted = UNTRUSTED.contains(&name) || ECHO_SINKS.contains(&name);
        let label = if untrusted {
            Class::Untrusted
        } else {
            Class::Trusted
        };
        self.push(conv.principal, handle, FlowAction::Read, label)?;
        // A sink's readers restate the agent's own arguments unless the result is third-party.
        if readers != Readers::Public && (untrusted || sink.is_none()) {
            self.push(conv.principal, handle, FlowAction::Read, Class::Private)?;
            conv.readers.intersect(&readers);
        }
        conv.tainted |= untrusted;
        if error.is_null() && ANCHOR_LOOKUPS.contains(&name) {
            self.anchors.record(&result);
        }
        self.calls.push(json!({
            "agent": conv.principal, "name": name, "args": args, "denied": false, "error": error
        }));
        Ok(if error.is_null() {
            result
        } else {
            json!({ "error": error })
        })
    }

    /// Records each argument's declassifications and contacts and checks every contact; returns
    /// the first enforced denial's reason.
    async fn judge(
        &mut self,
        conv: &Conversation,
        sink: &Sink,
        args: &Map<String, Value>,
    ) -> Result<Option<String>, String> {
        let mut recipients = BTreeSet::new();
        match sink.audience {
            Audience::None => {}
            Audience::Args(keys) | Audience::ArgsOrTrusted(keys) => {
                for key in keys {
                    if let Some(value) = args.get(*key) {
                        push_recipients(value, &mut recipients);
                    }
                }
            }
            Audience::Environment => {
                // An unknown file, event or transaction makes the call itself fail.
                let response = self
                    .bridge
                    .call("recipients", json!({"name": sink.name, "args": args}))
                    .await;
                if let Ok(Value::Array(items)) = response {
                    recipients.extend(items.iter().filter_map(Value::as_str).map(str::to_owned));
                }
            }
        }
        let has_recipients = !recipients.is_empty();
        let untainted = !self.tainted(conv.principal);
        let mut denial = None;
        for (key, value) in args {
            let handle = self.handle();
            let role = role(sink.name, key);
            if endorse(role, value, has_recipients, &self.anchors, self.declassify) {
                self.declassified(
                    conv,
                    handle,
                    sink,
                    key,
                    Class::Untrusted,
                    &format!("{role:?}"),
                )?;
            }
            let verdict = self.check(conv.principal, handle, Class::Sink, sink.name, key);
            denial = denial.or(verdict);
            if has_recipients && sink.data.contains(&key.as_str()) {
                if untainted || conv.readers.can_read(&recipients) {
                    self.declassified(conv, handle, sink, key, Class::Private, "readers")?;
                }
                let verdict = self.check(conv.principal, handle, Class::Peer, sink.name, key);
                denial = denial.or(verdict);
            }
        }
        Ok(denial)
    }

    fn declassified(
        &mut self,
        conv: &Conversation,
        handle: Handle,
        sink: &Sink,
        key: &str,
        class: Class,
        reason: &str,
    ) -> Result<(), String> {
        self.push(conv.principal, handle, FlowAction::Declassify, class)?;
        self.declassifications.push(json!({
            "agent": conv.principal, "handle": handle.to_string(), "tool": sink.name, "key": key,
            "class": class.to_string(), "reason": reason, "tainted": conv.tainted
        }));
        Ok(())
    }

    /// Checks one contact; returns the denial's reason when enforced. Every decision is logged,
    /// and the first would-be denial is kept in audit mode too.
    fn check(
        &mut self,
        principal: Principal,
        handle: Handle,
        label: Class,
        sink: &str,
        key: &str,
    ) -> Option<String> {
        let event = Event {
            principal,
            handle,
            action: FlowAction::Contact,
            label,
        };
        let started = Instant::now();
        let result = self.policy.check(
            &mut self.history,
            std::slice::from_ref(&event),
            |event, decision| {
                let reason = match decision {
                    PolicyDecision::Grant => None,
                    PolicyDecision::Deny {
                        failed_precondition,
                        ..
                    } => Some(failed_precondition.clone()),
                };
                if let Some(reason) = &reason {
                    self.first_denial.get_or_insert_with(
                        || json!({"agent": principal, "sink": sink, "key": key, "message": reason}),
                    );
                }
                self.policy_decisions.push(json!({
                    "agent": event.principal, "handle": event.handle.to_string(), "sink": sink,
                    "key": key, "class": event.label.to_string(),
                    "decision": if reason.is_some() { "deny" } else { "grant" },
                    "reason": reason, "seconds": started.elapsed().as_secs_f64()
                }));
            },
        );
        self.policy_seconds += started.elapsed().as_secs_f64();
        result
            .err()
            .map(|denials| denials[0].failed_precondition.clone())
    }

    /// Events as `[principal, "$n", action, label]`.
    pub fn events(&self) -> Value {
        self.history
            .as_slice()
            .iter()
            .map(|event| {
                json!([
                    event.principal,
                    event.handle.to_string(),
                    event.action.to_string(),
                    event.label.to_string()
                ])
            })
            .collect()
    }
}

/// The recipients named by an argument value: strings and possibly nested arrays.
fn push_recipients(value: &Value, recipients: &mut BTreeSet<String>) {
    match value {
        Value::String(recipient) => {
            recipients.insert(recipient.clone());
        }
        Value::Array(items) => items
            .iter()
            .for_each(|item| push_recipients(item, recipients)),
        _ => {}
    }
}
