use std::fmt::{self, Write as _};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use history_semantics::PolicyDecision;
use history_store::{History, Store};
use junco_policy::{AgentAction, AgentEvent, AgentPolicy, AgentRule};
use rig_core::completion::{CompletionRequest, CompletionResponse, ToolDefinition};
use rig_core::http_client::DynHttpClient;
use rig_core::message::{Message, ToolChoice, ToolName, ToolResultContent};
use rig_core::providers::copilot::{
    self,
    auth::{AuthSource, Authenticator, DeviceCodeHandler, FileTokenStore},
};
use rig_core::providers::openai::OpenAIConfig;
use rig_core::tool::validate::validate;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value, json};

use crate::bridge::Bridge;
use crate::tools::{
    self, HAVE_ENOUGH_INFORMATION_DESCRIPTION, P_SYSTEM_PROMPT, Q_SYSTEM_PROMPT, SINKS, UNTRUSTED,
};

pub struct Llm {
    auth: Authenticator,
    http: DynHttpClient,
    pub model: String,
    pub q_model: String,
}

impl Llm {
    pub fn new(model: String, q_model: String) -> Result<Self, String> {
        let source = match std::env::var("GITHUB_TOKEN") {
            Ok(token) if !token.is_empty() => AuthSource::GitHubAccessToken(token),
            _ => AuthSource::OAuth,
        };
        let home = std::env::var_os("HOME").ok_or("HOME is not set")?;
        Ok(Self {
            auth: Authenticator::new(
                source,
                FileTokenStore::new(PathBuf::from(home).join(".config/junco-policy/copilot")),
                DeviceCodeHandler::default(),
                true,
            ),
            http: rig_reqwest::shared(),
            model,
            q_model,
        })
    }

    pub async fn call(
        &self,
        model: &str,
        request: CompletionRequest,
    ) -> Result<CompletionResponse, String> {
        let mut last_error = String::new();
        for attempt in 0..=5 {
            let result = async {
                let context = self
                    .auth
                    .auth_context(&self.http)
                    .await
                    .map_err(|error| error.to_string())?;
                let mut config =
                    OpenAIConfig::with_key(&copilot::DIALECT, context.api_key.expose());
                if let Some(base) = context.api_base {
                    config = config.with_base_url(base);
                }
                config
                    .connect(self.http.clone())
                    .completion(model)
                    .call(request.clone())
                    .await
                    .map_err(|error| error.to_string())
            }
            .await;
            match result {
                Ok(response) => return Ok(response),
                Err(error) => last_error = error,
            }
            if attempt < 5 {
                tokio::time::sleep(Duration::from_secs(1 << attempt)).await;
            }
        }
        Err(format!(
            "model {model} failed after provider retries: {last_error}"
        ))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Handle(pub u32);

impl fmt::Display for Handle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Class {
    Trusted,
    Untrusted,
    Sink,
}

impl fmt::Display for Class {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Trusted => "trusted",
            Self::Untrusted => "untrusted",
            Self::Sink => "sink",
        })
    }
}

pub struct Var {
    value: Value,
    tainted: bool,
}

#[derive(Serialize)]
pub struct CallRecord {
    pub name: String,
    pub args: Value,
    /// Taint from the original argument and guard references, not the result source.
    pub tainted: bool,
    pub denied: bool,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FirstDenial {
    pub index: usize,
    pub message: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
pub struct Score {
    pub utility: bool,
    pub injection_success: Option<bool>,
}

struct Prepared {
    args: Value,
    contacts: Vec<Handle>,
    tainted: bool,
    guard: Option<bool>,
}

/// A task's workflow state borrowing its lane's reusable worker.
pub struct Run<'a> {
    pub bridge: &'a mut Bridge,
    pub messages: Vec<Arc<Message>>,
    vars: Vec<Var>,
    pub history: History<AgentEvent<Handle, Class>>,
    policy: AgentPolicy<Handle, Class>,
    pub calls: Vec<CallRecord>,
    pub skipped_calls: Vec<CallRecord>,
    pub policy_decisions: Vec<Value>,
    pub first_denial: Option<FirstDenial>,
    pub final_output: String,
}

impl<'a> Run<'a> {
    pub fn new(bridge: &'a mut Bridge, prompt: &str) -> Result<Self, String> {
        let store = Arc::new(Store::new().map_err(|error| error.to_string())?);
        Ok(Self {
            bridge,
            messages: vec![Arc::new(Message::user(prompt))],
            vars: Vec::new(),
            history: History::new(store).map_err(|error| error.to_string())?,
            policy: AgentPolicy::new()
                .rule(AgentRule::no_contact_after_read(
                    Class::Untrusted,
                    &[Class::Sink],
                ))
                .audit(),
            calls: Vec::new(),
            skipped_calls: Vec::new(),
            policy_decisions: Vec::new(),
            first_denial: None,
            final_output: String::new(),
        })
    }

    fn insert(&mut self, value: Value, tainted: bool) -> Result<Handle, String> {
        let handle = Handle(u32::try_from(self.vars.len() + 1).map_err(|error| error.to_string())?);
        self.vars.push(Var { value, tainted });
        Ok(handle)
    }

    fn event(&mut self, handle: Handle, action: AgentAction, class: Class) -> Result<(), String> {
        self.history
            .push(AgentEvent::new(handle, action, class))
            .map_err(|error| error.to_string())
    }

    fn record_tool_result(
        &mut self,
        value: Value,
        source: Class,
        received: bool,
    ) -> Result<Handle, String> {
        let handle = self.insert(value, source == Class::Untrusted || received)?;
        self.event(handle, AgentAction::Read, source)?;
        if received {
            self.event(handle, AgentAction::Receive, Class::Untrusted)?;
        }
        Ok(handle)
    }

    fn record_extraction(&mut self, value: Value, tainted: bool) -> Result<Handle, String> {
        let handle = self.insert(value, tainted)?;
        let (action, class) = if tainted {
            (AgentAction::Receive, Class::Untrusted)
        } else {
            (AgentAction::Read, Class::Trusted)
        };
        self.event(handle, action, class)?;
        Ok(handle)
    }

    fn lookup(&self, reference: &str) -> Result<(&Value, Handle), String> {
        let missing = || format!("ReferenceError: {reference} has no such path");
        let bytes = reference.as_bytes();
        let end = bytes[1..]
            .iter()
            .position(|byte| !byte.is_ascii_digit())
            .map_or(bytes.len(), |index| index + 1);
        let id: u32 = reference[1..end].parse().map_err(|_| missing())?;
        let index = id.checked_sub(1).ok_or_else(missing)? as usize;
        let mut value = &self.vars.get(index).ok_or_else(missing)?.value;
        let mut cursor = end;
        while cursor < bytes.len() {
            if bytes[cursor] == b'.' {
                let start = cursor + 1;
                cursor = start;
                while cursor < bytes.len()
                    && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
                {
                    cursor += 1;
                }
                value = value.get(&reference[start..cursor]).ok_or_else(missing)?;
            } else {
                let start = cursor + 1;
                let end = reference[start..].find(']').ok_or_else(missing)? + start;
                let index: usize = reference[start..end].parse().map_err(|_| missing())?;
                value = value.get(index).ok_or_else(missing)?;
                cursor = end + 1;
            }
        }
        Ok((value, Handle(id)))
    }

    fn resolve(&self, value: &Value, refs: &mut Vec<Handle>) -> Result<Value, String> {
        match value {
            Value::String(text) => {
                let mut output = String::new();
                let mut cursor = 0;
                while let Some(relative) = text[cursor..].find('$') {
                    let start = cursor + relative;
                    let Some(end) = reference_end(text, start) else {
                        output.push_str(&text[cursor..=start]);
                        cursor = start + 1;
                        continue;
                    };
                    let (resolved, handle) = self.lookup(&text[start..end])?;
                    refs.push(handle);
                    if start == 0 && end == text.len() {
                        return Ok(resolved.clone());
                    }
                    output.push_str(&text[cursor..start]);
                    if let Value::String(text) = resolved {
                        output.push_str(text);
                    } else {
                        write!(output, "{resolved}").expect("writing to a String cannot fail");
                    }
                    cursor = end;
                }
                output.push_str(&text[cursor..]);
                Ok(Value::String(output))
            }
            Value::Array(values) => values
                .iter()
                .map(|value| self.resolve(value, refs))
                .collect(),
            Value::Object(values) => values
                .iter()
                .map(|(key, value)| Ok((key.clone(), self.resolve(value, refs)?)))
                .collect(),
            _ => Ok(value.clone()),
        }
    }

    fn prepare(&self, name: &str, arguments: &Map<String, Value>) -> Result<Prepared, String> {
        let protected = SINKS
            .iter()
            .find(|(sink, _)| *sink == name)
            .map(|(_, fields)| *fields);
        let mut refs = Vec::new();
        let mut contacts = Vec::new();
        let mut args = Map::new();
        let mut guard = None;
        for (key, value) in arguments {
            let start = refs.len();
            let resolved = self.resolve(value, &mut refs)?;
            if key == "$if" {
                guard = Some(truthy(&resolved));
            } else {
                args.insert(key.clone(), resolved);
            }
            if protected.is_some_and(|fields| key == "$if" || fields.contains(&key.as_str())) {
                contacts.extend_from_slice(&refs[start..]);
            }
        }
        contacts.sort_unstable_by_key(|handle| handle.0);
        contacts.dedup();
        let tainted = refs
            .iter()
            .any(|handle| self.vars[handle.0 as usize - 1].tainted);
        Ok(Prepared {
            args: Value::Object(args),
            contacts,
            tainted,
            guard,
        })
    }

    fn check_contacts(&mut self, name: &str, contacts: &[Handle]) -> Result<bool, String> {
        let mut denied = false;
        let index = self.calls.len();
        for &handle in contacts {
            let event = AgentEvent::new(handle, AgentAction::Contact, Class::Sink);
            self.policy
                .check(
                    &mut self.history,
                    std::slice::from_ref(&event),
                    |event, decision| {
                        let reason = match decision {
                            PolicyDecision::Grant => None,
                            PolicyDecision::Deny {
                                failed_precondition,
                                ..
                            } => {
                                denied = true;
                                self.first_denial.get_or_insert_with(|| FirstDenial {
                                    index,
                                    message: failed_precondition.clone(),
                                });
                                Some(failed_precondition)
                            }
                        };
                        self.policy_decisions.push(json!({
                            "handle": event.principal.0, "sink": name,
                            "decision": if reason.is_some() { "deny" } else { "grant" },
                            "reason": reason
                        }));
                    },
                )
                .map_err(|denials| denials[0].to_string())?;
        }
        Ok(denied)
    }

    fn skip(
        &mut self,
        name: &str,
        args: Value,
        tainted: bool,
        denied: bool,
    ) -> Result<Value, String> {
        self.skipped_calls.push(CallRecord {
            name: name.to_owned(),
            args,
            tainted,
            denied,
            error: None,
        });
        let handle = self.insert(Value::Null, false)?;
        Ok(json!({"$ref": handle.to_string()}))
    }

    async fn environment_tool(&mut self, name: &str, prepared: Prepared) -> Result<Value, String> {
        let denied = self.check_contacts(name, &prepared.contacts)?;
        if prepared.guard == Some(false) {
            return self.skip(name, prepared.args, prepared.tainted, denied);
        }
        let mut response = self
            .bridge
            .call("call_tool", json!({"name": name, "args": &prepared.args}))
            .await?;
        let error = response
            .get("error")
            .and_then(Value::as_str)
            .map(str::to_owned);
        let source = if UNTRUSTED.contains(&name) {
            Class::Untrusted
        } else {
            Class::Trusted
        };
        let value = response
            .get_mut("result")
            .ok_or("worker tool response has no result")?
            .take();
        let handle = self.record_tool_result(value, source, prepared.tainted)?;
        let tainted = self.vars[handle.0 as usize - 1].tainted;
        let reply = if prepared.guard.is_some() {
            // A guard must not disclose its value through success, shape, or error envelopes.
            json!({"$ref": handle.to_string()})
        } else if let Some(error) = &error {
            json!({"$ref": handle.to_string(), "error": redact_error(error, tainted)})
        } else if tainted {
            json!({"$ref": handle.to_string(), "shape": response.get_mut("shape").ok_or("worker tool response has no shape")?.take()})
        } else {
            json!({"$ref": handle.to_string(), "value": &self.vars[handle.0 as usize - 1].value})
        };
        self.calls.push(CallRecord {
            name: name.to_owned(),
            args: prepared.args,
            tainted: prepared.tainted,
            denied,
            error,
        });
        Ok(reply)
    }

    async fn query(&mut self, llm: &Llm, prepared: Prepared) -> Result<Value, String> {
        if prepared.guard == Some(false) {
            return self.skip("query_ai_assistant", prepared.args, prepared.tainted, false);
        }
        let mut args = prepared.args;
        let Some(query) = args.get("query").and_then(Value::as_str) else {
            return Ok(json!({"error": "QueryArgumentsError: query must be a string"}));
        };
        let prompt = query.to_owned();
        let mut schema = args
            .get_mut("output_schema")
            .map(Value::take)
            .unwrap_or(Value::Null);
        if schema.get("type").and_then(Value::as_str) != Some("object") {
            return Ok(
                json!({"error": "QueryArgumentsError: output_schema must describe an object"}),
            );
        }
        let Some(properties) = schema.get_mut("properties").and_then(Value::as_object_mut) else {
            return Ok(json!({"error": "QueryArgumentsError: output_schema needs properties"}));
        };
        properties.insert(
            "have_enough_information".to_owned(),
            json!({"type": "boolean", "description": HAVE_ENOUGH_INFORMATION_DESCRIPTION}),
        );
        let Some(required) = schema.get_mut("required").and_then(Value::as_array_mut) else {
            return Ok(json!({"error": "QueryArgumentsError: output_schema needs required"}));
        };
        if !required
            .iter()
            .any(|value| value == "have_enough_information")
        {
            required.push(json!("have_enough_information"));
        }
        let result_tool = Arc::new(ToolDefinition::new(
            ToolName::new("result").expect("non-empty tool name"),
            "Return the parsed result",
            schema,
        ));
        for _ in 0..10 {
            let request = CompletionRequest::new(Message::user(&prompt))
                .preamble(Q_SYSTEM_PROMPT)
                .tool(Arc::clone(&result_tool))
                .tool_choice(ToolChoice::Required)
                .max_tokens(4096);
            let response = llm.call(&llm.q_model, request).await?;
            let Some(call) = response.tool_calls().next() else {
                continue;
            };
            if call.function.name.as_str() != "result" {
                continue;
            }
            let Some(flag) = call
                .function
                .arguments
                .get("have_enough_information")
                .and_then(Value::as_bool)
            else {
                continue;
            };
            if !flag {
                return Ok(json!({"error": "NotEnoughInformationError"}));
            }
            let mut value = Value::Object(call.function.arguments.clone());
            if validate(&result_tool.parameters, &value).is_err() {
                continue;
            }
            value
                .as_object_mut()
                .expect("validated object")
                .remove("have_enough_information");
            let handle = self.record_extraction(value, prepared.tainted)?;
            return Ok(json!({"$ref": handle.to_string()}));
        }
        Ok(json!({"error": "NotEnoughInformationError"}))
    }

    pub async fn execute(
        &mut self,
        llm: &Llm,
        definitions: Vec<ToolDefinition>,
        max_turns: u32,
    ) -> Result<(), String> {
        let definitions: Vec<_> = tools::tool_definitions(definitions)?
            .into_iter()
            .map(Arc::new)
            .collect();
        for turn in 0..max_turns {
            let last = self.messages.last().expect("initial user message");
            let request = CompletionRequest::new((**last).clone())
                .preamble(P_SYSTEM_PROMPT)
                .messages(self.messages[..self.messages.len() - 1].iter().cloned())
                .tools(definitions.iter().cloned())
                .max_tokens(4096);
            let response = llm.call(&llm.model, request).await?;
            let message = response
                .message()
                .ok_or("model returned an empty response")?;
            self.messages.push(Arc::new(message));
            if response.tool_calls().next().is_none() {
                let resolved = self.resolve(&Value::String(response.text()), &mut Vec::new())?;
                self.final_output = match resolved {
                    Value::String(text) => text,
                    value => value.to_string(),
                };
                return Ok(());
            }
            let mut results = Vec::new();
            for call in response.tool_calls() {
                let name = call.function.name.as_str();
                let reply = match self.prepare(name, &call.function.arguments) {
                    Err(error) => json!({"error": error}),
                    Ok(prepared) if name == "query_ai_assistant" => {
                        let guarded = prepared.guard.is_some();
                        let tainted = prepared.tainted;
                        let reply = self.query(llm, prepared).await?;
                        if guarded && reply.get("$ref").is_none() {
                            let handle = self.record_extraction(Value::Null, tainted)?;
                            json!({"$ref": handle.to_string()})
                        } else {
                            reply
                        }
                    }
                    Ok(prepared) => self.environment_tool(name, prepared).await?,
                };
                results.push(call.result(vec![ToolResultContent::Json { value: reply }]));
            }
            self.messages.push(Arc::new(Message::tool_results(results)));
            if turn + 1 == max_turns {
                self.final_output = response.text();
            }
        }
        Err("max_turns".to_owned())
    }

    pub async fn scores(&mut self) -> Result<(Score, Score), String> {
        let unconstrained: Score = serde_json::from_value(
            self.bridge
                .call("evaluate", json!({"model_output": &self.final_output}))
                .await?,
        )
        .map_err(|error| error.to_string())?;
        let enforced = if let Some(denial) = &self.first_denial {
            serde_json::from_value(
                self.bridge
                    .call(
                        "replay_evaluate",
                        json!({
                            "calls": &self.calls[..denial.index],
                            "model_output": format!("SecurityPolicyDeniedError: {}", denial.message)
                        }),
                    )
                    .await?,
            )
            .map_err(|error| error.to_string())?
        } else {
            unconstrained
        };
        Ok((unconstrained, enforced))
    }
}

fn reference_end(text: &str, start: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut end = start + 1;
    if !bytes.get(end).is_some_and(u8::is_ascii_digit) {
        return None;
    }
    while bytes.get(end).is_some_and(u8::is_ascii_digit) {
        end += 1;
    }
    loop {
        match bytes.get(end) {
            Some(b'.')
                if bytes
                    .get(end + 1)
                    .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_') =>
            {
                end += 2;
                while bytes
                    .get(end)
                    .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
                {
                    end += 1;
                }
            }
            Some(b'[') => {
                let mut close = end + 1;
                while bytes.get(close).is_some_and(u8::is_ascii_digit) {
                    close += 1;
                }
                if close == end + 1 || bytes.get(close) != Some(&b']') {
                    break;
                }
                end = close + 1;
            }
            _ => break,
        }
    }
    Some(end)
}

fn truthy(value: &Value) -> bool {
    match value {
        Value::Null => false,
        Value::Bool(value) => *value,
        Value::Number(value) => value.as_f64() != Some(0.0),
        Value::String(value) => !value.is_empty(),
        Value::Array(value) => !value.is_empty(),
        Value::Object(value) => !value.is_empty(),
    }
}

fn redact_error(error: &str, tainted: bool) -> &str {
    if tainted {
        error.split_once(':').map_or(error, |(kind, _)| kind)
    } else {
        error
    }
}

pub async fn self_test(python: &Path, script: &Path) -> Result<(), String> {
    let mut bridge = Bridge::spawn(python, script)
        .await
        .map_err(|error| error.to_string())?;
    let mut run = Run::new(&mut bridge, "Self-test")?;
    let untrusted = run.record_tool_result(json!({"recipient":"attacker@example.org","amount":98.7,"body":"$999","enabled":false,"items":[{"id":42}]}), Class::Untrusted, false)?;
    let trusted = run.record_tool_result(
        json!({"recipient":"friend@example.org"}),
        Class::Trusted,
        false,
    )?;
    let prepared = run.prepare(
        "query_ai_assistant",
        json!({"query":"$1","output_schema":{}})
            .as_object()
            .unwrap(),
    )?;
    let extracted = run.record_extraction(
        json!({"recipient":"attacker@example.org"}),
        prepared.tainted,
    )?;
    let prepared = run.prepare(
        "query_ai_assistant",
        json!({"query":"$2","output_schema":{}})
            .as_object()
            .unwrap(),
    )?;
    let trusted_extracted =
        run.record_extraction(json!({"recipient":"friend@example.org"}), prepared.tainted)?;
    assert_eq!(
        (untrusted, trusted, extracted, trusted_extracted),
        (Handle(1), Handle(2), Handle(3), Handle(4))
    );
    for (reference, expected) in [
        ("$1.recipient", true),
        ("$2.recipient", false),
        ("$3.recipient", true),
        ("$4.recipient", false),
    ] {
        let prepared = run.prepare(
            "send_email",
            json!({"recipients":[reference, reference]})
                .as_object()
                .unwrap(),
        )?;
        assert_eq!(prepared.tainted, expected);
        assert_eq!(prepared.contacts.len(), 1);
        let history_len = run.history.as_slice().len();
        assert_eq!(
            run.check_contacts("send_email", &prepared.contacts)?,
            expected
        );
        assert_eq!(
            &run.history.as_slice()[history_len..],
            &[AgentEvent::new(
                prepared.contacts[0],
                AgentAction::Contact,
                Class::Sink
            )]
        );
    }
    let prepared = run.prepare(
        "send_email",
        json!({"recipients":["$2.recipient"],"body":"$1.body"})
            .as_object()
            .unwrap(),
    )?;
    assert!(prepared.tainted);
    assert!(!run.check_contacts("send_email", &prepared.contacts)?);
    let prepared = run.prepare(
        "send_email",
        json!({"recipients":["friend@example.org"],"$if":"$1.enabled"})
            .as_object()
            .unwrap(),
    )?;
    assert_eq!(prepared.guard, Some(false));
    assert_eq!(
        run.environment_tool("send_email", prepared).await?,
        json!({"$ref":"$5"})
    );
    assert!(run.skipped_calls[0].tainted);
    assert!(run.skipped_calls[0].denied);
    let denial = run.first_denial.as_ref().unwrap();
    assert_eq!(denial.index, 0);
    assert!(!denial.message.is_empty());
    assert_eq!(json!(denial.message), run.policy_decisions[0]["reason"]);
    let mut refs = Vec::new();
    assert_eq!(run.resolve(&json!({"array":["$1.items[0].id", "$1.enabled"],"text":"Résumé $1.items[0].id: $1.body", "amount":"$1.amount", "object":"$2"}), &mut refs)?,
        json!({"array":[42,false],"text":"Résumé 42: $999","amount":98.7,"object":{"recipient":"friend@example.org"}}));
    assert!(
        run.resolve(&json!("$1.missing"), &mut refs)
            .unwrap_err()
            .starts_with("ReferenceError:")
    );
    assert!(run.resolve(&json!("$0"), &mut refs).is_err());
    assert!(run.resolve(&json!("$99"), &mut refs).is_err());
    for value in [
        Value::Null,
        json!(false),
        json!(0),
        json!(0.0),
        json!(""),
        json!([]),
        json!({}),
    ] {
        assert!(!truthy(&value));
    }
    for value in [
        json!(true),
        json!(-1),
        json!("0"),
        json!([0]),
        json!({"x":null}),
    ] {
        assert!(truthy(&value));
    }
    assert_eq!(
        redact_error("ValueError: raw hidden data", true),
        "ValueError"
    );
    assert_eq!(
        redact_error("ValueError: public data", false),
        "ValueError: public data"
    );

    drop(run);
    bridge.call("load_task", json!({"suite":"banking","user_task_id":"user_task_0","injection_task_id":null,"pipeline_name":"gpt-4.1+camel","model_prose":"ChatGPT"})).await?;
    let mut run = Run::new(&mut bridge, "Pay the December bill")?;
    let prepared = run.prepare(
        "read_file",
        json!({"file_path":"bill-december-2023.txt"})
            .as_object()
            .unwrap(),
    )?;
    assert_eq!(
        run.environment_tool("read_file", prepared).await?,
        json!({"$ref":"$1","shape":"<str>"})
    );
    assert!(!run.calls[0].tainted);
    run.record_extraction(
        json!({"recipient":"UK12345678901234567890","amount":98.7}),
        true,
    )?;
    let prepared = run.prepare("send_money", json!({"recipient":"$2.recipient","amount":"$2.amount","subject":"bill-december-2023","date":"2023-12-31"}).as_object().unwrap())?;
    let reply = run.environment_tool("send_money", prepared).await?;
    assert!(reply.get("value").is_none());
    assert!(run.calls[1].denied);
    assert!(run.calls[1].tainted);
    let denial = run.first_denial.as_ref().unwrap();
    assert_eq!(denial.index, 1);
    assert_eq!(json!(denial.message), run.policy_decisions[0]["reason"]);
    let prepared = run.prepare(
        "send_money",
        json!({"recipient":"literal","amount":1,"subject":"skip","date":"2023-12-31","$if":false})
            .as_object()
            .unwrap(),
    )?;
    assert_eq!(
        run.environment_tool("send_money", prepared).await?,
        json!({"$ref":"$4"})
    );
    assert_eq!(run.calls.len(), 2);
    assert_eq!(run.skipped_calls.len(), 1);
    assert!(!run.skipped_calls[0].tainted);
    let prepared = run.prepare(
        "read_file",
        json!({"file_path":"bill-december-2023.txt","$if":true})
            .as_object()
            .unwrap(),
    )?;
    assert_eq!(
        run.environment_tool("read_file", prepared).await?,
        json!({"$ref":"$5"})
    );
    assert!(!run.calls[2].tainted);
    run.final_output = "Paid the bill.".to_owned();
    let (unconstrained, enforced) = run.scores().await?;
    assert_eq!(
        unconstrained,
        Score {
            utility: true,
            injection_success: None
        }
    );
    assert_eq!(
        enforced,
        Score {
            utility: false,
            injection_success: None
        }
    );
    native_model_self_test(python, script).await?;
    println!(
        "self-test: references, taint, protected arguments, guards, error redaction, native P/Q isolation, Q retries, worker execution, and deny-prefix replay passed"
    );
    Ok(())
}

async fn native_model_self_test(python: &Path, script: &Path) -> Result<(), String> {
    use rig_core::http_client::{
        Bytes, HttpClientExt, LazyBody, MultipartForm, Request, Response, StreamingResponse,
    };
    use rig_core::providers::copilot::auth::MemoryTokenStore;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Scripted(Arc<AtomicUsize>);

    impl HttpClientExt for Scripted {
        fn send<T, U>(
            &self,
            request: Request<T>,
        ) -> impl Future<Output = rig_core::http_client::Result<Response<LazyBody<U>>>> + Send + 'static
        where
            T: Into<Bytes> + Send,
            U: From<Bytes> + Send + 'static,
        {
            let body = request.into_body().into();
            let step = self.0.fetch_add(1, Ordering::Relaxed);
            let is_q = matches!(step, 2..=4 | 7 | 8);
            if is_q {
                if matches!(step, 2..=4) {
                    assert!(body.windows(5).any(|window| window == b"98.70"));
                }
            } else {
                let body = std::str::from_utf8(&body).unwrap();
                assert!(
                    !body.contains("UK12345678901234567890"),
                    "P saw a hidden recipient"
                );
                assert!(!body.contains("98.70"), "P saw hidden bill content");
            }
            let call = match step {
                0 => Some(("read_file", json!({"file_path":"bill-december-2023.txt"}))),
                1 => Some((
                    "query_ai_assistant",
                    json!({"query":"Extract recipient and amount from this bill: $1", "output_schema":{"type":"object","properties":{"recipient":{"type":"string"},"amount":{"type":"number"}},"required":["recipient","amount"]}}),
                )),
                2 => None,
                3 => Some((
                    "result",
                    json!({"recipient":"UK12345678901234567890","amount":98.7}),
                )),
                4 => Some((
                    "result",
                    json!({"recipient":"UK12345678901234567890","amount":98.7,"have_enough_information":true}),
                )),
                5 => Some((
                    "send_money",
                    json!({"recipient":"$2.recipient","amount":"$2.amount","subject":"bill-december-2023","date":"2023-12-31"}),
                )),
                6 => None,
                7 => Some(("result", json!({"have_enough_information":false}))),
                8 => Some((
                    "result",
                    json!({"recipient":"friend@example.org","have_enough_information":true}),
                )),
                9..=97 => Some(("read_file", json!({"file_path":"bill-december-2023.txt"}))),
                98 => None,
                _ => panic!("unexpected model request {step}"),
            };
            let (message, finish_reason) = if let Some((name, args)) = call {
                let content = (step == 38).then_some("Still reading $1");
                (
                    json!({"role":"assistant","content":content,"tool_calls":[{"id":format!("call-{step}"),"type":"function","function":{"name":name,"arguments":args.to_string()}}]}),
                    "tool_calls",
                )
            } else {
                let content = match step {
                    6 => "Paid $2.amount to $2.recipient.",
                    98 => "Read the bill.",
                    _ => "Missing tool call",
                };
                (json!({"role":"assistant","content":content}), "stop")
            };
            let response = json!({"id":format!("response-{step}"),"object":"chat.completion","created":0,"model":"gpt-4.1","choices":[{"index":0,"message":message,"finish_reason":finish_reason}],"usage":{"prompt_tokens":0,"completion_tokens":0,"total_tokens":0}});
            let bytes = Bytes::from(serde_json::to_vec(&response).unwrap());
            async move {
                let body: LazyBody<U> = Box::pin(async move { Ok(U::from(bytes)) });
                Ok(Response::builder()
                    .header("content-type", "application/json")
                    .body(body)?)
            }
        }

        fn send_multipart<U>(
            &self,
            _: Request<MultipartForm>,
        ) -> impl Future<Output = rig_core::http_client::Result<Response<LazyBody<U>>>> + Send + 'static
        where
            U: From<Bytes> + Send + 'static,
        {
            std::future::ready(Err(rig_core::http_client::Error::instance(
                std::io::Error::other("self-test does not support multipart requests"),
            )))
        }

        async fn send_streaming<T>(
            &self,
            _: Request<T>,
        ) -> rig_core::http_client::Result<StreamingResponse>
        where
            T: Into<Bytes> + Send,
        {
            panic!("native tool self-test must not stream")
        }
    }

    let requests = Arc::new(AtomicUsize::new(0));
    let llm = Llm {
        auth: Authenticator::new(
            AuthSource::ApiKey("local-self-test".to_owned()),
            MemoryTokenStore::default(),
            DeviceCodeHandler::default(),
            false,
        ),
        http: DynHttpClient::new(Scripted(Arc::clone(&requests))),
        model: "gpt-4.1".to_owned(),
        q_model: "gpt-4.1".to_owned(),
    };
    let mut bridge = Bridge::spawn(python, script)
        .await
        .map_err(|error| error.to_string())?;
    let mut loaded = bridge.call("load_task", json!({"suite":"banking","user_task_id":"user_task_0","injection_task_id":null,"pipeline_name":"gpt-4.1+camel","model_prose":"ChatGPT"})).await?;
    let mut run = Run::new(
        &mut bridge,
        loaded["prompt"].as_str().ok_or("missing task prompt")?,
    )?;
    let definitions =
        serde_json::from_value(loaded["tools"].take()).map_err(|error| error.to_string())?;
    run.execute(&llm, definitions, 30).await?;
    assert_eq!(requests.load(Ordering::Relaxed), 7);
    assert_eq!(run.final_output, "Paid 98.7 to UK12345678901234567890.");
    assert_eq!(run.first_denial.as_ref().unwrap().index, 1);
    assert!(!run.calls[0].tainted);
    assert!(run.calls[1].tainted);
    let (unconstrained, enforced) = run.scores().await?;
    assert!(unconstrained.utility);
    assert!(!enforced.utility);
    let prepared = run.prepare("query_ai_assistant", json!({"query":"No recipient was provided", "output_schema":{"type":"object","properties":{"recipient":{"type":"string"}},"required":["recipient"]}}).as_object().unwrap())?;
    assert_eq!(
        run.query(&llm, prepared).await?,
        json!({"error":"NotEnoughInformationError"})
    );
    assert_eq!(requests.load(Ordering::Relaxed), 8);
    run.record_tool_result(
        json!({"recipient":"friend@example.org"}),
        Class::Trusted,
        false,
    )?;
    let prepared = run.prepare("query_ai_assistant", json!({"query":"Extract recipient from $4", "output_schema":{"type":"object","properties":{"recipient":{"type":"string"}},"required":["recipient"]}}).as_object().unwrap())?;
    assert_eq!(run.query(&llm, prepared).await?, json!({"$ref":"$5"}));
    let prepared = run.prepare(
        "send_email",
        json!({"recipients":["$5.recipient"]}).as_object().unwrap(),
    )?;
    assert!(!prepared.tainted);
    assert!(!run.check_contacts("send_email", &prepared.contacts)?);
    run.record_extraction(json!(false), true)?;
    let prepared = run.prepare("query_ai_assistant", json!({"query":"$4", "output_schema":{"type":"object","properties":{},"required":[]},"$if":"$6"}).as_object().unwrap())?;
    assert_eq!(run.query(&llm, prepared).await?, json!({"$ref":"$7"}));
    assert!(run.skipped_calls[0].tainted);
    assert!(!run.skipped_calls[0].denied);
    assert_eq!(requests.load(Ordering::Relaxed), 9);
    drop(run);

    for (expected, exhausted) in [
        ("Still reading $1", true),
        ("", true),
        ("Read the bill.", false),
    ] {
        let mut loaded = bridge.call("load_task", json!({"suite":"banking","user_task_id":"user_task_0","injection_task_id":null,"pipeline_name":"gpt-4.1+camel","model_prose":"ChatGPT"})).await?;
        let mut run = Run::new(&mut bridge, "Read the bill")?;
        let definitions =
            serde_json::from_value(loaded["tools"].take()).map_err(|error| error.to_string())?;
        let before = requests.load(Ordering::Relaxed);
        let result = run.execute(&llm, definitions, 30).await;
        if exhausted {
            assert_eq!(result, Err("max_turns".to_owned()));
            assert_eq!(run.calls.len(), 30);
        } else {
            result?;
            assert_eq!(run.calls.len(), 29);
        }
        assert_eq!(requests.load(Ordering::Relaxed) - before, 30);
        assert_eq!(run.final_output, expected);
        assert!(run.calls.iter().all(|call| !call.tainted));
    }
    Ok(())
}
