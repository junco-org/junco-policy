use std::path::PathBuf;
use std::time::Duration;

use rig_core::completion::{CompletionRequest, CompletionResponse};
use rig_core::http_client::DynHttpClient;
use rig_core::providers::copilot::{
    self,
    auth::{AuthSource, Authenticator, DeviceCodeHandler, FileTokenStore},
};
use rig_core::providers::openai::OpenAIConfig;
use serde::Deserialize;
use serde_json::{Value, json};

pub struct Llm {
    backend: Backend,
    pub model: String,
    pub q_model: String,
}

enum Backend {
    Live {
        auth: Authenticator,
        http: DynHttpClient,
    },
    /// Replays one task's recorded model turns: the P-LLM's assistant messages verbatim and the
    /// Q-LLM's `result` arguments reconstructed from the values the run used downstream.
    Scripted(std::sync::Mutex<Script>),
}

#[derive(Default, Deserialize)]
pub struct Script {
    /// Recorded assistant messages, one per P-LLM turn.
    p: std::collections::VecDeque<Value>,
    /// `result` tool arguments (with `have_enough_information`), one per Q-LLM call.
    q: std::collections::VecDeque<Value>,
}

impl Llm {
    pub fn new(model: String, q_model: String) -> Result<Self, String> {
        let source = match std::env::var("GITHUB_TOKEN") {
            Ok(token) if !token.is_empty() => AuthSource::GitHubAccessToken(token),
            _ => AuthSource::OAuth,
        };
        let home = std::env::var_os("HOME").ok_or("HOME is not set")?;
        Ok(Self::live(
            Authenticator::new(
                source,
                FileTokenStore::new(PathBuf::from(home).join(".config/junco-policy/copilot")),
                DeviceCodeHandler::default(),
                true,
            ),
            rig_reqwest::shared(),
            model,
            q_model,
        ))
    }

    pub fn live(auth: Authenticator, http: DynHttpClient, model: String, q_model: String) -> Self {
        Self {
            backend: Backend::Live { auth, http },
            model,
            q_model,
        }
    }

    /// A model that answers from [`Llm::load_script`] instead of a provider.
    pub fn scripted(model: String, q_model: String) -> Self {
        Self {
            backend: Backend::Scripted(std::sync::Mutex::new(Script::default())),
            model,
            q_model,
        }
    }

    pub fn load_script(&self, script: Script) -> Result<(), String> {
        match &self.backend {
            Backend::Scripted(current) => {
                *current.lock().map_err(|error| error.to_string())? = script;
                Ok(())
            }
            Backend::Live { .. } => Err("a live model takes no script".to_owned()),
        }
    }

    /// A P-LLM turn.
    pub async fn complete(&self, request: CompletionRequest) -> Result<CompletionResponse, String> {
        match &self.backend {
            Backend::Live { .. } => self.call(&self.model, request).await,
            Backend::Scripted(script) => {
                let message = script
                    .lock()
                    .map_err(|error| error.to_string())?
                    .p
                    .pop_front()
                    .ok_or("script exhausted: the recorded run had no further P-LLM turn")?;
                scripted_response(message["content"].clone(), message["origin"].clone())
            }
        }
    }

    /// A Q-LLM extraction.
    pub async fn extract(&self, request: CompletionRequest) -> Result<CompletionResponse, String> {
        match &self.backend {
            Backend::Live { .. } => self.call(&self.q_model, request).await,
            Backend::Scripted(script) => {
                let arguments = script
                    .lock()
                    .map_err(|error| error.to_string())?
                    .q
                    .pop_front()
                    .ok_or("script exhausted: the recorded run had no further Q-LLM call")?;
                scripted_response(
                    json!([{"type":"toolcall","id":{"provider":"scripted"},"function":{"name":"result","arguments":arguments}}]),
                    json!({"api":"openai.chat","provider":"scripted","model":self.q_model}),
                )
            }
        }
    }

    async fn call(
        &self,
        model: &str,
        request: CompletionRequest,
    ) -> Result<CompletionResponse, String> {
        let Backend::Live { auth, http } = &self.backend else {
            unreachable!("call is only reached from the live backend");
        };
        let mut last_error = String::new();
        let mut attempt = 0;
        let mut throttled = 0;
        while attempt <= 5 {
            let result = async {
                let context = auth
                    .auth_context(http)
                    .await
                    .map_err(|error| error.to_string())?;
                let mut config =
                    OpenAIConfig::with_key(&copilot::DIALECT, context.api_key.expose());
                if let Some(base) = context.api_base {
                    config = config.with_base_url(base);
                }
                config
                    .connect(http.clone())
                    .completion(model)
                    .call(request.clone())
                    .await
                    .map_err(|error| error.to_string())
            }
            .await;
            match result {
                Ok(response) => return Ok(response),
                // shortcut: rig drops Copilot's Retry-After (hours for the per-user quota), so
                // poll every 10 minutes for up to 8 hours; read the header if rig exposes it.
                Err(error) if error.contains("status 429") && throttled < 48 => {
                    throttled += 1;
                    tokio::time::sleep(Duration::from_secs(600)).await;
                    continue;
                }
                Err(error) => last_error = error,
            }
            if attempt < 5 {
                tokio::time::sleep(Duration::from_secs(1 << attempt)).await;
            }
            attempt += 1;
        }
        Err(format!(
            "model {model} failed after provider retries: {last_error}"
        ))
    }
}

fn scripted_response(choice: Value, origin: Value) -> Result<CompletionResponse, String> {
    serde_json::from_value(json!({"choice": choice, "usage": {}, "origin": origin, "raw": {}}))
        .map_err(|error| format!("recorded turn is not a completion: {error}"))
}
