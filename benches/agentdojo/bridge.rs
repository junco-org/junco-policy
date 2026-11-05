use std::io;
use std::path::Path;
use std::process::Stdio;

use serde_json::{Value, json};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, ChildStdin, ChildStdout, Command};

pub const SCRIPT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/benches/agentdojo/bridge.py");

pub struct Bridge {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    next_id: u64,
}

impl Bridge {
    pub async fn spawn(python: &Path, script: &Path) -> io::Result<Self> {
        let mut child = Command::new(python)
            .arg(script)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .kill_on_drop(true)
            .spawn()?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| io::Error::other("missing worker stdin"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| io::Error::other("missing worker stdout"))?;
        Ok(Self {
            child,
            stdin,
            stdout: BufReader::new(stdout),
            next_id: 0,
        })
    }

    pub async fn call(&mut self, method: &str, params: Value) -> Result<Value, String> {
        let id = self.next_id;
        self.next_id += 1;
        let mut request =
            serde_json::to_vec(&json!({"id": id, "method": method, "params": params}))
                .map_err(|error| error.to_string())?;
        request.push(b'\n');
        self.stdin
            .write_all(&request)
            .await
            .map_err(|error| format!("worker write: {error}"))?;
        self.stdin
            .flush()
            .await
            .map_err(|error| format!("worker flush: {error}"))?;
        let mut line = String::new();
        let read = self
            .stdout
            .read_line(&mut line)
            .await
            .map_err(|error| format!("worker read: {error}"))?;
        if read == 0 {
            return Err(format!(
                "worker closed stdout (status: {:?})",
                self.child.try_wait()
            ));
        }
        let mut response: Value =
            serde_json::from_str(&line).map_err(|error| format!("worker JSON: {error}"))?;
        if response.get("id").and_then(Value::as_u64) != Some(id) {
            return Err(format!("worker response id does not match request {id}"));
        }
        if let Some(error) = response.get("error") {
            return Err(error
                .as_str()
                .unwrap_or("worker returned a non-string error")
                .to_owned());
        }
        response
            .get_mut("result")
            .map(Value::take)
            .ok_or_else(|| "worker response has no result".to_owned())
    }
}
