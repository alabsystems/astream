#![forbid(unsafe_code)]
//! `astream-live` — the live-capture bridge: a real Anthropic Messages turn becomes
//! a unified four-stream session that replays through the in-tree substrate.
//!
//! This is the master seed's **non-hermetic** step. The capture is a real model
//! call, so its output differs run to run and can never be a green (SHA-pinned)
//! claim — but the two deterministic halves *are* gated: the response-format
//! **parse** ([`parse_completion`]) and the **replay** of a captured turn (via
//! `astream_agent::replay_session`). `cargo test -p astream-live` proves both with a
//! real-format fixture. The live half runs over either of TWO non-hermetic paths,
//! both `#[ignore]`-gated: [`capture_live`] (a key-gated `curl` to the Messages
//! API) or [`capture_via_cli`] (the authenticated `claude` CLI — **no key
//! needed**; it uses the local session).
//!
//! ### Honest boundary
//!
//! What either path captures is the model's **completion** (its text and the
//! tool call it chose). Neither path runs that tool: [`unified_from_capture`]
//! takes the tool output, its error flag, and the effect clock value from the
//! CALLER, so the In/Effect/Out/ToolResult events of the assembled session are
//! whatever the caller supplied (the `capture` binary and the `#[ignore]` tests
//! pass fixed placeholders). A real tool run under a recording seam is a
//! documented seed, not something this crate does. And the `claude` CLI path asks
//! the model to *write* a Messages-shaped JSON object as text, so its `tool_use`
//! block is model-authored prose in that shape, not an API-emitted tool_use block.
//!
//! Zero third-party dependencies: a real JSON parser is hand-rolled ([`json`]) and
//! the live call shells out via `std::process` (`curl` / `claude`), so this crate
//! joins the workspace without diluting astream's reproducible-build graph.

pub mod json;

use astream_agent::cog::{CogRecord, StopReason, ToolUse};
use astream_agent::unified::Event;
use astream_effects::EffectRecord;
use json::Json;

/// Parse one Anthropic Messages API response into a [`CogRecord::Completion`]: its
/// text, the tool calls it emitted (inputs kept as opaque JSON bytes), and why it
/// stopped. Returns an error on malformed input (never panics).
pub fn parse_completion(response: &str) -> Result<CogRecord, String> {
    let v = json::parse(response)?;
    let content = v
        .get("content")
        .and_then(Json::as_array)
        .ok_or("response has no `content` array")?;
    let mut text = String::new();
    let mut calls = Vec::new();
    for block in content {
        match block.get("type").and_then(Json::as_str) {
            Some("text") => {
                if let Some(t) = block.get("text").and_then(Json::as_str) {
                    text.push_str(t);
                }
            }
            Some("tool_use") => {
                calls.push(ToolUse {
                    id: block
                        .get("id")
                        .and_then(Json::as_str)
                        .unwrap_or("")
                        .to_string(),
                    name: block
                        .get("name")
                        .and_then(Json::as_str)
                        .unwrap_or("")
                        .to_string(),
                    input: render_input(block.get("input")),
                });
            }
            _ => {}
        }
    }
    let stop = match v.get("stop_reason").and_then(Json::as_str) {
        Some("tool_use") => StopReason::ToolUse,
        _ => StopReason::EndTurn,
    };
    Ok(CogRecord::Completion { text, calls, stop })
}

/// Escape a string for embedding in a JSON document: the two structural bytes
/// (`"` and `\`) and every C0 control character (< 0x20) become an escape
/// sequence. Without this, a tool-input string (or a `model` argument) containing
/// a quote or newline would break out of the surrounding JSON — producing
/// invalid, non-round-trippable bytes on the durable log.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Re-serialize a tool `input` object to deterministic, **valid, round-trippable**
/// JSON bytes (the opaque payload the cognition model keeps). String contents and
/// object keys are JSON-escaped, and numbers are re-emitted from their preserved
/// raw lexeme — so `parse_completion`'s `parse(render_input(x)) == x` holds even
/// for inputs with quotes, control bytes, or integers larger than `2^53`. Object
/// keys are emitted in their parsed order.
fn render_input(input: Option<&Json>) -> Vec<u8> {
    fn write(out: &mut String, j: &Json) {
        match j {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => out.push_str(n),
            Json::Str(s) => {
                out.push('"');
                out.push_str(&json_escape(s));
                out.push('"');
            }
            Json::Arr(a) => {
                out.push('[');
                for (i, e) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write(out, e);
                }
                out.push(']');
            }
            Json::Obj(entries) => {
                out.push('{');
                for (i, (k, val)) in entries.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push('"');
                    out.push_str(&json_escape(k));
                    out.push_str("\":");
                    write(out, val);
                }
                out.push('}');
            }
        }
    }
    let mut s = String::new();
    match input {
        Some(j) => write(&mut s, j),
        None => s.push_str("{}"),
    }
    s.into_bytes()
}

/// Assemble a unified session spanning ALL FOUR streams from a captured completion
/// plus a CALLER-SUPPLIED account of its first tool call: the **Cognition** of the
/// completion, the **Input** command it issued (the first tool call's raw input
/// bytes), an **Effect** (`Clock(clock)`, the value given), the tool **Output**
/// (`tool_output`, verbatim), and the **Cognition** of the tool result (the same
/// `tool_output` + `is_error`, answering the first call's id).
///
/// This function does NOT run the tool or read a clock: it is a pure assembler.
/// `tool_output`/`is_error`/`clock` are whatever the caller passes — a real tool
/// result if the caller ran one, or a placeholder (as the `capture` binary and the
/// `#[ignore]` live tests pass) if not.
pub fn unified_from_capture(
    completion: CogRecord,
    tool_output: &str,
    is_error: bool,
    clock: u64,
) -> Vec<Event> {
    let (tool_id, cmd) = match &completion {
        CogRecord::Completion { calls, .. } => calls
            .first()
            .map(|c| (c.id.clone(), c.input.clone()))
            .unwrap_or_default(),
        _ => (String::new(), Vec::new()),
    };
    vec![
        Event::Cognition(completion),
        Event::In(cmd),
        Event::Effect(EffectRecord::Clock(clock)),
        Event::Out(tool_output.as_bytes().to_vec()),
        Event::Cognition(CogRecord::ToolResult {
            tool_use_id: tool_id,
            content: tool_output.as_bytes().to_vec(),
            is_error,
        }),
    ]
}

/// Strip an optional ```json … ``` markdown fence the model may wrap output in,
/// so a fenced completion still parses.
fn strip_fences(s: &str) -> &str {
    let t = s.trim();
    let t = t
        .strip_prefix("```json")
        .or_else(|| t.strip_prefix("```"))
        .unwrap_or(t);
    t.strip_suffix("```").unwrap_or(t).trim()
}

/// Capture ONE real model turn via the authenticated `claude` CLI — **no API key
/// required**, because the CLI uses the local Claude Code session. The model is
/// asked to emit a raw Anthropic Messages response calling a `bash` tool to
/// accomplish `task`; its completion is parsed by [`parse_completion`]. Like
/// [`capture_live`] this is a NON-hermetic step (a real, non-deterministic model
/// call), so it is a runnable tool, never a green claim — but unlike the key-gated
/// `curl` path it runs wherever the `claude` CLI is authenticated, with no key
/// gate at all. Because the model WRITES the Messages-shaped JSON as text, the
/// `tool_use` block is model-authored prose in that shape, not an API-emitted
/// block. Shells out via `std::process` (zero new deps).
pub fn capture_via_cli(task: &str) -> Result<CogRecord, String> {
    let prompt = format!(
        "You are an assistant with a `bash` tool. Respond with ONLY a raw JSON object \
         (no markdown fences, no prose) in EXACTLY this Anthropic Messages API response shape: \
         {{\"content\":[{{\"type\":\"text\",\"text\":\"<one short sentence of reasoning>\"}},\
         {{\"type\":\"tool_use\",\"id\":\"toolu_01\",\"name\":\"bash\",\
         \"input\":{{\"command\":\"<a single shell command>\"}}}}],\"stop_reason\":\"tool_use\"}}. \
         The task: {task}"
    );
    let out = std::process::Command::new("claude")
        .args(["-p", &prompt, "--output-format", "json"])
        .output()
        .map_err(|e| format!("claude cli: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "claude cli failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    // The CLI may print a one-time notice line before the JSON result object; skip
    // to the first `{` so a preamble doesn't break the parse.
    let raw = String::from_utf8_lossy(&out.stdout);
    let start = raw.find('{').ok_or("claude cli produced no JSON result")?;
    let wrapper = json::parse(raw[start..].trim_end())?;
    let result = wrapper
        .get("result")
        .and_then(Json::as_str)
        .ok_or("claude cli output has no `result` string")?;
    parse_completion(strip_fences(result))
}

/// Capture ONE real turn from the Anthropic Messages API (key-gated, non-hermetic).
/// The curl config line carrying the API key. The value sits in a quoted config
/// string, so a key holding a quote, a backslash or a line break could end it and
/// inject further curl directives; real keys are printable ASCII without either,
/// so anything else is refused rather than escaped.
fn curl_key_header(key: &str) -> Result<String, String> {
    if key.is_empty()
        || !key
            .bytes()
            .all(|b| b.is_ascii_graphic() && b != b'"' && b != b'\\')
    {
        return Err(
            "ANTHROPIC_API_KEY must be non-empty printable ASCII with no quote or backslash"
                .to_string(),
        );
    }
    Ok(format!("header = \"x-api-key: {key}\"\n"))
}

/// Shells out to `curl` so no HTTP/TLS crate is pulled in. Returns the completion as
/// a [`CogRecord`]; feed it to [`unified_from_capture`] then replay it in-tree.
pub fn capture_live(prompt: &str, model: &str) -> Result<CogRecord, String> {
    use std::io::Write;
    use std::process::Stdio;

    let key =
        std::env::var("ANTHROPIC_API_KEY").map_err(|_| "ANTHROPIC_API_KEY not set".to_string())?;
    // Both interpolated values are JSON-escaped: an unescaped `model` (or prompt)
    // containing a quote would corrupt the request body (JSON injection).
    let body = format!(
        concat!(
            "{{\"model\":\"{}\",\"max_tokens\":1024,",
            "\"tools\":[{{\"name\":\"bash\",\"description\":\"run a shell command\",",
            "\"input_schema\":{{\"type\":\"object\",\"properties\":{{\"command\":{{\"type\":\"string\"}}}},\"required\":[\"command\"]}}}}],",
            "\"messages\":[{{\"role\":\"user\",\"content\":\"{}\"}}]}}"
        ),
        json_escape(model),
        json_escape(prompt)
    );
    // The API key goes to curl via a config file on **stdin** (`-K -`), never argv,
    // so it does not leak to other local users through `ps`/`/proc`.
    let header = curl_key_header(&key)?;
    let mut child = std::process::Command::new("curl")
        .args([
            "-sS",
            "-m",
            "60",
            "https://api.anthropic.com/v1/messages",
            "-H",
            "content-type: application/json",
            "-H",
            "anthropic-version: 2023-06-01",
            "-d",
            &body,
            "-K",
            "-",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("curl: {e}"))?;
    {
        let stdin = child.stdin.as_mut().ok_or("curl: stdin unavailable")?;
        stdin
            .write_all(header.as_bytes())
            .map_err(|e| format!("curl stdin: {e}"))?;
    }
    // `wait_with_output` closes stdin (curl sees EOF on its config) then collects output.
    let out = child.wait_with_output().map_err(|e| format!("curl: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "curl failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    parse_completion(&String::from_utf8_lossy(&out.stdout))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `render_input` produces valid JSON that re-parses to the same value — even
    /// for inputs with quotes, backslashes, control bytes, and large integers,
    /// the cases the unescaped re-serializer corrupted.
    fn round_trips(src: &str) {
        let parsed = json::parse(src).expect("fixture parses");
        let rendered = render_input(Some(&parsed));
        let text = std::str::from_utf8(&rendered).expect("render is valid utf8");
        let reparsed =
            json::parse(text).unwrap_or_else(|e| panic!("render must be valid JSON: {e} ({text})"));
        assert_eq!(parsed, reparsed, "render_input is not injective for {src}");
    }

    #[test]
    fn render_input_round_trips_adversarial_inputs() {
        round_trips(r#"{"command":"echo \"hi\" && ls"}"#);
        round_trips(r#"{"path":"C:\\Users\\x","note":"line1\nline2\ttab"}"#);
        round_trips(r#"{"id":9007199254740993,"ratio":-3.5e10}"#);
        round_trips(r#"{"nested":{"a":[1,"x\"y",true,null]}}"#);
    }

    #[test]
    fn render_input_escapes_so_a_quote_cannot_break_structure() {
        let j = json::parse(r#"{"command":"a\"b"}"#).unwrap();
        let bytes = render_input(Some(&j));
        let text = std::str::from_utf8(&bytes).unwrap();
        // The embedded quote is escaped, not raw — so it cannot terminate the value.
        assert!(text.contains(r#"a\"b"#), "quote must stay escaped: {text}");
    }

    #[test]
    fn an_api_key_cannot_inject_curl_config() {
        assert_eq!(
            curl_key_header("sk-ant-api03-AbC_09").unwrap(),
            "header = \"x-api-key: sk-ant-api03-AbC_09\"\n"
        );
        for bad in [
            "",
            "k\"\nurl = \"http://evil\"",
            "k\\x",
            "k y",
            "k\r",
            "k\u{e9}",
        ] {
            assert!(curl_key_header(bad).is_err(), "{bad:?} must be refused");
        }
    }
}
