//! Evidence for `cognition.live-bridge.parse-and-replay`: a REAL-format Anthropic
//! Messages response parses into a unified four-stream session that replays through
//! the in-tree astream substrate deterministically and forks coherently. The two
//! non-hermetic steps — the keyed API call (`capture_live`, via `curl`) and the
//! un-keyed `claude` CLI call (`capture_via_cli`) — are both `#[ignore]` tests at
//! the bottom of this file and are NOT exercised by the claim's command. Neither
//! runs the tool the model called: `unified_from_capture` takes the tool output
//! and clock from the caller (placeholders, here and in the `capture` binary).

use astream_agent::cog::{CogRecord, StopReason};
use astream_agent::unified::Event;
use astream_agent::{fork_session, replay_session};
use astream_live::json::{self, Json};
use astream_live::{capture_live, capture_via_cli, parse_completion, unified_from_capture};

/// A real-shape Anthropic Messages API response (the documented JSON), so the parse
/// is tested against the actual format — including a nested tool `input` object.
const REAL_FORMAT_RESPONSE: &str = r#"{
  "id": "msg_01XYZ",
  "type": "message",
  "role": "assistant",
  "model": "claude-sonnet-4-6",
  "content": [
    {"type": "text", "text": "Let me build the project."},
    {"type": "tool_use", "id": "toolu_01ABC", "name": "bash", "input": {"command": "make build", "timeout": 120}}
  ],
  "stop_reason": "tool_use",
  "usage": {"input_tokens": 12, "output_tokens": 34}
}"#;

#[test]
fn a_real_format_response_parses_and_replays_deterministically() {
    let completion = parse_completion(REAL_FORMAT_RESPONSE).expect("parse");
    match &completion {
        CogRecord::Completion { text, calls, stop } => {
            assert!(text.contains("build"), "text parsed");
            assert_eq!(calls.len(), 1, "one tool call parsed");
            assert_eq!(calls[0].name, "bash");
            // the nested input object survived as opaque bytes
            assert!(String::from_utf8_lossy(&calls[0].input).contains("make build"));
            assert_eq!(*stop, StopReason::ToolUse);
        }
        _ => panic!("expected a Completion"),
    }

    // Assemble the unified four-stream session and replay it — deterministically.
    let events = unified_from_capture(completion, "BUILD FAILED: 1 error", true, 1_700_000_000);
    let a = replay_session(&events, 80, 12);
    let b = replay_session(&events, 80, 12);
    assert_eq!(
        a, b,
        "a captured turn replays bit-identically through astream"
    );
    assert_eq!(
        a.inputs_applied, 1,
        "the captured command is an Input stream event"
    );
    assert!(
        !a.decisions.is_empty(),
        "the captured turn produced decisions"
    );

    // And forks coherently: swapping the captured tool result re-drives the policy.
    let forked = fork_session(
        &events,
        4,
        Event::Cognition(CogRecord::ToolResult {
            tool_use_id: "toolu_01ABC".into(),
            content: b"BUILD OK".to_vec(),
            is_error: false,
        }),
    );
    let f = replay_session(&forked, 80, 12);
    assert_ne!(
        f.decisions, a.decisions,
        "the forked turn decides differently"
    );
}

#[test]
fn parse_rejects_malformed_responses() {
    assert!(parse_completion("not json").is_err());
    assert!(parse_completion(r#"{"no_content":true}"#).is_err());
}

#[test]
fn parse_captures_multiple_text_and_tool_use_blocks_in_order() {
    // A real response can interleave several text blocks and emit more than one
    // tool_use; the bridge must preserve every call, in order, with its nested
    // input intact — not just the first.
    let resp = r#"{
      "content": [
        {"type": "text", "text": "First I will build, "},
        {"type": "text", "text": "then run the tests."},
        {"type": "tool_use", "id": "toolu_1", "name": "bash", "input": {"command": "make build"}},
        {"type": "tool_use", "id": "toolu_2", "name": "bash", "input": {"command": "make test", "env": {"RUST_LOG": "debug"}}}
      ],
      "stop_reason": "tool_use"
    }"#;
    let completion = parse_completion(resp).expect("parse");
    match &completion {
        CogRecord::Completion { text, calls, stop } => {
            assert_eq!(
                text, "First I will build, then run the tests.",
                "text blocks concatenated in order"
            );
            assert_eq!(calls.len(), 2, "both tool calls captured");
            assert_eq!(calls[0].id, "toolu_1");
            assert_eq!(calls[1].id, "toolu_2");
            // The second call's nested object survives faithfully (incl. the env map).
            let second = std::str::from_utf8(&calls[1].input).unwrap();
            assert!(
                second.contains("make test") && second.contains("RUST_LOG"),
                "nested input intact: {second}"
            );
            assert_eq!(*stop, StopReason::ToolUse);
        }
        _ => panic!("expected a Completion"),
    }
    // The assembled turn still replays deterministically.
    let events = unified_from_capture(completion, "ok", false, 1_700_000_000);
    assert_eq!(
        replay_session(&events, 80, 12),
        replay_session(&events, 80, 12)
    );
}

#[test]
fn parse_is_faithful_and_panic_free_on_adversarial_input() {
    // The nested tool input is re-serialized to FAITHFUL, round-trippable bytes:
    // a command containing a quote, a newline, a backslash, and a control byte is
    // escaped, so none of them can corrupt the payload that lands on the durable,
    // forkable log — and the bytes re-parse to the same value.
    let resp = r#"{"content":[{"type":"tool_use","id":"t","name":"bash","input":{"command":"echo \"hi\"","script":"a\nb\\c\td\u0001e","n":9007199254740993}}],"stop_reason":"tool_use"}"#;
    let completion = parse_completion(resp).expect("parse");
    if let CogRecord::Completion { calls, .. } = &completion {
        let s = std::str::from_utf8(&calls[0].input).expect("input bytes are valid utf8");
        assert!(
            s.contains(r#"echo \"hi\""#),
            "the quoted command survives escaped: {s}"
        );
        assert!(
            s.contains(r#"a\nb\\c\td\u0001e"#),
            "newline, backslash, tab and a control byte survive escaped: {s}"
        );
        assert!(
            !s.contains('\n') && !s.contains('\u{1}'),
            "no raw newline/control byte reaches the payload: {s:?}"
        );
        assert!(
            s.contains("9007199254740993"),
            "a >2^53 integer survives verbatim: {s}"
        );
        // Round-trippable: the payload re-parses to the SAME value the API sent.
        let reparsed = json::parse(s).expect("the payload is valid JSON");
        assert_eq!(
            reparsed.get("script").and_then(Json::as_str),
            Some("a\nb\\c\td\u{1}e"),
            "the escaped string decodes back to the original"
        );
        assert_eq!(
            reparsed.get("command").and_then(Json::as_str),
            Some("echo \"hi\"")
        );
    } else {
        panic!("expected a Completion");
    }

    // A non-RFC number lexeme in the tool input (`007`, `1.`) — realistic on the
    // CLI path, where the JSON is model-authored text — is REJECTED, never
    // re-emitted verbatim onto the log for a real JSON consumer to choke on.
    for bad in [r#"{"timeout":007}"#, r#"{"ratio":1.}"#, r#"{"x":-.5}"#] {
        let resp = format!(
            r#"{{"content":[{{"type":"tool_use","id":"t","name":"bash","input":{bad}}}],"stop_reason":"tool_use"}}"#
        );
        assert!(
            parse_completion(&resp).is_err(),
            "a non-JSON number lexeme must be rejected: {bad}"
        );
    }

    // Adversarial responses are rejected WITHOUT panicking: deeply-nested input
    // (a stack-overflow attempt) and an ill-formed surrogate escape both Err.
    let deep = format!(r#"{{"content":{}"#, "[".repeat(500));
    assert!(
        parse_completion(&deep).is_err(),
        "deep nesting must Err, not overflow"
    );
    assert!(
        parse_completion(r#"{"content":[{"type":"text","text":"\uD800x"}]}"#).is_err(),
        "an ill-formed surrogate must Err, not panic"
    );
}

/// LIVE (CLI): capture one real turn via the authenticated `claude` CLI — NO API
/// key, it uses the local Claude Code session — and replay it. Requires the
/// `claude` CLI; the capture is non-deterministic, so `#[ignore]` (run with
/// `cargo test -p astream-live -- --ignored`). The CAPTURE varies run to run, but
/// the REPLAY of whatever was captured is deterministic — that is what is asserted.
/// The tool result and clock passed below are PLACEHOLDERS: the tool is not run.
#[test]
#[ignore]
fn a_cli_captured_turn_replays() {
    let completion = capture_via_cli("Build the Rust workspace and report whether it compiles")
        .expect("cli capture (needs the authenticated `claude` CLI)");
    let events = unified_from_capture(completion, "BUILD OK: 0 errors", false, 1_700_000_000);
    let a = replay_session(&events, 80, 12);
    let b = replay_session(&events, 80, 12);
    assert_eq!(a, b, "the captured turn replays bit-identically");
    assert!(
        !a.decisions.is_empty(),
        "the captured turn produced decisions"
    );
    println!(
        "CLI live turn captured + replayed: {} decisions, {} inputs, screen_hash={:016x}",
        a.decisions.len(),
        a.inputs_applied,
        a.screen_hash
    );
}

/// LIVE: capture one real turn and replay it. Requires `ANTHROPIC_API_KEY` + network;
/// run with `cargo test -p astream-live -- --ignored`. Non-deterministic capture, so
/// NOT a hermetic claim — it demonstrates the bridge over a real completion. The
/// tool result and clock passed below are PLACEHOLDERS: the tool is not run.
#[test]
#[ignore]
fn a_live_captured_turn_replays() {
    let completion = capture_live(
        "Use the bash tool to run `make build`, then stop. Respond with a tool call.",
        "claude-sonnet-4-6",
    )
    .expect("live capture (needs ANTHROPIC_API_KEY)");
    let events = unified_from_capture(completion, "BUILD OK: 0 errors", false, 1_700_000_000);
    let r = replay_session(&events, 80, 12);
    assert!(!r.decisions.is_empty());
    println!(
        "LIVE turn captured + replayed: {} decisions, {} inputs, screen_hash={:016x}",
        r.decisions.len(),
        r.inputs_applied,
        r.screen_hash
    );
}
