//! Evidence for `term.session.unified-replay-and-fork`: a whole session — all four
//! streams of the determinism dial (Inputs, Outputs, Effects, Cognition) on ONE
//! offset axis — replays deterministically, and a counterfactual fork of ONE
//! recorded cognition record makes all four streams diverge coherently. The master
//! seed's hermetic form.

use astream_agent::cog::{CogRecord, StopReason, ToolUse};
use astream_agent::unified::Event;
use astream_agent::{fork_session, replay_session};
use astream_effects::EffectRecord;
use astream_term::Screen;

const COLS: u16 = 60;
const ROWS: u16 = 12;
const FAILED_IDX: usize = 5; // the FAILED tool result in the session below

fn completion(text: &str, tool: Option<&str>) -> CogRecord {
    CogRecord::Completion {
        text: text.into(),
        calls: tool
            .map(|t| {
                vec![ToolUse {
                    id: t.into(),
                    name: "bash".into(),
                    input: b"cmd".to_vec(),
                }]
            })
            .unwrap_or_default(),
        stop: if tool.is_some() {
            StopReason::ToolUse
        } else {
            StopReason::EndTurn
        },
    }
}

fn tool_result(id: &str, content: &str, is_error: bool) -> CogRecord {
    CogRecord::ToolResult {
        tool_use_id: id.into(),
        content: content.as_bytes().to_vec(),
        is_error,
    }
}

/// A unified session interleaving all four streams. The build's tool result FAILED
/// (index 5), so the agent recovers; the recovery output appears only because the
/// recovery records are reached.
fn session() -> Vec<Event> {
    vec![
        Event::Cognition(completion("let me build", Some("t1"))), // 0: CallTool
        Event::In(b"make build\n".to_vec()),                      // 1: input
        Event::Out(b"$ make build\r\nbuilding...\r\n".to_vec()),  // 2: screen
        Event::Effect(EffectRecord::Clock(1234)),                 // 3: effect
        Event::Effect(EffectRecord::Rand(99)),                    // 4: effect
        Event::Cognition(tool_result("t1", "FAILED", true)),      // 5: Speak (recover)
        Event::Cognition(completion("let me recover", Some("t2"))), // 6: CallTool
        Event::In(b"fix\n".to_vec()),                             // 7: input
        Event::Out(b"$ fix\r\nrecovered cleanly\r\n".to_vec()),   // 8: screen (recovery)
        Event::Effect(EffectRecord::Clock(5678)),                 // 9: effect
        Event::Cognition(tool_result("t2", "ok", false)),         // 10: Finish
        Event::Out(b"$ exit\r\n".to_vec()),                       // 11: NOT reached
    ]
}

fn text(s: &Screen) -> String {
    let (_, rows) = s.dims();
    (0..rows)
        .map(|r| s.line_text(r))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn unified_session_replays_deterministically_and_forks_all_four_streams() {
    let events = session();

    // Deterministic replay: every stream reconstructs bit-identically twice.
    let a = replay_session(&events, COLS, ROWS);
    let b = replay_session(&events, COLS, ROWS);
    assert_eq!(a, b, "the unified session replays bit-identically");

    // The original session recovers — the recovery output is on the screen.
    assert!(
        text(&a.screen).contains("recovered"),
        "original reaches recovery"
    );
    assert_eq!(a.inputs_applied, 2, "both inputs reached");

    // FORK: swap the ONE FAILED tool result for a clean one.
    let forked = fork_session(
        &events,
        FAILED_IDX,
        Event::Cognition(tool_result("t1", "ok", false)),
    );
    let f = replay_session(&forked, COLS, ROWS);

    // ALL FOUR streams diverge coherently from that single swap:
    // Cognition — the decision trace is shorter and differs.
    assert_ne!(
        f.decisions, a.decisions,
        "cognition: decision trace diverges"
    );
    assert!(f.decisions.len() < a.decisions.len());
    assert_eq!(a.decisions[0], f.decisions[0], "shared decision prefix");
    // Outputs — the screen omits the unreached recovery output, and its hash moves.
    assert!(
        !text(&f.screen).contains("recovered"),
        "outputs: recovery never painted"
    );
    assert_ne!(
        f.screen_hash, a.screen_hash,
        "outputs: screen (pixels) diverge"
    );
    // Inputs — fewer keystrokes were reached.
    assert!(f.inputs_applied < a.inputs_applied, "inputs: fewer reached");
    // Effects — fewer effects were folded.
    assert_ne!(f.effect_digest, a.effect_digest, "effects: digest diverges");
    // And the whole session reached fewer events.
    assert!(
        f.events_reached < a.events_reached,
        "the forked turn finishes earlier"
    );
}

/// The effects stream is compared through `effect_digest`, so that digest must be
/// as discriminating as the records: a value-only fold made `Clock(v)` and
/// `Rand(v)` (and a file read moved to a different path with the same bytes)
/// digest identically — a swap the "effects reconstruct bit-identically" check
/// could not see. Each of these single-record swaps must move the digest.
#[test]
fn effect_digest_is_kind_and_path_aware() {
    let events = session();
    let base = replay_session(&events, COLS, ROWS);
    let swaps: Vec<(usize, Event, &str)> = vec![
        (
            3,
            Event::Effect(EffectRecord::Rand(1234)),
            "Clock(v) -> Rand(v)",
        ),
        (
            4,
            Event::Effect(EffectRecord::Clock(99)),
            "Rand(v) -> Clock(v)",
        ),
        (
            3,
            Event::Effect(EffectRecord::File {
                path: "/a".into(),
                bytes: vec![],
            }),
            "Clock -> an empty File",
        ),
    ];
    for (idx, replacement, what) in swaps {
        let f = replay_session(&fork_session(&events, idx, replacement), COLS, ROWS);
        assert_eq!(f.events_reached, base.events_reached, "{what}: same reach");
        assert_ne!(f.effect_digest, base.effect_digest, "{what}: digest moves");
    }
    // Same bytes, different path: the path is part of the recorded effect.
    let file = |path: &str| {
        Event::Effect(EffectRecord::File {
            path: path.into(),
            bytes: b"same bytes".to_vec(),
        })
    };
    let a = replay_session(&fork_session(&events, 3, file("/etc/a")), COLS, ROWS);
    let b = replay_session(&fork_session(&events, 3, file("/etc/b")), COLS, ROWS);
    assert_ne!(a.effect_digest, b.effect_digest, "path moves the digest");
    // A read that errored is not the same effect as a read of an empty file.
    let err = Event::Effect(EffectRecord::FileErr {
        path: "/etc/a".into(),
        kind: std::io::ErrorKind::NotFound,
    });
    let empty = Event::Effect(EffectRecord::File {
        path: "/etc/a".into(),
        bytes: vec![],
    });
    let e = replay_session(&fork_session(&events, 3, err), COLS, ROWS);
    let n = replay_session(&fork_session(&events, 3, empty), COLS, ROWS);
    assert_ne!(e.effect_digest, n.effect_digest, "error != empty read");
}
