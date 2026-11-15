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

/// The door records (`Mono`, `Exchange`, `Emit`, `Raised`) each fold under a tag
/// of their own (5-8) with every field length-prefixed, so none of them digests
/// like another record or like itself with its fields slid around. Each pair
/// here differs in exactly the way a value-only or unprefixed fold would miss;
/// every one must move the digest, and the identical-record control must not.
#[test]
fn effect_digest_tags_the_door_records() {
    let events = session();
    let digest_with = |e: EffectRecord| {
        replay_session(&fork_session(&events, 3, Event::Effect(e)), COLS, ROWS).effect_digest
    };
    let bytes = |s: &str| s.as_bytes().to_vec();
    let exchange = |door: &str, request: &str, reply: &str| EffectRecord::Exchange {
        door: door.into(),
        request: bytes(request),
        reply: bytes(reply),
    };
    let emit = |door: &str, out: &str| EffectRecord::Emit {
        door: door.into(),
        bytes: bytes(out),
    };
    let raised = |door: &str, false_reads: u64| EffectRecord::Raised {
        door: door.into(),
        false_reads,
    };
    let pairs: Vec<(EffectRecord, EffectRecord, &str)> = vec![
        (
            EffectRecord::Clock(1234),
            EffectRecord::Mono(1234),
            "Clock(v) vs Mono(v)",
        ),
        (
            EffectRecord::Rand(1234),
            EffectRecord::Mono(1234),
            "Rand(v) vs Mono(v)",
        ),
        (
            exchange("ab", "c", "d"),
            exchange("a", "bc", "d"),
            "the door absorbing the head of the request",
        ),
        (
            exchange("a", "b", "cd"),
            exchange("a", "bc", "d"),
            "the request absorbing the head of the reply",
        ),
        (
            exchange("a", "q", "r"),
            exchange("a", "r", "q"),
            "request and reply swapped",
        ),
        (
            exchange("ctl", "status", ""),
            emit("ctl", "status"),
            "an exchange with an empty reply vs an output of its request",
        ),
        (
            emit("out", "x"),
            emit("journal", "x"),
            "an output through another door",
        ),
        (emit("out", "x"), emit("out", "y"), "another output"),
        (
            raised("stop", 0),
            raised("stop", 1),
            "a rise one read later",
        ),
        (raised("stop", 0), raised("handover", 0), "another flag"),
        (
            raised("x", 0),
            emit("x", ""),
            "a raised flag vs an empty output through its door",
        ),
    ];
    for (a, b, what) in pairs {
        assert_ne!(digest_with(a), digest_with(b), "{what}: digest moves");
    }
    // Control: the same record twice digests the same (the digest is a
    // function of the record, so the inequalities above are not noise).
    assert_eq!(
        digest_with(exchange("a", "q", "r")),
        digest_with(exchange("a", "q", "r"))
    );
}

/// The decision steps count cognition records only (0, 1, 2, ... with Input, Output
/// and Effect events interleaved), `inputs_applied` counts Input events, and
/// `events_reached` counts every event up to and including the finishing one.
#[test]
fn replay_numbers_decisions_by_cognition_record_and_counts_reached_events() {
    let r = replay_session(&session(), COLS, ROWS);
    let steps: Vec<u32> = r.decisions.iter().map(|d| d.step).collect();
    assert_eq!(steps, [0, 1, 2, 3], "cognition events 0, 5, 6, 10");
    assert_eq!(r.inputs_applied, 2);
    assert_eq!(r.events_reached, 11, "event 11 follows the Finish");
    let empty = replay_session(&[], COLS, ROWS);
    assert!(empty.decisions.is_empty());
    assert_eq!((empty.inputs_applied, empty.events_reached), (0, 0));
}

#[test]
fn fleet_cognition_consistent_cut_and_counterfactual_fork_across_agents() {
    use astream_agent::{
        fleet_causal_edges, fork_fleet_session, replay_fleet_causal, replay_fleet_cut,
        AgentSession, FleetEvent, FleetReplayError, Offset,
    };
    use astream_wire::CausalCut;

    // Multi-agent fleet modelling an aterm orchestrator (`s-orch`) that runs a test,
    // sees `"FAILED"` at offset 4, spawns worker `s-worker` at offset 6 (`s-orch@6 ->
    // s-worker@0`), which in turn spawns sub-worker `s-sub` at offset 3 (`s-worker@3 ->
    // s-sub@0`) and reports back to `s-orch` at offset 5 (`s-worker@5 -> s-orch@7`)!
    let orch = AgentSession::new(
        "s-orch",
        COLS,
        ROWS,
        vec![
            FleetEvent::local(Event::Cognition(completion("run suite", Some("t1")))), // 0
            FleetEvent::local(Event::In(b"make test\n".to_vec())),                    // 1
            FleetEvent::local(Event::Out(b"$ make test\r\nFAIL\r\n".to_vec())),       // 2
            FleetEvent::local(Event::Effect(EffectRecord::Clock(100))),               // 3
            FleetEvent::local(Event::Cognition(tool_result("t1", "FAILED", true))),   // 4: Speak
            FleetEvent::local(Event::Cognition(completion("spawn worker", Some("t2")))), // 5
            FleetEvent::local(Event::In(b"aterm ctl @self spawn agent=claude\n".to_vec())), // 6: spawns worker!
            FleetEvent::caused(
                Event::Cognition(tool_result("t2", "worker landed fix", false)), // 7: Finish (awaits s-worker@5)
                "s-worker",
                Offset(5),
            ),
            FleetEvent::local(Event::Out(b"orchestrator done\r\n".to_vec())), // 8: past Finish
        ],
    );

    let worker = AgentSession::new(
        "s-worker",
        COLS,
        ROWS,
        vec![
            FleetEvent::caused(
                Event::In(b"fix failing test\n".to_vec()),
                "s-orch",
                Offset(6),
            ), // 0: caused by s-orch@6
            FleetEvent::local(Event::Cognition(completion("delegate lint", Some("w1")))), // 1
            FleetEvent::local(Event::Effect(EffectRecord::Rand(77))),                     // 2
            FleetEvent::local(Event::Out(b"worker patching...\r\n".to_vec())), // 3: spawns s-sub!
            FleetEvent::caused(
                Event::Cognition(tool_result("w1", "sub clean", false)), // 4: Finish (awaits s-sub@2)
                "s-sub",
                Offset(2),
            ),
            FleetEvent::local(Event::Out(b"worker trailing\r\n".to_vec())), // 5: wait — if Finish is at 4, 5 wouldn't be reached!
        ],
    );
    // Make `s-worker` finish at offset 5 so `s-worker@5` IS reached when `s-orch` spawns it!
    let mut worker = worker;
    worker.events[4] = FleetEvent::caused(
        Event::Out(b"worker patched cleanly\r\n".to_vec()),
        "s-sub",
        Offset(2),
    );
    worker.events[5] = FleetEvent::local(Event::Cognition(tool_result("w1", "ok", false)));

    let sub = AgentSession::new(
        "s-sub",
        COLS,
        ROWS,
        vec![
            FleetEvent::caused(Event::In(b"tippy\n".to_vec()), "s-worker", Offset(3)), // 0
            FleetEvent::local(Event::Effect(EffectRecord::Clock(200))),                // 1
            FleetEvent::local(Event::Out(b"0 warnings\r\n".to_vec())),                 // 2
            FleetEvent::local(Event::Cognition(tool_result("s0", "ok", false))),       // 3: Finish
        ],
    );

    let fleet = vec![orch, worker, sub];
    let edges = fleet_causal_edges(&fleet);
    assert_eq!(edges.len(), 4, "4 cross-session causal edges");

    // 1. Consistent-cut enforcement: admitting `s-worker@0` while `s-orch` is only at
    //    `Offset(3)` (< `Offset(6)`) MUST be refused with `InconsistentCut`.
    let mut bad_cut = CausalCut::new();
    bad_cut.set("s-orch".to_string(), Offset(3));
    bad_cut.set("s-worker".to_string(), Offset(2));
    let err = replay_fleet_cut(&fleet, &bad_cut).unwrap_err();
    assert!(
        matches!(err, FleetReplayError::InconsistentCut(ref v) if v.edge.cause == ("s-orch".into(), Offset(6))),
        "must pinpoint s-orch@6 -> s-worker@0 violation: {err:?}"
    );

    // Healing `bad_cut` via Chandy-Lamport closure (`CausalCut::heal`) makes it replayable!
    let mut healed_cut = bad_cut.clone();
    assert!(healed_cut.heal(&edges) > 0);
    assert!(healed_cut.is_consistent(&edges));
    let cut_replay = replay_fleet_cut(&fleet, &healed_cut).unwrap();
    assert_eq!(cut_replay.sessions.len(), 2);

    // 2. Full causal replay (`replay_fleet_causal`) resolves the bidirectional
    //    `s-orch -> s-worker -> s-sub -> s-worker -> s-orch` event DAG deterministically.
    let base_a = replay_fleet_causal(&fleet).unwrap();
    let base_b = replay_fleet_causal(&fleet).unwrap();
    assert_eq!(base_a, base_b, "fleet causal replay is bit-identical");
    assert!(
        base_a.effective_cut.is_consistent(&edges),
        "effective_cut is Chandy-Lamport consistent"
    );
    assert_eq!(base_a.sessions["s-orch"].events_reached, 8);
    assert_eq!(base_a.sessions["s-worker"].events_reached, 6);
    assert_eq!(base_a.sessions["s-sub"].events_reached, 4);
    assert!(text(&base_a.sessions["s-worker"].screen).contains("worker patched cleanly"));
    assert!(text(&base_a.sessions["s-sub"].screen).contains("0 warnings"));

    // 3. Counterfactual fork on `s-orch` at offset 4 (`"FAILED"` -> `"ok"`):
    //    `s-orch` finishes early at offset 4 (`events_reached == 5`), BEFORE offset 6!
    //    Therefore `s-orch@6` is NEVER reached -> `s-worker` is causally gated
    //    (`events_reached == 0`) -> `s-sub` is transitively gated (`events_reached == 0`)!
    let forked_fleet = fork_fleet_session(
        &fleet,
        "s-orch",
        4,
        Event::Cognition(tool_result("t1", "ok", false)),
    );
    let forked = replay_fleet_causal(&forked_fleet).unwrap();
    assert_ne!(forked.fleet_digest, base_a.fleet_digest);
    assert!(
        forked.effective_cut.is_consistent(&edges),
        "forked effective_cut remains Chandy-Lamport consistent"
    );
    assert_eq!(forked.sessions["s-orch"].events_reached, 5);
    assert_eq!(forked.sessions["s-orch"].inputs_applied, 1);
    assert_eq!(forked.sessions["s-worker"].events_reached, 0);
    assert_eq!(forked.sessions["s-worker"].inputs_applied, 0);
    assert!(forked.sessions["s-worker"].decisions.is_empty());
    assert!(!text(&forked.sessions["s-worker"].screen).contains("worker patched"));
    assert_eq!(forked.sessions["s-sub"].events_reached, 0);
    assert!(!forked.effective_cut.includes(&"s-worker".into(), Offset(0)));
    assert!(!forked.effective_cut.includes(&"s-sub".into(), Offset(0)));
}

#[test]
fn fleet_cognition_rejects_causal_cycles() {
    use astream_agent::{replay_fleet_causal, AgentSession, FleetEvent, FleetReplayError, Offset};

    let cyclic = vec![
        AgentSession::new(
            "a",
            COLS,
            ROWS,
            vec![FleetEvent::caused(
                Event::In(b"x\n".to_vec()),
                "b",
                Offset(0),
            )],
        ),
        AgentSession::new(
            "b",
            COLS,
            ROWS,
            vec![FleetEvent::caused(
                Event::In(b"y\n".to_vec()),
                "a",
                Offset(0),
            )],
        ),
    ];
    assert_eq!(
        replay_fleet_causal(&cyclic),
        Err(FleetReplayError::CausalCycle {
            session: "a".to_string()
        })
    );
}
