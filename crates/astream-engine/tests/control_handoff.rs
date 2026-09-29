//! Evidence for `term.fleet.control-handoff`: a shared session has one writer at
//! a time, and the ENGINE enforces it — `Session::apply_input_as` takes the
//! session's `ControlToken` and refuses a non-holder (`EngineError::NotHolder`)
//! before the log or the dedup map is touched. Control transfers between the
//! orchestrator and a human (a claim, then a grant back; a non-holder cannot
//! grant); the log's `In`-client-id sequence is the auditable, replayable
//! handoff history, and refused attempts leave no trace.

use astream_engine::{CausedBy, ControlToken, EngineError, Log, Offset, Seeded, Session};
use astream_term::Record;

const ORCH: u64 = 1; // the orchestrator agent
const HUMAN: u64 = 2; // a human who can claim the keyboard
const VIEWER: u64 = 3; // a read-only attached client

/// The `(client_id, bytes)` of every `In` in the stored log, in order.
fn ins(bytes: &[u8]) -> Vec<(u64, Vec<u8>)> {
    Log::read_bytes(bytes, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .filter_map(|r| match r {
            Record::In {
                client_id, bytes, ..
            } => Some((client_id, bytes)),
            _ => None,
        })
        .collect()
}

#[test]
fn the_engine_refuses_a_non_holder_and_the_log_is_the_handoff_history() {
    let mut session = Session::new(Seeded::new(0));
    let mut token = ControlToken::new(ORCH);

    // The orchestrator holds control: its input applies.
    assert_eq!(
        session.apply_input_as(&token, ORCH, 1, b"a".to_vec()),
        Ok(Some(Offset(0)))
    );

    // A viewer (never granted) is read-only: the ENGINE refuses it, naming the
    // holder, and nothing reaches the log or the dedup map.
    let before = session.log_bytes();
    assert_eq!(
        session.apply_input_as(&token, VIEWER, 1, b"x".to_vec()),
        Err(EngineError::NotHolder {
            holder: ORCH,
            client: VIEWER
        })
    );
    assert_eq!(
        session.log_bytes(),
        before,
        "a refused input leaves no trace"
    );
    assert_eq!(session.next_offset(), Offset(1));
    assert!(!session.is_duplicate(VIEWER, 1), "nor a dedup entry");
    // The viewer cannot grant itself the keyboard either.
    assert_eq!(
        token.grant(VIEWER, VIEWER),
        Err(EngineError::NotHolder {
            holder: ORCH,
            client: VIEWER
        })
    );
    assert_eq!(token.holder(), ORCH);

    // The human claims the keyboard (the explicit, unconditional override).
    token.claim(HUMAN);
    assert!(token.may_write(HUMAN) && token.is_read_only(ORCH));
    // The human writes; the now-read-only orchestrator is refused by the engine.
    assert_eq!(
        session.apply_input_as(&token, HUMAN, 1, b"b".to_vec()),
        Ok(Some(Offset(1)))
    );
    assert_eq!(
        session.apply_input_as(&token, ORCH, 2, b"c".to_vec()),
        Err(EngineError::NotHolder {
            holder: HUMAN,
            client: ORCH
        })
    );

    // The human hands control back — only the holder can grant.
    token.grant(HUMAN, ORCH).unwrap();
    // The refused "c" never bumped the orchestrator's high-water: seq 2 is still
    // fresh and is applied exactly once now.
    assert_eq!(
        session.apply_input_as(&token, ORCH, 2, b"d".to_vec()),
        Ok(Some(Offset(2)))
    );

    // The log's In records ARE the control history: exactly the applied inputs,
    // in order, each carrying the controller's client_id. The refused attempts
    // (viewer "x", read-only orchestrator "c") left no trace.
    let history = ins(&session.log_bytes());
    assert_eq!(
        history,
        vec![
            (ORCH, b"a".to_vec()),
            (HUMAN, b"b".to_vec()),
            (ORCH, b"d".to_vec()),
        ],
        "the log records exactly the holder's inputs, in handoff order"
    );
    assert!(
        history.iter().all(|(c, _)| *c != VIEWER),
        "a read-only client's input never entered the log"
    );

    // Replay is exact: re-decoding the stored bytes yields the same handoff history.
    assert_eq!(
        ins(&session.log_bytes()),
        history,
        "the handoff history replays deterministically"
    );
}

#[test]
fn the_caused_ingest_is_gated_the_same_way() {
    let mut session = Session::new(Seeded::new(0));
    let token = ControlToken::new(ORCH);
    let cause = CausedBy {
        partition: Some(9),
        offset: 4,
    };
    assert!(matches!(
        session.apply_input_caused_as(&token, VIEWER, 1, b"x".to_vec(), cause),
        Err(EngineError::NotHolder { .. })
    ));
    assert!(session.log_bytes().is_empty(), "no trace");
    assert_eq!(
        session.apply_input_caused_as(&token, ORCH, 1, b"y".to_vec(), cause),
        Ok(Some(Offset(0)))
    );
}
