//! Rung 3 evidence: fleet capabilities. Backs the claim `term.fork.multi-client`.
//!
//! Multi-client attach is consistent (independent clients fold the same log to
//! the same screen); a capability is a Filter over the session's subject subtree
//! (read-only attach matches the stream subtree but not the inbox; control
//! matches the inbox); and the counterfactual fork is deterministic and exact.

use astream_engine::{fork_swap, record_session, Log, MemDisk, Offset};
use astream_term::{screen, Record};
use astream_wire::{Filter, Subject};

const SEED: u64 = 0xF02C;
const COLS: u16 = 40;
const ROWS: u16 = 6;

fn agent_session() -> Vec<Record> {
    vec![
        Record::Out(b"$ make\r\n".to_vec()),
        Record::In {
            bytes: b"make\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Out(b"BUILD FAILED: 3 errors\r\n".to_vec()),
        Record::In {
            bytes: b"echo recover\n".to_vec(),
            client_id: 1,
            client_seq: 2,
        },
        Record::Out(b"recover\r\n".to_vec()),
    ]
}

fn decode(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

#[test]
fn counterfactual_fork_is_deterministic_and_exact() {
    let original = agent_session();
    let alt = fork_swap(
        &original,
        Offset(2),
        Record::Out(b"BUILD OK: 0 errors\r\n".to_vec()),
    );

    assert_eq!(
        record_session(SEED, &alt),
        record_session(SEED, &alt),
        "deterministic"
    );
    assert_ne!(record_session(SEED, &alt), record_session(SEED, &original));

    let orig = screen::fold(COLS, ROWS, &original);
    let forked = screen::fold(COLS, ROWS, &alt);
    assert!(orig.line_text(1).contains("FAILED"));
    assert!(forked.line_text(1).contains("BUILD OK"));
    assert_eq!(orig.line_text(0), forked.line_text(0));
    assert_eq!(orig.line_text(2), forked.line_text(2));
}

#[test]
fn multiple_clients_fold_the_same_log_to_the_same_screen() {
    // Two independent "clients" each record + decode the session through their
    // OWN MemDisk and fold — a genuinely independent reconstruction path, not
    // f(x) == f(x).
    let a = screen::fold(COLS, ROWS, &decode(&record_session(SEED, &agent_session())));
    let b = screen::fold(COLS, ROWS, &decode(&record_session(SEED, &agent_session())));
    assert_eq!(a.serialize(), b.serialize());
    // ...and against ground truth, so a deterministic-but-wrong fold is caught.
    assert!(a.line_text(1).contains("FAILED"));
    assert!(a.line_text(2).contains("recover"));
}

#[test]
fn capability_is_a_filter_over_the_session_subtree() {
    let s = "01HZXBYK7Q";

    // A read-only attach: subscribe to the session's stream subtree only.
    let read_only = Filter::new(format!("/a/stream/ssh/{s}/>")).unwrap();
    assert!(read_only.matches(&Subject::new(format!("/a/stream/ssh/{s}/out")).unwrap()));
    assert!(read_only.matches(&Subject::new(format!("/a/stream/ssh/{s}/log")).unwrap()));
    // ...which does NOT grant writing input (a different verb subtree)...
    assert!(!read_only.matches(&Subject::new(format!("/a/inbox/ssh/{s}/host")).unwrap()));
    // ...nor reading ANOTHER session's stream.
    assert!(!read_only.matches(&Subject::new("/a/stream/ssh/OTHER/out").unwrap()));
    assert!(!read_only.matches(&Subject::new("/a/stream/ssh/OTHER/log").unwrap()));

    // A control grant covers the inbox; a different session's subtree does not.
    let control = Filter::new(format!("/a/inbox/ssh/{s}/>")).unwrap();
    assert!(control.matches(&Subject::new(format!("/a/inbox/ssh/{s}/host")).unwrap()));
    assert!(!control.matches(&Subject::new("/a/inbox/ssh/OTHER/host").unwrap()));
    assert!(!control.matches(&Subject::new(format!("/a/stream/ssh/{s}/out")).unwrap()));
}
