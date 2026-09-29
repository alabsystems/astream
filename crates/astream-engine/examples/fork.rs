//! THE rung-3 evidence command, behind claim `term.fork.counterfactual-replay`.
//!
//! Records an agent's build session, then forks the log at the offset where the
//! world answered and injects the build result the agent did *not* see. The
//! alternate timeline is byte-exact and screen-exact, and re-forking is
//! deterministic — the fork is frozen as a re-runnable regression. A failed
//! assert panics (non-zero exit), so the asserts gate the run; success prints one
//! deterministic line whose SHA-256 the manifest pins.

use astream_engine::{fork_swap, record_session, Offset};
use astream_term::{screen, Record};
use astream_wire::fnv1a_64;

const SEED: u64 = 0xF02C;
const COLS: u16 = 40;
const ROWS: u16 = 6;

/// An agent session: it ran a build, the world answered, it reacted.
fn agent_session() -> Vec<Record> {
    vec![
        Record::Out(b"$ make\r\n".to_vec()),
        Record::In {
            bytes: b"make\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Out(b"BUILD FAILED: 3 errors\r\n".to_vec()), // offset 2: the world's answer
        Record::In {
            bytes: b"echo recover\n".to_vec(),
            client_id: 1,
            client_seq: 2,
        },
        Record::Out(b"recover\r\n".to_vec()),
    ]
}

fn main() {
    let original = agent_session();
    let orig_log = record_session(SEED, &original);
    let orig_screen = screen::fold(COLS, ROWS, &original);

    // Counterfactual: fork at offset 2 and inject the build the agent did NOT see.
    let alt = fork_swap(
        &original,
        Offset(2),
        Record::Out(b"BUILD OK: 0 errors\r\n".to_vec()),
    );
    let alt_log = record_session(SEED, &alt);
    let alt_screen = screen::fold(COLS, ROWS, &alt);

    // Deterministic: re-forking is byte-identical.
    assert_eq!(
        alt_log,
        record_session(SEED, &alt),
        "fork must be deterministic"
    );
    // A real alternate history: differs from the original, in the log and on screen.
    assert_ne!(alt_log, orig_log, "the alternate log differs");
    assert_ne!(
        alt_screen.serialize(),
        orig_screen.serialize(),
        "the alternate screen differs"
    );
    // Exact: each timeline shows its own build result; untouched lines are identical.
    assert!(orig_screen.line_text(1).contains("BUILD FAILED"));
    assert!(alt_screen.line_text(1).contains("BUILD OK"));
    assert!(!alt_screen.line_text(1).contains("FAILED"));
    assert_eq!(
        orig_screen.line_text(0),
        alt_screen.line_text(0),
        "prompt line identical"
    );
    assert_eq!(
        orig_screen.line_text(2),
        alt_screen.line_text(2),
        "recover line identical"
    );

    println!(
        "fork ok orig_log={:016x} alt_log={:016x} orig_screen={:016x} alt_screen={:016x}",
        fnv1a_64(&orig_log),
        fnv1a_64(&alt_log),
        fnv1a_64(&orig_screen.serialize()),
        fnv1a_64(&alt_screen.serialize()),
    );
}
