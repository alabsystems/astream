//! Selftest for `term.cognition.replay-and-fork`: record a turn to a cognition
//! log, replay it hermetically (no network, no tools) to a deterministic decision
//! trace + screen, and counterfactually fork one tool result to re-drive the same
//! fixed policy down a different branch. On success it prints exactly one line,
//! whose hash is pinned in the manifest; any assertion failure aborts non-zero.

use astream_agent::fixtures::{build_ok_result, build_then_recover};
use astream_agent::{
    cog_fork_swap, decode_turn, record_turn, run_turn, trace_fnv, Offset, ReplayPlanner,
};
use astream_term::Screen;

const COLS: u16 = 60;
const ROWS: u16 = 10;
const SEED: u64 = 0xC0;

fn has(s: &Screen, needle: &str) -> bool {
    let (_, rows) = s.dims();
    (0..rows).any(|r| s.line_text(r).contains(needle))
}

fn main() {
    // Record the turn as a cognition log and decode it back (the durable path).
    let recs = build_then_recover();
    let log = record_turn(SEED, &recs).expect("a 5-record turn frames well within the cap");
    let decoded = decode_turn(&log);
    assert_eq!(decoded, recs, "cognition log round-trips through frames");

    // Replay is deterministic.
    let (orig_trace, orig_screen) = run_turn(&mut ReplayPlanner, &decoded, COLS, ROWS);
    let (orig_trace2, orig_screen2) = run_turn(&mut ReplayPlanner, &decoded, COLS, ROWS);
    assert_eq!(
        trace_fnv(&orig_trace),
        trace_fnv(&orig_trace2),
        "replay deterministic"
    );
    assert_eq!(orig_screen.serialize(), orig_screen2.serialize());
    assert!(has(&orig_screen, "recover"), "the recorded turn recovers");

    // Counterfactual fork: swap the FAILED tool result for BUILD OK.
    let alt = cog_fork_swap(&decoded, Offset(1), build_ok_result());
    let (alt_trace, alt_screen) = run_turn(&mut ReplayPlanner, &alt, COLS, ROWS);
    assert_eq!(
        orig_trace[0], alt_trace[0],
        "decision prefix shared up to the swap"
    );
    assert_ne!(
        orig_trace[1].action, alt_trace[1].action,
        "trace diverges after the swap"
    );
    assert!(
        !has(&alt_screen, "recover"),
        "the alternate turn never recovers"
    );
    assert!(
        has(&alt_screen, "BUILD OK"),
        "the alternate turn shows BUILD OK"
    );

    println!(
        "agent ok orig_trace={:016x} alt_trace={:016x} orig_recover={} alt_recover={} alt_ok={} steps={}/{}",
        trace_fnv(&orig_trace),
        trace_fnv(&alt_trace),
        has(&orig_screen, "recover") as u8,
        has(&alt_screen, "recover") as u8,
        has(&alt_screen, "BUILD OK") as u8,
        alt_trace.len(),
        orig_trace.len(),
    );
}
