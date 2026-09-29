//! Evidence support for `term.cognition.replay-and-fork` (the in-`#[test]`
//! assertions the tautology lint can see — the selftest example's `main` escapes
//! it). Planner-driven replay is deterministic and recovers; a counterfactual
//! tool-result swap re-drives the SAME policy down a different branch; and a
//! mutation guard proves the decision trace is real content, not `f(x) == f(x)`.

use astream_agent::fixtures::{build_ok_result, build_then_recover};
use astream_agent::{
    cog_fork_swap, decode_turn, record_turn, run_turn, trace_fnv, Action, ConstantPlanner, Offset,
    ReplayPlanner,
};
use astream_term::Screen;

const COLS: u16 = 60;
const ROWS: u16 = 10;

fn text(s: &Screen) -> String {
    let (_, rows) = s.dims();
    (0..rows)
        .map(|r| s.line_text(r))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn replay_is_deterministic_and_recovers() {
    let recs = build_then_recover();
    let (t1, s1) = run_turn(&mut ReplayPlanner, &recs, COLS, ROWS);
    let (t2, s2) = run_turn(&mut ReplayPlanner, &recs, COLS, ROWS);
    assert_eq!(trace_fnv(&t1), trace_fnv(&t2), "replay is deterministic");
    assert_eq!(s1.serialize(), s2.serialize());
    assert!(text(&s1).contains("recover"), "the recorded turn recovers");
    // The policy reached the recovery records then finished at the clean result.
    assert_eq!(
        t1.len(),
        4,
        "reached 4 of 5 records (the final EndTurn is not reached)"
    );
}

#[test]
fn a_constant_planner_yields_a_different_trace() {
    // Mutation guard: a degenerate policy reaches one record and produces a
    // different trace fnv -- so the trace is real decision content.
    let recs = build_then_recover();
    let (replay_trace, _) = run_turn(&mut ReplayPlanner, &recs, COLS, ROWS);
    let (const_trace, _) = run_turn(&mut ConstantPlanner, &recs, COLS, ROWS);
    assert_eq!(
        const_trace.len(),
        1,
        "the constant planner finishes immediately"
    );
    assert_ne!(
        trace_fnv(&replay_trace),
        trace_fnv(&const_trace),
        "the trace reflects which records the policy reached, not f(x)==f(x)"
    );
}

#[test]
fn forking_one_tool_result_re_drives_the_policy_down_a_different_branch() {
    let recs = build_then_recover();
    let (orig_trace, orig_screen) = run_turn(&mut ReplayPlanner, &recs, COLS, ROWS);

    // Swap the FAILED result (offset 1) for BUILD OK.
    let alt = cog_fork_swap(&recs, Offset(1), build_ok_result());
    let (alt_trace, alt_screen) = run_turn(&mut ReplayPlanner, &alt, COLS, ROWS);

    // Decision trace: shared prefix at step 0, forward divergence at step 1.
    assert_eq!(orig_trace[0], alt_trace[0], "decision prefix is shared");
    assert_eq!(
        orig_trace[1].action,
        Action::Speak,
        "original keeps going to recover"
    );
    assert_eq!(
        alt_trace[1].action,
        Action::Finish,
        "the clean result finishes the turn"
    );
    assert!(
        alt_trace.len() < orig_trace.len(),
        "the alternate turn is shorter"
    );

    // Screen: the alternate omits "recover" (those records were never reached) and
    // shows BUILD OK -- a genuine consequence of swapped evidence re-driving the
    // policy, not raw byte substitution.
    assert!(text(&orig_screen).contains("recover"));
    assert!(
        !text(&alt_screen).contains("recover"),
        "the alternate never recovers"
    );
    assert!(text(&alt_screen).contains("BUILD OK"));
}

#[test]
fn cognition_log_round_trips_through_frames() {
    let recs = build_then_recover();
    let log = record_turn(0xC0, &recs).expect("the fixture turn frames");
    assert_eq!(
        decode_turn(&log),
        recs,
        "the framed cognition log decodes back"
    );
}
