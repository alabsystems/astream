//! Rung 2.5 evidence: speculative local echo + reconciliation. Backs the claim
//! `term.echo.predict-and-reconcile`.
//!
//! Speculation renders before the round-trip; after the authoritative `/out` is
//! folded, a prediction is confirmed (it matched) or rolled back to ground truth
//! (contradicted / lost), and the reconciled view equals the pure authoritative
//! screen — for any prediction whatsoever (the proptest, which also checks every
//! verdict against an independent oracle and that the speculation is painted at
//! exactly the predicted cells and nowhere else).

use astream_term::screen::{attr, Cell};
use astream_term::{
    program_ops_within_cap, program_rule_cap_clamp, screen, Predictor, ProgramPredictor, Record,
    ScreenOp, SpeculativeTerminal, Verdict, MAX_OPS_PER_RULE, MAX_PROGRAM_RULES,
};
use proptest::prelude::*;

fn out(s: &[u8]) -> Record {
    Record::Out(s.to_vec())
}

#[test]
fn speculative_echo_renders_before_the_round_trip() {
    let mut p = Predictor::new(20, 3);
    assert!(p.predict(1, b"hi"), "printable input is predicted");

    // The user sees "hi" immediately, faint, before any /out arrives.
    let view = p.view();
    assert_eq!(view.line_text(0), "hi");
    assert_ne!(
        view.cell(0, 0).unwrap().attrs & attr::FAINT,
        0,
        "unconfirmed = faint"
    );
    // The authoritative screen is still blank.
    assert_eq!(p.authoritative().line_text(0), "");
}

#[test]
fn confirmed_predictions_match_and_leave_no_residue() {
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"hi");
    p.apply_output(&out(b"hi")); // the server echoes exactly what we guessed

    let verdicts = p.reconcile();
    assert!(verdicts.iter().all(|(_, v)| *v == Verdict::Confirmed));

    // After reconciliation the view is the authoritative screen (no faint cells).
    let view = p.view();
    assert_eq!(view.serialize(), p.authoritative().serialize());
    assert_eq!(view.cell(0, 0).unwrap().attrs & attr::FAINT, 0);
}

#[test]
fn contradicted_prediction_is_rolled_back_to_ground_truth() {
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"x"); // we guessed the keystroke echoes 'x'...
    p.apply_output(&out(b"*")); // ...but the server echoed '*' (e.g. a password)

    let verdicts = p.reconcile();
    assert_eq!(verdicts, vec![(1, Verdict::Contradicted)]);
    assert_eq!(
        p.view().line_text(0),
        "*",
        "ground truth wins, not the prediction"
    );
}

#[test]
fn lost_prediction_is_rolled_back() {
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"z"); // guessed an echo...
                        // ...but the server never echoed it (no output at that cell).

    let verdicts = p.reconcile();
    assert_eq!(verdicts, vec![(1, Verdict::Lost)]);
    assert_eq!(p.view().line_text(0), "", "the unconfirmed glyph is gone");
}

#[test]
fn a_predicted_space_is_confirmed_only_once_the_cursor_has_passed_it() {
    // A never-painted blank cell already matches a space, so the cell alone can
    // not confirm one: with no echo at all the space is Lost, not Confirmed.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b" ");
    assert_eq!(p.reconcile(), vec![(1, Verdict::Lost)]);

    // Echoed: the authoritative cursor moved past the cell, so it is Confirmed.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b" ");
    p.apply_output(&out(b" "));
    assert_eq!(p.reconcile(), vec![(1, Verdict::Confirmed)]);

    // Watermark retirement: "ls " with only "ls" echoed so far confirms l and s
    // and leaves the trailing space UNDECIDED (the walk stops there); the space's
    // own echo then confirms it.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"ls ");
    assert_eq!(
        p.apply_output_at(1, &out(b"ls")),
        vec![(1, Verdict::Confirmed), (1, Verdict::Confirmed)]
    );
    assert_eq!(
        p.apply_output_at(2, &out(b" ")),
        vec![(1, Verdict::Confirmed)]
    );
}

#[test]
fn a_repaint_that_moves_the_cursor_back_over_an_echoed_space_still_confirms() {
    // The cursor is only ONE proof that a cell was traversed. A bare CR, a CUP
    // repaint, a zle/readline line redraw all echo the space and then park the
    // cursor at or before it — a glyph painted strictly to its right is the
    // other proof, and without it the space would be reported Lost and the
    // client would retransmit a keystroke the server already has.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"ls -la");
    // Echo, then a bare CR: the cursor is back at column 0, behind the space.
    p.apply_output(&out(b"ls -la\r"));
    assert_eq!(p.authoritative().cursor(), (0, 0));
    assert!(
        p.reconcile().iter().all(|&(_, v)| v == Verdict::Confirmed),
        "every glyph of the echoed line, the space included, is Confirmed"
    );

    // A full redraw that repaints the line from home is the same shape.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"a b");
    p.apply_output(&out(b"a b\x1b[H"));
    assert_eq!(
        p.reconcile(),
        vec![
            (1, Verdict::Confirmed),
            (1, Verdict::Confirmed),
            (1, Verdict::Confirmed)
        ]
    );

    // And on the watermark path the walk no longer stalls at the space: every
    // later prediction retires behind it.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"a b");
    assert_eq!(
        p.apply_output_at(1, &out(b"a b\r")),
        vec![
            (1, Verdict::Confirmed),
            (1, Verdict::Confirmed),
            (1, Verdict::Confirmed)
        ]
    );

    // The widening is only about a glyph to the RIGHT: a trailing space with
    // nothing beyond it, cursor parked back at home, is still undecided/Lost.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"ls ");
    p.apply_output(&out(b"ls \r"));
    let v = p.reconcile();
    assert_eq!(v[0..2], [(1, Verdict::Confirmed), (1, Verdict::Confirmed)]);
    assert_eq!(v[2], (1, Verdict::Lost), "no glyph right of the space");
}

#[test]
fn a_lost_space_keystroke_is_reported_not_confirmed() {
    // The transport drops the space of "ls -la": the shell echoes "ls-la". The
    // space is Contradicted (a '-' landed on its cell) and the tail is squashed —
    // never Confirmed, so the client can retransmit.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"ls");
    p.predict(2, b" ");
    p.predict(3, b"-la");
    let v = p.apply_output_at(1, &out(b"ls-la"));
    assert_eq!(v[0..2], [(1, Verdict::Confirmed), (1, Verdict::Confirmed)]);
    assert_eq!(v[2], (2, Verdict::Contradicted));
    assert_eq!(v.len(), 6);
    assert!(v[3..]
        .iter()
        .all(|(seq, verdict)| *seq == 3 && *verdict == Verdict::Lost));

    // A masked field: nothing echoed yet keeps the space undecided (no verdict,
    // no retirement), so the later '*' echo can still contradict it.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b" x");
    assert!(p.apply_output_at(1, &out(b"")).is_empty());
    let v = p.apply_output_at(2, &out(b"*y"));
    assert_eq!(v, vec![(1, Verdict::Contradicted), (1, Verdict::Lost)]);

    // A cell painted with something other than a glyph — a bce erase carrying a
    // blue background over the predicted space, cursor not past it — is
    // Contradicted, not Confirmed: the cell is no longer a never-painted blank.
    let mut p = Predictor::new(20, 3);
    p.predict(1, b" ");
    assert_eq!(
        p.apply_output_at(1, &out(b"\x1b[44m\x1b[K")),
        vec![(1, Verdict::Contradicted)]
    );
}

#[test]
fn predictor_abstains_on_control_and_escape_input() {
    let mut p = Predictor::new(20, 3);
    assert!(
        !p.predict(1, b"\x1b[A"),
        "an arrow-key escape is not predicted"
    );
    assert!(!p.predict(2, b"\r"), "a carriage return is not predicted");
    assert!(!p.predict(3, b""), "empty input is not predicted");
    assert_eq!(p.view().serialize(), p.authoritative().serialize());
}

#[test]
fn predictions_across_a_row_wrap_do_not_collide() {
    // A first run fills row 0 and wraps onto row 1; a second prediction must land
    // AFTER the wrapped glyph, not collide back onto the cursor row. With cols=3,
    // "abcd" lays a,b,c on row 0 and d on row 1; then "e" must sit at (1,1).
    let mut p = Predictor::new(3, 4);
    assert!(p.predict(1, b"abcd"));
    assert!(p.predict(2, b"e"));
    let view = p.view();
    assert_eq!(view.line_text(0), "abc");
    assert_eq!(view.line_text(1), "de", "e must follow d, not overwrite it");
}

#[test]
fn clean_origin_echo_causal_watermark_kernel_enforces_monotone_retirement() {
    use astream_term::{
        echo_admit_causal_watermark, echo_causal_watermark_select, echo_watermark_monotone,
        watermark_advances,
    };

    assert!(watermark_advances(10, 11));
    assert!(!watermark_advances(10, 10));
    assert!(!watermark_advances(10, 9));

    assert_eq!(echo_watermark_monotone(10, 15), 15);
    assert_eq!(echo_watermark_monotone(10, 8), 10);

    assert_eq!(echo_causal_watermark_select(7, 7, 25, 10), 25);
    assert_eq!(echo_causal_watermark_select(7, 8, 25, 10), 10);

    // Matching causal in-offset + strictly advancing out-offset -> advances to 25.
    assert_eq!(echo_admit_causal_watermark(7, 7, 10, 25), 25);
    // Matching causal in-offset + stale out-offset -> retains 10 (monotone).
    assert_eq!(echo_admit_causal_watermark(7, 7, 10, 8), 10);
    // Mismatched causal in-offset -> retains 10 even if cand_wm > cur_wm.
    assert_eq!(echo_admit_causal_watermark(7, 8, 10, 25), 10);
}

// `echo_admit_causal_watermark` is hand-written Rust, not compiled from Clean: it answers
// as `echo_admit_causal_watermark_isl`, the island's composition of
// `echo_causal_watermark_select` and `echo_watermark_monotone`, on every tuple of a grid of
// boundary operands.
#[test]
fn echo_admit_causal_watermark_answers_as_its_island_composition() {
    use astream_term::{
        echo_admit_causal_watermark, echo_causal_watermark_select, echo_watermark_monotone,
    };

    const GRID: [u64; 5] = [0, 1, 2, u64::MAX - 1, u64::MAX];
    let mut unmatched_kept = false;
    for in_off in GRID {
        for pred_in_off in GRID {
            for cur in GRID {
                for cand in GRID {
                    let advanced = echo_watermark_monotone(cur, cand);
                    let island = echo_causal_watermark_select(in_off, pred_in_off, advanced, cur);
                    assert_eq!(
                        echo_admit_causal_watermark(in_off, pred_in_off, cur, cand),
                        island,
                        "echo_admit_causal_watermark({in_off}, {pred_in_off}, {cur}, {cand})"
                    );
                    unmatched_kept |= island != advanced;
                }
            }
        }
    }
    // Not vacuous: the grid reaches an advance an unmatched in-offset holds back.
    assert!(unmatched_kept);
}

proptest! {
    /// For ANY interleaving of predictions and authoritative output: before
    /// reconciliation the view differs from the authoritative fold at EXACTLY the
    /// outstanding prediction cells (the speculation is painted, and painted
    /// nowhere else); every verdict equals an independently computed oracle over
    /// the final authoritative screen; and the reconciled view equals the pure
    /// authoritative fold — a prediction can never corrupt the final screen, and
    /// nothing panics.
    #[test]
    fn predictions_never_corrupt_the_final_screen(
        inputs in prop::collection::vec(prop::collection::vec(0x20u8..0x7f, 0..6), 0..8),
        outs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..12), 0..8),
    ) {
        let (cols, rows) = (20u16, 6u16);
        let mut p = Predictor::new(cols, rows);
        let mut authoritative_out = Vec::new();
        // An independent model of where each predicted glyph lands: at the
        // authoritative cursor when nothing is queued, else right after the last
        // queued glyph, wrapping at the right edge.
        let mut expected: Vec<(u64, u16, u16, char)> = Vec::new();
        let n = inputs.len().max(outs.len());
        for i in 0..n {
            if let Some(inp) = inputs.get(i) {
                let accepted = p.predict(i as u64, inp);
                prop_assert_eq!(accepted, !inp.is_empty());
                if accepted {
                    let (mut r, mut c) = match expected.last() {
                        Some(&(_, r, c, _)) => (r, c + 1),
                        None => p.authoritative().cursor(),
                    };
                    for &b in inp {
                        if c >= cols {
                            c = 0;
                            r = r.saturating_add(1);
                        }
                        expected.push((i as u64, r, c, b as char));
                        c += 1;
                    }
                }
            }
            if let Some(o) = outs.get(i) {
                let rec = out(o);
                p.apply_output(&rec);
                authoritative_out.push(rec);
            }
        }
        let authoritative = screen::fold(cols, rows, &authoritative_out);

        // The speculative view differs from ground truth at exactly the (in-bounds)
        // predicted cells: the faint overlay is real, and it leaks nowhere.
        let view = p.view();
        for r in 0..rows {
            for c in 0..cols {
                let predicted = expected.iter().any(|&(_, pr, pc, _)| pr == r && pc == c);
                let differs = view.cell(r, c) != authoritative.cell(r, c);
                prop_assert_eq!(differs, predicted, "cell ({}, {})", r, c);
            }
        }

        // Every verdict matches the oracle: a matching glyph confirms (a space only
        // once its cell is shown traversed — the cursor passed it, or a glyph was
        // painted to its right), a cell painted with anything else
        // (a glyph, or a coloured erase) contradicts, a never-painted blank is lost.
        let verdicts = p.reconcile();
        prop_assert_eq!(verdicts.len(), expected.len());
        for ((seq, verdict), &(eseq, r, c, ch)) in verdicts.iter().zip(&expected) {
            prop_assert_eq!(*seq, eseq);
            let oracle = match authoritative.cell(r, c) {
                Some(cell)
                    if cell.ch == ch
                        && (ch != ' '
                            || authoritative.cursor() > (r, c)
                            || authoritative.line_text(r).chars().count() > c as usize + 1) =>
                {
                    Verdict::Confirmed
                }
                Some(cell) if *cell != Cell::BLANK => Verdict::Contradicted,
                _ => Verdict::Lost,
            };
            prop_assert_eq!(*verdict, oracle, "prediction {:?} at ({}, {})", ch, r, c);
        }

        // And afterwards the view IS the authoritative fold: no residue.
        prop_assert_eq!(p.view().serialize(), authoritative.serialize());
    }
}

#[test]
fn program_predictor_learns_tui_navigation_and_generalizes_cursor_relative_ops() {
    let mut p = ProgramPredictor::new(24, 6);
    // Enter alternate screen (`?1049h`) and draw a 4-row TUI menu, parking cursor at (0, 0).
    p.apply_output(&out(
        b"\x1b[?1049hitem-0\r\nitem-1\r\nitem-2\r\nitem-3\x1b[H",
    ));
    assert!(p.authoritative().is_altscreen());
    assert_eq!(p.authoritative().cursor(), (0, 0));

    // Cold-start Down arrow (`ESC [ B`): abstains on first press, records context for learning.
    assert!(!p.predict_at(1, 100, b"\x1b[B"));
    assert_eq!(p.abstentions(), 1);
    assert_eq!(p.rule_count(), 0);

    // Authoritative response arrives with `caused_by = 100`: teaches `ESC [ B -> [CursorDown(1)]`.
    let v0 = p.apply_output_caused(1, Some(100), &out(b"\x1b[B"));
    assert!(
        v0.is_empty(),
        "cold-start abstention had no pending overlay"
    );
    assert_eq!(p.rule_count(), 1);
    assert_eq!(p.authoritative().cursor(), (1, 0));

    // Chain TWO in-flight Down-arrow presses across a high-RTT link before any server reply:
    // cursor-relative generalization applies from row 1 -> row 2 -> row 3 immediately!
    assert!(p.predict_at(2, 101, b"\x1b[B"));
    assert!(p.predict_at(3, 102, b"\x1b[B"));
    assert_eq!(p.pending_count(), 2);
    assert_eq!(p.view().cursor(), (3, 0));
    assert_eq!(p.authoritative().cursor(), (1, 0));

    // Server replies arrive in order and both confirm with zero contradiction.
    assert_eq!(
        p.apply_output_caused(2, Some(101), &out(b"\x1b[B")),
        vec![(2, Verdict::Confirmed)]
    );
    assert_eq!(
        p.apply_output_caused(3, Some(102), &out(b"\x1b[B")),
        vec![(3, Verdict::Confirmed)]
    );
    assert_eq!(p.hits(), 2);
    assert_eq!(p.misses(), 0);
    assert_eq!(p.pending_count(), 0);
    assert_eq!(p.view().serialize(), p.authoritative().serialize());
}

#[test]
fn program_predictor_screen_confluence_confirms_equivalent_vt_encodings() {
    let mut p = ProgramPredictor::new(20, 4);
    p.apply_output(&out(b"hello"));
    // Seed rule for Enter (`\r`) predicting `[CarriageReturn, LineFeed]` -> cursor (1, 0).
    let auth = p.authoritative().clone();
    let seeded = p.seed_rule(
        &auth,
        b"\r",
        vec![ScreenOp::CarriageReturn, ScreenOp::LineFeed],
    );
    assert!(seeded);

    assert!(p.predict_at(1, 10, b"\r"));
    assert_eq!(p.view().cursor(), (1, 0));

    // Server instead emits absolute CUP `ESC [ 2 ; 1 H` (`MoveTo(1, 0)`): different ScreenOp
    // representation, identical terminal Screen state -> confirmed by confluence!
    let verdicts = p.apply_output_caused(1, Some(10), &out(b"\x1b[2;1H"));
    assert_eq!(verdicts, vec![(1, Verdict::Confirmed)]);
    assert_eq!(p.hits(), 1);
    assert_eq!(p.misses(), 0);
    assert_eq!(p.view().serialize(), p.authoritative().serialize());
}

#[test]
fn program_predictor_squash_and_rebuild_reprojects_remaining_inflight_transitions() {
    let mut p = ProgramPredictor::new(24, 3);
    // Pipeline two printable inputs before server replies: speculative view shows "ab".
    assert!(p.predict_at(1, 50, b"a"));
    assert!(p.predict_at(2, 51, b"b"));
    assert_eq!(p.view().line_text(0), "ab");

    // Server contradicts input 50 by painting "> " instead of echoing "a":
    // input 50 retires Contradicted AND input 51 ("b") is squash-rebuilt on top of "> "!
    let v1 = p.apply_output_caused(10, Some(50), &out(b"> "));
    assert_eq!(v1, vec![(1, Verdict::Contradicted)]);
    assert_eq!(p.pending_count(), 1);
    assert_eq!(p.authoritative().line_text(0), ">");
    assert_eq!(p.view().line_text(0), "> b");
    assert_ne!(
        p.view().cell(0, 2).unwrap().attrs & attr::FAINT,
        0,
        "rebuilt speculative glyph stays faint until confirmed"
    );

    // Now input 51's authoritative echo "b" arrives and confirms cleanly!
    let v2 = p.apply_output_caused(11, Some(51), &out(b"b"));
    assert_eq!(v2, vec![(2, Verdict::Confirmed)]);
    assert_eq!(p.pending_count(), 0);
    assert_eq!(p.view().line_text(0), "> b");
    assert_eq!(p.view().cell(0, 2).unwrap().attrs & attr::FAINT, 0);
    assert_eq!(p.view().serialize(), p.authoritative().serialize());
}

#[test]
fn program_predictor_rule_cache_is_bounded_and_tui_hit_rate_exceeds_floor() {
    assert_eq!(program_rule_cap_clamp(500, MAX_PROGRAM_RULES as u64), 256);
    assert!(program_ops_within_cap(MAX_OPS_PER_RULE, MAX_OPS_PER_RULE));
    assert!(!program_ops_within_cap(
        MAX_OPS_PER_RULE + 1,
        MAX_OPS_PER_RULE
    ));

    let mut p = ProgramPredictor::new(40, 10);
    let auth = p.authoritative().clone();
    // Overflow rule cache with 300 distinct exact-context inputs: stays capped at MAX_PROGRAM_RULES.
    for i in 0..300u16 {
        let key = [(i & 0x7f) as u8, ((i >> 7) & 0x7f) as u8, b'!'];
        assert!(p.seed_rule(&auth, &key, vec![ScreenOp::CursorForward(1)]));
    }
    assert_eq!(p.rule_count(), MAX_PROGRAM_RULES);

    // Interactive TUI + readline workload: 50 causal turns mixing Down/Up navigation,
    // Backspace (`0x7f` -> `\x08\x1b[P`), and printable command typing.
    let mut tui = ProgramPredictor::new(40, 12);
    tui.apply_output(&out(b"\x1b[?1049h[0]\r\n[1]\r\n[2]\r\n[3]\r\n[4]\x1b[H"));
    let mut seq = 1u64;
    // 20 TUI navigation turns (first Down and first Up abstain on cold start; remaining 18 hit).
    for step in 0..10u64 {
        let _ = tui.predict_at(seq, seq, b"\x1b[B");
        let _ = tui.apply_output_caused(seq, Some(seq), &out(b"\x1b[B"));
        seq += 1;
        if step % 2 == 1 {
            let _ = tui.predict_at(seq, seq, b"\x1b[A");
            let _ = tui.apply_output_caused(seq, Some(seq), &out(b"\x1b[A"));
            seq += 1;
        }
    }
    // Leave altscreen to main prompt and run 30 readline typing + backspace turns.
    tui.apply_output(&out(b"\x1b[?1049l$ "));
    for step in 0..20u64 {
        let ch = [b'a' + ((step % 26) as u8)];
        let _ = tui.predict_at(seq, seq, &ch);
        let _ = tui.apply_output_caused(seq, Some(seq), &out(&ch));
        seq += 1;
        if step % 3 == 2 {
            // Readline backspace (`0x7f` -> `\x08\x1b[P`): cold-start abstains once, then hits!
            let _ = tui.predict_at(seq, seq, b"\x7f");
            let _ = tui.apply_output_caused(seq, Some(seq), &out(b"\x08\x1b[P"));
            seq += 1;
        }
    }
    let rate_bps = tui.hit_rate_bps();
    let rate = (rate_bps as f64) / 10_000.0;
    println!("METRIC program_predict_hit_rate={rate:.4}");
    assert!(
        rate_bps >= 9_000,
        "expected TUI + readline speculative hit rate >= 0.90 (9000 bps), got {rate:.4} ({rate_bps} bps; hits={}, misses={}, abstentions={})",
        tui.hits(),
        tui.misses(),
        tui.abstentions()
    );
    assert_eq!(tui.view().serialize(), tui.authoritative().serialize());
}

proptest! {
    #[test]
    fn proptest_program_predictor_always_converges_to_authoritative_screen(
        cols in 8u16..24,
        rows in 3u16..8,
        inputs in prop::collection::vec(prop::collection::vec(0u8..=127, 1..6), 0..20),
        outputs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..24), 0..20),
    ) {
        let mut p = ProgramPredictor::new(cols, rows);
        let mut auth_records = Vec::new();
        let n = inputs.len().max(outputs.len());
        for i in 0..n {
            let seq = (i as u64) + 1;
            if let Some(inp) = inputs.get(i) {
                let _ = p.predict_at(seq, seq, inp);
            }
            if let Some(out_bytes) = outputs.get(i) {
                let rec = out(out_bytes);
                let _ = p.apply_output_caused(seq, Some(seq), &rec);
                auth_records.push(rec);
            }
        }
        let _ = p.reconcile();
        let expected = screen::fold(cols, rows, &auth_records);
        prop_assert_eq!(p.pending_count(), 0);
        prop_assert_eq!(p.view().serialize(), expected.serialize());
    }
}

#[test]
fn speculative_terminal_cooked_line_edit_watermark_squash_and_password_suppression() {
    let mut term = SpeculativeTerminal::new(32, 6);
    term.apply_output(&out(b"$ "));

    // 1. Zero-cold-start cooked printable + Backspace (`0x7f`) + cursor motion (`ESC [ D`, `ESC [ C`):
    // Backspace predicts `[Backspace, DeleteChars(1)]`, which is screen-confluent with tty `\x08 \x08`!
    assert!(term.predict_at(1, 1, b"gitx"));
    assert!(term.predict_at(2, 2, b"\x7f"));
    assert_eq!(term.view().line_text(0), "$ git");
    assert_eq!(
        term.apply_output_caused(1, Some(1), &out(b"gitx")),
        vec![(1, Verdict::Confirmed)]
    );
    assert_eq!(
        term.apply_output_caused(2, Some(2), &out(b"\x08 \x08")),
        vec![(2, Verdict::Confirmed)]
    );
    assert!(term.predict_at(3, 3, b"\x1b[D"));
    assert_eq!(term.view().cursor(), (0, 4));
    assert_eq!(
        term.apply_output_caused(3, Some(3), &out(b"\x1b[D")),
        vec![(3, Verdict::Confirmed)]
    );
    assert!(term.predict_at(4, 4, b"\x1b[C"));
    assert_eq!(term.view().cursor(), (0, 5));
    assert_eq!(
        term.apply_output_caused(4, Some(4), &out(b"\x1b[C")),
        vec![(4, Verdict::Confirmed)]
    );

    // 2. Monotone watermark retirement (`apply_output_at`): batched echo, split echo,
    // stale-watermark rejection, and contradiction squash-rebuild.
    assert!(term.predict(5, b" "));
    assert!(term.predict(6, b"st"));
    // Batched echo confirms both seq 5 and seq 6 in one watermark step!
    assert_eq!(
        term.apply_output_at(10, &out(b" st")),
        vec![(5, Verdict::Confirmed), (6, Verdict::Confirmed)]
    );
    assert_eq!(term.out_watermark(), Some(10));
    // Stale/duplicate watermark is rejected without mutating screen.
    assert!(term.apply_output_at(10, &out(b"BOGUS")).is_empty());
    assert_eq!(term.authoritative().line_text(0), "$ git st");

    // Split echo of multi-byte prediction `"atus"` across watermarks 11 and 12:
    assert!(term.predict(7, b"atus"));
    assert!(term.apply_output_at(11, &out(b"at")).is_empty());
    assert_eq!(term.view().line_text(0), "$ git status");
    assert_eq!(
        term.apply_output_at(12, &out(b"us")),
        vec![(7, Verdict::Confirmed)]
    );

    // 3. Password / `stty -echo` prompt: first keystroke contradicts & squashes, engaging
    // row echo suppression so remaining secret bytes never flash faint on screen!
    term.apply_output(&out(b"\r\nPassword: "));
    assert!(term.predict_at(8, 8, b"s"));
    assert!(term.predict_at(9, 9, b"e"));
    assert_eq!(term.view().line_text(1), "Password: se");
    // Server answers keystroke 8 with silent/masked `*`: contradicts 8, engages no-echo on row 1,
    // and drops speculative `e` (9 -> Lost) so plaintext secret leaves the screen immediately!
    let v_pw = term.apply_output_caused(20, Some(8), &out(b"*"));
    assert_eq!(v_pw, vec![(8, Verdict::Contradicted), (9, Verdict::Lost)]);
    assert_eq!(term.squashes(), 1);
    assert_eq!(term.view().line_text(1), "Password: *");
    // Subsequent password chars on row 1 abstain cleanly without flashing plaintext!
    assert!(!term.predict_at(10, 10, b"c"));
    assert!(!term.predict_at(11, 11, b"r"));
    assert_eq!(term.view().line_text(1), "Password: *");

    // Pressing Enter (`\r`) moves to row 2 `$ `, restoring 0-RTT cooked echo immediately.
    let _ = term.predict_at(12, 12, b"\r");
    let _ = term.apply_output_caused(21, Some(12), &out(b"\r\n$ "));
    assert!(term.predict_at(13, 13, b"ok"));
    assert_eq!(term.view().line_text(2), "$ ok");
    assert_eq!(
        term.apply_output_caused(22, Some(13), &out(b"ok")),
        vec![(13, Verdict::Confirmed)]
    );
    assert_eq!(term.view().serialize(), term.authoritative().serialize());
}

proptest! {
    #[test]
    fn proptest_speculative_terminal_dual_retire_always_converges(
        cols in 8u16..24,
        rows in 3u16..8,
        inputs in prop::collection::vec(prop::collection::vec(0u8..=127, 1..5), 0..20),
        outputs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..20), 0..20),
        use_caused in prop::collection::vec(any::<bool>(), 0..20),
    ) {
        let mut term = SpeculativeTerminal::new(cols, rows);
        let mut auth_records = Vec::new();
        let n = inputs.len().max(outputs.len());
        let mut wm = 1u64;
        for i in 0..n {
            let seq = (i as u64) + 1;
            let caused = use_caused.get(i).copied().unwrap_or(false);
            if let Some(inp) = inputs.get(i) {
                if caused {
                    let _ = term.predict_at(seq, seq, inp);
                } else {
                    let _ = term.predict(seq, inp);
                }
            }
            if let Some(out_bytes) = outputs.get(i) {
                let rec = out(out_bytes);
                if caused {
                    let _ = term.apply_output_caused(wm, Some(seq), &rec);
                } else {
                    let _ = term.apply_output_at(wm, &rec);
                }
                wm += 1;
                auth_records.push(rec);
            }
        }
        let _ = term.reconcile();
        let expected = screen::fold(cols, rows, &auth_records);
        prop_assert_eq!(term.pending_count(), 0);
        prop_assert_eq!(term.view().serialize(), expected.serialize());
    }
}

#[test]
fn clean_origin_wide_cell_surface_and_speculative_wide_healing() {
    assert_eq!(astream_term::wide_cell_width_clamp(2, 2), 2);
    assert_eq!(astream_term::wide_cell_width_clamp(9, 2), 2);
    assert_eq!(astream_term::wide_cell_width_clamp(1, 2), 1);
    assert_eq!(astream_term::wide_spacer_col_clamp(4, 7), 4);
    assert_eq!(astream_term::wide_spacer_col_clamp(9, 7), 7);
    assert!(astream_term::cell_width_is_valid(0));
    assert!(astream_term::cell_width_is_valid(1));
    assert!(astream_term::cell_width_is_valid(2));
    assert!(!astream_term::cell_width_is_valid(3));
    assert_eq!(astream_term::char_display_width('A'), 1);
    assert_eq!(astream_term::char_display_width('\u{0301}'), 0);
    assert_eq!(astream_term::char_display_width('\u{200D}'), 0);
    assert_eq!(astream_term::char_display_width('漢'), 2);
    assert_eq!(astream_term::char_display_width('🚀'), 2);

    // Speculative ASCII prediction over half of a wide CJK glyph heals the orphaned half in `view()`.
    let mut term = SpeculativeTerminal::new(8, 2);
    let _ = term.apply_output_at(1, &out("漢字\r".as_bytes()));
    assert!(term.predict(1, b"X"));
    let v = term.view();
    assert_eq!(v.line_text(0), "X 字");
    assert_eq!(v.cell(0, 1).unwrap().width, 1);
}
