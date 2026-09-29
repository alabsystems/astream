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
use astream_term::{screen, Predictor, Record, Verdict};
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
