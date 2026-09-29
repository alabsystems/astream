//! Evidence for `term.echo.watermark-retire`: verified-speculation v1 — retire
//! speculative echo against the engine OUT-offset (`in_watermark`), squashing the
//! speculative tail on a contradiction, with the safety theorem preserved.
//!
//! The watermark is the authoritative output's engine offset, read BACK from a
//! real single-writer `Session` log via `Log::read_from` — a different numbering
//! domain from the per-client `client_seq`, never conflated. Retirement is by
//! monotone out-offset progress, not by a causal link; exact `caused_by`
//! retirement is a separate built property (`term.echo.caused-by-retire`,
//! `tests/caused_by_retire.rs`), not a later rung.

use astream_engine::{Log, MemDisk, Offset, Seeded, Session};
use astream_term::{screen, Predictor, Record, Verdict};
use proptest::prelude::*;

fn decode(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

#[test]
fn confirmed_predictions_retire_at_their_watermark() {
    let mut p = Predictor::new(20, 3);
    assert!(p.predict(1, b"hi"));

    // A real session echoes "hi"; capture the Out record's engine offset.
    let mut s = Session::new(Seeded::new(1));
    let off = s.append_output(b"hi".to_vec()).unwrap();
    let recs = decode(&s.log_bytes());

    let verdicts = p.apply_output_at(off.0, &recs[0]);
    assert!(
        !verdicts.is_empty() && verdicts.iter().all(|(_, v)| *v == Verdict::Confirmed),
        "the echoed predictions are confirmed at their watermark; got {verdicts:?}"
    );
    assert_eq!(p.in_watermark(), Some(off.0));
    assert_eq!(
        p.view().serialize(),
        p.authoritative().serialize(),
        "no residue"
    );
}

#[test]
fn contradiction_squashes_the_speculative_tail() {
    let mut p = Predictor::new(20, 3);
    p.predict(1, b"x");
    p.predict(2, b"y");
    p.predict(3, b"z");

    // The server echoes "xQz": the middle contradicts the 'y' prediction.
    let mut s = Session::new(Seeded::new(1));
    let off = s.append_output(b"xQz".to_vec()).unwrap();
    let recs = decode(&s.log_bytes());

    let verdicts = p.apply_output_at(off.0, &recs[0]);
    assert_eq!(
        verdicts,
        vec![
            (1, Verdict::Confirmed),
            (2, Verdict::Contradicted),
            (3, Verdict::Lost) // the tail after the contradiction is squashed
        ]
    );
    assert_eq!(p.view().serialize(), p.authoritative().serialize());
    assert_eq!(
        p.view().line_text(0),
        "xQz",
        "the view is the authoritative ground truth"
    );
}

#[test]
fn out_of_order_watermark_is_rejected() {
    let mut p = Predictor::new(20, 3);
    let mut s = Session::new(Seeded::new(1));
    s.append_output(b"a".to_vec()).unwrap(); // offset 0
    s.append_output(b"b".to_vec()).unwrap(); // offset 1
    let recs = decode(&s.log_bytes());

    p.apply_output_at(1, &recs[1]); // advance to watermark 1
    let auth = p.authoritative().serialize();

    let verdicts = p.apply_output_at(0, &recs[0]); // stale watermark
    assert!(verdicts.is_empty(), "a stale watermark retires nothing");
    assert_eq!(
        p.in_watermark(),
        Some(1),
        "the watermark never moves backward"
    );
    assert_eq!(
        p.authoritative().serialize(),
        auth,
        "a stale watermark does not re-fold"
    );
}

proptest! {
    /// For any predictions interleaved with watermark-ordered output, the
    /// authoritative screen stays the pure fold of the output (predictions never
    /// corrupt it — the safety theorem), and after final reconciliation no
    /// speculative residue remains.
    #[test]
    fn watermark_retirement_never_corrupts_the_authoritative_screen(
        inputs in prop::collection::vec(prop::collection::vec(0x20u8..0x7f, 0..5), 0..6),
        outs in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..8), 0..6),
    ) {
        let mut p = Predictor::new(20, 6);
        let mut s = Session::new(Seeded::new(3));
        for o in &outs { s.append_output(o.clone()).unwrap(); }
        let recs = decode(&s.log_bytes());

        let n = inputs.len().max(recs.len());
        for i in 0..n {
            if let Some(inp) = inputs.get(i) {
                p.predict(i as u64, inp);
            }
            if let Some(rec) = recs.get(i) {
                p.apply_output_at(i as u64, rec); // watermark == offset (dense log)
            }
        }
        prop_assert_eq!(p.authoritative().serialize(), screen::fold(20, 6, &recs).serialize());
        p.reconcile();
        prop_assert_eq!(p.view().serialize(), p.authoritative().serialize());
    }
}
