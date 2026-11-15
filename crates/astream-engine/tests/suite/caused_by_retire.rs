//! Evidence for `term.echo.caused-by-retire`: when echoes REORDER, positional /
//! watermark retirement (`apply_output_at`) mis-assigns a verdict, but exact
//! `caused_by` retirement (`apply_output_caused`) assigns every keystroke its
//! correct verdict — matched to a ground-truth map built independently of the
//! predictor, by comparing the Out's bytes (not a screen cell).
//!
//! The fixture log holds two REAL `In` records (applied through the session
//! ingest, so their in-offsets are the ones the appends returned) and two echo
//! `Out`s that arrive REORDERED, each stamped `caused_by` = the in-offset of the
//! keystroke it echoes. The engine validates that a same-log cause precedes its
//! record (a forward or self pointer is refused), and the test asserts each
//! decoded pointer names an `In`. HONEST: the correlation itself — which
//! keystroke an echo answers — is authored by the fixture; no host-side PTY
//! write->read correlation exists, so the pointers are stamped, not observed.

use astream_engine::{CausedBy, EngineError, Log, Offset, Seeded, Session};
use astream_term::{Predictor, Record, Verdict};

/// Keystroke client_seqs: keystroke A typed 'a', keystroke C typed 'c'.
const KEY_A: u64 = 1;
const KEY_C: u64 = 2;

/// Build a child log with two real keystrokes (in-offsets 0 and 1) whose echoes
/// arrive REORDERED — keystroke C's echo ('c', caused by in-offset 1) before
/// keystroke A's ('a', caused by in-offset 0) — and decode it back, so each Out
/// carries the in-offset it answers. Returns `(out_offset, in_offset, record)`
/// for every record (an `In` carries no cause).
fn reordered_echo_log() -> Vec<(u64, Option<u64>, Record)> {
    let mut s = Session::new(Seeded::new(0));
    let in_a = s.apply_input(1, KEY_A, b"a".to_vec()).unwrap().unwrap();
    let in_c = s.apply_input(1, KEY_C, b"c".to_vec()).unwrap().unwrap();
    assert_eq!((in_a, in_c), (Offset(0), Offset(1)));
    s.append_output_caused(
        b"c".to_vec(),
        CausedBy {
            partition: None,
            offset: in_c.0,
        },
    )
    .unwrap(); // Out@2 answers keystroke C
    s.append_output_caused(
        b"a".to_vec(),
        CausedBy {
            partition: None,
            offset: in_a.0,
        },
    )
    .unwrap(); // Out@3 answers keystroke A

    let bytes = s.log_bytes();
    let envs: Vec<_> = Log::read_bytes(&bytes, Offset::ZERO)
        .map(|r| r.unwrap())
        .collect();
    // Every decoded caused_by names a REAL In record that precedes its Out.
    let causes: Vec<u64> = envs
        .iter()
        .filter_map(|e| e.caused_by.map(|cb| cb.offset))
        .collect();
    assert_eq!(
        causes,
        vec![1, 0],
        "the echoes point at in-offsets 1 then 0"
    );
    for e in &envs {
        if let Some(cb) = e.caused_by {
            assert!(cb.offset < e.seq.0, "a cause precedes its effect");
            assert!(
                matches!(envs[cb.offset as usize].record, Record::In { .. }),
                "the cause is a keystroke, not another Out"
            );
        }
    }
    envs.into_iter()
        .map(|e| (e.seq.0, e.caused_by.map(|cb| cb.offset), e.record))
        .collect()
}

fn verdict_of(v: &[(u64, Verdict)], client_seq: u64) -> Option<Verdict> {
    v.iter().find(|(c, _)| *c == client_seq).map(|(_, vd)| *vd)
}

#[test]
fn caused_by_retirement_is_correct_under_reorder_where_positional_mis_assigns() {
    // GROUND TRUTH G, built independently of any predictor: keystroke A typed 'a'
    // and is answered by the echo 'a'; keystroke C typed 'c', answered by 'c'.
    // Each keystroke's own echo therefore CONFIRMS it.
    let g_confirmed = [KEY_A, KEY_C];

    let stream = reordered_echo_log();
    let outs: Vec<&(u64, Option<u64>, Record)> = stream
        .iter()
        .filter(|(_, _, r)| matches!(r, Record::Out(_)))
        .collect();
    assert_eq!(outs.len(), 2);

    // caused_by retirement: match each Out to the keystroke it answers by in-offset.
    let mut caused = Predictor::new(20, 4);
    caused.predict_at(KEY_A, 0, b"a"); // keystroke A sits at in-offset 0
    caused.predict_at(KEY_C, 1, b"c"); // keystroke C sits at in-offset 1
    let mut caused_verdicts = Vec::new();
    for (out_off, in_off, record) in &outs {
        caused_verdicts.extend(caused.apply_output_caused(*out_off, *in_off, record));
    }
    // Every keystroke gets its correct verdict from G.
    for k in g_confirmed {
        assert_eq!(
            verdict_of(&caused_verdicts, k),
            Some(Verdict::Confirmed),
            "caused_by retires keystroke {k} as Confirmed, matching G"
        );
    }

    // The DISCRIMINATING half: a masked echo. Keystroke A predicts 'a' but its
    // echo (matched by in-offset) carries bytes that do NOT contain 'a' -> the
    // verdict must be Contradicted, decided by comparing the Out's BYTES (a screen
    // cell would not discriminate here). Without this, the byte comparison could be
    // a no-op that always returns Confirmed and the test would still pass.
    let mut masked = Predictor::new(20, 4);
    masked.predict_at(KEY_A, 0, b"a");
    let masked_verdicts = masked.apply_output_caused(2, Some(0), &Record::Out(b"*".to_vec()));
    assert_eq!(
        verdict_of(&masked_verdicts, KEY_A),
        Some(Verdict::Contradicted),
        "caused_by decides Contradicted by comparing the Out's bytes to the predicted char"
    );

    // THE FOIL: positional/watermark retirement over the SAME reordered stream
    // mis-assigns — keystroke A's prediction sits at the cursor cell the
    // out-of-order 'c' lands on, so it is marked Contradicted though the world
    // never contradicted it.
    let mut positional = Predictor::new(20, 4);
    positional.predict_at(KEY_A, 0, b"a");
    positional.predict_at(KEY_C, 1, b"c");
    let mut foil_verdicts = Vec::new();
    let mut wm = 0u64;
    for (_out_off, _in_off, record) in &outs {
        wm += 1;
        foil_verdicts.extend(positional.apply_output_at(wm, record));
    }
    assert_eq!(
        verdict_of(&foil_verdicts, KEY_A),
        Some(Verdict::Contradicted),
        "positional retirement MIS-ASSIGNS keystroke A (the documented foil)"
    );
    // So caused_by does load-bearing work: it disagrees with the positional foil
    // and agrees with the ground truth.
    assert_ne!(
        verdict_of(&caused_verdicts, KEY_A),
        verdict_of(&foil_verdicts, KEY_A),
        "caused_by corrects the verdict the positional rule got wrong"
    );

    // Safety theorem preserved: the authoritative screen is a pure fold of the
    // recorded (arrival-order) output, untouched by any prediction.
    let out_records: Vec<Record> = outs.iter().map(|(_, _, r)| r.clone()).collect();
    let direct = astream_term::screen::fold(20, 4, &out_records);
    assert_eq!(
        caused.authoritative().serialize(),
        direct.serialize(),
        "authoritative == pure fold of the recorded outs (safety)"
    );
}

#[test]
fn the_engine_refuses_a_same_log_cause_that_does_not_precede_its_record() {
    let mut s = Session::new(Seeded::new(0));
    // Nothing precedes offset 0: a forward (or self) pointer is refused and the
    // log stays empty — a synthesized causality cannot be stored.
    assert_eq!(
        s.append_output_caused(
            b"c".to_vec(),
            CausedBy {
                partition: None,
                offset: 1,
            },
        ),
        Err(EngineError::CauseNotEarlier {
            cause: 1,
            seq: Offset(0)
        })
    );
    assert!(s.log_bytes().is_empty());
    // Once the keystroke is on the log, its echo may name it.
    let in0 = s.apply_input(1, KEY_A, b"a".to_vec()).unwrap().unwrap();
    assert_eq!(
        s.append_output_caused(
            b"a".to_vec(),
            CausedBy {
                partition: None,
                offset: in0.0,
            },
        ),
        Ok(Offset(1))
    );
}
