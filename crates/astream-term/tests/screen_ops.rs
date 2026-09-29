//! Evidence for `term.screen-ops.lossless-projection`: the single canonical VT
//! parser projects the raw Out byte log into a normalized typed screen-op stream,
//! and re-applying that op stream reproduces a byte-equal screen.
//!
//! One parser emits both the fold and the ops, so two viewers cannot disagree;
//! the SetSgr ops carry the resolved pen, not raw params. The equivalence is
//! non-trivial because `apply_ops` is an independent dispatch path that re-drives
//! the shared mutators from typed ops (bypassing only the VT state machine). The
//! proptest over arbitrary bytes is the safety net: a missed dispatch site
//! diverges and fails it.

use astream_term::{apply_ops, emit_ops, screen, Record, ScreenOp};
use proptest::prelude::*;

const COLS: u16 = 30;
const ROWS: u16 = 6;

/// An adversarial fixture exercising printable runs, SGR, erase, cursor moves,
/// the alternate screen, an inline resize, UTF-8, tab, backspace, the DECSTBM
/// scroll region, a background-colour erase, and string sequences (OSC + DCS)
/// — the whole subset the claim says the ops project losslessly.
fn fixture() -> Vec<Record> {
    vec![
        Record::Out(b"\x1b[2J\x1b[H".to_vec()),
        Record::Out(b"\x1b[31;1mERR\x1b[0m boot\r\n".to_vec()),
        Record::Out(b"line2 \x1b[1mbo".to_vec()), // bold on, split across...
        Record::Out(b"ld\x1b[22m end\r\n".to_vec()), // ...the next record
        Record::Resize { cols: 20, rows: 8 },
        Record::Out(b"\x1b[?1049h\x1b[2JALT".to_vec()), // enter altscreen
        Record::Out(b"caf\xc3\xa9\x1b[K".to_vec()),     // UTF-8 + erase-line
        Record::Out(b"\x1b[?1049l".to_vec()),           // leave altscreen
        Record::Out(b"\x1b[3;5Hmoved\t!".to_vec()),     // move + tab
        Record::Out(b"\x1b[2;6r\x1b[44m\x1b[2Kbce\r\nscroll\r\n".to_vec()), // DECSTBM + bce erase
        Record::Out(b"\x1b]0;~t~\x07\x1bPq~d~\x1b\\ok".to_vec()), // OSC + DCS: no ops
        Record::Out(b"\x1b[7mZ\x08x".to_vec()),         // reverse + backspace
        Record::Exit { code: 0 },
    ]
}

#[test]
fn ops_re_apply_to_a_byte_equal_screen() {
    let recs = fixture();
    let ops = emit_ops(COLS, ROWS, &recs);
    let from_ops = apply_ops(COLS, ROWS, &ops);
    let from_fold = screen::fold(COLS, ROWS, &recs);

    assert_eq!(
        from_ops.serialize(),
        from_fold.serialize(),
        "re-applying the op stream reproduces the raw VT fold"
    );

    // The projection is non-vacuous: it carries real typed ops.
    assert!(
        ops.iter().any(|o| matches!(o, ScreenOp::Print(_))),
        "has Print ops"
    );
    assert!(
        ops.iter().any(|o| matches!(o, ScreenOp::SetSgr { .. })),
        "has resolved SetSgr ops"
    );
    assert!(
        ops.iter().any(|o| matches!(o, ScreenOp::Resize(..))),
        "has a Resize op"
    );
    // The scroll region and background-colour erase are inside the projection...
    assert!(
        ops.iter()
            .any(|o| matches!(o, ScreenOp::SetScrollRegion { .. })),
        "has a SetScrollRegion op"
    );
    // ...and the swallowed string sequences are outside it: `~` occurs only
    // inside the OSC title and the DCS payload, and neither leaves a Print op.
    assert!(
        !ops.iter().any(|o| matches!(o, ScreenOp::Print('~'))),
        "string-sequence payloads emit no op"
    );
}

proptest! {
    /// For ANY byte stream at any small viewport, re-applying the emitted ops
    /// reproduces the raw fold. A missed mutator dispatch site fails this.
    #[test]
    fn ops_equal_the_fold_for_arbitrary_bytes(
        chunks in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..12), 0..6),
        cols in 1u16..24,
        rows in 1u16..8,
    ) {
        let recs: Vec<Record> = chunks.iter().map(|c| Record::Out(c.clone())).collect();
        let ops = emit_ops(cols, rows, &recs);
        let from_ops = apply_ops(cols, rows, &ops);
        let from_fold = screen::fold(cols, rows, &recs);
        prop_assert_eq!(from_ops.serialize(), from_fold.serialize());
    }
}
