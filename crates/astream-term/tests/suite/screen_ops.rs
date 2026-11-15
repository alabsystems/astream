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

use astream_term::screen::attr;
use astream_term::{
    apply_ops, apply_ops_to, decode_ops, emit_ops, encode_ops, screen, Charset, Color, Folder,
    OpsWireError, Record, Screen, ScreenOp, Underline, MAX_MODE_PARAMS, MAX_OPS_PER_BATCH,
    OPS_WIRE_MAGIC, OPS_WIRE_VERSION, WIRE_UNDERLINE,
};
use proptest::prelude::*;

const COLS: u16 = 30;
const ROWS: u16 = 6;

/// An adversarial fixture exercising printable runs, SGR, erase, cursor moves,
/// the alternate screen, an inline resize, UTF-8, tab, backspace, the DECSTBM
/// scroll region, a background-colour erase, origin, insert and newline mode,
/// the character sets, left/right margins, the underline's style and colour, and
/// string sequences (OSC + DCS)
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
        Record::Out(b"\x1b[0m\x1b[2;1H\x1bM\x1bD\x1bE\x0b\x0c".to_vec()), // RI, IND, NEL, VT, FF
        Record::Out(b"\x1b[3;2H\x1b[2@\x1b[P\x1b[3X\x1b[L\x1b[2M".to_vec()), // ICH DCH ECH IL DL
        // DECOM (addressing from the top margin), IRM, SU and SD.
        Record::Out(b"\x1b[?6h\x1b[2;2H\x1b7\x1b[4hin\x1b[4l\x1b[2S\x1b[T\x1b[?6l\x1b8".to_vec()),
        Record::Out(b"\x1b[20hnl\nnl\x1b[20l".to_vec()), // LNM
        Record::Out(b"\x1b)0\x0eqx\x1b7\x0f\x1b(0lk\x1b(B\x1b8".to_vec()), // SCS, SO/SI
        // DECLRMM and DECSLRM: a wrap on the right margin, ICH/DCH/IL/DL and
        // a scroll inside the margins, the wrap saved and restored.
        Record::Out(
            b"\x1b[?69h\x1b[5;12s\x1b[?6h\x1b[1;1Hmargin wrap\x1b7\x1b[2@\x1b[P\x1b[L\x1b[M\x1b[S\x1b8!\x1b[?6l\x1b[?69l"
                .to_vec(),
        ),
        // 24-bit truecolour (both `;` and `:` forms) + zero-width combining marks +
        // East Asian wide CJK & ZWJ emoji grapheme clusters.
        Record::Out(
            "\x1b[38;2;240;120;60;48:2::15:25:35me\u{0301}\u{0327}漢👨\u{200D}💻\x1b[39;49m"
                .as_bytes()
                .to_vec(),
        ),
        // The underline's styles and colours: a curly one in 24-bit colour, saved by
        // DECSC; a double one in a palette colour; 59, 24 and 0 taking them off.
        Record::Out(
            b"\x1b[4:3;58:2::200:100:0mcurl\x1b7\x1b[21;58;5;161mdbl\x1b[59mx\x1b8y\x1b[24mz\x1b[4;58:5:9m\x1b[0mw"
                .to_vec(),
        ),
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
        ops.iter().any(|o| matches!(o, ScreenOp::SetSgrRgb { .. })),
        "has resolved SetSgrRgb ops"
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
    // ...and so are insert mode and the scrolls...
    assert!(
        ops.iter()
            .any(|o| matches!(o, ScreenOp::SetInsertMode(true))),
        "has a SetInsertMode op"
    );
    assert!(
        ops.iter().any(|o| matches!(o, ScreenOp::ScrollUp(2)))
            && ops.iter().any(|o| matches!(o, ScreenOp::ScrollDown(1))),
        "has ScrollUp and ScrollDown ops"
    );
    // ...and the left/right margins...
    assert!(
        ops.iter()
            .any(|o| matches!(o, ScreenOp::SetLeftRightMargins { left: 4, right: 11 })),
        "has a SetLeftRightMargins op"
    );
    // ...and the swallowed string sequences are outside it: `~` occurs only
    // inside the OSC title and the DCS payload, and neither leaves a Print op.
    assert!(
        !ops.iter().any(|o| matches!(o, ScreenOp::Print('~'))),
        "string-sequence payloads emit no op"
    );
}

#[test]
fn ops_wire_codec_roundtrips_all_variants_and_incremental_folder_recording() {
    // 1. Every `ScreenOp` variant + all `Color` & `Charset` variants roundtrips
    // byte-identically through `encode_ops` -> `decode_ops`.
    let exhaustive = vec![
        ScreenOp::Print('λ'),
        ScreenOp::CarriageReturn,
        ScreenOp::LineFeed,
        ScreenOp::Tab,
        ScreenOp::Backspace,
        ScreenOp::CursorUp(2),
        ScreenOp::CursorDown(4),
        ScreenOp::CursorForward(7),
        ScreenOp::CursorBack(3),
        ScreenOp::MoveTo(3, 17),
        ScreenOp::EraseDisplay(2),
        ScreenOp::EraseLine(1),
        ScreenOp::EraseChars(5),
        ScreenOp::InsertChars(4),
        ScreenOp::DeleteChars(1),
        ScreenOp::InsertLines(2),
        ScreenOp::DeleteLines(1),
        ScreenOp::ReverseIndex,
        ScreenOp::SetSgr {
            fg: Color::Default,
            bg: Color::Indexed(208),
            attrs: attr::BOLD | WIRE_UNDERLINE | attr::REVERSE,
        },
        ScreenOp::SetSgr {
            fg: Color::Indexed(42),
            bg: Color::Default,
            attrs: attr::FAINT,
        },
        ScreenOp::SetSgrRgb {
            fg: Color::Default,
            fg_rgb: Some((240, 120, 60)),
            bg: Color::Indexed(18),
            bg_rgb: None,
            attrs: attr::BOLD,
        },
        ScreenOp::SetSgrRgb {
            fg: Color::Indexed(7),
            fg_rgb: None,
            bg: Color::Default,
            bg_rgb: Some((15, 25, 35)),
            attrs: WIRE_UNDERLINE,
        },
        ScreenOp::SetSgrRgb {
            fg: Color::Default,
            fg_rgb: Some((1, 2, 3)),
            bg: Color::Default,
            bg_rgb: Some((4, 5, 6)),
            attrs: attr::REVERSE,
        },
        ScreenOp::SetUnderline {
            style: Underline::Curly,
            ul: Color::Default,
            ul_rgb: Some((200, 100, 0)),
        },
        ScreenOp::SetUnderline {
            style: Underline::Dashed,
            ul: Color::Indexed(161),
            ul_rgb: None,
        },
        ScreenOp::SetUnderline {
            style: Underline::None,
            ul: Color::Default,
            ul_rgb: None,
        },
        ScreenOp::SetMode {
            params: vec![1, 25, 2004],
            set: true,
        },
        ScreenOp::SaveCursor,
        ScreenOp::RestoreCursor,
        ScreenOp::SetScrollRegion { top: 1, bottom: 5 },
        ScreenOp::SetInsertMode(true),
        ScreenOp::SetNewlineMode(true),
        ScreenOp::Designate {
            g1: true,
            charset: Charset::DecSpecial,
        },
        ScreenOp::Designate {
            g1: false,
            charset: Charset::Ascii,
        },
        ScreenOp::LockShift { g1: true },
        ScreenOp::SetLeftRightMargins { left: 2, right: 18 },
        ScreenOp::ScrollUp(3),
        ScreenOp::ScrollDown(2),
        ScreenOp::Reset,
        ScreenOp::Resize(42, 11),
    ];
    let wire = encode_ops(&exhaustive).expect("exhaustive batch encodes");
    assert_eq!(&wire[..4], &OPS_WIRE_MAGIC);
    assert_eq!(wire[4], OPS_WIRE_VERSION);
    let decoded = decode_ops(&wire).expect("exhaustive batch decodes");
    assert_eq!(decoded, exhaustive);

    // 2. Fixture batch wire roundtrip + incremental per-record `Folder::new_recording`
    // -> `take_ops` -> `encode_ops` -> `decode_ops` -> `apply_ops_to` viewer parity.
    let recs = fixture();
    let mut host = Folder::new_recording(COLS, ROWS);
    let mut viewer = Screen::new(COLS, ROWS);
    for (idx, rec) in recs.iter().enumerate() {
        host.apply(rec);
        let delta = host.take_ops();
        let packet = encode_ops(&delta).expect("delta batch encodes");
        let rx_delta = decode_ops(&packet).expect("delta batch decodes");
        assert_eq!(rx_delta, delta, "step {idx} wire roundtrip");
        apply_ops_to(&mut viewer, &rx_delta);
        assert_eq!(
            viewer.serialize(),
            host.screen().serialize(),
            "step {idx} incremental viewer matches host VT fold"
        );
    }

    // 3. Reject malformed/hostile frames deterministically without panicking or OOMing.
    assert_eq!(decode_ops(b"ASO"), Err(OpsWireError::Truncated));
    assert_eq!(decode_ops(b"ASOP\x01\x00"), Err(OpsWireError::Truncated));
    assert_eq!(
        decode_ops(b"NOPE\x01\x00\x00\x00\x00"),
        Err(OpsWireError::BadMagic(*b"NOPE"))
    );
    assert_eq!(
        decode_ops(b"ASOP\x02\x00\x00\x00\x00"),
        Err(OpsWireError::UnsupportedVersion(2))
    );
    let mut over_cap = Vec::from(&b"ASOP\x01"[..]);
    over_cap.extend_from_slice(&((MAX_OPS_PER_BATCH as u32 + 1).to_le_bytes()));
    assert_eq!(
        decode_ops(&over_cap),
        Err(OpsWireError::TooManyOps(MAX_OPS_PER_BATCH + 1))
    );
    // Max legal count with empty body hits Truncated immediately without allocating
    // 1M ScreenOps up front.
    let mut truncated_huge = Vec::from(&b"ASOP\x01"[..]);
    truncated_huge.extend_from_slice(&(MAX_OPS_PER_BATCH as u32).to_le_bytes());
    assert_eq!(decode_ops(&truncated_huge), Err(OpsWireError::Truncated));

    // Invalid UTF-32 surrogate in Print (`tag = 1`).
    let mut bad_char = Vec::from(&b"ASOP\x01\x01\x00\x00\x00\x01"[..]);
    bad_char.extend_from_slice(&0xD800u32.to_le_bytes());
    assert_eq!(
        decode_ops(&bad_char),
        Err(OpsWireError::InvalidChar(0xD800))
    );

    // An underline style past `4:5` (`tag = 0x22`, style 6).
    assert_eq!(
        decode_ops(b"ASOP\x01\x01\x00\x00\x00\x22\x06\x00\x00\x00"),
        Err(OpsWireError::InvalidUnderlineStyle(6))
    );

    // A colour tag past `1` names the op it sits in: SetUnderline's colour (`tag = 0x22`,
    // style 3, colour tag 7), SetSgr's background (`0x13`) and SetSgrRgb's foreground (`0x21`).
    assert_eq!(
        decode_ops(b"ASOP\x01\x01\x00\x00\x00\x22\x03\x07")
            .expect_err("colour tag 7")
            .to_string(),
        "invalid Color wire tag 0x07 in ScreenOp::SetUnderline"
    );
    for (frame, op, tag) in [
        (
            &b"ASOP\x01\x01\x00\x00\x00\x22\x00\x02"[..],
            "SetUnderline",
            2,
        ),
        (&b"ASOP\x01\x01\x00\x00\x00\x13\x00\x05"[..], "SetSgr", 5),
        (&b"ASOP\x01\x01\x00\x00\x00\x21\x09"[..], "SetSgrRgb", 9),
    ] {
        assert_eq!(
            decode_ops(frame),
            Err(OpsWireError::InvalidColorTag { op, tag })
        );
    }

    // Unknown op tag (`0xfe`).
    assert_eq!(
        decode_ops(b"ASOP\x01\x01\x00\x00\x00\xfe"),
        Err(OpsWireError::UnknownOpTag(0xfe))
    );

    // SetMode exceeding MAX_MODE_PARAMS on encode and decode.
    let huge_mode = [ScreenOp::SetMode {
        params: vec![0; MAX_MODE_PARAMS + 1],
        set: true,
    }];
    assert_eq!(
        encode_ops(&huge_mode),
        Err(OpsWireError::TooManyModeParams(MAX_MODE_PARAMS + 1))
    );

    // Trailing garbage byte after valid 0-op batch.
    assert_eq!(
        decode_ops(b"ASOP\x01\x00\x00\x00\x00\xff"),
        Err(OpsWireError::TrailingBytes(1))
    );
}

#[test]
fn dec_session_modes_and_osc_metadata_project_and_reset_cleanly() {
    let mut folder = Folder::new_recording(40, 6);
    let baseline = folder.screen().serialize();

    // 1. Split OSC 0/2 title + OSC 7 working directory (with percent-encoding & ST terminator)
    // leave Screen::serialize() and recorded ScreenOps 100% untouched.
    folder.apply(&Record::Out(b"\x1b]0;claude:\x07".to_vec()));
    assert_eq!(folder.title(), "claude:");
    folder.apply(&Record::Out(b"\x1b]2;agy \x1b".to_vec()));
    folder.apply(&Record::Out(b"\\".to_vec()));
    assert_eq!(folder.title(), "agy ");
    // Control bytes inside OSC 0/2 are stripped; abandoned OSC (`ESC [`) does not clobber title.
    folder.apply(&Record::Out(b"\x1b]0;clean\n\x07".to_vec()));
    assert_eq!(folder.title(), "clean");
    folder.apply(&Record::Out(b"\x1b]0;abandoned\x1b[0m".to_vec()));
    assert_eq!(folder.title(), "clean");

    // OSC 7 with hostname + percent-encoded spaces across a record split.
    folder.apply(&Record::Out(b"\x1b]7;file://mac.local/fixture-".to_vec()));
    folder.apply(&Record::Out(b"home/my%20repo\x07".to_vec()));
    assert_eq!(folder.cwd(), "/fixture-home/my repo");
    assert_eq!(
        folder.screen().serialize(),
        baseline,
        "OSC 0/2/7 metadata must not perturb Screen::serialize() when SGR is at reset"
    );

    // 2. DEC private modes ?1 (DECCKM), ?1004 (focus), ?2004 (bracketed paste), ?2026 (sync)
    // roundtrip through ScreenOp projection and reset on RIS (`ESC c`).
    let mode_recs = vec![
        Record::Out(b"\x1b[?1;1004;2004;2026hhello".to_vec()),
        Record::Out(b"\x1b[?2026l!".to_vec()),
    ];
    let folded = screen::fold(40, 6, &mode_recs);
    assert!(folded.app_cursor_keys());
    assert!(folded.focus_events());
    assert!(folded.bracketed_paste());
    assert!(!folded.synchronized_output());

    let ops = emit_ops(40, 6, &mode_recs);
    let replayed = apply_ops(40, 6, &ops);
    assert_eq!(replayed, folded);
    assert_eq!(replayed.serialize(), folded.serialize());

    // RIS clears all 4 modes plus Folder title & cwd, restoring reset Tag-4 absence.
    folder.apply(&Record::Out(b"\x1b[?1;1004;2004;2026h\x1bc".to_vec()));
    assert!(!folder.screen().app_cursor_keys());
    assert!(!folder.screen().focus_events());
    assert!(!folder.screen().bracketed_paste());
    assert!(!folder.screen().synchronized_output());
    assert_eq!(folder.title(), "");
    assert_eq!(folder.cwd(), "");
    assert_eq!(folder.screen().serialize(), baseline);
}

fn assert_osc_title_at_every_record_split(payload: &[u8], expected: &str) {
    let mut osc = b"\x1b]2;".to_vec();
    osc.extend_from_slice(payload);
    osc.push(0x07);
    for split in 0..=osc.len() {
        let mut folder = Folder::new_recording(8, 2);
        let baseline = folder.screen().serialize();
        folder.apply(&Record::Out(osc[..split].to_vec()));
        folder.apply(&Record::Out(osc[split..].to_vec()));
        assert_eq!(folder.title(), expected, "record split at byte {split}");
        assert_eq!(
            folder.screen().serialize(),
            baseline,
            "metadata paints no cells"
        );
    }
}

#[test]
fn osc_title_replaces_malformed_utf8_once_per_invalid_sequence() {
    // The truncated three-byte sequence is one invalid sequence; each following
    // isolated 0xff is another. A record boundary must not change that grouping.
    assert_osc_title_at_every_record_split(b"A\xe2\x82Z\xff\xff", "A\u{fffd}Z\u{fffd}\u{fffd}");
}

#[test]
fn osc_title_strips_controls_and_preserves_unicode() {
    assert_osc_title_at_every_record_split("α\n\r\0\u{007f}\u{0085}β".as_bytes(), "αβ");
}

#[test]
fn osc_title_stops_at_a_nonfitting_unicode_scalar() {
    let prefix = "a".repeat(screen::MAX_OSC_TITLE_BYTES - 2);
    // The three-byte scalar cannot fit. The later one-byte character must not
    // be admitted after skipping it.
    assert_osc_title_at_every_record_split(format!("{prefix}€x").as_bytes(), &prefix);

    let prefix = "a".repeat(screen::MAX_OSC_TITLE_BYTES - 3);
    let expected = format!("{prefix}€");
    assert_eq!(expected.len(), screen::MAX_OSC_TITLE_BYTES);
    assert_osc_title_at_every_record_split(format!("{expected}x").as_bytes(), &expected);
}

#[test]
fn osc_title_counts_replacement_bytes_toward_the_limit() {
    for remaining in [2, 3] {
        let prefix = "a".repeat(screen::MAX_OSC_TITLE_BYTES - remaining);
        let mut payload = prefix.as_bytes().to_vec();
        payload.extend_from_slice(b"\xffx");
        let expected = if remaining == 3 {
            format!("{prefix}\u{fffd}")
        } else {
            prefix
        };
        assert_osc_title_at_every_record_split(&payload, &expected);
    }
}

proptest! {
    /// For ANY byte stream at any small viewport, re-applying the emitted ops
    /// reproduces the raw fold, AND roundtripping the ops through `encode_ops` /
    /// `decode_ops` reproduces the exact op list and serialized screen.
    #[test]
    fn ops_equal_the_fold_for_arbitrary_bytes(
        chunks in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..12), 0..6),
        cols in 1u16..24,
        rows in 1u16..8,
    ) {
        let recs: Vec<Record> = chunks.iter().map(|c| Record::Out(c.clone())).collect();
        let ops = emit_ops(cols, rows, &recs);
        let wire = encode_ops(&ops).expect("emitted ops fit batch limits");
        let decoded = decode_ops(&wire).expect("encoded ops decode");
        prop_assert_eq!(&decoded, &ops);
        let from_ops = apply_ops(cols, rows, &decoded);
        let from_fold = screen::fold(cols, rows, &recs);
        prop_assert_eq!(from_ops.serialize(), from_fold.serialize());
    }

    /// Arbitrary hostile byte slices (including valid `ASOP\x01` headers followed by
    /// arbitrary counts/tags/payloads) never panic or over-allocate in `decode_ops`.
    #[test]
    fn decode_ops_never_panics_on_arbitrary_bytes(
        body in prop::collection::vec(any::<u8>(), 0..96),
        valid_header in any::<bool>(),
    ) {
        let mut buf = if valid_header {
            b"ASOP\x01".to_vec()
        } else {
            Vec::new()
        };
        buf.extend_from_slice(&body);
        let _ = decode_ops(&buf);
    }
}
