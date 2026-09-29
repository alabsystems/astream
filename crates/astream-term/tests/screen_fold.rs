//! The rung-0.5 evidence: the VT screen fold is a deterministic, I/O-free
//! function of the recorded output. Backs the manifest claim
//! `term.screen-fold.deterministic`.
//!
//! Three independent guarantees, none of them a constant-only tautology: (1)
//! folding a fixed adversarial record sequence matches an independently
//! reasoned-out expected screen (cursor, modes, specific cells); (2) folding it
//! twice is byte-identical (determinism); (3) In/Exit records never paint (input
//! does not draw the screen). Plus a property test: folding arbitrary bytes is
//! panic-free and deterministic.
//!
//! The remaining tests pin the parser's ECMA-48 edges against xterm's behaviour
//! (each one a case where a naive fold paints garbage or misplaces the cursor):
//! string sequences and two-byte escapes are swallowed, truecolour SGR
//! and private-marker CSI never reset the pen, ESC restarts inside a CSI, DEL and
//! malformed UTF-8 never land a control in a cell, the deferred wrap resolves the
//! way xterm's last-column flag does, and the saved cursor is per screen buffer.

use astream_term::screen::{attr, fold, Color};
use astream_term::Record;
use proptest::prelude::*;

fn out(b: &[u8]) -> Vec<Record> {
    vec![Record::Out(b.to_vec())]
}

/// A deliberately adversarial session: erase, cursor addressing, SGR colour and
/// bold, a full alternate-screen round-trip, an inline resize, and re-addressing
/// after the resize. Reasoning about its final screen by hand is the oracle.
fn adversarial() -> Vec<Record> {
    vec![
        Record::Out(b"\x1b[2J".to_vec()),            // clear whole screen
        Record::Out(b"\x1b[1;1HHELLO".to_vec()),     // home, write HELLO
        Record::Out(b"\x1b[31mRED\x1b[0m".to_vec()), // red "RED", then reset
        Record::Out(b"\r\n".to_vec()),               // CRLF -> row 1, col 0
        Record::Out(b"line2 \x1b[1mbold\x1b[22m end".to_vec()), // bold in the middle
        Record::Out(b"\x1b[?1049h".to_vec()),        // enter alternate screen
        Record::Out(b"\x1b[2JALT".to_vec()),         // clear alt, write ALT
        Record::Out(b"\x1b[?1049l".to_vec()),        // leave alt -> main restored
        Record::Resize { cols: 40, rows: 10 },       // grow the viewport
        Record::Out(b"\x1b[5;3Hmoved".to_vec()),     // address row 5 col 3, write
    ]
}

#[test]
fn fold_is_deterministic_and_matches_expected_screen() {
    let recs = adversarial();
    let a = fold(20, 6, &recs);
    let b = fold(20, 6, &recs);

    // (2) Determinism: identical input -> byte-identical screen.
    assert_eq!(
        a.serialize(),
        b.serialize(),
        "the fold must be deterministic"
    );

    // (1) Oracle: the screen we reasoned out by hand.
    assert_eq!(a.dims(), (40, 10), "resized viewport");
    assert!(!a.is_altscreen(), "back on the main screen after ?1049l");
    assert!(a.cursor_visible(), "cursor visibility untouched");
    assert_eq!(
        a.cursor(),
        (4, 7),
        "cursor after writing 'moved' at row5 col3"
    );

    // Main-screen content survived the alternate-screen round-trip.
    assert_eq!(a.line_text(0), "HELLORED", "HELLO then red RED, contiguous");
    assert_eq!(a.line_text(1), "line2 bold end");
    assert_eq!(
        a.line_text(4),
        "  moved",
        "addressed to col 3 (0-based col 2)"
    );

    // The 'R' of RED is red; the 'b' of bold is bold; the 'e' of end is not.
    let r = a.cell(0, 5).unwrap();
    assert_eq!(r.ch, 'R');
    assert_eq!(r.fg, Color::Indexed(1));
    let bold = a.cell(1, 6).unwrap();
    assert_eq!(bold.ch, 'b');
    assert_ne!(bold.attrs & attr::BOLD, 0);
    let e = a.cell(1, 11).unwrap();
    assert_eq!(e.ch, 'e');
    assert_eq!(e.attrs & attr::BOLD, 0);
}

#[test]
fn input_and_exit_records_do_not_paint() {
    // (3) Splice keystrokes and a child exit into the stream; neither may change
    // a single cell. Only echoed Out paints.
    let base = adversarial();
    let mut noisy = adversarial();
    noisy.insert(
        4,
        Record::In {
            bytes: b"rm -rf / # never echoed by this record".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
    );
    noisy.push(Record::Exit { code: 0 });

    assert_eq!(
        fold(20, 6, &base).serialize(),
        fold(20, 6, &noisy).serialize(),
        "In and Exit records must not paint the screen"
    );
}

#[test]
fn string_sequences_are_swallowed_never_painted() {
    // A title-setting prompt (OSC 0 ... BEL), OSC-133 shell marks, an OSC ended
    // by ST (ESC \), a DCS and an APC (kitty-graphics shaped) payload: none of
    // them paints, and the text after each lands where it would on xterm. A fold
    // that dropped only the introducer would paint "0;user@host: ~$ ls".
    let recs = vec![
        Record::Out(b"\x1b]0;user@host: ~\x07$ ls".to_vec()),
        Record::Out(b"\r\n\x1b]133;A\x07$ \x1b]133;B\x07ls\r\n\x1b]133;C\x07out\r\n".to_vec()),
        Record::Out(b"\x1b]2;st title\x1b\\a".to_vec()),
        Record::Out(b"\x1bPq#0;2;0;0;0#0~~\x1b\\b".to_vec()),
        Record::Out(b"\x1b_Gf=100,a=T;AAAA\x1b\\c".to_vec()),
    ];
    let s = fold(40, 6, &recs);
    assert_eq!(s.line_text(0), "$ ls");
    assert_eq!(s.line_text(1), "$ ls");
    assert_eq!(s.line_text(2), "out");
    assert_eq!(s.line_text(3), "abc");
    assert_eq!(s.cursor(), (3, 3));
}

#[test]
fn two_byte_escapes_and_charset_designations_paint_nothing() {
    // xterm's sgr0 is `ESC ( B ESC [ m`: the charset designation must not paint
    // a stray 'B'. Keypad-mode, index and DECALN escapes are consumed whole too.
    let s = fold(20, 3, &out(b"\x1b(B\x1b[mok\x1b)0\x1b=\x1b>\x1bM\x1b#8!"));
    assert_eq!(s.line_text(0), "ok!");
    assert_eq!(s.line_text(1), "");
    assert_eq!(s.cursor(), (0, 3));
}

#[test]
fn truecolour_sgr_is_consumed_not_redispatched_as_codes() {
    // `48;2;30;30;30` (a dark-grey background) used to re-dispatch 2/30/30/30, and
    // the `30` turned the foreground black. Out of scope must mean untouched.
    let s = fold(10, 1, &out(b"\x1b[1;31mX\x1b[48;2;30;30;30mY"));
    let y = s.cell(0, 1).unwrap();
    assert_eq!(y.fg, Color::Indexed(1), "foreground stays red");
    assert_eq!(
        y.bg,
        Color::Default,
        "truecolour bg is out of scope: ignored"
    );
    assert_ne!(y.attrs & attr::BOLD, 0, "bold survives");
    // `38;2;255;0;0` used to re-dispatch its `0` and reset the pen.
    let s = fold(10, 1, &out(b"\x1b[1mX\x1b[38;2;255;0;0mY"));
    assert_ne!(s.cell(0, 1).unwrap().attrs & attr::BOLD, 0);
    // The 256-colour form still selects, in both the `;` and the `:` forms; the
    // colon truecolour form (with a colour-space id) is consumed whole as well.
    let s = fold(
        10,
        1,
        &out(b"\x1b[38;5;196mA\x1b[0;48:5:21mB\x1b[1;38:2::10:20:30mC"),
    );
    assert_eq!(s.cell(0, 0).unwrap().fg, Color::Indexed(196));
    assert_eq!(s.cell(0, 1).unwrap().bg, Color::Indexed(21));
    let c = s.cell(0, 2).unwrap();
    assert_eq!(c.fg, Color::Default);
    assert_ne!(c.attrs & attr::BOLD, 0);
}

#[test]
fn backspace_and_cub_after_a_full_line_land_on_the_second_to_last_column() {
    // xterm keeps the cursor ON the last column with a wrap pending, so
    // readline's `BS X` echo after a line that exactly fills the width overwrites
    // the second-to-last cell. The fold used to overwrite the last one ("abcdX").
    let s = fold(5, 2, &out(b"abcde\x08X"));
    assert_eq!(s.line_text(0), "abcXe");
    assert_eq!(s.cursor(), (0, 4));
    let s = fold(5, 2, &out(b"abcde\x1b[DX"));
    assert_eq!(s.line_text(0), "abcXe");
    let s = fold(5, 2, &out(b"abcde\x1b[2DX"));
    assert_eq!(s.line_text(0), "abXde");
}

#[test]
fn cursor_motion_resolves_a_pending_wrap_but_tab_and_erase_keep_it() {
    // LF and CUU/CUD clear xterm's last-column flag: the next glyph lands on the
    // last column of the new row instead of wrapping a second time.
    let s = fold(4, 3, &out(b"abcd\nZ"));
    assert_eq!(s.line_text(1), "   Z");
    assert_eq!(s.line_text(2), "");
    let s = fold(4, 3, &out(b"\x1b[2;1Habcd\x1b[AZ"));
    assert_eq!(s.line_text(0), "   Z");
    let s = fold(4, 3, &out(b"abcd\x1b[BZ"));
    assert_eq!(s.line_text(1), "   Z");
    // DECSC/DECRC round-trip a pending wrap (aterm/xterm): after a save at the
    // margin, a home and a restore, the next glyph still wraps.
    let s = fold(4, 3, &out(b"abcd\x1b7\x1b[H\x1b8Z"));
    assert_eq!(s.line_text(0), "abcd");
    assert_eq!(s.line_text(1), "Z");
    // TAB and erase leave the wrap pending: the next glyph wraps. Erase-to-end
    // (EL 0 / ED 0) starts logically past the parked glyph, so it survives;
    // erase-to-cursor (EL 1) includes it.
    let s = fold(4, 3, &out(b"abcd\tZ"));
    assert_eq!(s.line_text(1), "Z");
    let s = fold(4, 3, &out(b"abcd\x1b[KZ"));
    assert_eq!(
        s.line_text(0),
        "abcd",
        "EL 0 from a pending wrap erases nothing"
    );
    assert_eq!(s.line_text(1), "Z");
    let s = fold(4, 3, &out(b"\x1b[2;1Hxyz\x1b[1;1Habcd\x1b[JZ"));
    assert_eq!(s.line_text(0), "abcd", "ED 0 keeps the parked row");
    assert_eq!(s.line_text(1), "Z", "…and clears the rows below");
    let s = fold(4, 3, &out(b"abcd\x1b[1KZ"));
    assert_eq!(
        s.line_text(0),
        "",
        "EL 1 through a pending wrap erases the row"
    );
    assert_eq!(s.line_text(1), "Z");
}

#[test]
fn esc_inside_an_unfinished_csi_starts_a_new_escape_and_c0_executes() {
    // A program killed mid-sequence leaves `ESC [ 3`; the next record's `ESC [ 2 J`
    // must be parsed (the screen cleared), not painted as "[2Jhi".
    let recs = vec![
        Record::Out(b"junk\x1b[3".to_vec()),
        Record::Out(b"\x1b[2Jhi".to_vec()),
    ];
    let s = fold(20, 3, &recs);
    assert_eq!(s.line_text(0), "    hi");
    // CR/LF arriving inside a CSI execute (ECMA-48), and the CSI still completes.
    let s = fold(20, 3, &out(b"ab\x1b[2\r\nCZ"));
    assert_eq!(s.line_text(0), "ab");
    assert_eq!(s.line_text(1), "  Z");
}

#[test]
fn del_is_ignored_and_malformed_utf8_never_lands_a_control_in_a_cell() {
    let s = fold(10, 1, &out(b"a\x7fb"));
    assert_eq!(s.line_text(0), "ab");
    // Overlong encodings of NUL and LF, then a validly encoded C1 control (CSI).
    let s = fold(10, 1, &out(b"\xc0\x80\xe0\x80\x8a\xc2\x9bx"));
    assert_eq!(s.line_text(0), "\u{fffd}\u{fffd}x");
    assert!(s.line_text(0).chars().all(|c| !c.is_control()));
    // A well-formed multibyte glyph still decodes.
    let s = fold(10, 1, &out("caf\u{e9}".as_bytes()));
    assert_eq!(s.line_text(0), "caf\u{e9}");
}

#[test]
fn private_marker_csi_and_colon_sgr_never_reset_the_pen() {
    // neovim's modifyOtherKeys handshake `CSI > 4 ; 2 m` used to parse as SGR 0;2
    // and reset the pen; `=`/`?`-marked and intermediate-bearing CSIs likewise.
    let s = fold(
        10,
        1,
        &out(b"\x1b[1;31mX\x1b[>4;2mY\x1b[=1mZ\x1b[?1;2mW\x1b[1 qV"),
    );
    for col in 0..5 {
        let cell = s.cell(0, col).unwrap();
        assert_eq!(cell.fg, Color::Indexed(1), "col {col} stays red");
        assert_ne!(cell.attrs & attr::BOLD, 0, "col {col} stays bold");
    }
    // Colon sub-parameters select (38:5:n, 4:n) instead of collapsing to SGR 0.
    let s = fold(10, 1, &out(b"\x1b[1mX\x1b[38:5:196mY\x1b[4:3mZ\x1b[4:0mW"));
    let y = s.cell(0, 1).unwrap();
    assert_eq!(y.fg, Color::Indexed(196));
    assert_ne!(y.attrs & attr::BOLD, 0);
    assert_ne!(s.cell(0, 2).unwrap().attrs & attr::UNDERLINE, 0);
    assert_eq!(s.cell(0, 3).unwrap().attrs & attr::UNDERLINE, 0);
}

#[test]
fn the_saved_cursor_survives_an_alt_screen_round_trip_and_is_per_buffer() {
    // DECSC at (2,3); `?1049h` saves into the SAME main slot (as xterm); a DECSC
    // inside the alt screen goes to the alt slot; `?1049l` restores (2,3); a later
    // bare DECRC on main still restores (2,3) — the slot is never consumed.
    let s = fold(
        20,
        12,
        &out(b"\x1b[3;4H\x1b7\x1b[?1049h\x1b[10;1Hx\x1b7\x1b[?1049l"),
    );
    assert_eq!(s.cursor(), (2, 3), "?1049l restores the main-screen cursor");
    let s = fold(
        20,
        12,
        &out(b"\x1b[3;4H\x1b7\x1b[?1049h\x1b[10;1Hx\x1b7\x1b[?1049l\x1b[1;1H\x1b8"),
    );
    assert_eq!(
        s.cursor(),
        (2, 3),
        "ESC 8 after the round trip still restores"
    );
    // The rxvt/screen rmcup shape `ESC 7 … ?47h … ESC 7 (in alt) … ?47l ESC 8`:
    // ?47 swaps buffers without moving the shared cursor; ESC 8 then restores
    // the main slot, which the alt-screen DECSC must not have clobbered.
    let s = fold(
        20,
        12,
        &out(b"\x1b[3;4H\x1b7\x1b[?47h\x1b[10;1Hxyz\x1b7\x1b[2J\x1b[?47l"),
    );
    assert_eq!(
        s.cursor(),
        (9, 3),
        "?47l leaves the cursor where the alt left it"
    );
    let s = fold(
        20,
        12,
        &out(b"\x1b[3;4H\x1b7\x1b[?47h\x1b[10;1Hxyz\x1b7\x1b[2J\x1b[?47l\x1b8"),
    );
    assert_eq!(
        s.cursor(),
        (2, 3),
        "the alt-screen DECSC did not clobber main"
    );
    assert!(!s.is_altscreen());
}

#[test]
fn entering_the_alternate_screen_keeps_the_shared_cursor_in_place() {
    // xterm's 1049 saves the cursor and switches; it does not home. An app that
    // paints before positioning paints where the cursor was.
    let s = fold(20, 3, &out(b"abc\x1b[?1049hXYZ"));
    assert!(s.is_altscreen());
    assert_eq!(s.line_text(0), "   XYZ");
    let s = fold(20, 3, &out(b"abc\x1b[?1049hXYZ\x1b[?1049lD"));
    assert!(!s.is_altscreen());
    assert_eq!(
        s.line_text(0),
        "abcD",
        "main restored, cursor back at (0,3)"
    );
}

proptest! {
    /// Folding any byte stream, at any small viewport, is panic-free and
    /// deterministic — the property the one adversarial fixture is an instance of.
    #[test]
    fn fold_arbitrary_bytes_is_panic_free_and_deterministic(
        bytes in prop::collection::vec(any::<u8>(), 0..512),
        cols in 1u16..40,
        rows in 1u16..20,
    ) {
        let recs = vec![Record::Out(bytes)];
        let a = fold(cols, rows, &recs);
        let b = fold(cols, rows, &recs);
        prop_assert_eq!(a.serialize(), b.serialize());
    }
}
