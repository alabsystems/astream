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

use astream_term::screen::{attr, fold, Color, Underline};
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
    // a stray 'B'. Keypad-mode and DECALN escapes are consumed whole too.
    let s = fold(20, 3, &out(b"\x1b(B\x1b[mok\x1b)0\x1b=\x1b>\x1b#8!"));
    assert_eq!(s.line_text(0), "ok!");
    assert_eq!(s.line_text(1), "");
    assert_eq!(s.cursor(), (0, 3));
}

#[test]
fn truecolour_sgr_is_consumed_not_redispatched_as_codes() {
    // `48;2;30;30;30` (a dark-grey background) must not re-dispatch 2/30/30/30
    // (where `30` would turn the foreground black); it sets 24-bit `bg_rgb`
    // while leaving `fg` untouched.
    let s = fold(10, 1, &out(b"\x1b[1;31mX\x1b[48;2;30;30;30mY"));
    let y = s.cell(0, 1).unwrap();
    assert_eq!(y.fg, Color::Indexed(1), "foreground stays red");
    assert_eq!(y.fg_rgb, None);
    assert_eq!(y.bg, Color::Default);
    assert_eq!(y.bg_rgb, Some((30, 30, 30)), "24-bit truecolour bg stored");
    assert_ne!(y.attrs & attr::BOLD, 0, "bold survives");
    // `38;2;255;0;0` sets 24-bit `fg_rgb` without re-dispatching `0` as SGR reset.
    let s = fold(10, 1, &out(b"\x1b[1mX\x1b[38;2;255;0;0mY"));
    let y = s.cell(0, 1).unwrap();
    assert_eq!(y.fg_rgb, Some((255, 0, 0)));
    assert_ne!(y.attrs & attr::BOLD, 0);
    // The 256-colour form selects in both `;` and `:` forms, and the colon
    // truecolour form (with an optional colour-space id) sets 24-bit `fg_rgb`.
    let s = fold(
        10,
        1,
        &out(b"\x1b[38;5;196mA\x1b[0;48:5:21mB\x1b[1;38:2::10:20:30mC"),
    );
    assert_eq!(s.cell(0, 0).unwrap().fg, Color::Indexed(196));
    assert_eq!(s.cell(0, 1).unwrap().bg, Color::Indexed(21));
    let c = s.cell(0, 2).unwrap();
    assert_eq!(c.fg, Color::Default);
    assert_eq!(c.fg_rgb, Some((10, 20, 30)));
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
fn cursor_motion_and_erase_resolve_a_pending_wrap_but_tab_keeps_it() {
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
    // TAB leaves the wrap pending: the next glyph wraps.
    let s = fold(4, 3, &out(b"abcd\tZ"));
    assert_eq!(s.line_text(1), "Z");
    // ED/EL clear it and erase from the parked glyph: xterm's `ClearRight`
    // clears from `cur_col` (the last column, where xterm parks the cursor)
    // inclusive and ends in `ResetWrap`, so the next glyph overwrites the last
    // column instead of wrapping (Ghostty's goldens and aterm agree). The
    // xterm.js reading, an erase that starts past the parked glyph, keeps it.
    let s = fold(4, 3, &out(b"abcd\x1b[KZ"));
    assert_eq!(s.line_text(0), "abcZ", "EL 0 erases the parked glyph");
    assert_eq!(s.line_text(1), "", "and the wrap is gone");
    let s = fold(4, 3, &out(b"\x1b[2;1Hxyz\x1b[1;1Habcd\x1b[JZ"));
    assert_eq!(s.line_text(0), "abcZ", "ED 0 erases it too");
    assert_eq!(s.line_text(1), "", "and clears the rows below");
    let s = fold(4, 3, &out(b"abcd\x1b[1KZ"));
    assert_eq!(s.line_text(0), "   Z", "EL 1 erases through it");
    assert_eq!(s.cursor(), (0, 4));
    // `ED 3` erases saved lines only: the screen and the pending wrap stay.
    let s = fold(4, 3, &out(b"abcd\x1b[3JZ"));
    assert_eq!(s.line_text(0), "abcd", "ED 3 spares the screen");
    assert_eq!(s.line_text(1), "Z", "and the wrap");
}

#[test]
fn a_width_resize_clips_each_row_and_keeps_the_next_write() {
    // aterm's `resize-keeps-the-next-write` (aterm-grid) without reflow, which aterm's
    // differential VT oracle holds the two engines to wherever aterm does not rewrap: a wrap
    // pending at the edge (`col == cols`) keeps its next write, and a cursor whose cell a
    // narrowing cuts off is clamped as xterm clamps it.
    let resized = |cols: u16, before: &[u8], to: u16, after: &[u8]| {
        let recs = [
            Record::Out(before.to_vec()),
            Record::Resize { cols: to, rows: 2 },
            Record::Out(after.to_vec()),
        ];
        fold(cols, 2, &recs)
    };
    // A widening leaves the cursor on the column after the glyph it wrapped from.
    let s = resized(5, b"abcde", 10, b"X");
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        ("abcdeX".into(), String::new())
    );
    // A narrowing that cuts off the cursor's own cell clamps it onto the last column with no
    // wrap, as xterm does, so the next glyph neither wraps onto the row below nor scrolls.
    let s = resized(10, b"abc\x1b[8G", 5, b"");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 4), false));
    let s = resized(10, b"abc\r\ndef\x1b[1;8H", 5, b"X");
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        ("abc X".into(), "def".into())
    );
    let s = resized(10, b"\r\nabc\x1b[2;8H", 5, b"X");
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        (String::new(), "abc X".into()),
        "on the bottom row: no scroll"
    );
    // A wrap pending at the edge stays pending on a narrowing.
    let s = resized(10, b"abcdefghij", 5, b"");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 5), true));
    let s = resized(10, b"abcdefghij", 5, b"X");
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        ("abcde".into(), "X".into()),
        "clipped, and X wraps"
    );
    // A cursor in a gap keeps its column; a same-size resize keeps the wrap.
    let s = resized(10, b"abc\x1b[8G", 20, b"X");
    assert_eq!(s.line_text(0), "abc    X");
    let s = resized(5, b"abcde", 5, b"X");
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        ("abcde".into(), "X".into())
    );
    // A wrap pending at a right margin stays pending on its column across a widening, which
    // resets the margins: the next glyph starts the next row.
    let s = resized(10, b"\x1b[?69h\x1b[1;3sabc", 12, b"");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 3), true));
    let s = resized(10, b"\x1b[?69h\x1b[1;3sabc", 12, b"X");
    assert_eq!((s.line_text(0), s.line_text(1)), ("abc".into(), "X".into()));
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
    // One U+FFFD per maximal subpart (Unicode 3.9, as WHATWG and aterm): C0 can
    // start no well-formed sequence, nor can E0 be followed by 80, so the two
    // overlongs are five replacements, not two.
    let s = fold(10, 1, &out(b"\xc0\x80\xe0\x80\x8a\xc2\x9bx"));
    assert_eq!(s.line_text(0), "\u{fffd}\u{fffd}\u{fffd}\u{fffd}\u{fffd}x");
    // A surrogate, a codepoint past U+10FFFF, and a truncated sequence whose
    // prefix was well-formed (one replacement for E2 82, then the A).
    let s = fold(12, 1, &out(b"\xed\xa0\x80|\xf4\x90\x80\x80|\xe2\x82A"));
    assert_eq!(
        s.line_text(0),
        "\u{fffd}\u{fffd}\u{fffd}|\u{fffd}\u{fffd}\u{fffd}\u{fffd}|\u{fffd}A"
    );
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
    assert_eq!(s.cell(0, 2).unwrap().underline, Underline::Curly);
    assert_eq!(s.cell(0, 3).unwrap().underline, Underline::None);
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

#[test]
fn one_alternate_buffer_persists_across_switches_as_in_xterm() {
    // `?47` only switches: a second visit finds what the first left.
    let s = fold(10, 2, &out(b"main\x1b[?47h\x1b[HALT\x1b[?47l\x1b[?47h"));
    assert!(s.is_altscreen());
    assert_eq!(s.line_text(0), "ALT");
    // `?1047` clears it on the way out, `?1049` on the way in.
    let s = fold(10, 2, &out(b"\x1b[?47hALT\x1b[?1047l\x1b[?47h"));
    assert_eq!(s.line_text(0), "");
    let s = fold(10, 2, &out(b"\x1b[?47hALT\x1b[?47l\x1b[?1049h"));
    assert_eq!(s.line_text(0), "");
    // The alternate buffer's DECSC slot lasts as long as the buffer does.
    let s = fold(
        10,
        4,
        &out(b"\x1b[?47h\x1b[3;5H\x1b7\x1b[?47l\x1b[?47h\x1b[H\x1b8"),
    );
    assert_eq!(s.cursor(), (2, 4));
}

#[test]
fn ris_keeps_the_alternate_buffer_and_its_slot_as_xterm_does() {
    // xterm's full reset (charproc.c `ReallyReset`) is `FromAlternate(xw, True)`
    // — which does nothing on the main screen — then `ClearScreen` of the main
    // buffer and `CursorSave` into the main slot (`sc[0]`). Nothing frees the
    // alternate buffer or touches its slot (`sc[1]`).
    let s = fold(10, 3, &out(b"\x1b[?47hX\x1b[?47l\x1bc\x1b[?47h"));
    assert!(s.is_altscreen());
    assert_eq!(s.line_text(0), "X", "the buffer the last visit left");
    let s = fold(
        10,
        3,
        &out(b"\x1b[?1049h\x1b[2;5H\x1b7\x1b[?1049l\x1bc\x1b[?1049h\x1b8Z"),
    );
    assert_eq!(
        s.line_text(1),
        "    Z",
        "the alternate slot's save restored"
    );
    // On the alternate screen the reset clears that buffer before it leaves.
    let s = fold(10, 3, &out(b"\x1b[?47hX\x1bc"));
    assert!(!s.is_altscreen());
    let s = fold(10, 3, &out(b"\x1b[?47hX\x1bc\x1b[?47h"));
    assert_eq!(s.line_text(0), "", "cleared on the way out");
    // The main screen and its slot are reset: home, and the reset pen.
    let s = fold(10, 3, &out(b"ab\x1b[31m\x1b[2;3H\x1b7\x1bc\x1b8"));
    assert_eq!(s.line_text(0), "");
    assert_eq!(s.cursor(), (0, 0));
}

#[test]
fn a_second_1049_set_clears_again_and_a_stray_reset_still_restores() {
    // xterm's 1049 set is `CursorSave; ToAlternate; ClearScreen`, and only the
    // switch is conditional; the reset is `FromAlternate; CursorRestore`.
    let s = fold(10, 2, &out(b"\x1b[?1049hX\x1b[?1049h"));
    assert_eq!(s.line_text(0), "", "the second set cleared the screen");
    let s = fold(10, 4, &out(b"\x1b[3;4H\x1b7\x1b[H\x1b[?1049l"));
    assert!(!s.is_altscreen());
    assert_eq!(s.cursor(), (2, 3), "a stray reset restores the main slot");
}

#[test]
fn the_alternate_screen_clears_reset_a_pending_wrap() {
    // xterm's ClearScreen calls ResetWrap: after `?1049h` (and `?1047l`) the
    // cursor sits ON the last column and the next glyph overwrites it.
    let s = fold(2, 3, &out(b"ab\x1b[?1049hZ"));
    assert_eq!(s.line_text(0), " Z");
    assert_eq!(s.line_text(1), "");
    let s = fold(2, 3, &out(b"\x1b[?1047hab\x1b[?1047lZ"));
    assert_eq!(s.line_text(0), " Z");
    // `?47` clears nothing and keeps the wrap: the next glyph wraps.
    let s = fold(2, 3, &out(b"ab\x1b[?47hZ"));
    assert_eq!(s.line_text(1), "Z");
}

#[test]
fn decsc_saves_and_decrc_restores_the_rendition() {
    // xterm's CursorSave keeps the SGR flags and colours with the position;
    // CursorRestore puts them back. `?1049` uses the same slot.
    let s = fold(10, 2, &out(b"\x1b[1;31;44m\x1b7\x1b[0m\x1b8X"));
    let x = s.cell(0, 0).unwrap();
    assert_eq!((x.fg, x.bg), (Color::Indexed(1), Color::Indexed(4)));
    assert_ne!(x.attrs & attr::BOLD, 0);
    let s = fold(10, 2, &out(b"\x1b[32m\x1b[?1049h\x1b[0m\x1b[?1049lY"));
    assert_eq!(
        s.cell(0, 0).unwrap().fg,
        Color::Indexed(2),
        "?1049l restores it too"
    );
    // A slot never saved restores home and the default rendition.
    let s = fold(10, 2, &out(b"\x1b[2;3H\x1b[7;35m\x1b8Z"));
    let z = s.cell(0, 0).unwrap();
    assert_eq!((z.ch, z.fg, z.attrs), ('Z', Color::Default, 0));
}

#[test]
fn vt_ff_ind_and_nel_feed_lines_as_in_xterm() {
    // xterm's CASE_VMOT sends VT and FF through xtermIndex like LF; IND is the
    // same index, NEL an index and a carriage return.
    let s = fold(10, 3, &out(b"a\x0bb\x0cc"));
    assert_eq!(
        (s.line_text(1), s.line_text(2)),
        (" b".into(), "  c".into())
    );
    let s = fold(10, 2, &out(b"a\r\nb\x1bDx"));
    assert_eq!(s.line_text(0), "b", "IND at the bottom scrolls");
    assert_eq!(s.line_text(1), " x");
    let s = fold(10, 3, &out(b"ab\x1bEx"));
    assert_eq!(s.line_text(1), "x");
}

#[test]
fn ich_dch_and_ech_edit_the_cursor_line_as_in_xterm() {
    // InsertChar opens blanks at the cursor, pushing the tail off the edge;
    // DeleteChar closes them, blanks entering at the right; ClearRight(n)
    // blanks n cells. Each resets a pending wrap and takes the bce blank.
    let s = fold(6, 1, &out(b"abcdef\x1b[1;3H\x1b[2@X"));
    assert_eq!(s.line_text(0), "abX cd");
    let s = fold(6, 1, &out(b"abcdef\x1b[1;3H\x1b[2P"));
    assert_eq!(s.line_text(0), "abef");
    let s = fold(6, 1, &out(b"abcdef\x1b[1;2H\x1b[44m\x1b[3X"));
    assert_eq!(s.line_text(0), "a   ef");
    assert_eq!(s.cell(0, 3).unwrap().bg, Color::Indexed(4));
    // From a pending wrap the cursor is on the last column, and stays there.
    let s = fold(4, 2, &out(b"abcd\x1b[@Z"));
    assert_eq!(s.line_text(0), "abcZ");
    assert_eq!(s.line_text(1), "");
    let s = fold(4, 2, &out(b"abcd\x1b[9PZ"));
    assert_eq!(s.line_text(0), "abcZ");
    // Counts past the edge clamp; 0 means 1.
    let s = fold(4, 1, &out(b"abcd\x1b[1;2H\x1b[99@"));
    assert_eq!(s.line_text(0), "a");
    let s = fold(4, 1, &out(b"abcd\x1b[1;2H\x1b[0P"));
    assert_eq!(s.line_text(0), "acd");
}

#[test]
fn origin_mode_counts_rows_from_the_top_margin() {
    // xterm `srm_DECOM` homes through `CursorSet(screen, 0, 0, flags)`: with
    // the region on rows 2..4 (1-based) that is the top margin.
    let s = fold(10, 6, &out(b"\x1b[2;4r\x1b[?6h"));
    assert_eq!(s.cursor(), (1, 0), "?6h homes to the top margin");
    // CUP counts from the top margin and stops at the bottom one; VPA too;
    // CHA keeps the row.
    let s = fold(
        10,
        6,
        &out(b"\x1b[2;4r\x1b[?6h\x1b[1;1HX\x1b[99;2HY\x1b[2dZ\x1b[5GW"),
    );
    assert_eq!(s.line_text(1), "X");
    assert_eq!(s.line_text(2), "  Z W");
    assert_eq!(s.line_text(3), " Y");
    assert_eq!(s.cursor(), (2, 5));
    // DECSTBM under origin mode homes to the new top margin, and `?6l` homes
    // to the screen's corner.
    let s = fold(10, 6, &out(b"\x1b[?6h\x1b[3;5r"));
    assert_eq!(s.cursor(), (2, 0));
    let s = fold(10, 6, &out(b"\x1b[3;5r\x1b[?6h\x1b[2;2H\x1b[?6l"));
    assert_eq!(s.cursor(), (0, 0));
    // The home resolves a pending wrap.
    let s = fold(3, 3, &out(b"abc\x1b[?6hZ"));
    assert_eq!(s.line_text(0), "Zbc");
}

#[test]
fn decsc_saves_origin_mode_and_an_unsaved_decrc_clears_it() {
    // xterm's DECSC_FLAGS hold ORIGIN: a restore puts it back, so the CUP
    // after it still counts from the top margin.
    let s = fold(
        10,
        6,
        &out(b"\x1b[2;5r\x1b[?6h\x1b[2;3H\x1b7\x1b[?6l\x1b8\x1b[1;1HX"),
    );
    assert_eq!(s.line_text(1), "X", "origin mode came back with the slot");
    // A slot never saved clears it and homes to the screen's corner
    // (aterm's `unsaved_decrc_still_resets_origin_and_homes`).
    let s = fold(20, 20, &out(b"\x1b[5;15r\x1b[?6h\x1b[3;3Hx\x1b8Z"));
    assert_eq!(s.line_text(0), "Z");
    assert_eq!(s.cursor(), (0, 1));
    // RIS clears it.
    let s = fold(10, 6, &out(b"\x1b[?6h\x1bc\x1b[2;4r\x1b[1;1HX"));
    assert_eq!(s.line_text(0), "X");
    // The restored row goes through `CursorSet` under the restored flag: it
    // stops at the bottom margin, whatever the region now is.
    let s = fold(10, 6, &out(b"\x1b[?6h\x1b[5;1H\x1b7\x1b[1;3r\x1b8X"));
    assert_eq!(
        s.line_text(2),
        "X",
        "row 4 clamped to the new bottom margin"
    );
}

#[test]
fn insert_mode_shifts_the_line_under_each_glyph() {
    // xterm's WriteText runs InsertChar first: the rest of the line moves
    // right and what passes the last column is lost.
    let s = fold(6, 1, &out(b"abcdef\x1b[1;2H\x1b[4hXY"));
    assert_eq!(s.line_text(0), "aXYbcd");
    assert_eq!(s.cursor(), (0, 3));
    // `CSI 4 l` turns it off again; ANSI modes other than IRM and LNM are
    // consumed.
    let s = fold(6, 1, &out(b"abcdef\x1b[1;2H\x1b[4h\x1b[4lX\x1b[2;12lY"));
    assert_eq!(s.line_text(0), "aXYdef");
    // A glyph that wraps inserts at the left of the next line.
    let s = fold(3, 2, &out(b"\x1b[2;1Hxyz\x1b[1;1Habc\x1b[4hQ"));
    assert_eq!(s.line_text(1), "Qxy");
    // DECSC does not save it; RIS clears it.
    let s = fold(4, 1, &out(b"ab\x1b[1;1H\x1b[4h\x1bcX"));
    assert_eq!(s.line_text(0), "X");
}

#[test]
fn su_and_sd_scroll_the_region_and_keep_the_cursor_and_its_wrap() {
    // xterm's xtermScroll/RevScroll move the region's lines, not the cursor,
    // and SU keeps a pending wrap (aterm's `su_preserves_pending_wrap`).
    let s = fold(4, 4, &out(b"a\r\nb\r\nc\r\nd\x1b[2;3r\x1b[1;1H\x1b[S"));
    assert_eq!(
        (
            s.line_text(0),
            s.line_text(1),
            s.line_text(2),
            s.line_text(3)
        ),
        ("a".into(), "c".into(), "".into(), "d".into())
    );
    assert_eq!(s.cursor(), (0, 0));
    let s = fold(4, 4, &out(b"a\r\nb\r\nc\r\nd\x1b[2;3r\x1b[1;1H\x1b[T"));
    assert_eq!((s.line_text(1), s.line_text(2)), ("".into(), "b".into()));
    // A count past the region clears it; the lines take the bce blank.
    let s = fold(4, 3, &out(b"a\r\nb\r\nc\x1b[44m\x1b[9S"));
    assert_eq!(s.line_text(0), "");
    assert_eq!(s.cell(2, 3).unwrap().bg, Color::Indexed(4));
    let s = fold(4, 2, &out(b"abcd\x1b[S!"));
    assert_eq!(s.line_text(1), "!", "the wrap survived SU");
    // SD moved `abcd` down a row, under the wrapped glyph.
    let s = fold(4, 2, &out(b"abcd\x1b[T!"));
    assert_eq!(
        (s.line_text(0), s.line_text(1)),
        ("".into(), "!bcd".into()),
        "and SD"
    );
    // xterm CASE_TRACK_MOUSE: `CSI 0 T` and a `T` with five parameters are
    // highlight mouse tracking, not SD.
    let s = fold(4, 2, &out(b"a\x1b[0T\x1b[1;2;3;4;5T"));
    assert_eq!(s.line_text(0), "a");
}

#[test]
fn newline_mode_returns_the_carriage_on_lf_vt_and_ff_only() {
    // xterm CASE_VMOT: `xtermIndex`, then `CarriageReturn` under LINEFEED.
    let s = fold(6, 4, &out(b"\x1b[20hab\ncd\x0bef\x0cgh"));
    assert_eq!(
        (
            s.line_text(0),
            s.line_text(1),
            s.line_text(2),
            s.line_text(3)
        ),
        ("ab".into(), "cd".into(), "ef".into(), "gh".into())
    );
    // IND and NEL are not CASE_VMOT: IND still keeps the column.
    let s = fold(6, 3, &out(b"\x1b[20hab\x1bDc"));
    assert_eq!(s.line_text(1), "  c");
    // `CSI 20 l` turns it off; RIS clears it.
    let s = fold(6, 3, &out(b"\x1b[20h\x1b[20lab\nc"));
    assert_eq!(s.line_text(1), "  c");
    let s = fold(6, 3, &out(b"\x1b[20h\x1bcab\nc"));
    assert_eq!(s.line_text(1), "  c");
}

#[test]
fn dec_special_graphics_in_g0_and_g1_with_so_and_si() {
    // `ESC ( 0` puts DEC Special Graphics in G0: `lqk` is a box corner run.
    let s = fold(10, 2, &out(b"\x1b(0lqk\x1b(Bx"));
    assert_eq!(s.line_text(0), "\u{250c}\u{2500}\u{2510}x");
    // In G1 it shows only while SO maps G1 into GL; SI maps G0 back.
    let s = fold(10, 2, &out(b"\x1b)0a\x0ea\x0fa"));
    assert_eq!(s.line_text(0), "a\u{2592}a");
    // SO with nothing designated prints ASCII (xterm's resetCharsets puts
    // ASCII in G1; aterm's `g1_defaults_to_ascii_so_prints_plain_text`).
    let s = fold(10, 2, &out(b"\x0eabc"));
    assert_eq!(s.line_text(0), "abc");
    // xterm's table: `_` is a blank, `~` a centred dot, and bytes below 0x5F
    // are themselves. A decoded UTF-8 character is never translated.
    let s = fold(12, 2, &out("\x1b(0_~AZ^\u{e9}q".as_bytes()));
    assert_eq!(s.line_text(0), " \u{b7}AZ^\u{e9}\u{2500}");
    // Sets the fold does not model (UK, G2, a 96-character set, a two-byte
    // name) change nothing.
    let s = fold(10, 2, &out(b"\x1b(0\x1b(A\x1b*B\x1b-A\x1b(%5q"));
    assert_eq!(s.line_text(0), "\u{2500}");
}

#[test]
fn decsc_saves_the_character_sets_and_an_unsaved_decrc_resets_them() {
    // xterm's CursorSave keeps gsets and curgl; CursorRestore puts them back.
    let s = fold(10, 2, &out(b"\x1b(0\x1b7\x1b(Bq\x1b8\x1b[2Gq"));
    assert_eq!(s.line_text(0), "q\u{2500}");
    let s = fold(10, 2, &out(b"\x1b)0\x0e\x1b7\x0fq\x1b8\x1b[2Gq"));
    assert_eq!(s.line_text(0), "q\u{2500}", "the shift comes back too");
    // A slot never saved resets them (resetCharsets), as RIS does.
    let s = fold(10, 2, &out(b"\x1b(0\x1b8q"));
    assert_eq!(s.line_text(0), "q");
    let s = fold(10, 2, &out(b"\x1b(0\x0e\x1bcq"));
    assert_eq!(s.line_text(0), "q");
    // An SCS split across two records still designates.
    let recs = vec![Record::Out(b"\x1b(".to_vec()), Record::Out(b"0q".to_vec())];
    assert_eq!(fold(10, 2, &recs).line_text(0), "\u{2500}");
}

#[test]
fn truecolour_forms_palette_reset_bce_decsc_and_truncated_sequences() {
    // 4-subparam colon form `38:2:r:g:b`, 5-subparam `48:2:1:r:g:b`, trailing SGR
    // `;4` after `;`-form RGB, and `39`/`49`/palette clearing `fg_rgb`/`bg_rgb`.
    let s = fold(
        12,
        1,
        &out(
            b"\x1b[38:2:11:22:33;48:2:1:44:55:66mA\x1b[38;2;200;100;50;4mB\x1b[39mC\x1b[49mD\x1b[38;2;9;8;7;32mE",
        ),
    );
    let a = s.cell(0, 0).unwrap();
    assert_eq!(a.fg_rgb, Some((11, 22, 33)));
    assert_eq!(a.bg_rgb, Some((44, 55, 66)));
    let b = s.cell(0, 1).unwrap();
    assert_eq!(b.fg_rgb, Some((200, 100, 50)));
    assert_eq!(b.bg_rgb, Some((44, 55, 66)));
    assert_eq!(b.underline, Underline::Single);
    let c = s.cell(0, 2).unwrap();
    assert_eq!(c.fg, Color::Default);
    assert_eq!(c.fg_rgb, None, "39 clears fg_rgb");
    assert_eq!(c.bg_rgb, Some((44, 55, 66)));
    let d = s.cell(0, 3).unwrap();
    assert_eq!(d.bg, Color::Default);
    assert_eq!(d.bg_rgb, None, "49 clears bg_rgb");
    let e = s.cell(0, 4).unwrap();
    assert_eq!(e.fg, Color::Indexed(2), "32 selects ANSI green");
    assert_eq!(e.fg_rgb, None, "palette selection clears prior fg_rgb");

    // Truncated extended colours leave the pen untouched; unknown selector `38;7;1`
    // consumes only `7` so `;1` still sets BOLD (matches aterm-conformance corpus).
    let s = fold(
        8,
        1,
        &out(b"\x1b[31;44m\x1b[38;5mA\x1b[48;5mB\x1b[38;2;1;2mC\x1b[0;38;7;1mD"),
    );
    assert_eq!(s.cell(0, 0).unwrap().fg, Color::Indexed(1));
    assert_eq!(s.cell(0, 1).unwrap().bg, Color::Indexed(4));
    assert_eq!(s.cell(0, 2).unwrap().fg, Color::Indexed(1));
    assert_eq!(s.cell(0, 2).unwrap().fg_rgb, None);
    assert_ne!(s.cell(0, 3).unwrap().attrs & attr::BOLD, 0);

    // BCE and DECSC/DECRC preserve 24-bit RGB, and `serialize()` is injective.
    let s1 = fold(
        6,
        1,
        &out(b"\x1b[38;2;1;2;3;48;2;12;34;56m\x1b7\x1b[0m\x1b8\x1b[2KX"),
    );
    assert_eq!(s1.cell(0, 0).unwrap().fg_rgb, Some((1, 2, 3)));
    assert_eq!(s1.cell(0, 0).unwrap().bg_rgb, Some((12, 34, 56)));
    assert_eq!(
        s1.cell(0, 5).unwrap().bg_rgb,
        Some((12, 34, 56)),
        "BCE fills 24-bit bg_rgb"
    );
    let s2 = fold(
        6,
        1,
        &out(b"\x1b[38;2;1;2;4;48;2;12;34;56m\x1b7\x1b[0m\x1b8\x1b[2KX"),
    );
    assert_ne!(s1.serialize(), s2.serialize());
}

#[test]
fn combining_marks_attach_without_moving_cursor_or_resolving_pending_wrap() {
    // Base glyph + combining acute accent attaches to cell (0, 0), keeps cursor at (0, 1),
    // and emits in `line_text`.
    let s = fold(8, 2, &out("e\u{0301}x".as_bytes()));
    let c0 = s.cell(0, 0).unwrap();
    assert_eq!(c0.ch, 'e');
    assert_eq!(c0.combining_marks(), &['\u{0301}']);
    assert_eq!(s.cell(0, 1).unwrap().ch, 'x');
    assert_eq!(s.cursor(), (0, 2));
    assert_eq!(s.line_text(0), "e\u{0301}x");

    // Up to MAX_COMBINING (16) combining marks are retained; extras are clamped cleanly.
    let s = fold(
        6,
        1,
        &out(
            "a\u{0300}\u{0301}\u{0302}\u{0303}\u{0304}\u{0305}\u{0306}\u{0307}\u{0308}\u{0309}\u{030A}\u{030B}\u{030C}\u{030D}\u{030E}\u{030F}\u{0310}b"
                .as_bytes(),
        ),
    );
    assert_eq!(
        s.cell(0, 0).unwrap().combining_marks(),
        &[
            '\u{0300}', '\u{0301}', '\u{0302}', '\u{0303}', '\u{0304}', '\u{0305}', '\u{0306}',
            '\u{0307}', '\u{0308}', '\u{0309}', '\u{030A}', '\u{030B}', '\u{030C}', '\u{030D}',
            '\u{030E}', '\u{030F}'
        ]
    );
    assert_eq!(s.cell(0, 1).unwrap().ch, 'b');

    // Tag-5 serialize() injectivity for deep combining marks (slots 4..16).
    let s_deep_a = fold(
        4,
        1,
        &out("a\u{0300}\u{0301}\u{0302}\u{0303}\u{0304}".as_bytes()),
    );
    let s_deep_b = fold(
        4,
        1,
        &out("a\u{0300}\u{0301}\u{0302}\u{0303}\u{0305}".as_bytes()),
    );
    assert_ne!(s_deep_a, s_deep_b);
    assert_ne!(s_deep_a.serialize(), s_deep_b.serialize());

    // U+FE0F (VS16) widens Text_Default_Emoji (e.g. U+2600 ☀) from 1 to 2 columns,
    // leaves non-emoji ASCII ('a') narrow, and U+FE0E (VS15) narrows wide emoji to 1 column.
    let s_vs16 = fold(8, 1, &out("\u{2600}\u{FE0F}X".as_bytes()));
    assert_eq!(s_vs16.cell(0, 0).unwrap().ch, '\u{2600}');
    assert_eq!(s_vs16.cell(0, 0).unwrap().width, 2);
    assert_eq!(s_vs16.cell(0, 0).unwrap().combining_marks(), &['\u{FE0F}']);
    assert_eq!(s_vs16.cell(0, 1).unwrap().width, 0);
    assert_eq!(s_vs16.cell(0, 2).unwrap().ch, 'X');
    assert_eq!(s_vs16.cursor(), (0, 3));

    let s_ascii_vs16 = fold(8, 1, &out("a\u{FE0F}X".as_bytes()));
    assert_eq!(s_ascii_vs16.cell(0, 0).unwrap().width, 1);
    assert_eq!(s_ascii_vs16.cell(0, 1).unwrap().ch, 'X');

    let s_vs15 = fold(8, 1, &out("\u{1F600}\u{FE0E}X".as_bytes()));
    assert_eq!(s_vs15.cell(0, 0).unwrap().ch, '\u{1F600}');
    assert_eq!(s_vs15.cell(0, 0).unwrap().width, 1);
    assert_eq!(s_vs15.cell(0, 0).unwrap().combining_marks(), &['\u{FE0E}']);
    assert_eq!(s_vs15.cell(0, 1).unwrap().ch, ' ');
    assert_eq!(s_vs15.cell(0, 1).unwrap().width, 1);
    assert_eq!(s_vs15.cell(0, 2).unwrap().ch, 'X');

    // Combining mark at column 0 attaches to cell (0, 0) without moving cursor; a
    // subsequent base glyph overwrites cell (0, 0) and resets combining marks.
    let s_col0 = fold(4, 1, &out("\u{0301}".as_bytes()));
    assert_eq!(s_col0.cursor(), (0, 0));
    assert_eq!(s_col0.cell(0, 0).unwrap().combining_marks(), &['\u{0301}']);
    let s_over = fold(4, 1, &out("\u{0301}Z".as_bytes()));
    assert_eq!(s_over.cell(0, 0).unwrap().ch, 'Z');
    assert!(s_over.cell(0, 0).unwrap().combining_marks().is_empty());

    // Combining mark when parked at right margin with wrap pending attaches to the
    // parked cell and preserves the pending wrap for the next spacing glyph.
    let s_wrap = fold(4, 2, &out("abcd\u{0308}Z".as_bytes()));
    assert_eq!(s_wrap.cell(0, 3).unwrap().ch, 'd');
    assert_eq!(s_wrap.cell(0, 3).unwrap().combining_marks(), &['\u{0308}']);
    assert_eq!(s_wrap.line_text(0), "abcd\u{0308}");
    assert_eq!(s_wrap.line_text(1), "Z");
    assert_ne!(
        s_wrap.serialize(),
        fold(4, 2, &out(b"abcdZ")).serialize(),
        "serialize() captures combining marks"
    );
}

fn assert_wide_pair_coherence(s: &astream_term::Screen) {
    let (cols, rows) = s.dims();
    for r in 0..rows {
        for c in 0..cols {
            let cell = s.cell(r, c).unwrap();
            assert!(
                astream_term::cell_width_is_valid(cell.width),
                "invalid width {} at ({r}, {c})",
                cell.width
            );
            if cell.width == 2 {
                assert!(
                    c + 1 < cols,
                    "wide lead cell at right edge ({r}, {c}) of {cols}-col screen"
                );
                let spacer = s.cell(r, c + 1).unwrap();
                assert_eq!(
                    spacer.width,
                    0,
                    "wide lead at ({r}, {c}) missing spacer at ({r}, {})",
                    c + 1
                );
            } else if cell.width == 0 {
                assert!(c > 0, "orphan spacer at column 0 of row {r}");
                let lead = s.cell(r, c - 1).unwrap();
                assert_eq!(
                    lead.width,
                    2,
                    "orphan spacer at ({r}, {c}) without wide lead at ({r}, {})",
                    c - 1
                );
            }
        }
    }
}

#[test]
fn east_asian_wide_cjk_emoji_prewrap_split_healing_and_zwj_grapheme_clusters() {
    // 1. Wide CJK, Kana, Hangul, Fullwidth, and Emoji each occupy 2 columns (`width = 2` + `width = 0`),
    //    while `line_text` skips the continuation spacer cells cleanly.
    let s = fold(12, 2, &out("漢あ한Ａ🚀!".as_bytes()));
    assert_wide_pair_coherence(&s);
    assert_eq!(s.cursor(), (0, 11));
    assert_eq!(s.line_text(0), "漢あ한Ａ🚀!");
    for (col, ch) in [(0, '漢'), (2, 'あ'), (4, '한'), (6, 'Ａ'), (8, '🚀')] {
        assert_eq!(s.cell(0, col).unwrap().ch, ch);
        assert_eq!(s.cell(0, col).unwrap().width, 2);
        assert_eq!(s.cell(0, col + 1).unwrap().width, 0);
    }
    assert_eq!(s.cell(0, 10).unwrap().ch, '!');
    assert_eq!(s.cell(0, 10).unwrap().width, 1);

    // 2. Right-margin pre-wrap: on a 5-column screen, `"ab漢漢"` places `'a'`,`'b'` at 0..2,
    //    first `'漢'` at 2..4, then pre-wraps before col 4 (painting BCE blank at col 4)
    //    so the second `'漢'` lands intact at `(1, 0..2)`.
    let s_pre = fold(5, 2, &out("\x1b[48;2;12;34;56mab漢漢".as_bytes()));
    assert_wide_pair_coherence(&s_pre);
    assert_eq!(s_pre.line_text(0), "ab漢");
    assert_eq!(s_pre.line_text(1), "漢");
    assert_eq!(
        s_pre.cell(0, 4).unwrap().bg_rgb,
        Some((12, 34, 56)),
        "pre-wrapped trailing column takes the BCE blank background"
    );
    assert_eq!(s_pre.cell(0, 4).unwrap().width, 1);
    assert_eq!(s_pre.cursor(), (1, 2));

    // A screen one column wide has no room for a wide glyph: it prints as a narrow space in
    // the pen, as aterm and Ghostty print it, and no `width = 2` lead is left unbacked.
    let s_one = fold(1, 2, &out("漢Z".as_bytes()));
    assert_wide_pair_coherence(&s_one);
    assert_eq!(s_one.cell(0, 0).unwrap().width, 1);
    assert_eq!(s_one.line_text(0), "");
    assert_eq!(s_one.line_text(1), "Z");

    // 3. Half-cell split healing on overwrite (left half, right half, straddling wide pair),
    //    EL / ECH / ICH / DCH, and narrower `Resize` clip.
    let s_left = fold(6, 1, &out("漢字\rX".as_bytes()));
    assert_wide_pair_coherence(&s_left);
    assert_eq!(s_left.line_text(0), "X 字");

    let s_right = fold(6, 1, &out("漢字\x1b[1;2HY".as_bytes()));
    assert_wide_pair_coherence(&s_right);
    assert_eq!(s_right.line_text(0), " Y字");

    let s_straddle = fold(6, 1, &out("漢字\x1b[1;2H語".as_bytes()));
    assert_wide_pair_coherence(&s_straddle);
    assert_eq!(s_straddle.line_text(0), " 語");

    let s_el0 = fold(6, 1, &out("漢字\x1b[1;2H\x1b[K".as_bytes()));
    assert_wide_pair_coherence(&s_el0);
    assert_eq!(s_el0.line_text(0), "");

    let s_el1 = fold(6, 1, &out("漢字\x1b[1;3H\x1b[1K".as_bytes()));
    assert_wide_pair_coherence(&s_el1);
    assert_eq!(s_el1.line_text(0), "");

    let s_ich = fold(6, 1, &out("漢字\x1b[1;2H\x1b[@".as_bytes()));
    assert_wide_pair_coherence(&s_ich);

    let s_dch = fold(6, 1, &out("漢字\x1b[1;2H\x1b[P".as_bytes()));
    assert_wide_pair_coherence(&s_dch);

    let s_clip = fold(
        6,
        1,
        &[
            Record::Out("漢字".as_bytes().to_vec()),
            Record::Resize { cols: 3, rows: 1 },
        ],
    );
    assert_wide_pair_coherence(&s_clip);
    assert_eq!(s_clip.line_text(0), "漢");

    // 4. ZWJ (`\u{200D}`), VS16 (`\u{FE0F}`), and skin-tone modifier (`\u{1F3FD}`) grapheme
    //    clusters on wide bases.
    let s_zwj = fold(
        10,
        1,
        &out("👨\u{200D}💻🐻\u{200D}❄\u{FE0F}👍\u{1F3FD}Z".as_bytes()),
    );
    assert_wide_pair_coherence(&s_zwj);
    assert_eq!(s_zwj.cursor(), (0, 7));
    assert_eq!(
        s_zwj.cell(0, 0).unwrap().combining_marks(),
        &['\u{200D}', '💻']
    );
    assert_eq!(
        s_zwj.cell(0, 2).unwrap().combining_marks(),
        &['\u{200D}', '❄', '\u{FE0F}']
    );
    assert_eq!(s_zwj.cell(0, 4).unwrap().combining_marks(), &['\u{1F3FD}']);
    assert_eq!(s_zwj.cell(0, 6).unwrap().ch, 'Z');
    assert_eq!(
        s_zwj.line_text(0),
        "👨\u{200D}💻🐻\u{200D}❄\u{FE0F}👍\u{1F3FD}Z"
    );
}

#[test]
fn clusters_join_as_aterm_joins_them() {
    let cell = |s: &astream_term::Screen, col: u16| *s.cell(0, col).unwrap();
    // A regional indicator takes two columns, as aterm draws it (East Asian Width leaves it
    // Neutral; xterm draws it one), and the second of a pair joins the first: a flag is one
    // wide cell, and a third indicator starts the next.
    let s = fold(8, 1, &out("\u{1F1FA}\u{1F1F8}\u{1F1EF}".as_bytes()));
    assert_wide_pair_coherence(&s);
    assert_eq!(s.cursor(), (0, 4));
    assert_eq!(cell(&s, 0).combining_marks(), &['\u{1F1F8}']);
    assert_eq!((cell(&s, 2).ch, cell(&s, 2).width), ('\u{1F1EF}', 2));
    // A skin-tone modifier joins the wide glyph before it and is a wide glyph of its own
    // anywhere else, as aterm and Ghostty draw it, never a mark on a narrow glyph.
    let s = fold(8, 1, &out("\u{1F44D}\u{1F3FD}a\u{1F3FD}".as_bytes()));
    assert_wide_pair_coherence(&s);
    assert_eq!(cell(&s, 0).combining_marks(), &['\u{1F3FD}']);
    assert_eq!(cell(&s, 2).ch, 'a');
    assert!(cell(&s, 2).combining_marks().is_empty());
    assert_eq!((cell(&s, 3).ch, cell(&s, 3).width), ('\u{1F3FD}', 2));
    assert_eq!(s.cursor(), (0, 5));
    // An ASCII glyph after a joiner starts a cell of its own, as aterm starts it.
    let s = fold(8, 1, &out("\u{1F468}\u{200D}a".as_bytes()));
    assert_eq!(cell(&s, 0).combining_marks(), &['\u{200D}']);
    assert_eq!(cell(&s, 2).ch, 'a');
    assert_eq!(s.cursor(), (0, 3));
}

#[test]
fn a_skin_tone_joins_only_a_wide_emoji_modifier_base() {
    let cell = |s: &astream_term::Screen, col: u16| *s.cell(0, col).unwrap();
    // Wide of itself, and wide by the VS16 it holds: both take the modifier (UTS #51).
    for (text, marks) in [
        ("\u{1F44D}\u{1F3FD}", vec!['\u{1F3FD}']),
        ("\u{261D}\u{FE0F}\u{1F3FD}", vec!['\u{FE0F}', '\u{1F3FD}']),
    ] {
        let s = fold(8, 1, &out(text.as_bytes()));
        assert_eq!(cell(&s, 0).combining_marks(), marks.as_slice(), "{text:?}");
        assert_eq!(s.cursor(), (0, 2), "{text:?}");
    }
    // Negative control: a wide glyph that is no modifier base, and a modifier base a VS15 has
    // narrowed, leave the modifier a wide glyph of its own.
    for (text, base_width) in [
        ("\u{4E2D}\u{1F3FD}", 2u8),
        ("\u{1F600}\u{1F3FD}", 2),
        ("\u{1F44D}\u{FE0E}\u{1F3FD}", 1),
    ] {
        let s = fold(8, 1, &out(text.as_bytes()));
        assert_eq!(cell(&s, 0).width, base_width, "{text:?}");
        assert!(
            !cell(&s, 0).combining_marks().contains(&'\u{1F3FD}'),
            "{text:?}"
        );
        assert_eq!(
            (cell(&s, 2).ch, cell(&s, 2).width),
            ('\u{1F3FD}', 2),
            "{text:?}"
        );
    }
}

#[test]
fn a_glyph_joins_a_joiner_only_while_it_is_the_last_thing_printed() {
    let cell = |s: &astream_term::Screen, col: u16| *s.cell(0, col).unwrap();
    let man_coder = "\u{1F468}\u{200D}\u{1F4BB}";
    assert_eq!(
        cell(&fold(8, 1, &out(man_coder.as_bytes())), 0).combining_marks(),
        &['\u{200D}', '\u{1F4BB}']
    );
    // A motion between them keeps it: nothing was printed.
    let s = fold(8, 1, &out("\u{1F468}\u{200D}\x1b[1;3H\u{1F4BB}".as_bytes()));
    assert_eq!(cell(&s, 0).combining_marks(), &['\u{200D}', '\u{1F4BB}']);
    // Negative control: a glyph printed in between closes it, though the motion back puts the
    // cursor beside the cell whose last mark is the joiner.
    let s = fold(
        8,
        1,
        &out("\u{1F468}\u{200D}x\x1b[1;3H\u{1F4BB}".as_bytes()),
    );
    assert_eq!(cell(&s, 0).combining_marks(), &['\u{200D}']);
    assert_eq!(cell(&s, 2).ch, '\u{1F4BB}');
    // The open joiner is state, so it serializes.
    let open = fold(8, 1, &out("\u{1F468}\u{200D}".as_bytes()));
    let closed = fold(8, 1, &out("\u{1F468}\u{200D}\u{301}".as_bytes()));
    assert_ne!(open, closed);
    assert_ne!(open.serialize(), closed.serialize());
}

#[test]
fn a_vs16_leaves_a_pending_wrap_where_it_is() {
    // A wrap on a right margin outlives the margin; the glyph parked on it can then widen, and
    // the next glyph still takes the next line.
    let s = fold(
        8,
        2,
        &out("\x1b[?69h\x1b[1;2sa\u{2600}\x1b[?69l\u{FE0F}X".as_bytes()),
    );
    assert_eq!(s.cell(0, 1).unwrap().width, 2);
    assert_eq!(s.cell(0, 2).unwrap().width, 0);
    assert_eq!(s.cell(1, 0).unwrap().ch, 'X');
    // Negative control: with no wrap pending, the cursor steps past the spacer.
    let s = fold(8, 2, &out("\u{2600}\u{FE0F}X".as_bytes()));
    assert_eq!(s.cell(0, 2).unwrap().ch, 'X');
}

#[test]
fn marks_at_column_0_and_the_left_margin_take_the_cursors_own_cell() {
    // Column 0 of a row that continues the one above has no glyph before it either: the
    // row's own cell takes the mark, never the glyph that ends the row above.
    let s = fold(4, 2, &out("abcde\r\u{301}".as_bytes()));
    assert!(s.cell(0, 3).unwrap().combining_marks().is_empty());
    assert_eq!(s.cell(1, 0).unwrap().combining_marks(), &['\u{301}']);
    // A left margin bounds it as column 0 does: the cell outside it is another region's.
    let s = fold(
        10,
        1,
        &out("abc\x1b[?69h\x1b[3;6s\x1b[1;3H\u{301}".as_bytes()),
    );
    assert!(s.cell(0, 1).unwrap().combining_marks().is_empty());
    assert_eq!(s.cell(0, 2).unwrap().combining_marks(), &['\u{301}']);
    // Standing on a spacer there, it rides the lead.
    let s = fold(
        10,
        1,
        &out("\u{4E2D}\x1b[?69h\x1b[2;6s\x1b[1;2H\u{301}".as_bytes()),
    );
    assert_eq!(s.cell(0, 0).unwrap().combining_marks(), &['\u{301}']);
    assert!(s.cell(0, 1).unwrap().combining_marks().is_empty());
}

#[test]
fn a_cluster_continues_the_glyph_printed_up_to_a_left_margin() {
    const MARGIN: &str = "\x1b[?69h\x1b[3;6s";
    let at = |col: u16, text: &str| {
        fold(
            10,
            2,
            &out(format!("{MARGIN}\x1b[1;{col}H{text}").as_bytes()),
        )
    };
    // A mark, whole or fed a chunk later.
    let s = at(2, "e\u{301}");
    assert_eq!(s.cell(0, 1).unwrap().combining_marks(), &['\u{301}']);
    assert!(s.cell(0, 2).unwrap().combining_marks().is_empty());
    let s = fold(
        10,
        2,
        &[
            Record::Out(format!("{MARGIN}\x1b[1;2He").into_bytes()),
            Record::Out("\u{301}".as_bytes().to_vec()),
        ],
    );
    assert_eq!(s.cell(0, 1).unwrap().combining_marks(), &['\u{301}']);
    // A VS16 widens across the margin and the next glyph goes after the spacer.
    let s = at(2, "\u{2600}\u{FE0F}X");
    assert_eq!(s.cell(0, 1).unwrap().width, 2);
    assert_eq!(s.cell(0, 3).unwrap().ch, 'X');
    // A joiner's glyph, a skin tone and a flag's pair join it.
    let s = at(1, "\u{1F468}\u{200D}\u{1F4BB}X");
    assert_eq!(
        s.cell(0, 0).unwrap().combining_marks(),
        &['\u{200D}', '\u{1F4BB}']
    );
    assert_eq!(s.cell(0, 2).unwrap().ch, 'X');
    let s = at(1, "\u{1F44D}\u{1F3FD}X");
    assert_eq!(s.cell(0, 0).unwrap().combining_marks(), &['\u{1F3FD}']);
    assert_eq!(s.cell(0, 2).unwrap().ch, 'X');
    let s = at(1, "\u{1F1FA}\u{1F1F8}X");
    assert_eq!(s.cell(0, 0).unwrap().combining_marks(), &['\u{1F1F8}']);
    assert_eq!(s.cell(0, 2).unwrap().ch, 'X');
    // A VS16 can step onto the margin itself, widening a glyph two left of it.
    let s = at(1, "\u{2600}\u{FE0F}\u{301}X");
    assert_eq!(
        s.cell(0, 0).unwrap().combining_marks(),
        &['\u{FE0F}', '\u{301}']
    );
    assert_eq!(s.cell(0, 2).unwrap().ch, 'X');
    // A rendition change moves nothing: the glyph still precedes the cursor.
    let s = at(2, "e\x1b[31m\u{301}");
    assert_eq!(s.cell(0, 1).unwrap().combining_marks(), &['\u{301}']);
    // Negative control: every motion onto the margin ends it, one that goes nowhere too, so the
    // cursor's own cell takes the mark.
    for motion in [
        "\r",
        "\x08",
        "\x1b[D",
        "\x1b[1;3H",
        "\x1b[3G",
        "\x1b7\x1b8",
        "\t\x1b[3G",
        "\x1b[K",
        "\x1b[?47h\x1b[?47l",
    ] {
        let s = at(2, &format!("e{motion}\u{301}"));
        assert!(
            s.cell(0, 1).unwrap().combining_marks().is_empty(),
            "{motion:?}"
        );
        assert_eq!(
            s.cell(0, 2).unwrap().combining_marks(),
            &['\u{301}'],
            "{motion:?}"
        );
    }
    // The cursor being on the margin is state of its own, so it serializes; and a screen that
    // never stepped onto one writes what it wrote before.
    let stepped = at(2, "e");
    let placed = at(2, "e\x1b[1;3H");
    assert_ne!(stepped, placed);
    assert_ne!(stepped.serialize(), placed.serialize());
    assert_eq!(placed.cursor(), stepped.cursor());
}

#[test]
fn italic_blink_strike_and_conceal_are_attributes_with_resets() {
    // xterm's CASE_SGR: 3 sets ATR_ITALIC and 23 clears it, 5 and 6 both set
    // BLINK and 25 clears it, 8 sets INVISIBLE and 28 clears it, 9 sets
    // ATR_STRIKEOUT and 29 clears it; 0 clears them all. Each is its own bit,
    // so setting one never touches another.
    let cases: [(&[u8], u8, &[u8]); 5] = [
        (b"3", attr::ITALIC, b"23"),
        (b"5", attr::BLINK, b"25"),
        (b"6", attr::BLINK, b"25"),
        (b"8", attr::CONCEAL, b"28"),
        (b"9", attr::STRIKE, b"29"),
    ];
    for (on, bit, off) in cases {
        let bytes = [
            b"\x1b[1m\x1b[".as_slice(),
            on,
            b"mA\x1b[",
            off,
            b"mB\x1b[",
            on,
            b"mC\x1b[0mD",
        ]
        .concat();
        let s = fold(8, 1, &out(&bytes));
        let attrs = |col| s.cell(0, col).unwrap().attrs;
        assert_eq!(
            attrs(0),
            attr::BOLD | bit,
            "{on:?} sets its bit beside bold"
        );
        assert_eq!(attrs(1), attr::BOLD, "{off:?} clears it and only it");
        assert_eq!(attrs(2), attr::BOLD | bit);
        assert_eq!(attrs(3), 0, "SGR 0 clears it");
    }
    // All four at once, then each reset: the bits are distinct.
    let s = fold(
        8,
        1,
        &out(b"\x1b[3;5;8;9mA\x1b[23mB\x1b[25mC\x1b[28mD\x1b[29mE"),
    );
    let all = attr::ITALIC | attr::BLINK | attr::CONCEAL | attr::STRIKE;
    let attrs: Vec<u8> = (0..5).map(|c| s.cell(0, c).unwrap().attrs).collect();
    assert_eq!(
        attrs,
        [
            all,
            all & !attr::ITALIC,
            attr::CONCEAL | attr::STRIKE,
            attr::STRIKE,
            0
        ]
    );
    // 21, xterm's double underline, is the underline's double style and no
    // attribute, cleared by 24 as `4:2` is; 22 clears bold only.
    let s = fold(8, 1, &out(b"\x1b[21mA\x1b[24mB\x1b[1;3;22mC"));
    assert_eq!(s.cell(0, 0).unwrap().attrs, 0);
    assert_eq!(s.cell(0, 0).unwrap().underline, Underline::Double);
    assert_eq!(s.cell(0, 1).unwrap().underline, Underline::None);
    assert_eq!(s.cell(0, 1).unwrap().attrs, 0);
    assert_eq!(s.cell(0, 2).unwrap().attrs, attr::ITALIC);
}

#[test]
fn the_new_attributes_ride_decsc_the_bce_blank_and_the_ops() {
    // DECSC saves the whole rendition (xterm `CursorSave` keeps `flags`), and
    // a restore brings the new bits back; an erased cell takes the colours
    // only, never an attribute.
    let s = fold(6, 1, &out(b"\x1b[3;9m\x1b7\x1b[0m\x1b8X\x1b[K"));
    assert_eq!(s.cell(0, 0).unwrap().attrs, attr::ITALIC | attr::STRIKE);
    assert_eq!(
        s.cell(0, 1).unwrap().attrs,
        0,
        "the bce blank carries no attribute"
    );
    // The resolved pen rides the typed ops: re-applying them is byte-equal,
    // and the screen serializes apart from one without the bits.
    let recs = out(b"\x1b[3;5;8;9mabc\x1b[23;29mdef");
    let ops = astream_term::screen::emit_ops(8, 1, &recs);
    assert_eq!(
        astream_term::screen::apply_ops(8, 1, &ops).serialize(),
        fold(8, 1, &recs).serialize()
    );
    assert_ne!(
        fold(4, 1, &out(b"\x1b[3mx")).serialize(),
        fold(4, 1, &out(b"x")).serialize()
    );
}

#[test]
fn a_truecolour_channel_past_255_is_clamped_in_every_spelling() {
    // The standards leave a channel past 255 undefined: xterm's
    // parse_extended_colors drops such a colour (`values[n] < 256` fails) and
    // Ghostty's parseDirectColor truncates it (`@truncate`, 300 -> 44). The
    // fold clamps it to 255, as aterm does, in the `;` form and both colon
    // forms alike; an in-range colour is kept exactly.
    let s = fold(
        8,
        1,
        &out(b"\x1b[38;2;1;2;300mA\x1b[38:2::1:999:3mB\x1b[48:2:0:256:0:0mC\x1b[38;2;255;0;7mD"),
    );
    let rgb = |col| {
        let c = s.cell(0, col).unwrap();
        (c.fg_rgb, c.bg_rgb)
    };
    assert_eq!(rgb(0), (Some((1, 2, 255)), None));
    assert_eq!(rgb(1), (Some((1, 255, 3)), None));
    assert_eq!(rgb(2), (Some((1, 255, 3)), Some((255, 0, 0))));
    assert_eq!(rgb(3), (Some((255, 0, 7)), Some((255, 0, 0))));
}

/// SGR 38, 48 and 58 in every spelling, each answer written out by hand: aterm's differential
/// oracle cannot see a mistake both engines share, so these values come from outside either
/// engine: ITU T.416 13.1.8 and xterm's `parse_extended_colors` where those two agree. Where they
/// do not, the answer is the rule's choice: 58 is in neither (here it reads as 38 does);
/// all-semicolon CMY and CMYK, and a sub-parameter after an all-semicolon colour, are not in
/// T.416 and run as codes in xterm, where here they do not; a short group (`:2:10:20`) names
/// nothing, as in xterm, where T.416's optional trailing elements would make it id 10, red 20.
///
/// The values are chosen to show a misreading. 3 is the colour-space id and is italic if it
/// reaches the SGR loop; 9, the last value, is crossed-out if it does; a reading off by one
/// gives (3, 10, 20) for (10, 20, 9).
mod sgr_colour {
    use super::{attr, fold, Color, Record, Underline};
    use astream_term::screen::Cell;

    #[derive(Clone, Copy, Debug)]
    enum Want {
        Rgb(u8, u8, u8),
        Palette(u8),
        /// No colour named: what the pen had stays.
        Unchanged,
    }
    use Want::{Palette, Rgb, Unchanged};

    /// What follows the code. The tests feed each at the end of the list and with a `;1` after it:
    /// that the bold lands proves the spelling consumed exactly its own arguments.
    const SPELLINGS: &[(&str, Want)] = &[
        // Direct colour. All semicolons carry no id (konsole's variation, which xterm accepts).
        (";2;10;20;9", Rgb(10, 20, 9)),
        // T.416: element 2 is the colour-space id, elements 3 to 5 are red, green and blue.
        (":2::10:20:9", Rgb(10, 20, 9)),
        (":2:3:10:20:9", Rgb(10, 20, 9)),
        // No id slot, which programs emit: three values are the channels.
        (":2:10:20:9", Rgb(10, 20, 9)),
        // After the first colon, colons hold (xterm's ctlseqs): the selector's group, read alike.
        (";2:3:10:20:9", Rgb(10, 20, 9)),
        (";2::10:20:9", Rgb(10, 20, 9)),
        (";2:10:20:9", Rgb(10, 20, 9)),
        // T.416's element 6 (no meaning), 7 (tolerance) and 8 (its colour space) change nothing.
        (":2:3:10:20:9:0:1:1", Rgb(10, 20, 9)),
        (";2:3:10:20:9:0:1:1", Rgb(10, 20, 9)),
        // A channel past 255 clamps; the id is still the first of four.
        (";2:3:10:300:9", Rgb(10, 255, 9)),
        // A trailing colon is an empty element (T.416: "represents a default value"; xterm's
        // CASE_ESC_COLON stores a 0 for it), and the count sees it: it can be the blue of any
        // form, and it makes three values into four.
        (":2::10:20:", Rgb(10, 20, 0)),
        (":2:3:10:20:", Rgb(10, 20, 0)),
        (";2::10:20:", Rgb(10, 20, 0)),
        (";2:3:10:20:", Rgb(10, 20, 0)),
        (":2:10:20:", Rgb(10, 20, 0)),
        (";2:10:20:", Rgb(10, 20, 0)),
        (":2:10:20:9:", Rgb(20, 9, 0)),
        (":5:", Palette(0)),
        (";5:", Palette(0)),
        (":2:", Unchanged),
        (":", Unchanged),
        (":3:3:10:20:", Unchanged),
        // Indexed colour.
        (";5;9", Palette(9)),
        (":5:9", Palette(9)),
        (";5:9", Palette(9)),
        (":5:9:7", Palette(9)),
        (";5:9:7", Palette(9)),
        // CMY and CMYK name a colour nothing here renders: a clean no-op, in each spelling.
        (":3:3:10:20:9", Unchanged),
        (":3::10:20:9", Unchanged),
        (":4:3:10:20:9:8", Unchanged),
        (":4::10:20:9:8", Unchanged),
        (";3:3:10:20:9", Unchanged),
        (";3::10:20:9", Unchanged),
        (";4:3:10:20:9:8", Unchanged),
        (";4::10:20:9:8", Unchanged),
        (";3;10;20;9", Unchanged),
        (";4;10;20;9;8", Unchanged),
        // T.416's 0 and 1 take no further elements, and an unknown selector consumes itself.
        (":0", Unchanged),
        (":1", Unchanged),
        (";0", Unchanged),
        (";1", Unchanged),
        (";7", Unchanged),
        (":7:9:9:9", Unchanged),
        (";7:9:9:9", Unchanged),
        // A group too short for its selector names nothing, and is still one group.
        (":2:10:20", Unchanged),
        (";2:10:20", Unchanged),
        (":2", Unchanged),
        (":5", Unchanged),
        // A sub-parameter is never a code, whatever a semicolon colour's values overlap.
        (";2;10;20;9:4", Rgb(10, 20, 9)),
        (";5;9:4", Palette(9)),
        (";5;9:", Palette(9)),
        (";3;10;20;9:4", Unchanged),
        (";4;10;20;9;8:4", Unchanged),
    ];

    /// Semicolon spellings cut short, which have no room for a `;1` after them.
    const CUT_SHORT: &[&str] = &[
        ";2;10;20",
        ";2;10",
        ";2",
        ";5",
        ";3;10;20",
        ";4;10;20;9",
        "",
    ];

    /// A cell's foreground, background and underline colour, each as its palette colour and its
    /// 24-bit override.
    type Drawn = [(Color, Option<(u8, u8, u8)>); 3];

    fn cell(sgr: &str) -> Cell {
        let bytes = format!("\x1b[33;44;58;5;5m\x1b[{sgr}mX").into_bytes();
        fold(4, 1, &[Record::Out(bytes)])
            .cell(0, 0)
            .copied()
            .expect("one cell")
    }

    /// The colours the pen starting at palette 3 on palette 4, underlined in palette 5, draws in
    /// after `want` on `code`.
    fn colours(code: u16, want: Want) -> Drawn {
        let picked = |base: u8| match want {
            Rgb(r, g, b) => (Color::Default, Some((r, g, b))),
            Palette(n) => (Color::Indexed(n), None),
            Unchanged => (Color::Indexed(base), None),
        };
        let plain = |n: u8| (Color::Indexed(n), None);
        match code {
            38 => [picked(3), plain(4), plain(5)],
            48 => [plain(3), picked(4), plain(5)],
            _ => [plain(3), plain(4), picked(5)],
        }
    }

    #[test]
    fn every_spelling_names_its_colour_and_consumes_exactly_its_arguments() {
        let mut wrong = Vec::new();
        let mut check = |sgr: String, want: Drawn, attrs: u8| {
            let c = cell(&sgr);
            let got = [(c.fg, c.fg_rgb), (c.bg, c.bg_rgb), (c.ul, c.ul_rgb)];
            if got != want || c.attrs != attrs {
                wrong.push(format!(
                    "{sgr}: {got:?} attrs {:#x}, not {want:?} attrs {attrs:#x}",
                    c.attrs
                ));
            }
        };
        for code in [38, 48, 58] {
            for &(tail, want) in SPELLINGS {
                check(format!("{code}{tail};1"), colours(code, want), attr::BOLD);
                check(format!("{code}{tail}"), colours(code, want), 0);
            }
            for tail in CUT_SHORT {
                check(format!("{code}{tail}"), colours(code, Unchanged), 0);
            }
        }
        assert!(
            wrong.is_empty(),
            "{} wrong:\n{}",
            wrong.len(),
            wrong.join("\n")
        );
    }

    /// A group earlier in the list does not move where a later one is read.
    #[test]
    fn the_spellings_read_alike_after_a_group_and_together() {
        let c = cell("4:3;38;2:3:10:20:9;48:2:3:30:40:8;58;5:9;1");
        assert_eq!(c.fg_rgb, Some((10, 20, 9)));
        assert_eq!(c.bg_rgb, Some((30, 40, 8)));
        assert_eq!(c.ul, Color::Indexed(9));
        assert_eq!(c.underline, Underline::Curly);
        assert_eq!(c.attrs, attr::BOLD);
    }

    /// Sub-parameters on any other code are ignored with it, a trailing colon's empty one too
    /// (xterm's "unexpected subparameter in SGR", Ghostty's and Alacritty's unknown), so none of
    /// their values lands as a code either.
    #[test]
    fn a_group_on_a_code_that_takes_none_is_ignored_whole() {
        for sgr in ["1:4", "3:4:9", "0:1", "22:9", "1:", "0:", "22:"] {
            let c = cell(&format!("7;{sgr}"));
            assert_eq!(c.attrs, attr::REVERSE, "{sgr}");
            assert_eq!(c.fg, Color::Indexed(3), "{sgr}");
        }
    }

    /// `4:n` is the one other code that takes a group: its first element is the style, and a
    /// trailing colon's empty one is `4:0`, off.
    #[test]
    fn four_takes_a_style_and_nothing_past_it() {
        assert_eq!(cell("4:3:9").underline, Underline::Curly);
        assert_eq!(cell("4:3:9").attrs, 0);
        assert_eq!(cell("4;4:").underline, Underline::None);
        assert_eq!(cell("4;4:;1").attrs, attr::BOLD);
    }
}
