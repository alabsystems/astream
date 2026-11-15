// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `term.fold.wide-glyphs`: the fold gives an East Asian Wide or
//! Fullwidth character two cells, a lead (`Cell::width` 2) and a spacer (0), and
//! no operation leaves half of one.
//!
//! Each fixed case is reasoned from xterm's source (charproc.c `dotext`, util.c
//! `WriteText`, `ClearRight`, `ClearLeft`, `InsertChar`, `DeleteChar` and the
//! `DamagedCells` repair, screen.c `ClearCells`) and Ghostty's (`Terminal.print`,
//! `printCell`, `insertBlanks`, `deleteChars`, `rowWillBeShifted` and
//! `Screen.splitCellBoundary`); where the two differ the case says which one the
//! fold follows. The generators state laws over random programs, each with a
//! negative control showing the programs reach what the law protects.
//! Cross-validated out of tree against the production aterm engine by aterm's
//! differential VT oracle, which this module does not run.

use astream_term::screen::{self, attr, Cell, Color, Folder, Screen, Underline};
use astream_term::{char_display_width, is_wide_char, Record};

fn out(b: &[u8]) -> Vec<Record> {
    vec![Record::Out(b.to_vec())]
}

fn fold(cols: u16, rows: u16, b: &str) -> Screen {
    screen::fold(cols, rows, &out(b.as_bytes()))
}

fn rows(s: &Screen) -> Vec<String> {
    (0..s.dims().1).map(|r| s.line_text(r)).collect()
}

fn cell(s: &Screen, row: u16, col: u16) -> Cell {
    *s.cell(row, col).expect("a cell on the screen")
}

/// Which part of a glyph each cell of row `row` holds: `L` a lead, `S` a
/// spacer, `.` a narrow cell.
fn halves(s: &Screen, row: u16) -> String {
    (0..s.dims().0)
        .map(|c| match cell(s, row, c).width {
            0 => 'S',
            2 => 'L',
            _ => '.',
        })
        .collect()
}

const ZHONG: char = '\u{4e2d}';
const WEN: char = '\u{6587}';

/// A dep-free splitmix64 PRNG so the generators are reproducible.
fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn below(state: &mut u64, n: u64) -> u64 {
    next(state) % n
}

#[test]
fn east_asian_wide_and_fullwidth_take_two_columns() {
    for wide in [
        ZHONG,
        WEN,
        '\u{3042}',  // HIRAGANA LETTER A
        '\u{30a2}',  // KATAKANA LETTER A
        '\u{ac00}',  // HANGUL SYLLABLE GA
        '\u{ff21}',  // FULLWIDTH LATIN CAPITAL LETTER A
        '\u{3000}',  // IDEOGRAPHIC SPACE (Fullwidth)
        '\u{1f600}', // GRINNING FACE (Wide since Unicode 9)
        '\u{20000}', // CJK EXTENSION B
        '\u{1f1e6}', // REGIONAL INDICATOR A (Neutral by East Asian Width; aterm draws it wide)
    ] {
        assert_eq!(char_display_width(wide), 2, "U+{:04X}", wide as u32);
    }
    // Narrow, ambiguous (narrow outside CJK contexts) and halfwidth forms take
    // one column; a combining mark takes none.
    for narrow in [
        'a',
        '\u{e9}',
        '\u{2500}',
        '\u{ff61}',
        '\u{fffd}',
        '\u{1f3f3}', // WAVING WHITE FLAG (N; aterm widens it only after a VS16)
        '\u{323b0}', // past CJK Extension H, unassigned: narrow in aterm and xterm
        '\u{10ffff}',
    ] {
        assert_eq!(char_display_width(narrow), 1, "U+{:04X}", narrow as u32);
    }
    assert_eq!(char_display_width('\u{301}'), 0);
}

#[test]
fn a_combining_mark_wide_by_east_asian_width_takes_no_column() {
    // U+302A..U+302D (the ideographic tone marks), U+3099/U+309A (the
    // combining kana voiced marks) and U+16FE4 (the Khitan small script
    // filler) are Mn marks whose East Asian Width is Wide. Measured alone they
    // take no column: xterm's wcwidth lists them in its combining table,
    // Ghostty gives them width 0 and aterm's char_width measures them zero.
    // So NFD kana, as macOS file names carry them, take the columns their NFC
    // form takes, the mark on the kana's lead.
    for mark in [
        '\u{302a}',
        '\u{302b}',
        '\u{302c}',
        '\u{302d}',
        '\u{3099}',
        '\u{309a}',
        '\u{16fe4}',
    ] {
        assert_eq!(char_display_width(mark), 0, "U+{:04X}", mark as u32);
        assert!(!is_wide_char(mark), "U+{:04X}", mark as u32);
    }
    let nfd = fold(8, 1, "\u{304b}\u{3099}x");
    assert_eq!(nfd.cursor(), fold(8, 1, "\u{304c}x").cursor());
    assert_eq!((nfd.cursor(), halves(&nfd, 0)), ((0, 3), "LS......".into()));
    assert_eq!(cell(&nfd, 0, 0).combining_marks(), ['\u{3099}']);
    let tone = fold(8, 1, "\u{4e2d}\u{302a}x");
    assert_eq!(
        (tone.cursor(), halves(&tone, 0)),
        ((0, 3), "LS......".into())
    );
    assert_eq!(cell(&tone, 0, 0).combining_marks(), ['\u{302a}']);
    // The kana and ideographs around them stay wide (negative control).
    assert_eq!(char_display_width('\u{309b}'), 2);
    assert_eq!(char_display_width('\u{3029}'), 2);
}

#[test]
fn a_wide_glyph_is_a_lead_and_a_spacer_and_moves_the_cursor_two() {
    let s = fold(6, 1, "a\u{4e2d}b");
    assert_eq!(s.line_text(0), "a\u{4e2d}b", "the glyph reads once");
    assert_eq!(halves(&s, 0), ".LS...");
    assert_eq!(s.cursor(), (0, 4));
    // The spacer carries the lead's rendition (xterm's ScrnWriteText writes
    // the attributes for every column the text takes).
    let s = fold(6, 1, "\x1b[1;31;44m\u{4e2d}");
    let (lead, spacer) = (cell(&s, 0, 0), cell(&s, 0, 1));
    assert_eq!((lead.ch, spacer.ch), (ZHONG, ' '));
    for c in [lead, spacer] {
        assert_eq!((c.fg, c.bg), (Color::Indexed(1), Color::Indexed(4)));
        assert_ne!(c.attrs & attr::BOLD, 0);
    }
}

#[test]
fn a_wide_glyph_ending_on_the_last_column_leaves_the_wrap_on_its_spacer() {
    // xterm's dotext: the glyph fills the line (`width_here ==
    // width_available`), so `do_wrap` is set and the cursor stays on the
    // last column, the spacer.
    let s = fold(5, 2, "abc\u{4e2d}");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 5), true));
    let s = fold(5, 2, "abc\u{4e2d}x");
    assert_eq!(rows(&s), ["abc\u{4e2d}", "x"]);
    // And at a right margin: the wrap is pending on the margin.
    let s = fold(8, 2, "\x1b[?69h\x1b[1;4sab\u{4e2d}");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 4), true));
}

#[test]
fn a_wide_glyph_with_one_column_left_wraps_and_blanks_that_column() {
    // xterm's dotext forces the wrap and writes nothing in the column it
    // skips; Ghostty (`spacer_head`), Alacritty and aterm blank it. The fold
    // blanks it with the bce blank, as every blank it makes.
    let s = fold(5, 2, "abcd\x1b[44m\u{4e2d}");
    assert_eq!(rows(&s), ["abcd", "\u{4e2d}"]);
    assert_eq!(halves(&s, 1), "LS...");
    assert_eq!(s.cursor(), (1, 2));
    let skipped = cell(&s, 0, 4);
    assert_eq!((skipped.ch, skipped.bg), (' ', Color::Indexed(4)));
    // What stood in that column is gone.
    let s = fold(5, 2, "abcde\x1b[1;5H\u{4e2d}");
    assert_eq!(rows(&s), ["abcd", "\u{4e2d}"]);
    // A pending wrap resolves first, so a glyph after a full line starts the
    // next one with no column skipped.
    let s = fold(5, 2, "abcde\u{4e2d}");
    assert_eq!(rows(&s), ["abcde", "\u{4e2d}"]);
    // At a right margin the line ends there: the margin column is blanked
    // and the glyph wraps onto the left margin. From past the right margin
    // the line runs to the screen's edge.
    let s = fold(8, 2, "\x1b[?69h\x1b[2;5s\x1b[1;2Habc\u{4e2d}");
    assert_eq!(rows(&s), [" abc", " \u{4e2d}"]);
    let s = fold(8, 2, "\x1b[?69h\x1b[2;5s\x1b[1;7Hx\u{4e2d}");
    assert_eq!(rows(&s), ["      x", " \u{4e2d}"]);
}

#[test]
fn a_screen_one_column_wide_prints_a_wide_glyph_as_a_narrow_space() {
    // Ghostty's print: `printCell(0, .narrow)` in the pen, then the cursor
    // moves as for a narrow glyph. xterm's dotext gives up on the glyph.
    let s = fold(1, 3, "\x1b[4;31m\u{4e2d}");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 1), true));
    let c = cell(&s, 0, 0);
    assert_eq!((c.ch, c.width, c.fg), (' ', 1, Color::Indexed(1)));
    assert_eq!(c.underline, Underline::Single);
    let s = fold(1, 3, "a\u{4e2d}b");
    assert_eq!(rows(&s), ["a", "", "b"]);
}

#[test]
fn writing_over_half_a_wide_glyph_blanks_the_other_half() {
    // xterm's WriteText clears its `DamagedCurCells` with ClearInLine, which
    // writes the current colours; Ghostty's printCell clears the other half
    // to its `blankCell`, the pen's background. Both are the bce blank.
    let base = "\u{4e2d}\u{6587}\x1b[44m";
    // A narrow glyph on a spacer: the lead goes.
    let s = fold(6, 1, &format!("{base}\x1b[1;2Hx"));
    assert_eq!(s.line_text(0), " x\u{6587}");
    assert_eq!(halves(&s, 0), "..LS..");
    assert_eq!(
        cell(&s, 0, 0).bg,
        Color::Indexed(4),
        "the orphan takes the bce blank"
    );
    // On a lead: the spacer goes.
    let s = fold(6, 1, &format!("{base}\x1b[1;1Hx"));
    assert_eq!(s.line_text(0), "x \u{6587}");
    assert_eq!(halves(&s, 0), "..LS..");
    assert_eq!(cell(&s, 0, 1).bg, Color::Indexed(4));
    // A wide glyph across two: the halves outside it go.
    let s = fold(6, 1, &format!("{base}\x1b[1;2H\u{4e2d}"));
    assert_eq!(s.line_text(0), " \u{4e2d}");
    assert_eq!(halves(&s, 0), ".LS...");
    assert_eq!(
        (cell(&s, 0, 0).bg, cell(&s, 0, 3).bg),
        (Color::Indexed(4), Color::Indexed(4))
    );
    // A wide glyph exactly over another replaces it with nothing left over.
    let s = fold(6, 1, &format!("{base}\x1b[1;1H\u{3042}"));
    assert_eq!(s.line_text(0), "\u{3042}\u{6587}");
    assert_eq!(halves(&s, 0), "LSLS..");
}

#[test]
fn an_erase_that_cuts_a_wide_glyph_erases_all_of_it() {
    // xterm's ClearRight and ClearLeft repair the `DamagedCurCells` around
    // the range; ClearCells widens a range to whole glyphs. Ghostty's erase
    // paths split the boundaries the same way.
    let base = "\u{4e2d}\u{6587}ab\x1b[44m";
    // ECH from a spacer takes its lead; ECH ending on a lead takes its spacer.
    let s = fold(8, 1, &format!("{base}\x1b[1;2H\x1b[X"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("  \u{6587}ab".into(), "..LS....".into())
    );
    let s = fold(8, 1, &format!("{base}\x1b[1;2H\x1b[2X"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("    ab".into(), "........".into())
    );
    assert_eq!(cell(&s, 0, 3).bg, Color::Indexed(4));
    // EL 0 from a spacer, EL 1 through a lead.
    let s = fold(8, 1, &format!("{base}\x1b[1;4H\x1b[K"));
    assert_eq!(s.line_text(0), "\u{4e2d}");
    let s = fold(8, 1, &format!("{base}\x1b[1;3H\x1b[1K"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("    ab".into(), "........".into())
    );
    // ED 0 and ED 1 cut the cursor's row the same way.
    let s = fold(8, 2, &format!("{base}\x1b[1;4H\x1b[J"));
    assert_eq!(s.line_text(0), "\u{4e2d}");
    let s = fold(8, 2, &format!("{base}\x1b[1;3H\x1b[1J"));
    assert_eq!(s.line_text(0), "    ab");
    // An erase that cuts nothing leaves a glyph whole (negative control).
    let s = fold(8, 1, &format!("{base}\x1b[1;5H\x1b[K"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("\u{4e2d}\u{6587}".into(), "LSLS....".into())
    );
}

#[test]
fn ich_and_dch_never_split_a_wide_glyph() {
    let base = "\u{4e2d}\u{6587}ab\x1b[44m";
    // ICH on a spacer: the glyph goes, then the line shifts (xterm's
    // RepairInsertChar at the cursor; Ghostty's insertBlanks).
    let s = fold(8, 1, &format!("{base}\x1b[1;2H\x1b[@"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("   \u{6587}ab".into(), "...LS...".into())
    );
    // ICH pushing a spacer past the last column: its lead goes too.
    let s = fold(6, 1, "ab\u{4e2d}\u{6587}\x1b[1;1H\x1b[@");
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        (" ab\u{4e2d}".into(), "...LS.".into())
    );
    // DCH on a spacer, and DCH of a lead whose spacer it keeps.
    let s = fold(8, 1, &format!("{base}\x1b[1;2H\x1b[P"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        (" \u{6587}ab".into(), ".LS.....".into())
    );
    let s = fold(8, 1, &format!("{base}\x1b[1;1H\x1b[P"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        (" \u{6587}ab".into(), ".LS.....".into())
    );
    assert_eq!(
        cell(&s, 0, 0).bg,
        Color::Indexed(4),
        "the kept spacer took the bce blank"
    );
    // Deleting a whole glyph shifts the next one whole.
    let s = fold(8, 1, &format!("{base}\x1b[1;1H\x1b[2P"));
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("\u{6587}ab".into(), "LS......".into())
    );
}

#[test]
fn a_glyph_straddling_the_right_margin_goes_whole_before_ich_and_dch() {
    // The glyph's lead is on the right margin, its spacer past it: Ghostty's
    // insertBlanks clears both halves up front, and its deleteChars splits
    // the boundary at the margin's edge. xterm moves the lead and leaves the
    // spacer torn.
    let setup = "xy\u{4e2d}z\x1b[?69h\x1b[1;3s\x1b[44m";
    for (op, want) in [("\x1b[@", " xy z"), ("\x1b[P", "y   z")] {
        let s = fold(6, 1, &format!("{setup}{op}"));
        assert_eq!(s.line_text(0), want, "{op:?}");
        assert_eq!(halves(&s, 0), "......", "{op:?}");
        assert_eq!(
            cell(&s, 0, 3).bg,
            Color::Indexed(4),
            "{op:?}: the outside half"
        );
    }
}

#[test]
fn insert_mode_makes_room_for_both_columns() {
    // xterm's WriteText runs InsertChar for the glyph's columns first.
    let s = fold(6, 1, "abcd\x1b[1;1H\x1b[4h\u{4e2d}");
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        ("\u{4e2d}abcd".into(), "LS....".into())
    );
    assert_eq!(s.cursor(), (0, 2));
}

#[test]
fn a_scroll_between_margins_unpairs_the_glyphs_straddling_them() {
    // Ghostty's rowWillBeShifted turns a wide glyph that straddles a margin
    // into two blank cells, each keeping its rendition, before the rows move;
    // xterm moves the inside half and leaves the outside one torn. With the
    // margins on columns 2..=3, row 0's glyph straddles the right one and
    // row 1's the left one.
    let s = fold(
        7,
        2,
        "\x1b[31mabc\u{4e2d}de\r\nx\u{6587}yzw\x1b[?69h\x1b[3;4s\x1b[0m\x1b[S",
    );
    assert_eq!(halves(&s, 0), ".......");
    assert_eq!(halves(&s, 1), ".......");
    assert_eq!(rows(&s), ["ab y de", "x   zw"]);
    for (row, col) in [(0, 4), (1, 1)] {
        let outside = cell(&s, row, col);
        assert_eq!(
            (outside.ch, outside.fg),
            (' ', Color::Indexed(1)),
            "({row},{col}) keeps its colour"
        );
    }
    // The two blanks drop the glyph's marks (Ghostty's `clearGrapheme`): the
    // lead left of the left margin, which stays, keeps no accent.
    let s = fold(
        7,
        2,
        "abcdefg\r\nx\u{6587}\u{301}yzw\x1b[?69h\x1b[3;4s\x1b[S",
    );
    assert_eq!(rows(&s)[1], "x   zw");
    assert!(cell(&s, 1, 1).combining_marks().is_empty());
    // A glyph wholly inside the margins moves whole (negative control).
    let s = fold(6, 2, "\x1b[?69h\x1b[2;5s\x1b[2;2H\u{4e2d}\x1b[S");
    assert_eq!(
        (s.line_text(0), halves(&s, 0)),
        (" \u{4e2d}".into(), ".LS...".into())
    );
}

#[test]
fn a_narrowing_that_cuts_a_spacer_off_blanks_its_lead() {
    let recs = [
        Record::Out("ab\u{4e2d}".as_bytes().to_vec()),
        Record::Resize { cols: 3, rows: 1 },
    ];
    let s = screen::fold(5, 1, &recs);
    assert_eq!((s.line_text(0), halves(&s, 0)), ("ab".into(), "...".into()));
    // One that keeps the whole glyph keeps it (negative control).
    let recs = [
        Record::Out("ab\u{4e2d}".as_bytes().to_vec()),
        Record::Resize { cols: 4, rows: 1 },
    ];
    let s = screen::fold(5, 1, &recs);
    assert_eq!(halves(&s, 0), "..LS");
}

#[test]
fn a_combining_mark_after_a_wide_glyph_rides_its_lead() {
    let s = fold(6, 1, "\u{4e2d}\u{301}x");
    assert_eq!(cell(&s, 0, 0).combining_marks(), ['\u{301}']);
    assert!(cell(&s, 0, 1).combining_marks().is_empty());
    assert_eq!(s.line_text(0), "\u{4e2d}\u{301}x");
}

#[test]
fn the_serialization_tells_the_halves_apart_and_keeps_narrow_bytes() {
    // A lead with its spacer and the same two cells narrow are different
    // screens, so they serialize differently.
    let wide = fold(4, 1, "\u{4e2d}");
    let mut narrow = wide.clone();
    narrow.set_cell(
        0,
        0,
        Cell {
            width: 1,
            ..cell(&wide, 0, 0)
        },
    );
    narrow.set_cell(
        0,
        1,
        Cell {
            width: 1,
            ..cell(&wide, 0, 1)
        },
    );
    assert_ne!(wide, narrow);
    assert_ne!(wide.serialize(), narrow.serialize());
    // A screen of narrow glyphs ends where it did before the wide state
    // existed: no trailer tag 3 follows the scroll region.
    let plain = fold(4, 1, "ab");
    let bytes = plain.serialize();
    assert_ne!(bytes.last(), Some(&3), "no wide trailer on a narrow screen");
    assert_eq!(bytes.len(), fold(4, 1, "cd").serialize().len());
}

#[test]
fn the_ops_re_apply_wide_glyphs_losslessly() {
    let recs = out(
        "\u{4e2d}\u{6587}ab\x1b[44m\x1b[1;2Hx\x1b[1;1H\u{3042}\x1b[2X\x1b[@\x1b[P\x1b[?69h\x1b[2;4s\u{ac00}\u{ac00}\x1b[S"
            .as_bytes(),
    );
    let ops = screen::emit_ops(6, 2, &recs);
    assert_eq!(
        screen::apply_ops(6, 2, &ops).serialize(),
        screen::fold(6, 2, &recs).serialize()
    );
}

/// One random token of a wide-glyph program: wide and narrow text, the
/// motions that land on a spacer, every edit that can cut a glyph, the
/// margins, insert mode and the scrolls.
fn wide_token(st: &mut u64) -> Vec<u8> {
    const GLYPHS: [char; 6] = [ZHONG, WEN, '\u{ac00}', 'a', 'b', '\u{e9}'];
    match below(st, 14) {
        0..=4 => (0..1 + below(st, 6))
            .map(|_| GLYPHS[below(st, GLYPHS.len() as u64) as usize])
            .collect::<String>()
            .into_bytes(),
        5 => format!("\x1b[{};{}H", 1 + below(st, 4), 1 + below(st, 10)).into_bytes(),
        6 => format!(
            "\x1b[{}{}",
            below(st, 4),
            ['@', 'P', 'X', 'K', 'J'][below(st, 5) as usize]
        )
        .into_bytes(),
        7 => [b"\x1b[?69h".as_slice(), b"\x1b[?69l"][below(st, 2) as usize].to_vec(),
        8 => format!("\x1b[{};{}s", below(st, 8), below(st, 12)).into_bytes(),
        9 => [b"\x1b[4h".as_slice(), b"\x1b[4l"][below(st, 2) as usize].to_vec(),
        10 => format!(
            "\x1b[{}{}",
            below(st, 3),
            ['S', 'T', 'L', 'M'][below(st, 4) as usize]
        )
        .into_bytes(),
        11 => format!("\x1b[4{}m", below(st, 8)).into_bytes(),
        12 => b"\r\n".to_vec(),
        _ => [b"\x1bD".as_slice(), b"\x1bM", b"\x1b[C", b"\x1b[D"][below(st, 4) as usize].to_vec(),
    }
}

/// Every spacer follows a lead and every lead is followed by a spacer.
fn torn_half(s: &Screen) -> Option<(u16, u16)> {
    let (cols, rows) = s.dims();
    for r in 0..rows {
        for c in 0..cols {
            let here = cell(s, r, c).width;
            let next = if c + 1 < cols {
                Some(cell(s, r, c + 1).width)
            } else {
                None
            };
            let prev = if c > 0 {
                Some(cell(s, r, c - 1).width)
            } else {
                None
            };
            let ok = match here {
                2 => next == Some(0),
                0 => prev == Some(2),
                1 => true,
                _ => false,
            };
            if !ok {
                return Some((r, c));
            }
        }
    }
    None
}

#[test]
fn random_wide_programs_never_leave_half_a_glyph_and_project_losslessly() {
    // The law: after every record no cell holds half a wide glyph whose other
    // half is gone, and the typed ops re-apply to a byte-equal screen. The
    // negative control counts the records that start with the cursor on a
    // spacer or with a glyph straddling a margin, the states a write, an
    // erase or a shift would tear: the programs reach both often.
    let (mut on_spacer, mut straddling) = (0u32, 0u32);
    for seed in 0..800u64 {
        let mut st = seed.wrapping_mul(0x0002_0005).wrapping_add(13);
        let (cols, rows) = (2 + below(&mut st, 9) as u16, 1 + below(&mut st, 4) as u16);
        let mut recs = Vec::new();
        for _ in 0..1 + below(&mut st, 24) {
            if below(&mut st, 12) == 0 {
                recs.push(Record::Resize {
                    cols: 1 + below(&mut st, 10) as u16,
                    rows,
                });
            } else {
                recs.push(Record::Out(wide_token(&mut st)));
            }
        }
        let mut folder = Folder::new(cols, rows);
        for rec in &recs {
            let s = folder.screen();
            let (c, _) = s.dims();
            let (row, col) = s.cursor();
            on_spacer += u32::from(col < c && cell(s, row, col).width == 0);
            let (left, right) = s.lr_margins();
            straddling += u32::from((0..s.dims().1).any(|r| {
                (left > 0 && cell(s, r, left).width == 0)
                    || (right + 1 < c && cell(s, r, right).width == 2)
            }));
            folder.apply(rec);
            assert_eq!(
                torn_half(folder.screen()),
                None,
                "seed {seed}: half a glyph after {rec:?}"
            );
        }
        let ops = screen::emit_ops(cols, rows, &recs);
        assert_eq!(
            screen::apply_ops(cols, rows, &ops).serialize(),
            folder.screen().serialize(),
            "seed {seed}: the ops re-apply to the fold"
        );
    }
    assert!(
        on_spacer >= 150,
        "only {on_spacer} records started on a spacer"
    );
    assert!(
        straddling >= 25,
        "only {straddling} records started with a glyph straddling a margin"
    );
}
