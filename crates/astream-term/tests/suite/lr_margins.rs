// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `term.fold.lr-margins`: the fold models DECLRMM (`?69`) and
//! DECSLRM (`CSI Pl ; Pr s`) as xterm does (charproc.c `CASE_DECSLRM`,
//! `srm_DECLRMM`; cursor.c and util.c for each operation the margins bound).
//!
//! Each fixed case below is reasoned from xterm's source; the two generators
//! state laws over random programs, each with a negative control showing the
//! programs reach what the law protects. Cross-validated out of tree against the
//! production aterm engine by aterm's differential VT oracle, which this module
//! does not run.

use astream_term::screen::{self, Folder, Screen};
use astream_term::{Record, ScreenOp};

fn out(b: &[u8]) -> Vec<Record> {
    vec![Record::Out(b.to_vec())]
}

fn fold(cols: u16, rows: u16, b: &[u8]) -> Screen {
    screen::fold(cols, rows, &out(b))
}

fn rows(s: &Screen) -> Vec<String> {
    (0..s.dims().1).map(|r| s.line_text(r)).collect()
}

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
fn declrmm_turns_csi_s_into_decslrm() {
    // Without DECLRMM a bare `CSI s` saves the cursor.
    let s = fold(10, 2, b"\x1b[1;3H\x1b[s\x1b[H\x1b[uX");
    assert_eq!(s.line_text(0), "  X");
    assert_eq!(s.lr_margins(), (0, 9));
    // Under it `CSI Pl ; Pr s` sets the margins (1-based in, 0-based out) and
    // homes the cursor; a save is `ESC 7` only.
    let s = fold(10, 2, b"\x1b[?69h\x1b[1;5H\x1b[3;6s");
    assert_eq!(s.lr_margins(), (2, 5));
    assert_eq!(s.cursor(), (0, 0), "DECSLRM homes the cursor");
    let s = fold(10, 2, b"\x1b[?69h\x1b[1;5H\x1b7\x1b[H\x1b8X");
    assert_eq!(s.line_text(0), "    X", "ESC 7 still saves");
    // A bare `CSI s` there is DECSLRM with both defaults: the full width.
    let s = fold(10, 2, b"\x1b[?69h\x1b[3;6s\x1b[1;5H\x1b[sX");
    assert_eq!(s.lr_margins(), (0, 9));
    assert_eq!(s.line_text(0), "X", "and it homed the cursor");
}

#[test]
fn decslrm_ignores_an_empty_or_inverted_pair_and_clamps_the_right() {
    let set = b"\x1b[?69h\x1b[3;6s\x1b[2;8H".to_vec();
    let s = fold(10, 3, &set);
    assert_eq!((s.lr_margins(), s.cursor()), ((2, 5), (1, 7)));
    // `right > left` (xterm `if (right > left)`), else nothing: neither the
    // margins nor the cursor move.
    for bad in [b"\x1b[4;4s".as_slice(), b"\x1b[5;2s", b"\x1b[10;10s"] {
        let s = fold(10, 3, &[set.as_slice(), bad].concat());
        assert_eq!(
            (s.lr_margins(), s.cursor()),
            ((2, 5), (1, 7)),
            "{bad:?} changed nothing"
        );
    }
    // A right past the screen, 0 or absent is the last column; a left of 0
    // is 1. Each valid pair homes the cursor.
    for (good, want) in [
        (b"\x1b[3;99s".as_slice(), (2, 9)),
        (b"\x1b[3;0s", (2, 9)),
        (b"\x1b[3s", (2, 9)),
        (b"\x1b[0;4s", (0, 3)),
        (b"\x1b[;4s", (0, 3)),
    ] {
        let s = fold(10, 3, &[set.as_slice(), good].concat());
        assert_eq!((s.lr_margins(), s.cursor()), (want, (0, 0)), "{good:?}");
    }
    // A one-column screen has no pair with `left < right`.
    let s = fold(1, 2, b"\x1b[?69h\x1b[1;1s\x1b[s\x1b[0;9s");
    assert_eq!(s.lr_margins(), (0, 0));
}

#[test]
fn declrmm_reset_restores_the_full_width_and_leaves_the_cursor() {
    // xterm `srm_DECLRMM` resets the margins (`reset_lr_margins`); the cursor
    // stays, and setting the mode again brings no old margins back.
    let s = fold(10, 2, b"\x1b[?69h\x1b[3;6s\x1b[1;4H\x1b[?69l");
    assert_eq!((s.lr_margins(), s.cursor()), ((0, 9), (0, 3)));
    let s = fold(
        10,
        2,
        b"\x1b[?69h\x1b[3;6s\x1b[?69l\x1b[?69h\x1b[1;1Habcdefgh",
    );
    assert_eq!(s.lr_margins(), (0, 9));
    assert_eq!(s.line_text(0), "abcdefgh", "no margin wraps the text");
    // With the mode off `CSI s` saves again; RIS turns the mode off too.
    let s = fold(10, 2, b"\x1b[?69h\x1b[?69l\x1b[1;3H\x1b[s\x1b[H\x1b[uX");
    assert_eq!(s.line_text(0), "  X");
    let s = fold(
        10,
        2,
        b"\x1b[?69h\x1b[3;6s\x1bc\x1b[1;3H\x1b[s\x1b[H\x1b[uX",
    );
    assert_eq!((s.lr_margins(), s.line_text(0)), ((0, 9), "  X".into()));
    // A wrap pending on the old right margin survives the reset, and the next
    // glyph still wraps (xterm keeps `do_wrap`; `WrapLine` goes to column 0).
    let s = fold(10, 2, b"\x1b[?69h\x1b[1;4sabcd\x1b[?69l");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 4), true));
    let s = fold(10, 2, b"\x1b[?69h\x1b[1;4sabcd\x1b[?69lX");
    assert_eq!(rows(&s), ["abcd", "X"]);
}

#[test]
fn a_glyph_wraps_at_the_right_margin_onto_the_left_one() {
    // xterm `dotext`: the line ends at the right margin for a cursor not past
    // it, left of the left margin too; `WrapLine` indexes and goes to the left
    // margin.
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6sabcdef");
    assert_eq!(s.line_text(0), "abcdef");
    assert_eq!(
        (s.cursor(), s.wrap_pending()),
        ((0, 6), true),
        "a wrap pending on the margin reads one past it"
    );
    // Standing on the column after the margin is another state.
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6sabcdef\x1b[1;7H");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 6), false));
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6sabcdefg");
    assert_eq!(rows(&s), ["abcdef", "  g", ""]);
    assert_eq!(s.cursor(), (1, 3));
    // From past the right margin the line runs to the screen's edge, and the
    // wrap still lands on the left margin.
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6s\x1b[1;9Hxyz");
    assert_eq!(rows(&s), ["        xy", "  z", ""]);
}

/// Six columns, three rows of distinct glyphs, margins on columns 2..=5
/// (1-based; 0-based `(1, 4)`).
const GRID: &[u8] = b"ABCDEF\r\nGHIJKL\r\nMNOPQR\x1b[?69h\x1b[2;5s";

fn on_grid(tail: &[u8]) -> Screen {
    fold(6, 3, &[GRID, tail].concat())
}

#[test]
fn every_scroll_moves_only_the_rectangle_between_the_margins() {
    assert_eq!(rows(&on_grid(b"")), ["ABCDEF", "GHIJKL", "MNOPQR"]);
    // LF, IND and a wrap at the bottom margin from inside the margins scroll
    // the rectangle up (xterm `xtermIndex` -> `xtermScroll` ->
    // `scrollInMargins`); the cells beside it stay.
    for lf in [b"\x1b[3;3H\n".as_slice(), b"\x1b[3;3H\x1bD"] {
        let s = on_grid(lf);
        assert_eq!(rows(&s), ["AHIJKF", "GNOPQL", "M    R"], "{lf:?}");
        assert_eq!(s.cursor(), (2, 2));
    }
    let s = on_grid(b"\x1b[3;2Hwxyz!");
    assert_eq!(rows(&s), ["AHIJKF", "GwxyzL", "M!   R"]);
    // From outside the margins the index is `CursorDown`, which the bottom
    // margin stops: nothing scrolls. NEL indexes first, then returns.
    let s = on_grid(b"\x1b[3;1H\n");
    assert_eq!(
        (rows(&s), s.cursor()),
        (
            vec!["ABCDEF".into(), "GHIJKL".into(), "MNOPQR".into()],
            (2, 0)
        )
    );
    let s = on_grid(b"\x1b[3;6H\x1bE");
    assert_eq!(
        s.line_text(0),
        "ABCDEF",
        "NEL from past the margin scrolls nothing"
    );
    assert_eq!(s.cursor(), (2, 1), "and returns to the left margin");
    // RI at the top margin from inside scrolls the rectangle down; from
    // outside it is CUU, which the top margin stops.
    let s = on_grid(b"\x1b[1;2H\x1bM");
    assert_eq!(rows(&s), ["A    F", "GBCDEL", "MHIJKR"]);
    let s = on_grid(b"\x1b[1;6H\x1bM");
    assert_eq!((s.line_text(0), s.cursor()), ("ABCDEF".into(), (0, 5)));
    // SU and SD scroll the rectangle wherever the cursor is, and leave it.
    let s = on_grid(b"\x1b[3;1H\x1b[S");
    assert_eq!(
        (rows(&s), s.cursor()),
        (
            vec!["AHIJKF".into(), "GNOPQL".into(), "M    R".into()],
            (2, 0)
        )
    );
    let s = on_grid(b"\x1b[1;6H\x1b[T");
    assert_eq!(rows(&s), ["A    F", "GBCDEL", "MHIJKR"]);
    // IL and DL inside the margins open or close lines in the rectangle and
    // go to the left margin.
    let s = on_grid(b"\x1b[2;3H\x1b[L");
    assert_eq!(
        (rows(&s), s.cursor()),
        (
            vec!["ABCDEF".into(), "G    L".into(), "MHIJKR".into()],
            (1, 1)
        )
    );
    let s = on_grid(b"\x1b[1;5H\x1b[2M");
    assert_eq!(
        (rows(&s), s.cursor()),
        (
            vec!["ANOPQF".into(), "G    L".into(), "M    R".into()],
            (0, 1)
        )
    );
}

#[test]
fn outside_the_margins_ich_dch_il_and_dl_change_nothing_not_even_the_wrap() {
    // xterm's InsertChar, DeleteChar, InsertLine and DeleteLine all return
    // before `ResetWrap` for a cursor outside the margins.
    for op in [b"\x1b[@".as_slice(), b"\x1b[P", b"\x1b[L", b"\x1b[M"] {
        let s = on_grid(&[b"\x1b[2;6H".as_slice(), op].concat());
        assert_eq!(
            (rows(&s), s.cursor()),
            (
                vec!["ABCDEF".into(), "GHIJKL".into(), "MNOPQR".into()],
                (1, 5)
            ),
            "{op:?} past the right margin"
        );
        let s = on_grid(&[b"\x1b[2;1H".as_slice(), op].concat());
        assert_eq!(s.line_text(1), "GHIJKL", "{op:?} left of the left margin");
        // A wrap pending on the last column, past the right margin, stays:
        // the next glyph wraps onto the left margin of the next row.
        let s = on_grid(&[b"\x1b[1;6HZ".as_slice(), op, b"Y"].concat());
        assert_eq!(
            rows(&s),
            ["ABCDEZ", "GYIJKL", "MNOPQR"],
            "{op:?} kept the wrap"
        );
    }
    // Negative control: inside the margins ICH acts and the wrap resets. `z`
    // parks a wrap on the right margin (column 4), ICH blanks that column,
    // and `Y` lands there instead of wrapping.
    let s = on_grid(b"\x1b[1;2Hwxyz\x1b[@Y");
    assert_eq!(rows(&s), ["AwxyYF", "GHIJKL", "MNOPQR"]);
}

#[test]
fn ich_dch_and_irm_shift_only_up_to_the_right_margin() {
    // Eight columns, margins 3..=6 (0-based (2, 5)).
    let grid = b"ABCDEFGH\x1b[?69h\x1b[3;6s";
    let at = |tail: &[u8]| fold(8, 1, &[grid.as_slice(), tail].concat());
    assert_eq!(at(b"\x1b[1;4H\x1b[2@").line_text(0), "ABC  DGH");
    assert_eq!(at(b"\x1b[1;4H\x1b[2P").line_text(0), "ABCF  GH");
    assert_eq!(at(b"\x1b[1;4H\x1b[9P").line_text(0), "ABC   GH");
    // IRM runs ICH before each glyph (xterm `WriteText`): what passes the
    // right margin is lost, G and H stay, and the line ends at the margin.
    let s = at(b"\x1b[1;4H\x1b[4hXYZ");
    assert_eq!(s.line_text(0), "ABCXYZGH");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 6), true));
    // From past the right margin IRM inserts nothing: the glyph overwrites.
    let s = at(b"\x1b[1;7H\x1b[4hX");
    assert_eq!(s.line_text(0), "ABCDEFXH");
}

#[test]
fn cr_cub_cuf_and_tab_stop_at_the_margins_unless_already_beyond_them() {
    // Twenty columns, margins 6..=15 (0-based (5, 14)).
    let at =
        |tail: &[u8]| fold(20, 1, &[b"\x1b[?69h\x1b[6;15s".as_slice(), tail].concat()).cursor();
    // CR (xterm `CarriageReturn`): the left margin from at or right of it,
    // column 0 from left of it.
    assert_eq!(at(b"\x1b[1;10H\r"), (0, 5));
    assert_eq!(at(b"\x1b[1;18H\r"), (0, 5));
    assert_eq!(at(b"\x1b[1;3H\r"), (0, 0));
    // CUB and BS (`CursorBack`): the left margin unless already left of it.
    assert_eq!(at(b"\x1b[1;10H\x1b[99D"), (0, 5));
    assert_eq!(at(b"\x1b[1;18H\x1b[99D"), (0, 5));
    assert_eq!(at(b"\x1b[1;4H\x1b[99D"), (0, 0));
    assert_eq!(at(b"\x1b[1;6H\x08"), (0, 5));
    // CUF (`CursorForward`): the right margin unless already past it.
    assert_eq!(at(b"\x1b[1;10H\x1b[99C"), (0, 14));
    assert_eq!(at(b"\x1b[1;2H\x1b[99C"), (0, 14));
    assert_eq!(at(b"\x1b[1;17H\x1b[99C"), (0, 19));
    // TAB stops every 8 columns, not past the right margin; past it, at the
    // screen's edge (the fold never tabs backward, as aterm).
    assert_eq!(at(b"\x1b[1;1H\t"), (0, 8));
    assert_eq!(at(b"\x1b[1;1H\t\t"), (0, 14));
    assert_eq!(at(b"\x1b[1;10H\t"), (0, 14));
    assert_eq!(at(b"\x1b[1;17H\t"), (0, 19));
}

#[test]
fn origin_mode_counts_columns_from_the_left_margin() {
    // Rows 2..=5 and columns 3..=8 (1-based) under origin mode: home is (1, 2).
    let set = b"\x1b[2;5r\x1b[?69h\x1b[3;8s\x1b[?6h".to_vec();
    let at = |tail: &[u8]| fold(10, 6, &[set.as_slice(), tail].concat());
    assert_eq!(at(b"").cursor(), (1, 2));
    assert_eq!(at(b"\x1b[1;1HX").cell(1, 2).map(|c| c.ch), Some('X'));
    // CUP stops at the bottom and right margins; the glyph there leaves a
    // wrap pending on the margin.
    let s = at(b"\x1b[99;99HY");
    assert_eq!(s.cell(4, 7).map(|c| c.ch), Some('Y'));
    assert_eq!((s.cursor(), s.wrap_pending()), ((4, 8), true));
    // CHA (xterm `CASE_HPA`) counts from the left margin and keeps the row;
    // VPA keeps the column so counted.
    assert_eq!(at(b"\x1b[3;1H\x1b[3G").cursor(), (3, 4));
    assert_eq!(at(b"\x1b[3;1H\x1b[99G").cursor(), (3, 7));
    assert_eq!(at(b"\x1b[3;4H\x1b[1d").cursor(), (1, 5));
    // CR under origin mode is the left margin; DECSLRM and DECSTBM home to
    // the corner of the margins.
    assert_eq!(at(b"\x1b[2;4H\r").cursor(), (2, 2));
    assert_eq!(at(b"\x1b[4;9s").cursor(), (1, 3));
    assert_eq!(at(b"\x1b[3;4r").cursor(), (2, 2));
    // Resetting origin mode homes to the screen's corner.
    assert_eq!(at(b"\x1b[3;3H\x1b[?6l").cursor(), (0, 0));
}

#[test]
fn decsc_round_trips_a_wrap_pending_on_the_right_margin() {
    // xterm `CursorSave` keeps `do_wrap`, `CursorRestore` puts it back after
    // the `CursorSet`: the next glyph wraps onto the left margin.
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6sabcdef\x1b7\x1b[1;1Hx\x1b8Z");
    assert_eq!(rows(&s), ["xbcdef", "  Z", ""]);
    // So does `?1049`, which saves into the same slot.
    let s = fold(10, 3, b"\x1b[?69h\x1b[3;6sabcdef\x1b[?1049h\x1b[?1049lZ");
    assert_eq!(rows(&s), ["abcdef", "  Z", ""]);
    // Under origin mode a restored column stops at the right margin.
    let s = fold(
        10,
        2,
        b"\x1b[?69h\x1b[1;8s\x1b[?6h\x1b[1;8H\x1b7\x1b[1;4s\x1b8X",
    );
    assert_eq!(s.line_text(0), "   X");
}

#[test]
fn a_tab_carries_a_wrap_left_short_of_the_line_end_to_the_next_stop() {
    // xterm `TabToNextStop` moves the column and never touches `do_wrap`. On
    // the right margin the tab goes nowhere and the wrap stays.
    let s = fold(20, 2, b"\x1b[?69h\x1b[1;3sabc\t");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 3), true));
    // Once DECLRMM is reset the line runs on to the screen's edge: the tab
    // reaches column 8 with the wrap still pending, and the next glyph wraps.
    let s = fold(20, 2, b"\x1b[?69h\x1b[1;3sabc\x1b[?69l\t");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 9), true));
    let s = fold(20, 2, b"\x1b[?69h\x1b[1;3sabc\x1b[?69l\tZ");
    assert_eq!(rows(&s), ["abc", "Z"]);
    // A stop past the last column leaves the wrap on the screen's edge.
    let s = fold(4, 2, b"\x1b[?69h\x1b[1;2sab\x1b[?69l\t");
    assert_eq!((s.cursor(), s.wrap_pending()), ((0, 4), true));
    // Without a pending wrap the same tab is a plain motion (the control).
    let s = fold(20, 2, b"\x1b[?69h\x1b[1;3sab\x1b[?69l\tZ");
    assert_eq!(rows(&s), ["ab      Z", ""]);
}

#[test]
fn a_resize_resets_the_margins_and_keeps_the_mode() {
    let recs = vec![
        Record::Out(b"\x1b[?69h\x1b[3;6s".to_vec()),
        Record::Resize { cols: 12, rows: 3 },
        Record::Out(b"\x1b[1;1Habcdefghij".to_vec()),
    ];
    let s = screen::fold(10, 3, &recs);
    assert_eq!(
        (s.lr_margins(), s.line_text(0)),
        ((0, 11), "abcdefghij".into())
    );
    let mut recs = recs;
    recs.push(Record::Out(b"\x1b[2;4s".to_vec()));
    assert_eq!(
        screen::fold(10, 3, &recs).lr_margins(),
        (1, 3),
        "CSI s is still DECSLRM"
    );
}

#[test]
fn the_serialization_tells_every_margin_state_apart() {
    // Back at the reset values the screen writes the bytes it always did.
    assert_eq!(
        fold(10, 2, b"\x1b[?69h\x1b[?69l").serialize(),
        Screen::new(10, 2).serialize()
    );
    // The mode, the margins and a wrap pending on a margin each change them.
    let plain = fold(10, 2, b"").serialize();
    let mode = fold(10, 2, b"\x1b[?69h").serialize();
    let margins = fold(10, 2, b"\x1b[?69h\x1b[3;6s").serialize();
    assert_ne!(plain, mode);
    assert_ne!(mode, margins);
    let parked = fold(10, 2, b"\x1b[?69h\x1b[1;6sabcdef");
    let standing = fold(10, 2, b"\x1b[?69h\x1b[1;6sabcdef\x1b[1;7H");
    assert_eq!(parked.cursor(), standing.cursor());
    assert_eq!(rows(&parked), rows(&standing));
    assert_ne!(parked.serialize(), standing.serialize());
    assert_ne!(parked, standing);
}

/// One random token of a program that keeps the cursor inside the margins
/// under origin mode: everything but the controls that ignore the margins
/// (ED, EL, ECH), move them (DECSTBM, DECSLRM, DECLRMM, a resize), leave
/// origin mode or restore a cursor.
fn confined_token(st: &mut u64) -> Vec<u8> {
    let n = 1 + below(st, 4);
    match below(st, 16) {
        0..=3 => {
            let len = 1 + below(st, 8);
            (0..len).map(|_| b'a' + below(st, 26) as u8).collect()
        }
        4 => [
            b"\r".as_slice(),
            b"\n",
            b"\x1bD",
            b"\x1bE",
            b"\x1bM",
            b"\x08",
            b"\t",
        ][below(st, 7) as usize]
            .to_vec(),
        5 => format!(
            "\x1b[{n}{}",
            ['A', 'B', 'C', 'D', 'E', 'F'][below(st, 6) as usize]
        )
        .into_bytes(),
        6 | 7 => format!(
            "\x1b[{n}{}",
            ['S', 'T', 'L', 'M', '@', 'P'][below(st, 6) as usize]
        )
        .into_bytes(),
        8 => format!("\x1b[{};{}H", below(st, 9), below(st, 14)).into_bytes(),
        9 => format!("\x1b[{}G", below(st, 14)).into_bytes(),
        10 => format!("\x1b[{}d", below(st, 9)).into_bytes(),
        11 => {
            if below(st, 2) == 0 {
                b"\x1b[4h".to_vec()
            } else {
                b"\x1b[4l".to_vec()
            }
        }
        12 => format!("\x1b[4{}m", below(st, 8)).into_bytes(),
        13 => {
            if below(st, 2) == 0 {
                b"\x1b[20h".to_vec()
            } else {
                b"\x1b[20l".to_vec()
            }
        }
        _ => b"\x1b[0m".to_vec(),
    }
}

/// The marker glyph of cell `(row, col)` before a confined program runs.
fn mark(row: u16, col: u16) -> char {
    char::from(b'A' + ((row * 7 + col) % 26) as u8)
}

#[test]
fn random_confined_programs_never_touch_the_cells_beside_the_margins() {
    // The law: under origin mode inside DECSLRM margins every glyph, scroll,
    // insert and delete stays in the rectangle, so the columns left and right
    // of it keep their markers, and the cursor never leaves the margins (a
    // wrap pending on the right one reads one past it). The negative control
    // runs each program again without the margins: most of them then reach
    // those columns, so the law is not vacuous.
    const COLS: u16 = 12;
    const ROWS: u16 = 6;
    let mut reached = 0u32;
    for seed in 0..300u64 {
        let mut st = seed.wrapping_mul(0x0010_0001).wrapping_add(7);
        let left = 1 + below(&mut st, 5) as u16;
        let right = left + 1 + below(&mut st, u64::from(COLS - left - 2)) as u16;
        let top = below(&mut st, 3) as u16;
        let bottom = top + 1 + below(&mut st, u64::from(ROWS - top - 1)) as u16;
        let mut marked = Vec::new();
        for r in 0..ROWS {
            marked.extend_from_slice(format!("\x1b[{};1H", r + 1).as_bytes());
            marked.extend((0..COLS).map(|c| mark(r, c) as u8));
        }
        marked.extend_from_slice(format!("\x1b[{};{}r", top + 1, bottom + 1).as_bytes());
        let mut body = Vec::new();
        for _ in 0..1 + below(&mut st, 40) {
            body.extend(confined_token(&mut st));
        }
        let margins = format!("\x1b[?69h\x1b[{};{}s\x1b[?6h", left + 1, right + 1);
        let s = fold(
            COLS,
            ROWS,
            &[marked.as_slice(), margins.as_bytes(), &body].concat(),
        );
        assert_eq!(s.lr_margins(), (left, right), "seed {seed}");
        for r in 0..ROWS {
            for c in (0..left).chain(right + 1..COLS) {
                assert_eq!(
                    s.cell(r, c).map(|x| x.ch),
                    Some(mark(r, c)),
                    "seed {seed}: ({r},{c}) beside the margins [{left},{right}] changed"
                );
            }
        }
        let (_, col) = s.cursor();
        assert!(
            (left..=right).contains(&col) || (col == right + 1 && s.wrap_pending()),
            "seed {seed}: the cursor left the margins [{left},{right}] at column {col}"
        );
        let twin = fold(
            COLS,
            ROWS,
            &[marked.as_slice(), b"\x1b[?6h", &body].concat(),
        );
        let touched = (0..ROWS).any(|r| {
            (0..left)
                .chain(right + 1..COLS)
                .any(|c| twin.cell(r, c).map(|x| x.ch) != Some(mark(r, c)))
        });
        reached += u32::from(touched);
    }
    assert!(
        reached >= 200,
        "only {reached} of 300 unmargined twins reached the columns beside the margins"
    );
}

/// One random token of a margin-rich program: any of the controls the fold
/// models around the margins, the ones that move or reset them included.
fn margin_token(st: &mut u64) -> Vec<u8> {
    match below(st, 12) {
        0 => [
            b"\x1b[?69h".as_slice(),
            b"\x1b[?69l",
            b"\x1b[?6h",
            b"\x1b[?6l",
        ][below(st, 4) as usize]
            .to_vec(),
        1 | 2 => format!("\x1b[{};{}s", below(st, 12), below(st, 14)).into_bytes(),
        3 => [
            b"\x1b7".as_slice(),
            b"\x1b8",
            b"\x1b[s",
            b"\x1b[u",
            b"\x1b[?1049h",
            b"\x1b[?1049l",
            b"\x1bc",
        ][below(st, 7) as usize]
            .to_vec(),
        4 => format!("\x1b[{};{}r", below(st, 7), below(st, 8)).into_bytes(),
        5 => format!(
            "\x1b[{}{}",
            below(st, 3),
            ['J', 'K', 'X'][below(st, 3) as usize]
        )
        .into_bytes(),
        _ => confined_token(st),
    }
}

#[test]
fn random_margin_programs_keep_one_spelling_and_a_lossless_projection() {
    // Over margin-rich programs, record by record: the margins stay a valid
    // pair, the cursor reads at most `cols` (and `cols` only with a wrap
    // pending), and the typed ops re-apply to a byte-equal screen. Negative
    // control: the programs do reach a wrap pending on a margin short of the
    // screen's edge, and margins narrower than the screen.
    let mut margin_wraps = 0u32;
    let mut narrowed = 0u32;
    for seed in 0..400u64 {
        let mut st = seed.wrapping_mul(0x0001_0003).wrapping_add(11);
        let (cols, rows) = (2 + below(&mut st, 12) as u16, 1 + below(&mut st, 6) as u16);
        let mut recs = Vec::new();
        for _ in 0..1 + below(&mut st, 8) {
            if below(&mut st, 10) == 0 {
                recs.push(Record::Resize {
                    cols: 2 + below(&mut st, 12) as u16,
                    rows: 1 + below(&mut st, 6) as u16,
                });
                continue;
            }
            let mut bytes = Vec::new();
            for _ in 0..1 + below(&mut st, 8) {
                bytes.extend(margin_token(&mut st));
            }
            recs.push(Record::Out(bytes));
        }
        let mut folder = Folder::new(cols, rows);
        for rec in &recs {
            folder.apply(rec);
            let s = folder.screen();
            let (c, _) = s.dims();
            let (left, right) = s.lr_margins();
            assert!(
                left <= right && right < c,
                "seed {seed}: margins ({left},{right}) on {c} columns"
            );
            let (_, col) = s.cursor();
            assert!(col <= c, "seed {seed}: cursor column {col} past {c}");
            assert!(
                col < c || s.wrap_pending(),
                "seed {seed}: column {c} without a pending wrap"
            );
            margin_wraps += u32::from(s.wrap_pending() && col < c);
            narrowed += u32::from(right - left + 1 < c);
        }
        let ops = screen::emit_ops(cols, rows, &recs);
        assert_eq!(
            screen::apply_ops(cols, rows, &ops).serialize(),
            folder.screen().serialize(),
            "seed {seed}: the ops re-apply to the fold"
        );
    }
    assert!(
        margin_wraps > 0,
        "no program reached a wrap pending on a margin"
    );
    assert!(narrowed > 0, "no program narrowed the margins");
}

#[test]
fn decslrm_is_its_own_op_and_re_applies() {
    let recs = out(b"\x1b[?69h\x1b[3;6s\x1b[?6h\x1b[1;1Habcdefg\x1b[4;4s\x1b[2;9s");
    let ops = screen::emit_ops(10, 3, &recs);
    let set: Vec<&ScreenOp> = ops
        .iter()
        .filter(|o| matches!(o, ScreenOp::SetLeftRightMargins { .. }))
        .collect();
    // The empty pair records nothing: it changed nothing.
    assert_eq!(
        set,
        [
            &ScreenOp::SetLeftRightMargins { left: 2, right: 5 },
            &ScreenOp::SetLeftRightMargins { left: 1, right: 8 },
        ]
    );
    assert_eq!(
        screen::apply_ops(10, 3, &ops).serialize(),
        screen::fold(10, 3, &recs).serialize()
    );
}
