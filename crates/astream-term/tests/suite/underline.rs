// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `term.fold.underline`: the fold keeps the underline's style and
//! colour on every cell and on the pen, as kitty, VTE and aterm keep them.
//!
//! 4 is a single underline and 21 a double one; `4:0` to `4:5` name none, single,
//! double, curly, dotted and dashed, `4:n` past 5 a single one (aterm's choice), and
//! 24 takes it off. 58 sets the colour in each spelling 38 takes and 59 takes it off;
//! SGR 0 resets both. DECSC saves them, a bce blank carries neither, the encodings
//! tell every style and colour apart while a screen whose underlines are single and
//! uncoloured keeps its bytes, and the typed screen-op projection stays lossless. Each
//! answer is written out by hand, and the negative controls show a fold that drops
//! 58's colour, or knows one underline style, fails them. Cross-validated out of tree
//! against the production aterm engine by aterm's differential VT oracle, which this
//! module does not run.

use astream_term::screen::{self, Cell, Color, Screen, Underline, WIRE_UNDERLINE};
use astream_term::{apply_ops, decode_ops, emit_ops, encode_ops, Record};

fn fold(cols: u16, rows: u16, bytes: &[u8]) -> Screen {
    screen::fold(cols, rows, &[Record::Out(bytes.to_vec())])
}

/// A cell's underline: its style, its palette colour and its 24-bit colour.
type Drawn = (Underline, Color, Option<(u8, u8, u8)>);

fn drawn(c: &Cell) -> Drawn {
    (c.underline, c.ul, c.ul_rgb)
}

const NONE: Drawn = (Underline::None, Color::Default, None);

/// Each program's first cell, written out by hand.
const ANSWERS: &[(&[u8], Drawn)] = &[
    (b"\x1b[4mX", (Underline::Single, Color::Default, None)),
    (b"\x1b[21mX", (Underline::Double, Color::Default, None)),
    (b"\x1b[4:0mX", NONE),
    (b"\x1b[4:1mX", (Underline::Single, Color::Default, None)),
    (b"\x1b[4:2mX", (Underline::Double, Color::Default, None)),
    (b"\x1b[4:3mX", (Underline::Curly, Color::Default, None)),
    (b"\x1b[4:4mX", (Underline::Dotted, Color::Default, None)),
    (b"\x1b[4:5mX", (Underline::Dashed, Color::Default, None)),
    (b"\x1b[4:9mX", (Underline::Single, Color::Default, None)),
    // A trailing colon is an empty element, 0.
    (b"\x1b[4:3m\x1b[4:mX", NONE),
    // What follows the style is nothing.
    (b"\x1b[4:3:9mX", (Underline::Curly, Color::Default, None)),
    (b"\x1b[4:5m\x1b[24mX", NONE),
    (
        b"\x1b[21m\x1b[4mX",
        (Underline::Single, Color::Default, None),
    ),
    (
        b"\x1b[4:4m\x1b[21mX",
        (Underline::Double, Color::Default, None),
    ),
    // 58 in every spelling 38 takes, over no underline (the colour rides without one).
    (b"\x1b[58;5;9mX", (Underline::None, Color::Indexed(9), None)),
    (b"\x1b[58:5:9mX", (Underline::None, Color::Indexed(9), None)),
    (b"\x1b[58;5:9mX", (Underline::None, Color::Indexed(9), None)),
    (
        b"\x1b[58;2;10;20;9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58:2::10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58:2:3:10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58:2:10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58;2:3:10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58;2::10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58;2:10:20:9mX",
        (Underline::None, Color::Default, Some((10, 20, 9))),
    ),
    (
        b"\x1b[58;2;10;300;9mX",
        (Underline::None, Color::Default, Some((10, 255, 9))),
    ),
    // The curly underline in 24-bit colour, as an editor draws a diagnostic.
    (
        b"\x1b[4:3;58:2::255:0:0mX",
        (Underline::Curly, Color::Default, Some((255, 0, 0))),
    ),
    // A palette colour replaces a 24-bit one and the other way about.
    (
        b"\x1b[58;2;1;2;3;58;5;7mX",
        (Underline::None, Color::Indexed(7), None),
    ),
    (
        b"\x1b[58;5;7;58;2;1;2;3mX",
        (Underline::None, Color::Default, Some((1, 2, 3))),
    ),
    // 59 takes the colour off and leaves the style; 24 and `4:0` leave the colour.
    (
        b"\x1b[4:3;58;5;5m\x1b[59mX",
        (Underline::Curly, Color::Default, None),
    ),
    (
        b"\x1b[4:3;58;5;5m\x1b[24mX",
        (Underline::None, Color::Indexed(5), None),
    ),
    (
        b"\x1b[4:3;58;5;5m\x1b[4:0mX",
        (Underline::None, Color::Indexed(5), None),
    ),
    // SGR 0, spelled out or empty, resets both.
    (b"\x1b[4:3;58;5;5m\x1b[0mX", NONE),
    (b"\x1b[4:3;58;5;5m\x1b[mX", NONE),
    (b"\x1b[4:3;58:2::1:2:3m\x1b[1;0mX", NONE),
    // A spelling that names nothing leaves the colour as it was.
    (
        b"\x1b[4;58;5;5m\x1b[58;3;1;2;3mX",
        (Underline::Single, Color::Indexed(5), None),
    ),
    (
        b"\x1b[4;58;5;5m\x1b[58:2:1:2mX",
        (Underline::Single, Color::Indexed(5), None),
    ),
    (
        b"\x1b[4;58;5;5m\x1b[58;0mX",
        (Underline::Single, Color::Indexed(5), None),
    ),
    // Other codes leave both alone.
    (
        b"\x1b[4:4;58;5;5m\x1b[1;7;22;27;31;44;39;49mX",
        (Underline::Dotted, Color::Indexed(5), None),
    ),
    // DECSC saves both; DECRC brings them back; a slot never saved resets them.
    (
        b"\x1b[4:5;58;5;6m\x1b7\x1b[0m\x1b8X",
        (Underline::Dashed, Color::Indexed(6), None),
    ),
    (b"\x1b[4:5;58;5;6m\x1b8X", NONE),
];

/// What `fold` gets wrong: each row of [`ANSWERS`], the bce blank an erase makes, and the
/// halves of a wide glyph. Empty when `fold` holds the claim.
fn wrong_answers(fold: &dyn Fn(&[u8]) -> Screen) -> Vec<String> {
    let mut wrong = Vec::new();
    for &(bytes, want) in ANSWERS {
        let got = fold(bytes).cell(0, 0).map(drawn);
        if got != Some(want) {
            wrong.push(format!(
                "{}: {got:?}, not {want:?}",
                String::from_utf8_lossy(bytes).escape_debug()
            ));
        }
    }
    // An erase makes the bce blank, which carries the background and no underline.
    let s = fold(b"\x1b[44;4:3;58;5;5mab\x1b[1G\x1b[K");
    if s.cell(0, 0).map(drawn) != Some(NONE) {
        wrong.push(format!(
            "the bce blank carries an underline: {:?}",
            s.cell(0, 0)
        ));
    }
    // A wide glyph's spacer carries its lead's underline.
    let s = fold("\x1b[4:2;58;5;3m\u{4e2d}".as_bytes());
    let lead = s.cell(0, 0).map(drawn);
    if lead != Some((Underline::Double, Color::Indexed(3), None)) || s.cell(0, 1).map(drawn) != lead
    {
        wrong.push(format!(
            "a wide glyph's halves: {lead:?} and {:?}",
            s.cell(0, 1).map(drawn)
        ));
    }
    wrong
}

fn real_fold(bytes: &[u8]) -> Screen {
    let whole = fold(8, 2, bytes);
    let mut step = screen::Folder::new(8, 2);
    for b in bytes {
        step.apply(&Record::Out(vec![*b]));
    }
    // The fold is one function of the bytes, however they are cut.
    assert_eq!(
        whole.serialize(),
        step.screen().serialize(),
        "{} fed whole and a byte at a time",
        String::from_utf8_lossy(bytes).escape_debug()
    );
    whole
}

#[test]
fn every_underline_program_draws_its_written_answer() {
    let wrong = wrong_answers(&real_fold);
    assert!(
        wrong.is_empty(),
        "{} wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Negative control: a fold that drops 58's colour (every cell's underline colour back to
/// the default) fails the written answers, at every row that names a colour.
#[test]
fn a_fold_that_drops_the_underline_colour_fails_the_answers() {
    let dropping = |bytes: &[u8]| {
        let mut s = fold(8, 2, bytes);
        let (cols, rows) = s.dims();
        for r in 0..rows {
            for c in 0..cols {
                if let Some(&cell) = s.cell(r, c) {
                    s.set_cell(
                        r,
                        c,
                        Cell {
                            ul: Color::Default,
                            ul_rgb: None,
                            ..cell
                        },
                    );
                }
            }
        }
        s
    };
    let coloured = ANSWERS
        .iter()
        .filter(|(_, (_, ul, rgb))| *ul != Color::Default || rgb.is_some())
        .count();
    let wrong = wrong_answers(&dropping);
    assert!(coloured > 0, "the answers name no colour");
    // Each coloured row, and the wide glyph's halves.
    assert_eq!(wrong.len(), coloured + 1, "{wrong:#?}");
}

/// Negative control: a fold that knows one underline style (the fold before this claim:
/// every style a single line) fails the written answers too.
#[test]
fn a_fold_with_one_underline_style_fails_the_answers() {
    let single = |bytes: &[u8]| {
        let mut s = fold(8, 2, bytes);
        let (cols, rows) = s.dims();
        for r in 0..rows {
            for c in 0..cols {
                if let Some(&cell) = s.cell(r, c) {
                    if cell.underline != Underline::None {
                        s.set_cell(
                            r,
                            c,
                            Cell {
                                underline: Underline::Single,
                                ..cell
                            },
                        );
                    }
                }
            }
        }
        s
    };
    let styled = ANSWERS
        .iter()
        .filter(|(_, (style, ..))| !matches!(style, Underline::None | Underline::Single))
        .count();
    assert_eq!(wrong_answers(&single).len(), styled + 1);
}

/// Screens that differ only in their underline serialize apart, a caller's `attrs` that holds
/// the wire's underline bit included; one whose underlines are single and uncoloured writes
/// no trailer for them, so it keeps the bytes it had when the fold knew one underline.
#[test]
fn the_encoding_tells_every_underline_apart_and_keeps_a_plain_one_s_bytes() {
    let styles = [
        Underline::None,
        Underline::Single,
        Underline::Double,
        Underline::Curly,
        Underline::Dotted,
        Underline::Dashed,
    ];
    let colours = [
        (Color::Default, None),
        (Color::Indexed(0), None),
        (Color::Indexed(9), None),
        (Color::Default, Some((0, 0, 0))),
        (Color::Default, Some((9, 8, 7))),
        // A caller's cell can hold both; it is still its own.
        (Color::Indexed(9), Some((9, 8, 7))),
    ];
    let mut seen = std::collections::BTreeMap::new();
    for attrs in [0, WIRE_UNDERLINE] {
        for style in styles {
            for (ul, ul_rgb) in colours {
                let mut s = Screen::new(2, 1);
                s.set_cell(
                    0,
                    1,
                    Cell {
                        ch: 'u',
                        attrs,
                        underline: style,
                        ul,
                        ul_rgb,
                        ..Cell::BLANK
                    },
                );
                let key = (attrs, style, ul, ul_rgb);
                if let Some(other) = seen.insert(s.serialize(), key) {
                    panic!("{key:?} serializes as {other:?} does");
                }
            }
        }
    }
    assert_eq!(seen.len(), 2 * styles.len() * colours.len());

    // A plain underline is its attribute byte's bit and nothing more: the screen is as
    // long as one with no underline, and differs from it in that one byte.
    let plain = fold(4, 1, b"\x1b[4mX\x1b[1mY").serialize();
    let none = fold(4, 1, b"X\x1b[1mY").serialize();
    assert_eq!(plain.len(), none.len());
    let differ: Vec<u8> = plain
        .iter()
        .zip(&none)
        .filter(|(a, b)| a != b)
        .map(|(a, b)| a ^ b)
        .collect();
    // The two cells and the pen.
    assert_eq!(differ, [WIRE_UNDERLINE; 3]);
    // A style or a colour adds the trailer.
    assert!(fold(4, 1, b"\x1b[4:3mX").serialize().len() > plain.len());
    assert!(fold(4, 1, b"\x1b[4;58;5;1mX").serialize().len() > plain.len());
}

/// splitmix64: the same programs on every host.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A program of underline SGRs in every spelling, mixed with text, wide glyphs, erases,
/// DECSC/DECRC and the alternate screen.
fn program(r: &mut Rng) -> Vec<u8> {
    let mut out = Vec::new();
    for _ in 0..(4 + r.below(28)) {
        let piece = match r.below(16) {
            0 => format!("\x1b[4:{}m", r.below(7)),
            1 => [
                "\x1b[4m", "\x1b[21m", "\x1b[24m", "\x1b[59m", "\x1b[0m", "\x1b[m",
            ][r.below(6) as usize]
                .to_string(),
            2 => format!("\x1b[58;5;{}m", r.below(256)),
            3 => format!(
                "\x1b[{}{}m",
                ["58:5:", "58;5:"][r.below(2) as usize],
                r.below(256)
            ),
            4 => format!(
                "\x1b[58;2;{};{};{}m",
                r.below(300),
                r.below(256),
                r.below(256)
            ),
            // The colon groups, on the code or on the selector, with an empty colour-space
            // id, a colour-space id or none.
            5 => format!(
                "\x1b[{}{}:{}:{}m",
                ["58:2::", "58;2::", "58:2:1:", "58;2:2:", "58:2:", "58;2:"][r.below(6) as usize],
                r.below(256),
                r.below(256),
                r.below(256)
            ),
            6 => format!(
                "\x1b[4:{};58:2:{}:{}:{}:{}m",
                r.below(6),
                r.below(3),
                r.below(256),
                r.below(256),
                r.below(256)
            ),
            7 => ["\x1b7", "\x1b8", "\x1b[?1049h", "\x1b[?1049l"][r.below(4) as usize].to_string(),
            8 => [
                "\x1b[K", "\x1b[2J", "\x1b[1G", "\x1b[2X", "\x1b[@", "\x1b[P",
            ][r.below(6) as usize]
                .to_string(),
            9 => "\u{4e2d}".to_string(),
            10 => "\r\n".to_string(),
            _ => ["a", "bc", "def", "x "][r.below(4) as usize].to_string(),
        };
        out.extend_from_slice(piece.as_bytes());
    }
    out
}

/// The typed screen-op projection stays lossless for the underline: over 400 random
/// programs, the ops (through the wire codec) re-apply to the fold's screen byte for byte,
/// and the programs reach every style and both kinds of colour on a cell, and a DECSC slot
/// that saved a style past single and one that saved a colour, read back by DECRC onto a
/// glyph (negative control: the law is not about screens that never hold an underline).
#[test]
fn random_underline_programs_project_losslessly() {
    let mut r = Rng(0x0E10_5EED);
    let mut reached = std::collections::BTreeSet::new();
    for n in 0..400 {
        let bytes = program(&mut r);
        let recs = [Record::Out(bytes.clone())];
        let folded = screen::fold(12, 4, &recs);
        let ops = emit_ops(12, 4, &recs);
        let wire = decode_ops(&encode_ops(&ops).expect("encodes")).expect("decodes");
        assert_eq!(wire, ops, "program {n}");
        assert_eq!(
            apply_ops(12, 4, &ops).serialize(),
            folded.serialize(),
            "program {n}: {}",
            String::from_utf8_lossy(&bytes).escape_debug()
        );
        for row in 0..4 {
            for col in 0..12 {
                if let Some(c) = folded.cell(row, col) {
                    reached.insert(format!("{:?}", c.underline));
                    if c.ul != Color::Default {
                        reached.insert("palette".to_string());
                    }
                    if c.ul_rgb.is_some() {
                        reached.insert("rgb".to_string());
                    }
                }
            }
        }
        // The pen the program left in the current buffer's DECSC slot: DECRC brings it
        // back (a slot never saved resets it), and the next glyph takes it.
        let mut saved = screen::Folder::new(12, 4);
        saved.apply(&Record::Out([bytes.as_slice(), b"\x1b8"].concat()));
        let (row, col) = saved.screen().cursor();
        if !saved.screen().wrap_pending() {
            saved.apply(&Record::Out(b"X".to_vec()));
            if let Some(c) = saved.screen().cell(row, col) {
                if !matches!(c.underline, Underline::None | Underline::Single) {
                    reached.insert("saved style".to_string());
                }
                if c.ul != Color::Default || c.ul_rgb.is_some() {
                    reached.insert("saved colour".to_string());
                }
            }
        }
    }
    for want in [
        "None",
        "Single",
        "Double",
        "Curly",
        "Dotted",
        "Dashed",
        "palette",
        "rgb",
        "saved style",
        "saved colour",
    ] {
        assert!(
            reached.contains(want),
            "no program reached {want}: {reached:?}"
        );
    }
}
