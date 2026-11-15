//! Evidence for `term.fold.bce`: every blank the fold makes (`ED`/`EL`, a line
//! scrolled in, the alternate-screen clears) takes the CURRENT SGR background
//! (background-colour-erase), not a hardcoded default blank — and the typed
//! screen-op projection stays lossless. Cross-validated against the production
//! aterm engine by aterm's differential VT oracle (aterm-conformance
//! `tests/vt_oracle`), which compares palette indices, never RGB triples (the
//! two engines' named-ANSI RGB tables deliberately differ).

use astream_term::{screen, Color, Record};

fn out(b: &[u8]) -> Vec<Record> {
    vec![Record::Out(b.to_vec())]
}

#[test]
fn ed_erases_the_display_with_the_current_background() {
    // \x1b[44m sets bg = blue(4); \x1b[2J erases the whole display with it.
    let s = screen::fold(8, 3, &out(b"\x1b[44m\x1b[2J"));
    for r in 0..3 {
        for c in 0..8 {
            assert_eq!(
                s.cell(r, c).unwrap().bg,
                Color::Indexed(4),
                "erased cell ({r},{c}) carries the SGR background"
            );
        }
    }
}

#[test]
fn a_default_erase_is_still_a_default_blank() {
    let s = screen::fold(8, 2, &out(b"hi\x1b[2J"));
    assert_eq!(s.cell(0, 0).unwrap().bg, Color::Default);
}

#[test]
fn el_erases_only_its_line_with_the_current_background() {
    // Two lines, then home, set red bg, erase line 0 to end.
    let s = screen::fold(8, 2, &out(b"AB\r\nCD\x1b[1;1H\x1b[41m\x1b[K"));
    assert_eq!(
        s.cell(0, 0).unwrap().bg,
        Color::Indexed(1),
        "line 0 erased with red"
    );
    assert_eq!(s.cell(1, 0).unwrap().bg, Color::Default, "line 1 untouched");
    assert_eq!(s.cell(1, 0).unwrap().ch, 'C', "line 1 content kept");
}

#[test]
fn screen_ops_projection_stays_lossless_through_bce() {
    // The erase op reproduces the resolved bg because the SetSgr op precedes it.
    let recs = out(b"\x1b[42mhi\x1b[2J\x1b[0mok\x1b[44m\x1b[K");
    let (cols, rows) = (10u16, 3u16);
    let folded = screen::fold(cols, rows, &recs);
    let ops = screen::emit_ops(cols, rows, &recs);
    let replayed = screen::apply_ops(cols, rows, &ops);
    assert_eq!(
        folded.serialize(),
        replayed.serialize(),
        "bce erase re-applies losslessly"
    );
}

#[test]
fn a_line_scrolled_in_takes_the_current_background() {
    // xterm's ScrnClearLines fills a new line with the current colour pair: a
    // full-screen scroll and a scroll inside a DECSTBM region both paint it.
    let s = screen::fold(4, 2, &out(b"a\r\nb\x1b[44m\r\nc"));
    assert_eq!(s.line_text(0), "b");
    assert_eq!(s.cell(1, 3).unwrap().bg, Color::Indexed(4), "the new line");
    assert_eq!(
        s.cell(0, 3).unwrap().bg,
        Color::Default,
        "the line scrolled up keeps its own"
    );
    let s = screen::fold(4, 4, &out(b"\x1b[2;3r\x1b[3;1H\x1b[42m\n"));
    assert_eq!(
        s.cell(2, 0).unwrap().bg,
        Color::Indexed(2),
        "inside the region"
    );
    assert_eq!(
        s.cell(3, 0).unwrap().bg,
        Color::Default,
        "below it, untouched"
    );
}

#[test]
fn the_alternate_screen_clears_take_the_current_background() {
    // `?1049h` ends in xterm's ClearScreen, as does `?1047l` before it leaves.
    let s = screen::fold(4, 2, &out(b"\x1b[45m\x1b[?1049h"));
    assert_eq!(s.cell(1, 3).unwrap().bg, Color::Indexed(5));
    let s = screen::fold(4, 2, &out(b"\x1b[?1047hX\x1b[46m\x1b[?1047l\x1b[?47h"));
    assert_eq!(s.line_text(0), "", "1047 cleared the buffer on the way out");
    assert_eq!(s.cell(0, 0).unwrap().bg, Color::Indexed(6));
}
