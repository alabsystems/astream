//! Evidence for `term.fold.bce`: `ED`/`EL` erase with the CURRENT SGR background
//! (background-colour-erase), not a hardcoded default blank — and the typed
//! screen-op projection stays lossless. Cross-validated STRUCTURALLY against the
//! production aterm engine (the aterm repo's `astream-oracle/tests/bce.rs`): each engine sources the
//! erased cell's background from the same SGR pen relative to its own default
//! (the two engines' named-ANSI RGB tables deliberately differ, so RGB-equality is
//! NOT asserted).

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
