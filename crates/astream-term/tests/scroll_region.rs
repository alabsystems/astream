//! Evidence for `term.fold.scroll-region`: the fold honours `DECSTBM` (the DEC
//! scrolling region) — text scrolls WITHIN the region while rows outside it are
//! untouched — and the typed screen-op projection of a scroll-region session
//! stays lossless. This closes the biggest text-visible gap vs a full terminal.
//!
//! Cross-validated OUT OF TREE against the real production aterm engine
//! (the aterm repo's `astream-oracle`, `cargo test --manifest-path
//! astream-oracle/Cargo.toml --test scroll_region`): the same DECSTBM fixtures +
//! 300 random region programs agree byte-for-byte. That manual oracle is the
//! deepest check; the assertions below — including a dep-free 300-program
//! region-invariant generator — are the in-tree restatement `make ci` enforces,
//! so a `screen.rs` edit that scrolls outside the region fails the gate.

use astream_term::{screen, Record};

fn out(b: &[u8]) -> Vec<Record> {
    vec![Record::Out(b.to_vec())]
}

/// A dep-free splitmix64 PRNG so the in-tree breadth check is reproducible.
fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

#[test]
fn decstbm_scrolls_within_the_region_only() {
    // Region = rows 2..=4 (1-based) = 0-based 1..=3. Home there, write 5 lines.
    let s = screen::fold(10, 6, &out(b"\x1b[2;4r\x1b[2;1HA\r\nB\r\nC\r\nD\r\nE"));
    // A and B scrolled off the top of the region; C, D, E remain in rows 1..=3.
    assert_eq!(s.line_text(0), "", "the row above the region is untouched");
    assert_eq!(s.line_text(1), "C");
    assert_eq!(s.line_text(2), "D");
    assert_eq!(s.line_text(3), "E");
    assert_eq!(s.line_text(4), "", "the row below the region is untouched");
    assert_eq!(s.line_text(5), "");
}

#[test]
fn rows_outside_the_region_are_never_scrolled() {
    // Mark the last row, set a region above it, then scroll hard inside it.
    let s = screen::fold(
        10,
        6,
        &out(b"\x1b[6;1HKEEP\x1b[1;3r\x1b[1;1H1\r\n2\r\n3\r\n4\r\n5"),
    );
    assert_eq!(
        s.line_text(5),
        "KEEP",
        "a row below the region is never scrolled"
    );
}

#[test]
fn bare_decstbm_resets_to_full_screen() {
    // Set a region, then `CSI r` resets to full; a full-screen scroll follows.
    let s = screen::fold(10, 3, &out(b"\x1b[1;2r\x1b[rA\r\nB\r\nC\r\nD"));
    assert_eq!(s.line_text(0), "B");
    assert_eq!(s.line_text(1), "C");
    assert_eq!(s.line_text(2), "D");
}

#[test]
fn a_resize_invalidates_the_region() {
    // Mark the top row, set region rows 2..=4, then GROW the screen: the region
    // must reset to the full new screen, so a line feed from the new last row
    // scrolls the whole screen (the top row is lost). A stale region would leave
    // the last row outside it and the line feed a no-op.
    let recs = vec![
        Record::Out(b"TOP\x1b[2;4r".to_vec()),
        Record::Resize { cols: 10, rows: 8 },
        Record::Out(b"\x1b[8;1HX\r\nY".to_vec()),
    ];
    let s = screen::fold(10, 6, &recs);
    assert_eq!(
        s.line_text(0),
        "",
        "the top row scrolled off: full-screen region"
    );
    assert_eq!(s.line_text(6), "X");
    assert_eq!(s.line_text(7), "Y");
    // SHRINK below the old region bottom: no region may outlive the last row —
    // a line feed from the new last row still scrolls the whole screen.
    let recs = vec![
        Record::Out(b"TOP\x1b[2;5r".to_vec()),
        Record::Resize { cols: 10, rows: 3 },
        Record::Out(b"\x1b[3;1HX\r\nY".to_vec()),
    ];
    let s = screen::fold(10, 6, &recs);
    assert_eq!(s.line_text(0), "");
    assert_eq!(s.line_text(1), "X");
    assert_eq!(s.line_text(2), "Y");
}

#[test]
fn screen_ops_projection_stays_lossless_through_a_scroll_region() {
    // The new SetScrollRegion op must keep emit_ops/apply_ops a lossless projection.
    let recs = out(b"\x1b[2;4r\x1b[2;1HX\r\nY\r\nZ\r\nW\r\nV\x1b[6;1Hbot");
    let (cols, rows) = (10u16, 6u16);
    let folded = screen::fold(cols, rows, &recs);
    let ops = screen::emit_ops(cols, rows, &recs);
    let replayed = screen::apply_ops(cols, rows, &ops);
    assert_eq!(
        folded.serialize(),
        replayed.serialize(),
        "the SetScrollRegion op re-applies losslessly"
    );
}

#[test]
fn random_region_programs_scroll_only_inside_the_region() {
    // The in-tree breadth check (no aterm): over 300 random DECSTBM programs, rows
    // OUTSIDE the region are never modified, and the region's top row scrolls off by
    // exactly the scroll count. A `screen.rs` edit that scrolls the full screen
    // (ignoring the margins) fails this under `make ci`.
    const COLS: u16 = 20;
    const ROWS: u16 = 8;
    for seed in 0..300u64 {
        let mut st = seed.wrapping_mul(0x0010_0001).wrapping_add(1);
        let top = 1 + (next(&mut st) % (ROWS as u64 - 2)) as u16; // 1..=ROWS-2
        let bottom =
            (top + 1 + (next(&mut st) % (ROWS as u64 - top as u64 - 1)) as u16).min(ROWS - 1);

        // Mark every row with a distinct glyph BEFORE setting the region.
        let mut prog = Vec::new();
        for r in 0..ROWS {
            prog.extend_from_slice(format!("\x1b[{};1H", r + 1).as_bytes());
            prog.push(b'A' + r as u8);
        }
        // Set the region (1-based), drop to its bottom, and line-feed N times.
        prog.extend_from_slice(format!("\x1b[{};{}r", top + 1, bottom + 1).as_bytes());
        prog.extend_from_slice(format!("\x1b[{};1H", bottom + 1).as_bytes());
        let scrolls = 1 + (next(&mut st) % 4) as u16;
        for _ in 0..scrolls {
            prog.extend_from_slice(b"\r\n");
        }

        let s = screen::fold(COLS, ROWS, &out(&prog));
        for r in 0..ROWS {
            let original = ((b'A' + r as u8) as char).to_string();
            if r < top || r > bottom {
                assert_eq!(
                    s.line_text(r),
                    original,
                    "seed {seed}: row {r} OUTSIDE region [{top},{bottom}] was modified"
                );
            }
        }
        // The region's first scrolled-off marker (its original top row) is gone,
        // and the row that was `top + scrolls` has shifted up to `top` (or the
        // region scrolled past it -> blank), proving real in-region movement.
        if (top + scrolls) <= bottom {
            let shifted = ((b'A' + (top + scrolls) as u8) as char).to_string();
            assert_eq!(
                s.line_text(top),
                shifted,
                "seed {seed}: region content did not shift up by {scrolls}"
            );
        }
    }
}

#[test]
fn an_out_of_range_bottom_margin_clamps_to_the_last_row() {
    // xterm CASE_DECSTBM (and aterm): a bottom past the screen is the last row,
    // not an invalid region. `CSI 2;99 r` on 4 rows is the region rows 2..=4, so
    // the top row survives the scroll below.
    let s = screen::fold(10, 4, &out(b"TOP\x1b[2;99r\x1b[4;1HA\r\nB\r\nC"));
    assert_eq!(
        s.line_text(0),
        "TOP",
        "the row above the region is untouched"
    );
    assert_eq!(s.line_text(1), "A");
    assert_eq!(s.line_text(2), "B");
    assert_eq!(s.line_text(3), "C");
}

#[test]
fn an_empty_region_is_ignored_entirely() {
    // xterm/aterm guard both the margins and the cursor home behind `bot > top`:
    // `CSI 3;3 r` changes nothing -- the earlier region and the cursor stay.
    let s = screen::fold(10, 5, &out(b"\x1b[2;3r\x1b[5;5H\x1b[3;3rX"));
    assert_eq!(s.cursor(), (4, 5), "the cursor was not homed");
    assert_eq!(s.line_text(4), "    X");
    // The region [2,3] (1-based) is still in force: a scroll inside it leaves
    // the rows outside it alone.
    let s = screen::fold(10, 5, &out(b"TOP\x1b[2;3r\x1b[3;3r\x1b[3;1HA\r\nB"));
    assert_eq!(s.line_text(0), "TOP");
    assert_eq!(s.line_text(1), "A");
    assert_eq!(s.line_text(2), "B");
}

#[test]
fn cursor_up_and_down_stop_at_the_margins() {
    // xterm CursorDown/CursorUp: from inside (or above) the region, CUD stops at
    // the bottom margin; from inside (or below) it, CUU stops at the top margin.
    // A status line below the region is never overwritten by `CSI 99 B`.
    let s = screen::fold(10, 5, &out(b"\x1b[5;1HSTATUS\x1b[1;4r\x1b[2;1H\x1b[99BX"));
    assert_eq!(s.line_text(3), "X", "CUD stopped at the bottom margin");
    assert_eq!(
        s.line_text(4),
        "STATUS",
        "the row below the region is intact"
    );
    // CUU from below the region stops at its top margin, not row 0.
    let s = screen::fold(10, 5, &out(b"\x1b[2;4r\x1b[5;1H\x1b[99AX"));
    assert_eq!(s.cursor(), (1, 1));
    // Past the far margin the whole screen is reachable: CUD from below the
    // region goes to the last row, CUU from above it to row 0.
    let s = screen::fold(10, 6, &out(b"\x1b[2;4r\x1b[5;1H\x1b[99B"));
    assert_eq!(s.cursor(), (5, 0));
    let s = screen::fold(10, 6, &out(b"\x1b[3;5r\x1b[2;1H\x1b[99A"));
    assert_eq!(s.cursor(), (0, 0));
    // CNL/CPL move like CUD/CUU.
    let s = screen::fold(10, 5, &out(b"\x1b[1;3r\x1b[1;4H\x1b[9E"));
    assert_eq!(s.cursor(), (2, 0));
    let s = screen::fold(10, 5, &out(b"\x1b[3;4r\x1b[4;4H\x1b[9F"));
    assert_eq!(s.cursor(), (2, 0));
}
