//! Evidence for `term.perceive.query`: an orchestrator reads any child terminal
//! as text + structured query, reconstructed from the recorded Out log at any
//! offset. Text/blocks/search agree with the folded screen at every offset; the
//! reads are deterministic and panic-free on arbitrary bytes (proptest).

use astream_term::perceive::{blocks, frame, search, text, Block, Hit};
use astream_term::{screen, Record};
use proptest::prelude::*;

const COLS: u16 = 40;
const ROWS: u16 = 6;

fn out(s: &[u8]) -> Record {
    Record::Out(s.to_vec())
}

/// A session that evolves over several offsets so "query at offset K" is real.
fn session() -> Vec<Record> {
    vec![
        out(b"\x1b[2J$ make\r\n"),          // offset 0
        out(b"BUILD FAILED: 2 errors\r\n"), // offset 1
        out(b"\r\n$ echo retry error\r\n"), // offset 2 (blank line, then prompt)
        out(b"retry error\r\n"),            // offset 3
    ]
}

#[test]
fn query_reconstructs_the_screen_at_every_offset() {
    let recs = session();

    for k in 0..recs.len() {
        // `frame(K)` is exactly the fold of the first K+1 records — the screen as
        // of that offset, the basis of every read.
        let f = frame(COLS, ROWS, &recs, k);
        let direct = screen::fold(COLS, ROWS, &recs[..=k]);
        assert_eq!(f.serialize(), direct.serialize(), "frame(K) == fold(0..=K)");

        // text() == the per-row line text of that screen.
        let t = text(&f);
        assert_eq!(t.len(), ROWS as usize);
        assert_eq!(t[0], f.line_text(0));
    }

    // At the final offset: text content, search hits, and blocks are exact.
    let f = frame(COLS, ROWS, &recs, recs.len() - 1);
    let lines = text(&f);
    assert_eq!(lines[0], "$ make");
    assert_eq!(lines[1], "BUILD FAILED: 2 errors");

    // "error" appears on the "echo retry error" line and the "retry error" line.
    let hits = search(&f, "error");
    assert!(hits.len() >= 2, "found {hits:?}");
    assert!(hits.iter().all(|h| lines[h.row as usize].contains("error")));

    // Blocks partition exactly the non-empty rows: rows 0-1 ("$ make", "BUILD
    // FAILED"), an empty row 2, then rows 3-4 — the exact Block list, bounds and
    // lines included (a one-block-per-row or mis-bounded split would not match).
    assert_eq!(
        blocks(&f),
        vec![
            Block {
                top: 0,
                bottom: 1,
                lines: vec!["$ make".into(), "BUILD FAILED: 2 errors".into()],
            },
            Block {
                top: 3,
                bottom: 4,
                lines: vec!["$ echo retry error".into(), "retry error".into()],
            },
        ]
    );
}

#[test]
fn search_hits_are_non_overlapping_left_to_right() {
    // The scan resumes after each match: `aa` in `aaa` is one hit at column 0.
    let f = frame(10, 1, &[out(b"aaa")], 0);
    assert_eq!(
        search(&f, "aa"),
        vec![Hit {
            row: 0,
            col: 0,
            len: 2
        }]
    );
    let f = frame(10, 1, &[out(b"-- --")], 0);
    assert_eq!(
        search(&f, "--"),
        vec![
            Hit {
                row: 0,
                col: 0,
                len: 2
            },
            Hit {
                row: 0,
                col: 3,
                len: 2
            }
        ]
    );
}

#[test]
fn string_sequences_never_reach_text_search_or_blocks() {
    // A title-setting prompt, OSC-133 shell marks and a DCS (sixel) payload —
    // the exact stream the pump classifies — leave no trace in the perceived
    // text. The DCS is ST-terminated and paints nothing, so every assertion
    // below is the same as without it.
    let recs = vec![
        out(b"\x1b]0;user@host: ~\x07$ make\r\n"),
        out(b"\x1b]133;C\x07BUILD FAILED\x1bPq#0;2;0;0;0\x1b\\\r\n\x1b]133;D;2\x07"),
        out(b"\x1b]133;A\x07$ "),
    ];
    let f = frame(COLS, ROWS, &recs, recs.len() - 1);
    assert_eq!(
        text(&f)[..3],
        [
            "$ make".to_string(),
            "BUILD FAILED".to_string(),
            "$".to_string()
        ]
    );
    assert!(search(&f, "133").is_empty());
    assert!(search(&f, "user@host").is_empty());
    let bs = blocks(&f);
    assert_eq!(bs.len(), 1);
    assert_eq!((bs[0].top, bs[0].bottom), (0, 2));
}

#[test]
fn search_is_char_column_accurate_with_multibyte() {
    let recs = vec![out("caf\u{e9} error caf\u{e9}".as_bytes())]; // 'é' is multibyte
    let f = frame(COLS, 2, &recs, 0);
    let hits = search(&f, "error");
    // "café " = 5 characters, so "error" starts at char column 5.
    assert_eq!(
        hits,
        vec![Hit {
            row: 0,
            col: 5,
            len: 5
        }]
    );
}

proptest! {
    /// The reads never panic and stay self-consistent on arbitrary bytes: blocks
    /// are the maximal contiguous non-empty regions (every block row non-empty,
    /// blocks ordered and separated by at least one empty row, carrying their
    /// rows' lines, and together covering exactly the non-empty rows), and every
    /// search hit re-reads as the needle at its character column.
    #[test]
    fn reads_are_panic_free_and_self_consistent(
        chunks in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..10), 0..5),
        cols in 1u16..30,
        rows in 1u16..8,
    ) {
        let recs: Vec<Record> = chunks.iter().map(|c| Record::Out(c.clone())).collect();
        let f = frame(cols, rows, &recs, recs.len().saturating_sub(1));
        let lines = text(&f);

        let bs = blocks(&f);
        let mut prev_bottom: Option<u16> = None;
        for b in &bs {
            prop_assert!(b.top <= b.bottom);
            if let Some(pb) = prev_bottom {
                prop_assert!(b.top > pb + 1, "blocks must be separated by an empty row");
            }
            for r in b.top..=b.bottom {
                prop_assert!(!lines[r as usize].is_empty(), "row {} in a block is empty", r);
            }
            prop_assert_eq!(&b.lines[..], &lines[b.top as usize..=b.bottom as usize]);
            prev_bottom = Some(b.bottom);
        }
        // Disjoint, all-non-empty blocks whose row count equals the number of
        // non-empty rows cover exactly those rows.
        let block_rows: usize = bs.iter().map(|b| (b.bottom - b.top + 1) as usize).sum();
        let nonempty = lines.iter().filter(|l| !l.is_empty()).count();
        prop_assert_eq!(block_rows, nonempty);

        for h in search(&f, "a") {
            let at: String = lines[h.row as usize]
                .chars()
                .skip(h.col as usize)
                .take(h.len as usize)
                .collect();
            prop_assert_eq!(at, "a");
        }
    }
}
