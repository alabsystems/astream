use super::pending_tests::LegacyPredictor;
use super::*;
use crate::screen::{apply_ops_to, MAX_COMBINING};
use crate::ScreenOp;

fn out(bytes: &[u8]) -> Record {
    Record::Out(bytes.to_vec())
}
fn compare(actual: &Predictor, reference: &LegacyPredictor) {
    assert_eq!(actual.authoritative(), reference.authoritative());
    assert_eq!(actual.in_watermark(), reference.in_watermark());
    assert_eq!(actual.view(), reference.view());
}

#[test]
fn blank_and_redrawn_spaces_scan_each_needed_row_once() {
    for width in [1u16, 2, 8, 80, 120, 240, 1000] {
        let spaces = vec![b' '; width as usize];
        let mut actual = Predictor::new(width, 2);
        let mut reference = LegacyPredictor::new(width, 2);
        assert!(actual.predict(1, &spaces));
        assert!(reference.predict(1, &spaces));
        let (a, new_work) = positional_work::capture(|| actual.reconcile());
        let (b, old_work) = positional_work::capture(|| reference.reconcile());
        assert_eq!(a, b);
        assert!(a.iter().all(|&(_, verdict)| verdict == Verdict::Lost));
        assert_eq!(new_work.memoized_rows, 1);
        assert_eq!(new_work.memoized_cells, width as usize);
        assert_eq!(old_work.legacy_rows, width as usize);
        assert_eq!(old_work.legacy_cells, (width as usize).pow(2));
        compare(&actual, &reference);
        if width == 1 {
            continue;
        }
        let spaces = vec![b' '; width as usize - 1];
        let mut echo = spaces.clone();
        echo.extend_from_slice(b"X\r");
        let mut actual = Predictor::new(width, 2);
        let mut reference = LegacyPredictor::new(width, 2);
        actual.predict(1, &spaces);
        reference.predict(1, &spaces);
        let (a, new_work) = positional_work::capture(|| actual.apply_output_at(1, &out(&echo)));
        let (b, old_work) = positional_work::capture(|| reference.apply_output_at(1, &out(&echo)));
        assert_eq!(a, b);
        assert_eq!(a.len(), spaces.len());
        assert!(a.iter().all(|&(_, verdict)| verdict == Verdict::Confirmed));
        assert_eq!(new_work.memoized_rows, 1);
        assert_eq!(old_work.legacy_rows, spaces.len());
        assert_eq!(old_work.legacy_cells, spaces.len() * width as usize);
        compare(&actual, &reference);
    }
}

#[test]
fn exact_row_text_semantics_survive_wide_combining_unicode_trim_and_overlays() {
    let mut screen = Screen::new(12, 4);
    let mut combining = Cell::BLANK;
    combining.ch = 'e';
    combining.combining[0] = '\u{301}';
    combining.combining[1] = '\u{2003}';
    combining.combining_len = 2;
    screen.set_cell(0, 2, combining);
    screen.set_cell(
        0,
        4,
        Cell {
            ch: '界',
            width: 2,
            ..Cell::BLANK
        },
    );
    screen.set_cell(
        0,
        5,
        Cell {
            ch: 'Q',
            width: 0,
            ..combining
        },
    ); // spacer text/marks are omitted
    screen.set_cell(
        0,
        8,
        Cell {
            ch: '\u{2003}',
            ..Cell::BLANK
        },
    );
    screen.set_cell(
        1,
        0,
        Cell {
            ch: ' ',
            combining: ['\u{301}'; MAX_COMBINING],
            combining_len: 255,
            ..Cell::BLANK
        },
    );
    screen.set_cell(
        1,
        2,
        Cell {
            ch: 'Q',
            width: 255,
            ..Cell::BLANK
        },
    );
    screen.set_cell(
        1,
        10,
        Cell {
            ch: '\t',
            ..Cell::BLANK
        },
    );
    screen.set_cell(
        2,
        0,
        Cell {
            ch: '\0',
            combining: ['\0'; MAX_COMBINING],
            combining_len: 16,
            ..Cell::BLANK
        },
    );
    // Direct context queries deliberately revisit rows out of prediction order.
    let mut lengths = RowTextLengths::default();
    let (_, work) = positional_work::capture(|| {
        for row in [0, 1, 0, 2, 1, 3, 0, 3, 4, 4, u16::MAX] {
            assert_eq!(
                lengths.get(&screen, row),
                screen.line_text(row).chars().count()
            );
            for col in [0, 1, 2, 4, 8, 11, 12, u16::MAX] {
                for ch in [' ', 'Q', 'e'] {
                    let p = Prediction {
                        client_seq: 1,
                        row,
                        col,
                        ch,
                        in_offset: None,
                    };
                    assert_eq!(
                        verdict_now(&screen, &p, &mut lengths),
                        legacy_verdict_now(&screen, &p)
                    );
                }
            }
        }
    });
    assert_eq!(work.memoized_rows, 6); // four valid rows and two invalid row keys
                                       // Cursor traversal is still sufficient even when the text count is zero.
    apply_ops_to(&mut screen, &[ScreenOp::MoveTo(3, 5)]);
    let mut lengths = RowTextLengths::default();
    let (_, work) = positional_work::capture(|| {
        for row in 0..3 {
            for col in 0..12 {
                let p = Prediction {
                    client_seq: 1,
                    row,
                    col,
                    ch: ' ',
                    in_offset: None,
                };
                assert_eq!(
                    verdict_now(&screen, &p, &mut lengths),
                    legacy_verdict_now(&screen, &p)
                );
            }
        }
    });
    assert_eq!(work.memoized_rows, 0);
    assert!(lengths.current.is_none());
    assert!(lengths.previous.is_empty());
}

#[test]
fn multiple_rows_resize_alt_buffers_and_new_calls_never_reuse_stale_lengths() {
    let mut actual = Predictor::new(12, 4);
    let mut reference = LegacyPredictor::new(12, 4);
    let line = [b"           X".as_slice(); 3].concat();
    actual.predict(1, &line);
    reference.predict(1, &line);
    let record = out(b"           X           X           X\x1b[H");
    let (a, work) = positional_work::capture(|| actual.apply_output_at(1, &record));
    let b = reference.apply_output_at(1, &record);
    assert_eq!(a, b);
    assert_eq!(work.memoized_rows, 3);
    compare(&actual, &reference);
    for record in [
        out(b"\x1b[2J\x1b[H"),
        out(b"\x1b[?1049h \x1b[H"),
        out(b"\x1b[?1049l"),
        Record::Resize { cols: 8, rows: 2 },
    ] {
        actual.predict(9, b"  x ");
        reference.predict(9, b"  x ");
        actual.apply_output(&record);
        reference.apply_output(&record);
        assert_eq!(actual.reconcile(), reference.reconcile());
        compare(&actual, &reference);
    }
    // Nonadvancing watermarks neither fold nor allocate a summary.
    actual.predict(10, b" ");
    reference.predict(10, b" ");
    let (a, work) = positional_work::capture(|| actual.apply_output_at(1, &out(b"X\r")));
    assert_eq!(a, reference.apply_output_at(1, &out(b"X\r")));
    assert_eq!(work.memoized_rows, 0);
    compare(&actual, &reference);
}

#[test]
fn ordinary_cursor_and_causal_paths_do_not_compute_row_text() {
    for bytes in [b"x".as_slice(), b" ", b"        ", b"plain text"] {
        let mut actual = Predictor::new(80, 24);
        let mut reference = LegacyPredictor::new(80, 24);
        actual.predict(1, bytes);
        reference.predict(1, bytes);
        let (a, work) = positional_work::capture(|| actual.apply_output_at(1, &out(bytes)));
        assert_eq!(a, reference.apply_output_at(1, &out(bytes)));
        assert_eq!(work.memoized_rows, 0);
        compare(&actual, &reference);
        actual.predict_at(2, 9, b" ");
        reference.predict_at(2, 9, b" ");
        let (a, work) =
            positional_work::capture(|| actual.apply_output_caused(2, Some(9), &out(b" ")));
        assert_eq!(a, reference.apply_output_caused(2, Some(9), &out(b" ")));
        assert_eq!(work.memoized_rows, 0);
        compare(&actual, &reference);
    }
}

// Same Pending representation as production; only the frozen verdict helper
// differs, so this manual control isolates row-text memoization.
fn reconcile_uncached(predictor: &mut Predictor) -> Vec<(u64, Verdict)> {
    let screen = predictor.base.screen();
    let verdicts = predictor
        .preds
        .iter()
        .map(|p| {
            (
                p.client_seq,
                legacy_verdict_now(screen, p).unwrap_or(Verdict::Lost),
            )
        })
        .collect();
    predictor.preds.clear();
    verdicts
}

#[test]
#[ignore = "manual same-process frozen-verdict versus memoized row-text control"]
fn positional_spaces_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    for width in [80u16, 120, 240, 1000] {
        let spaces = vec![b' '; width as usize];
        let mut old = Vec::new();
        let mut new = Vec::new();
        for _ in 0..128 {
            let mut a = Predictor::new(width, 2);
            a.predict(1, &spaces);
            new.push(a);
            let mut b = Predictor::new(width, 2);
            b.predict(1, &spaces);
            old.push(b);
        }
        let start = Instant::now();
        for p in &mut old {
            black_box(reconcile_uncached(p));
        }
        let old_ns = start.elapsed().as_nanos() / 128;
        let start = Instant::now();
        for p in &mut new {
            black_box(p.reconcile());
        }
        let new_ns = start.elapsed().as_nanos() / 128;
        for (a, b) in new.iter().zip(&old) {
            assert_eq!(a.authoritative(), b.authoritative());
            assert_eq!(a.in_watermark(), b.in_watermark());
            assert_eq!(a.view(), b.view());
        }
        println!("POSITIONAL_SPACE width={width} old_ns={old_ns} memoized_ns={new_ns}");
    }
}
