// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::render::frame_hash;

fn force_scalar<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool, bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            ascii_work::set(self.0);
            scroll_work::set(self.1);
        }
    }
    let restore = Restore(ascii_work::enabled(), scroll_work::enabled());
    ascii_work::set(false);
    scroll_work::set(false);
    let result = f();
    drop(restore);
    result
}

fn compare(actual: &Folder, reference: &Folder) {
    // Include parser state, pending ops, title/cwd and synchronized-output debt,
    // not merely the currently visible cells.
    assert_eq!(actual, reference);
    assert_eq!(actual.screen().serialize(), reference.screen().serialize());
    assert_eq!(frame_hash(actual.screen()), frame_hash(reference.screen()));
}

fn apply_pair(actual: &mut Folder, reference: &mut Folder, record: &Record) {
    force_scalar(|| reference.apply(record));
    actual.apply(record);
    compare(actual, reference);
}

#[test]
fn long_spans_execute_batched_paint_and_guarded_modes_stay_scalar() {
    let mut actual = Folder::new(80, 24);
    let mut reference = actual.clone();
    let _ = ascii_work::take();
    apply_pair(&mut actual, &mut reference, &Record::Out(vec![b'x'; 4096]));
    let (runs, bytes) = ascii_work::take();
    assert!(runs > 0, "the differential test must execute the fast path");
    assert!(bytes > 3000, "most of the long run should paint in spans");

    {
        let mut actual = Folder::new(40, 3);
        let mut reference = actual.clone();
        apply_pair(
            &mut actual,
            &mut reference,
            &Record::Out(b"\x1b[4h".to_vec()),
        );
        let _ = ascii_work::take();
        apply_pair(
            &mut actual,
            &mut reference,
            &Record::Out(b"abcdefghijklmnop".to_vec()),
        );
        assert_eq!(ascii_work::take(), (0, 0));
        assert_eq!(actual.take_ops(), reference.take_ops());
        compare(&actual, &reference);
    }

    // The selected GL set matters; the inactive set and SO itself must not
    // disable batching when the selected set still maps bytes to ASCII.
    for setup in [b"\x1b(0\x0e".as_slice(), b"\x1b)0\x0f"] {
        let mut actual = Folder::new(40, 3);
        let mut reference = actual.clone();
        apply_pair(&mut actual, &mut reference, &Record::Out(setup.to_vec()));
        let _ = ascii_work::take();
        apply_pair(
            &mut actual,
            &mut reference,
            &Record::Out(b"abcdefghijklmnop".to_vec()),
        );
        assert!(ascii_work::take().1 > 0);
    }
}

#[test]
fn every_dec_graphics_mapping_is_narrow_and_cannot_join_without_an_open_joiner() {
    let mut bases = vec![Cell::BLANK];
    for (ch, width, selector) in [
        ('a', 1, None),
        ('\u{1f44d}', 2, None),
        ('\u{261d}', 2, Some('\u{fe0f}')),
        ('\u{1f1fa}', 2, None),
        ('\u{1f468}', 2, Some('\u{200d}')),
        ('x', 0, Some('\u{200d}')),
        ('x', u8::MAX, Some('\u{200d}')),
    ] {
        let mut base = Cell::BLANK;
        base.ch = ch;
        base.width = width;
        if let Some(mark) = selector {
            base.push_combining(mark);
        }
        bases.push(base);
    }
    let mut full = Cell::BLANK;
    full.ch = '\u{1f468}';
    full.width = 2;
    full.combining = ['\u{0301}'; MAX_COMBINING];
    full.combining[MAX_COMBINING - 1] = '\u{200d}';
    full.combining_len = MAX_COMBINING as u8;
    bases.push(full);
    for byte in 0x20..=0x7e {
        let mapped = dec_special_graphic(byte);
        assert_eq!(char_display_width(mapped), 1, "byte={byte:#x}");
        assert!(!is_regional_indicator(mapped));
        assert!(!is_emoji_modifier(mapped));
        for base in &bases {
            assert!(!joins_cluster(base, mapped, false));
        }
    }
}

#[test]
fn selected_dec_spans_paint_visible_mappings_and_exact_recorded_prints() {
    let bytes: Vec<_> = (0x20..=0x7e).collect();
    let mapped: Vec<_> = bytes.iter().map(|&b| dec_special_graphic(b)).collect();
    assert_ne!(mapped, bytes.iter().map(|&b| b as char).collect::<Vec<_>>());
    for setup in [b"\x1b(0".as_slice(), b"\x1b)0\x0e"] {
        for recording in [false, true] {
            let mut actual = Folder::new(12, 10);
            actual.set_recording(recording);
            let mut reference = actual.clone();
            apply_pair(&mut actual, &mut reference, &Record::Out(setup.to_vec()));
            let _ = ascii_work::take();
            apply_pair(&mut actual, &mut reference, &Record::Out(bytes.clone()));
            assert!(ascii_work::take().1 > 0, "selected DEC must use spans");
            let ops = actual.take_ops();
            assert_eq!(ops, reference.take_ops());
            if recording {
                let prints: Vec<_> = ops
                    .iter()
                    .filter_map(|op| match op {
                        ScreenOp::Print(ch) => Some(*ch),
                        _ => None,
                    })
                    .collect();
                assert_eq!(prints, mapped);
                assert_eq!(&apply_ops(12, 10, &ops), actual.screen());
            }
            assert_eq!(actual.screen().cell(6, 9).unwrap().ch, '\u{2500}');
            compare(&actual, &reference);
        }
    }

    let fixture = b"\x1b(0lqkxjmnvuwtlqkxjmnvuwt\x0eASCII G1\x0flqk\x1b[?69h\x1b[3;10s\x1b[2;1Hlqkxjmnvuwtlqkxjmnvuwt\x1b[?69l\x1b)0\x0elqkxjmnvuwt\x0fback in G0";
    for recording in [false, true] {
        for split in 0..=fixture.len() {
            let mut actual = Folder::new(12, 5);
            actual.set_recording(recording);
            let mut reference = actual.clone();
            for part in [&fixture[..split], &fixture[split..]] {
                apply_pair(&mut actual, &mut reference, &Record::Out(part.to_vec()));
            }
            let ops = actual.take_ops();
            assert_eq!(ops, reference.take_ops());
            if recording {
                assert_eq!(&apply_ops(12, 5, &ops), actual.screen());
            }
            compare(&actual, &reference);
        }
    }
}

#[test]
fn open_zwj_keeps_dec_cluster_fallback_but_allows_ascii_spans() {
    for recording in [false, true] {
        let mut actual = Folder::new(12, 3);
        actual.set_recording(recording);
        actual.apply(&Record::Out("\x1b(0\u{1f468}\u{200d}".as_bytes().to_vec()));
        let mut base = *actual.screen().cell(0, 0).unwrap();
        base.combining = ['\u{0301}'; MAX_COMBINING];
        base.combining[MAX_COMBINING - 1] = '\u{200d}';
        base.combining_len = MAX_COMBINING as u8;
        actual.screen.set_cell(0, 0, base);
        assert!(actual.screen.joiner_open);
        let mut reference = actual.clone();
        let bytes = b"lqklqklqk";
        let _ = ascii_work::take();
        apply_pair(&mut actual, &mut reference, &Record::Out(bytes.to_vec()));
        assert_eq!(ascii_work::take(), (0, 0));
        assert_eq!(actual.screen().cursor(), (0, 2));
        assert_eq!(actual.screen().cell(0, 0), Some(&base));
        assert!(actual.screen.joiner_open);
        let ops = actual.take_ops();
        assert_eq!(ops, reference.take_ops());
        if recording {
            let mapped: Vec<_> = bytes
                .iter()
                .map(|&b| ScreenOp::Print(dec_special_graphic(b)))
                .collect();
            assert!(ops.ends_with(&mapped));
        }

        apply_pair(
            &mut actual,
            &mut reference,
            &Record::Out(b"\x1b(B".to_vec()),
        );
        assert!(actual.screen.joiner_open);
        let _ = ascii_work::take();
        apply_pair(
            &mut actual,
            &mut reference,
            &Record::Out(b"ASCII breaks the open joiner".to_vec()),
        );
        assert!(ascii_work::take().1 > 0);
        assert!(!actual.screen.joiner_open);
        assert_eq!(actual.screen().cell(0, 0), Some(&base));
        assert_eq!(actual.take_ops(), reference.take_ops());
        compare(&actual, &reference);
    }
}

#[test]
fn recording_spans_append_exact_print_ops_across_wraps_toggles_and_drains() {
    let mut actual = Folder::new_recording(9, 3);
    let mut reference = actual.clone();
    apply_pair(&mut actual, &mut reference, &Record::Out(b"old".to_vec()));
    let bytes: Vec<_> = (0..128).map(|at| b'a' + (at % 26) as u8).collect();
    let _ = ascii_work::take();
    apply_pair(&mut actual, &mut reference, &Record::Out(bytes.clone()));
    assert!(ascii_work::take().1 > 0, "recording must use ASCII spans");
    let expected: Vec<_> = b"old"
        .iter()
        .chain(&bytes)
        .map(|&b| ScreenOp::Print(b as char))
        .collect();
    assert_eq!(actual.take_ops(), expected);
    assert_eq!(reference.take_ops(), expected);
    compare(&actual, &reference);

    // Disabling recording neither drains already-recorded ops nor changes the
    // screen. Re-enabling it appends to the same exact operation sequence.
    for (recording, bytes) in [
        (false, b"unrecorded first".as_slice()),
        (true, b"recorded first".as_slice()),
        (false, b"unrecorded middle".as_slice()),
        (true, b"recorded second".as_slice()),
    ] {
        actual.set_recording(recording);
        reference.set_recording(recording);
        apply_pair(&mut actual, &mut reference, &Record::Out(bytes.to_vec()));
    }
    let expected: Vec<_> = b"recorded first"
        .iter()
        .chain(b"recorded second")
        .map(|&b| ScreenOp::Print(b as char))
        .collect();
    assert_eq!(actual.take_ops(), expected);
    assert_eq!(reference.take_ops(), expected);
    assert!(actual.take_ops().is_empty());
    compare(&actual, &reference);
}

#[test]
fn recording_byte_splits_keep_pending_ops_and_typed_replay_exact() {
    let fixtures: &[&[u8]] = &[
        b"ASCII words crossing several complete rows\r\nnext row",
        b"\x1b[38;2;1;2;3mcoloured ASCII\x1b[2;2Hpositioned\x1b(0lqk\x1b(Bback",
        "\u{1f468}\u{200d}ASCII#\u{fe0f}\u{20e3}e\u{0301}tail".as_bytes(),
        b"\xe2ab\xf0\x80xyz\x1b]2;ignored title\x07printable tail",
    ];
    let _ = ascii_work::take();
    for &(cols, rows) in &[(2, 2), (9, 4)] {
        for fixture in fixtures {
            for split in 0..=fixture.len() {
                let mut actual = Folder::new_recording(cols, rows);
                let mut reference = actual.clone();
                for bytes in [
                    b"pending old record".as_slice(),
                    &fixture[..split],
                    &fixture[split..],
                ] {
                    apply_pair(&mut actual, &mut reference, &Record::Out(bytes.to_vec()));
                }
                let ops = actual.take_ops();
                assert_eq!(ops, reference.take_ops());
                compare(&actual, &reference);
                assert_eq!(&apply_ops(cols, rows, &ops), actual.screen());
            }
        }
    }
    assert!(ascii_work::take().1 > 0);
}

#[test]
fn exact_row_end_preserves_an_orphan_spacer_in_the_following_row() {
    for recording in [false, true] {
        let mut actual = Folder::new(4, 2);
        actual.set_recording(recording);
        let mut marker = Cell::BLANK;
        marker.ch = 'X';
        marker.width = 0;
        marker.fg_rgb = Some((1, 2, 3));
        marker.bg_rgb = Some((4, 5, 6));
        marker.underline = Underline::Curly;
        marker.ul_rgb = Some((7, 8, 9));
        marker.combining[0] = '\u{0301}';
        marker.combining[MAX_COMBINING - 1] = '\u{200d}';
        marker.combining_len = 1;
        actual.screen.set_cell(1, 0, marker);
        let mut reference = actual.clone();
        apply_pair(&mut actual, &mut reference, &Record::Out(b"abcd".to_vec()));
        assert_eq!(actual.screen().cursor(), (0, 4));
        assert!(actual.screen().wrap_pending());
        assert_eq!(actual.screen().cell(1, 0), Some(&marker));
        assert_eq!(actual.take_ops(), reference.take_ops());
    }
}

#[test]
fn parser_states_and_every_record_split_match_the_scalar_feed() {
    let fixtures: &[&[u8]] = &[
        b" !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~",
        b"before\xe2ab\xc0\x80XYZ\xe0\x80end\xed\xa0\x80tail\xf4\x90\x80\x80!",
        b"left\tTAB\x08B\rRETURN\nLF\x0bVT\x0cFF\x00NUL\x7fDEL",
        b"ASCII\x1b(0lqk\x0eG1ASCII\x0fDEC\x1b(Bnormal\x1b)0\x0elqk\x0fplain",
        b"pre\x1b]2;ASCII title\x07post\x1b]7;file:///tmp/span%20test\x1b\\done\x1bPignored ASCII\x1b\\paint\x1bXignored\x18tail",
        b"\x1b[38;2;1;2;3mcolour\x1b[4:3munderline\x1b[4hINSERT\x1b[4lplain\x1b[?69h\x1b[3;7s\x1b[2;1Houtside and inside\x1b[?69l",
        "A\u{1f468}\u{200d}ascii#\u{fe0f}\u{20e3}*\u{fe0f}9\u{fe0f}e\u{0301}界\u{0301}last".as_bytes(),
        b"\x1b[?2026hheld ASCII\x1b[?2026l\x1b[?2026hnext\x1b[?2026lplain",
    ];
    for &(cols, rows) in &[(1, 1), (2, 2), (9, 4)] {
        for fixture in fixtures {
            for split in 0..=fixture.len() {
                let mut actual = Folder::new(cols, rows);
                let mut reference = actual.clone();
                for bytes in [&fixture[..split], &fixture[split..]] {
                    apply_pair(&mut actual, &mut reference, &Record::Out(bytes.to_vec()));
                }
                // Also inspect future effects of the exact partial parser and
                // cursor/combining state left at each split.
                apply_pair(
                    &mut actual,
                    &mut reference,
                    &Record::Out("\u{0301}Z\x1b[0m\r\nend".as_bytes().to_vec()),
                );
            }
        }
    }
}

fn seeded_overlay(cols: u16, seed: u16) -> Folder {
    let mut folder = Folder::new(cols, 3);
    folder.apply(&Record::Out(
        b"\x1b[38;2;3;4;5m\x1b[48;2;6;7;8m\x1b[4:3;58;2;9;10;11m".to_vec(),
    ));
    let widths = [0, 1, 2, 7, u8::MAX];
    for row in 0..3 {
        for col in 0..cols {
            let marker = row * cols + col + seed;
            let mut cell = Cell::BLANK;
            cell.ch = char::from(b'A' + (marker % 26) as u8);
            cell.fg = Color::Indexed(marker as u8);
            cell.bg_rgb = Some((marker as u8, 91, 203));
            cell.underline = Underline::Double;
            cell.ul_rgb = Some((44, 55, marker as u8));
            cell.width = widths[usize::from(marker) % widths.len()];
            cell.combining[0] = '\u{0301}';
            cell.combining[12] = '\u{200d}';
            cell.combining_len = if marker % 2 == 0 { 1 } else { u8::MAX };
            folder.screen.set_cell(row, col, cell);
        }
    }
    folder.screen.joiner_open = seed % 2 == 0;
    folder
}

#[test]
fn ascii_overwrites_preserve_scalar_repairs_of_arbitrary_cell_overlays() {
    // set_cell permits caller-created cells, including orphan spacers and
    // malformed widths. Compatibility must cover their old repair behavior.
    for cols in 1..=12u16 {
        for seed in 0..5 {
            for start in 0..cols {
                for len in 1..=usize::from(cols) + 2 {
                    let mut actual = seeded_overlay(cols, seed);
                    actual.screen.move_to(1, start);
                    let mut reference = actual.clone();
                    let bytes = (0..len).map(|at| b'a' + (at % 26) as u8).collect();
                    apply_pair(&mut actual, &mut reference, &Record::Out(bytes));
                    apply_pair(
                        &mut actual,
                        &mut reference,
                        &Record::Out("\u{0301}\u{fe0f}\u{200d}界Z".as_bytes().to_vec()),
                    );
                }
            }
        }
    }
}

#[test]
fn margins_wrap_alt_buffers_resize_and_recording_keep_exact_state() {
    for &(cols, rows) in &[(1, 1), (2, 2), (8, 4), (13, 7)] {
        for recording in [false, true] {
            let mut actual = Folder::new(cols, rows);
            actual.set_recording(recording);
            let mut reference = actual.clone();
            let records = [
                Record::Out(b"\x1b[48;2;3;45;67m\x1b[4:3mabcdefghijklmnop".to_vec()),
                Record::Out(b"\x1b[?69h\x1b[3;7s\x1b[1;1H12".to_vec()),
                Record::Out("\u{0301}3456789\u{fe0f}".as_bytes().to_vec()),
                Record::Out(b"\x1b[2;3r\x1b[3;3Hlong run crossing margins\r\nnext".to_vec()),
                Record::Out(b"\x1b[?6h\x1b[20h\norigin and newline\x1b[20l\x1b[?6l".to_vec()),
                Record::Out(b"\x1b7\x1b[?1049hALT text\r\nmore\x1b[?1049l\x1b8tail".to_vec()),
                Record::Resize { cols: 5, rows: 3 },
                Record::Out(b"\x1b[?47hSECOND alternate\x1b[?47lmain".to_vec()),
                Record::Resize { cols: 0, rows: 0 },
                Record::Out("narrow#\u{fe0f}\u{20e3}and e\u{0301}".as_bytes().to_vec()),
                Record::Resize { cols: 17, rows: 5 },
                Record::Out(b"\x1b[4hINSERT run\x1b[4lplain again\x1b[r\x1b[?69l".to_vec()),
                Record::In {
                    bytes: b"ignored input\x1b[?2026h".to_vec(),
                    client_id: 7,
                    client_seq: 11,
                },
                Record::Exit { code: 9 },
            ];
            for record in records {
                apply_pair(&mut actual, &mut reference, &record);
                assert_eq!(actual.take_ops(), reference.take_ops());
                compare(&actual, &reference);
            }
        }
    }
}

#[test]
fn ascii_span_sync_accounting_matches_each_byte_at_the_budget_boundary() {
    let cap = crate::events::MAX_SYNC_OUTPUT_BYTES;
    for synchronized in [false, true] {
        for initial in [0, 1, cap - 2, cap - 1, cap, cap + 7] {
            for len in [0, 1, 2, 3, 80] {
                let mut actual = Folder::new(64, 4);
                actual.screen.synchronized_output = synchronized;
                actual.sync_bytes = initial;
                let mut reference = actual.clone();
                apply_pair(&mut actual, &mut reference, &Record::Out(vec![b'x'; len]));
                let expected = if len == 0 {
                    initial
                } else if synchronized {
                    initial.saturating_add(len).min(cap)
                } else {
                    0
                };
                assert_eq!(actual.sync_output_bytes(), expected);
                apply_pair(
                    &mut actual,
                    &mut reference,
                    &Record::Out(b"\x1b[?2026l\x1b[?2026hASCII".to_vec()),
                );
                assert_eq!(actual.sync_output_bytes(), 5);
                apply_pair(&mut actual, &mut reference, &Record::Out(Vec::new()));
                assert_eq!(actual.sync_output_bytes(), 5);
                apply_pair(
                    &mut actual,
                    &mut reference,
                    &Record::Out(b"\x1b[?2026lplain".to_vec()),
                );
                assert_eq!(actual.sync_output_bytes(), 0);
            }
        }
    }
}

#[test]
fn deterministic_mixed_records_match_scalar_folder_and_ops() {
    let corpus: &[&[u8]] = &[
        b"ordinary ASCII words and numbers0123456789",
        b"\r\nshort line\tend\x08!",
        b"\x1b[4hinserted text\x1b[4l",
        b"\x1b[?69h\x1b[2;6s\x1b[1;1Hcross the left margin",
        b"\x1b[?69l\x1b[2;5r\x1b[5;1Hscrolling text\r\n",
        b"\x1b[r\x1b[38;2;2;3;4m\x1b[4:3mstyled ASCII",
        b"\x1b(0lqk\x1b(Bascii\x1b)0\x0ex\x0fplain",
        b"\x1b[?47hALT\x1b[?47l\x1b[?1049hother\x1b[?1049l",
        b"\x1b]2;title\x1b\\\x1bPswallowed ASCII\x1b\\painted",
        b"\xe2ab\xf0\x80xyz\x7f\x00",
        b"\x1b[?2026hheld\x1b[?2026l\x1b7saved\x1b8restored",
        "界\u{0301}#\u{fe0f}\u{20e3}\u{1f468}\u{200d}ASCII".as_bytes(),
        b"\x1bcreset ASCII",
    ];
    for seed in 1..=32u64 {
        let mut rng = seed * 0x9e37_79b9;
        let mut actual = Folder::new(11, 6);
        actual.set_recording(seed % 2 == 0);
        let mut reference = actual.clone();
        for at in 0..256 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            let record = if rng % 23 == 0 {
                Record::Resize {
                    cols: (rng % 19) as u16,
                    rows: (rng % 11) as u16,
                }
            } else if rng % 17 == 0 {
                Record::Out((0..rng % 41).map(|i| (rng >> (i % 8)) as u8).collect())
            } else {
                Record::Out(corpus[(rng as usize / 23) % corpus.len()].to_vec())
            };
            apply_pair(&mut actual, &mut reference, &record);
            if at % 13 == 0 {
                assert_eq!(actual.take_ops(), reference.take_ops());
                compare(&actual, &reference);
            }
        }
    }
}
