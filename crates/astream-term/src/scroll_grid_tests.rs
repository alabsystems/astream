use super::*;
use crate::render::{frame_hash, rasterize};

fn dense<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool, bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            scroll_work::set(self.0);
            ascii_work::set(self.1);
        }
    }
    let restore = Restore(scroll_work::enabled(), ascii_work::enabled());
    scroll_work::set(false);
    ascii_work::set(false);
    let result = f();
    drop(restore);
    result
}

fn seeded(cols: u16, rows: u16, uniform_rows: bool) -> Screen {
    let mut screen = Screen::new(cols, rows);
    for r in 0..rows {
        for c in 0..cols {
            let marker = if uniform_rows { c } else { r * cols + c };
            let mut cell = Cell::BLANK;
            cell.ch = char::from(b'a' + (marker % 26) as u8);
            cell.fg = Color::Indexed((marker % 256) as u8);
            cell.bg_rgb = Some((marker as u8, 91, 203));
            cell.fg_rgb = Some((19, marker as u8, 72));
            cell.underline = Underline::Curly;
            cell.ul_rgb = Some((44, 55, marker as u8));
            cell.combining[0] = '\u{0301}';
            cell.combining[12] = '\u{200d}'; // inactive combining slots are encoded too.
            cell.combining_len = 1;
            if c % 3 == 0 && c + 1 < cols {
                cell.width = 2;
            }
            if c % 3 == 1 {
                cell.width = 0;
            }
            screen.set_cell(r, c, cell);
        }
    }
    screen
}

fn compare(actual: &Screen, reference: &Screen) {
    assert_eq!(actual, reference);
    assert_eq!(actual.serialize(), reference.serialize());
    assert_eq!(frame_hash(actual), frame_hash(reference));
    assert_eq!(rasterize(actual), rasterize(reference));
    assert_eq!(
        actual.grid.iter().copied().collect::<Vec<_>>(),
        reference.grid.iter().copied().collect::<Vec<_>>()
    );
    for r in 0..actual.rows {
        assert_eq!(actual.line_text(r), reference.line_text(r));
        for c in 0..actual.cols {
            assert_eq!(actual.cell(r, c), reference.cell(r, c));
        }
    }
    assert!(actual.cell(u16::MAX, 0).is_none());
    assert!(actual.cell(0, u16::MAX).is_none());
}

fn op_pair(actual: &mut Screen, reference: &mut Screen, op: ScreenOp) {
    dense(|| apply_ops_to(reference, std::slice::from_ref(&op)));
    apply_ops_to(actual, &[op]);
    compare(actual, reference);
}

#[test]
fn viewport_rotation_moves_no_surviving_cells_and_preserves_zero_counts() {
    for (cols, rows) in [(1u16, 1u16), (4, 3), (80, 24), (120, 50)] {
        for count in [0, 1, rows.saturating_sub(1), rows, u16::MAX] {
            for down in [false, true] {
                let mut actual = seeded(cols, rows, false);
                let mut reference = actual.clone();
                let op = if down {
                    ScreenOp::ScrollDown(count)
                } else {
                    ScreenOp::ScrollUp(count)
                };
                let _ = scroll_work::take();
                dense(|| apply_ops_to(&mut reference, std::slice::from_ref(&op)));
                let old = scroll_work::take();
                apply_ops_to(&mut actual, &[op]);
                assert_eq!(scroll_work::take(), 0);
                assert_eq!(
                    old,
                    usize::from(rows.saturating_sub(count.min(rows)))
                        * usize::from(cols)
                        * usize::from(count > 0)
                );
                compare(&actual, &reference);
            }
        }
    }
}

#[test]
fn logical_equality_and_all_extension_indices_ignore_active_and_inactive_origins() {
    let mut canonical = seeded(12, 8, false);
    let mut rotated = canonical.clone();
    apply_ops_to(&mut rotated, &[ScreenOp::ScrollUp(3)]);
    assert_ne!(rotated.grid.origin, 0);
    for r in 0..8 {
        for c in 0..12 {
            rotated.set_cell(r, c, *canonical.cell(r, c).unwrap());
        }
    }
    compare(&rotated, &canonical);
    assert_eq!(format!("{rotated:?}"), format!("{canonical:?}"));
    canonical.enter_alt();
    rotated.enter_alt();
    canonical.grid = seeded(12, 8, false).grid;
    rotated.grid = canonical.grid.clone();
    apply_ops_to(&mut rotated, &[ScreenOp::ScrollDown(2)]);
    for r in 0..8 {
        for c in 0..12 {
            rotated.set_cell(r, c, *canonical.cell(r, c).unwrap());
        }
    }
    compare(&rotated, &canonical);
    canonical.leave_alt();
    rotated.leave_alt();
    compare(&rotated, &canonical);
    assert_ne!(rotated.inactive.as_ref().unwrap().origin, 0);
    let before = rotated.serialize();
    rotated.set_cell(u16::MAX, u16::MAX, Cell::BLANK);
    assert_eq!(rotated.serialize(), before);
}

#[test]
fn wrapped_grid_differential_covers_rows_ranges_margins_alt_buffers_and_resize() {
    let mut actual = seeded(12, 8, false);
    let mut reference = actual.clone();
    op_pair(&mut actual, &mut reference, ScreenOp::ScrollUp(3));
    let programs: &[&[u8]] = &[
        b"\x1b[48;2;3;45;67m\x1b[4;6H\x1b[1J",
        b"\x1b[4;6H\x1b[J\x1b[2K\x1b[1K\x1b[K\x1b[3X",
        b"\x1b[3;3H\x1b[3@abc\x1b[2P\x1b[4hXYZ\x1b[4l",
        b"\x1b[2;7r\x1b[4;1H\x1b[2L\x1b[M\x1b[7;1H\n\x1bM\x1b[r",
        b"\x1b[?69h\x1b[3;10s\x1b[8;3H\r\n\x1b[3S\x1b[2T\x1b[1;3H\x1bM\x1b[?69l",
        "\x1b[8;12H界😀\u{fe0f}\u{200d}🚀\u{0301}\r\n".as_bytes(),
        b"\x1b7\x1b[?6h\x1b[2;7r\x1b[?1049hALT\r\n\x1b[5S\x1b7\x1b[?1049l\x1b8\x1b[?6l\x1b[r",
        b"\x1b[?47h\x1b[3S\x1b[?47l\x1b[?1047h\x1b[2T\x1b[?1047l\x1b[?47h\x1bc\x1b[?47h\x1b8\x1b[?47l",
        b"\x1b[8;1H\n\x1bD\x1bE\x1b[1;1H\x1bM\x1b[65535S\x1b[65535T",
    ];
    for program in programs {
        let mut a = Folder::new(12, 8);
        let mut r = Folder::new(12, 8);
        a.screen = actual;
        r.screen = reference;
        for &byte in *program {
            let record = Record::Out(vec![byte]);
            dense(|| r.apply(&record));
            a.apply(&record);
            assert_eq!(a, r);
            compare(a.screen(), r.screen());
        }
        actual = a.into_screen();
        reference = r.into_screen();
        op_pair(&mut actual, &mut reference, ScreenOp::ScrollUp(3));
    }
    for op in [
        ScreenOp::InsertLines(0),
        ScreenOp::DeleteLines(0),
        ScreenOp::ScrollUp(0),
        ScreenOp::ScrollDown(0),
        ScreenOp::Resize(9, 5),
        ScreenOp::Resize(1, 1),
        ScreenOp::Resize(12, 8),
    ] {
        op_pair(&mut actual, &mut reference, op);
    }
}

#[test]
fn byte_split_folder_snapshots_resume_and_typed_projection_stay_canonical() {
    let bytes = "one\r\ntwo\r\nthree\r\nfour\r\nfive\r\n\x1b[2J\x1b[3;1H界\u{0301}\x1b[38;2;1;2;3mZ\r\n\x1b[?47hALT\x1b[3S\x1b[?47l\x1b]2;title\x07".as_bytes();
    let mut actual = Folder::new_recording(5, 3);
    let mut reference = Folder::new_recording(5, 3);
    let mut projected = Screen::new(5, 3);
    let mut snapshots = Vec::new();
    for (at, &byte) in bytes.iter().enumerate() {
        let record = Record::Out(vec![byte]);
        dense(|| reference.apply(&record));
        actual.apply(&record);
        assert_eq!(actual, reference);
        let ops = actual.take_ops();
        assert_eq!(ops, reference.take_ops());
        apply_ops_to(&mut projected, &ops);
        compare(&projected, actual.screen());
        snapshots.push((at + 1, actual.clone(), reference.clone()));
    }
    for (at, mut a, mut r) in snapshots {
        for &byte in &bytes[at..] {
            let record = Record::Out(vec![byte]);
            dense(|| r.apply(&record));
            a.apply(&record);
        }
        assert_eq!(a, r);
        a.take_ops();
        assert_eq!(a, actual);
    }
}

#[test]
fn seeded_mixed_programs_match_dense_at_every_record() {
    let corpus: &[&[u8]] = &[
        b"x\r\n",
        b"\x1b[3S",
        b"\x1b[2T",
        b"\x1b[4;1H\n",
        b"\x1b[1;1H\x1bM",
        b"\x1b[2;5r",
        b"\x1b[r",
        b"\x1b[?69h\x1b[2;6s",
        b"\x1b[?69l",
        b"\x1b[1J",
        b"\x1b[J",
        b"\x1b[2J",
        b"\x1b[2L\x1b[M",
        b"\x1b[3@Q\x1b[2P",
        b"\x1b[?47h",
        b"\x1b[?47l",
        b"\x1b[?1049h",
        b"\x1b[?1049l",
        b"\x1b7\x1b8",
        b"\x1bc",
        "界😀\u{fe0f}\u{200d}🚀\u{0301}".as_bytes(),
        b"\x1b[48;2;5;6;7m\x1b[4:3mQ",
    ];
    for seed in 1..=32u64 {
        let mut rng = seed * 0x9e37_79b9;
        let mut a = Folder::new(9, 6);
        let mut r = Folder::new(9, 6);
        for _ in 0..250 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            let record = if rng % 23 == 0 {
                Record::Resize {
                    cols: (rng % 17) as u16,
                    rows: (rng % 11) as u16,
                }
            } else {
                Record::Out(corpus[(rng as usize / 23) % corpus.len()].to_vec())
            };
            dense(|| r.apply(&record));
            a.apply(&record);
            assert_eq!(a, r);
            compare(a.screen(), r.screen());
        }
    }
}

#[test]
fn scalar_row_placement_matches_ordered_point_repairs_for_arbitrary_widths() {
    for cols in 1..=9 {
        for origin_rows in 0..3 {
            let mut seed = seeded(cols, 3, false);
            seed.shift_up(0, origin_rows);
            for col in 0..cols {
                for width in [1u8, 2] {
                    if col + width as u16 > cols {
                        continue;
                    }
                    for pattern in 0..64usize {
                        let mut actual = seed.clone();
                        for r in 0..3 {
                            for c in 0..cols {
                                let mut cell = *actual.cell(r, c).unwrap();
                                cell.width = ((pattern >> ((c as usize % 3) * 2)) & 3) as u8;
                                actual.set_cell(r, c, cell);
                            }
                        }
                        actual.pen.bg_rgb = Some((31, 42, 53));
                        let mut reference = actual.clone();
                        actual.place_glyph_in_row(1, col, cols - 1, '界', width);
                        reference.place_glyph_at_points(1, col, cols - 1, '界', width);
                        assert_eq!(actual, reference, "cols={cols} origin={origin_rows} col={col} width={width} pattern={pattern}");
                        assert_eq!(actual.serialize(), reference.serialize());
                    }
                }
            }
        }
    }
}

#[test]
fn scalar_join_prefilter_preserves_cluster_edges_and_capacity() {
    for cols in [1, 2, 7] {
        for origin_rows in 0..3 {
            for (base, last_mark) in [
                ('A', '\u{1f1e8}'),
                ('界', '\u{200d}'),
                ('\u{1f44d}', '\u{200d}'),
                ('\u{1f1e6}', '\u{1f1e8}'),
                ('\u{1f1e7}', '\u{200d}'),
            ] {
                for combining_len in [0, 1, MAX_COMBINING as u8, u8::MAX] {
                    for col in 0..=cols {
                        for joiner_open in [false, true] {
                            let mut seed = seeded(cols, 3, false);
                            seed.shift_up(0, origin_rows);
                            seed.row = 1;
                            seed.col = col;
                            seed.joiner_open = joiner_open;
                            for c in 0..cols {
                                let mut cell = *seed.cell(1, c).unwrap();
                                cell.ch = base;
                                cell.combining_len = combining_len;
                                if combining_len > 0 {
                                    let last = (combining_len as usize).min(MAX_COMBINING) - 1;
                                    cell.combining[last] = last_mark;
                                }
                                seed.set_cell(1, c, cell);
                            }
                            for ch in [
                                'x',
                                'é',
                                '界',
                                '\u{1f3fb}',
                                '\u{1f1e9}',
                                '\u{200d}',
                                '\u{0301}',
                            ] {
                                let mut actual = seed.clone();
                                let mut reference = seed.clone();
                                dense(|| reference.put(ch));
                                actual.put(ch);
                                assert_eq!(actual, reference, "cols={cols} origin={origin_rows} base={base} len={combining_len} col={col} joiner={joiner_open} ch={ch}");
                                assert_eq!(actual.serialize(), reference.serialize());
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn bulk_row_copy_matches_cell_loop_for_every_small_origin_row_pair_and_margin() {
    for (cols, rows) in [(1, 1), (2, 3), (5, 4), (8, 5), (13, 4)] {
        for origin_rows in 0..rows {
            let mut seed = seeded(cols, rows, false);
            if origin_rows > 0 {
                seed.shift_up(0, origin_rows);
            }
            for src in (0..rows).chain([u16::MAX]) {
                for dst in (0..rows).chain([u16::MAX]) {
                    for left in 0..cols {
                        for right in left..cols {
                            let mut actual = seed.clone();
                            actual.left = left;
                            actual.right = right;
                            let mut reference = actual.clone();
                            let from = reference.idx(src, left);
                            let to = reference.idx(dst, left);
                            let len = (right - left + 1) as usize;
                            reference.copy_span_cells(from, to, len);
                            actual.copy_span(src, dst);
                            assert_eq!(actual, reference, "cols={cols} rows={rows} origin={origin_rows} src={src} dst={dst} left={left} right={right}");
                            assert_eq!(actual.serialize(), reference.serialize());
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn bulk_grid_copy_rejects_noncontiguous_overlap_and_invalid_ranges_without_mutation() {
    let mut screen = seeded(5, 4, false);
    screen.shift_up(0, 2);
    for (from, to, len) in [
        (0, 1, 3),
        (1, 0, 3),
        (8, 0, 4),
        (0, 8, 4),
        (usize::MAX, 0, 1),
        (0, usize::MAX, 1),
        (0, 1, usize::MAX),
    ] {
        let before = screen.clone();
        assert!(!screen.grid.copy_span(from, to, len));
        assert_eq!(screen, before);
    }
    let before = screen.clone();
    assert!(screen.grid.copy_span(2, 2, usize::MAX));
    assert!(screen.grid.copy_span(usize::MAX, 0, 0));
    assert_eq!(screen, before);
}

#[test]
fn row_copy_boundaries_match_point_oracle_across_origins_scrolls_and_line_edits() {
    fn wide_pair(screen: &mut Screen, row: u16, col: u16) {
        let lead = Cell {
            ch: '界',
            width: 2,
            ..*screen.cell(row, col).unwrap()
        };
        screen.set_cell(row, col, lead);
        screen.set_cell(
            row,
            col + 1,
            Cell {
                ch: ' ',
                width: 0,
                combining: ['\0'; MAX_COMBINING],
                combining_len: 0,
                ..lead
            },
        );
    }
    for width in [6u16, 8, 127, 128, 129, 255, 256, 257] {
        let (cols, rows, left) = (width + 4, 6, 2);
        let right = left + width - 1;
        let mut seed = seeded(cols, rows, false);
        for row in 0..rows {
            for col in 0..cols {
                let mut cell = *seed.cell(row, col).unwrap();
                cell.width = 1;
                seed.set_cell(row, col, cell);
            }
            // One pair crosses the left margin; another stays inside the right
            // margin. At widths 129/257 the latter crosses a copy-chunk boundary,
            // and its row-specific rendition makes a missed one-cell tail visible.
            wide_pair(&mut seed, row, left - 1);
            wide_pair(&mut seed, row, right - 1);
        }
        for rotated in [false, true] {
            let mut actual = seed.clone();
            if rotated {
                actual.shift_up(0, 2);
                for row in 0..rows {
                    for col in 0..cols {
                        actual.set_cell(row, col, *seed.cell(row, col).unwrap());
                    }
                }
                assert_ne!(actual.grid.origin, 0);
            }
            let mut reference = seed.clone();
            let setup = [
                ScreenOp::SetMode {
                    params: vec![69],
                    set: true,
                },
                ScreenOp::SetLeftRightMargins { left, right },
                ScreenOp::SetScrollRegion {
                    top: 1,
                    bottom: rows - 2,
                },
                ScreenOp::MoveTo(2, left),
                ScreenOp::SetSgrRgb {
                    fg: Color::Default,
                    fg_rgb: Some((51, 62, 73)),
                    bg: Color::Default,
                    bg_rgb: Some((83, 94, 105)),
                    attrs: 0,
                },
            ];
            dense(|| apply_ops_to(&mut reference, &setup));
            apply_ops_to(&mut actual, &setup);
            compare(&actual, &reference);
            for op in [
                ScreenOp::ScrollUp(0),
                ScreenOp::ScrollUp(1),
                ScreenOp::ScrollUp(2),
                ScreenOp::ScrollDown(0),
                ScreenOp::ScrollDown(1),
                ScreenOp::ScrollDown(2),
                ScreenOp::InsertLines(0),
                ScreenOp::InsertLines(1),
                ScreenOp::InsertLines(2),
                ScreenOp::DeleteLines(0),
                ScreenOp::DeleteLines(1),
                ScreenOp::DeleteLines(2),
            ] {
                let mut a = actual.clone();
                let mut r = reference.clone();
                dense(|| apply_ops_to(&mut r, std::slice::from_ref(&op)));
                apply_ops_to(&mut a, &[op]);
                compare(&a, &r);
            }
        }
    }
}
