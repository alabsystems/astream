// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::render::frame_hash;

// Frozen from main screen.rs SHA-256
// 4db04efa7fc71b37402ee69c8f02b0fdf6a3bcfe7d8e744feb631fba33cbe93c.
// Only the method name/visibility changes; the old presence/count scans remain.
mod reference {
    use super::*;

    const fn underline_ext(
        attrs: u8,
        underline: Underline,
        ul: Color,
        ul_rgb: Option<(u8, u8, u8)>,
    ) -> bool {
        !matches!(underline, Underline::None | Underline::Single)
            || !matches!(ul, Color::Default)
            || ul_rgb.is_some()
            || attrs & WIRE_UNDERLINE != 0
    }

    const fn cell_underline_ext(c: &Cell) -> bool {
        underline_ext(c.attrs, c.underline, c.ul, c.ul_rgb)
    }

    impl Screen {
        pub(super) fn serialize_into_reference<S: ByteSink>(&self, out: &mut S) {
            out.extend_from_slice(&encode_screen_header(
                self.cols,
                self.rows,
                self.row,
                self.col,
                self.cursor_visible,
                self.altscreen,
            ));
            self.grid
                .for_each(|cell| out.extend_from_slice(&encode_cell_bytes(cell)));
            // Internal state that derived `Eq` distinguishes but the grid alone does
            // not — without these, two unequal screens could serialize identically
            // (e.g. a pending SGR pen with nothing yet printed). The grid length is
            // fixed by cols*rows above, so what follows is self-delimiting.
            out.extend_from_slice(&encode_pen_bytes(
                self.pen.fg,
                self.pen.bg,
                self.pen.wire_attrs(),
            ));
            match self.saved_cursor {
                Some(saved) => out.extend_from_slice(&encode_saved_cursor_bytes(
                    saved.row,
                    saved.col,
                    saved.pen.fg,
                    saved.pen.bg,
                    saved.pen.wire_attrs(),
                )),
                None => out.extend_from_slice(&[0]),
            }
            match self.alt_saved_cursor {
                Some(saved) => out.extend_from_slice(&encode_saved_cursor_bytes(
                    saved.row,
                    saved.col,
                    saved.pen.fg,
                    saved.pen.bg,
                    saved.pen.wire_attrs(),
                )),
                None => out.extend_from_slice(&[0]),
            }
            match &self.inactive {
                Some(cells) => {
                    out.extend_from_slice(&[1]);
                    out.extend_from_slice(&encode_u32_le_bytes(cells.len() as u32));
                    cells.for_each(|cell| out.extend_from_slice(&encode_cell_bytes(cell)));
                }
                None => out.extend_from_slice(&[0]),
            }
            out.extend_from_slice(&encode_scroll_region_bytes(
                self.scroll_top,
                self.scroll_bottom,
            ));
            // The state the fold gained after this encoding was fixed, written only
            // when some of it is away from its reset value: every screen an earlier
            // fold could make keeps its bytes (and its pinned hashes). It stays
            // injective because everything above is self-delimiting (a decoder
            // knows where it ends), so the trailer is either absent or starts with
            // its own tag byte.
            let modes = encode_modes_bytes(
                [
                    self.origin,
                    self.insert,
                    self.newline,
                    self.lrmm,
                    self.margin_wrap,
                ],
                self.saved_cursor
                    .map_or([false; 2], |s| [s.origin, s.margin_wrap]),
                self.alt_saved_cursor
                    .map_or([false; 2], |s| [s.origin, s.margin_wrap]),
            );
            // The character sets in use and as each DECSC slot saved them (an
            // empty slot reads as the reset sets, all zero).
            let charsets = [
                self.charsets.encode(),
                self.saved_cursor.map_or(0, |s| s.charsets.encode()),
                self.alt_saved_cursor.map_or(0, |s| s.charsets.encode()),
            ];
            let margins = encode_scroll_region_bytes(self.left, self.right);
            let full_width = encode_scroll_region_bytes(0, self.cols.saturating_sub(1));
            if modes != MODES_AT_RESET || charsets != [0; 3] || margins != full_width {
                out.extend_from_slice(&[1]);
                out.extend_from_slice(&modes);
                out.extend_from_slice(&charsets);
                out.extend_from_slice(&margins);
            }
            // Tag-2 extension trailer for 24-bit truecolour (`fg_rgb` / `bg_rgb`) and
            // per-cell zero-width combining marks: emitted ONLY when any cell, pen, or
            // saved-cursor slot carries extended colour or combining state, keeping every
            // non-truecolour / non-combining screen byte-identical to its pinned digest
            // while preserving strict `s1 == s2 <=> s1.serialize() == s2.serialize()`
            // injectivity across all reachable and caller-constructed `Cell` values.
            let inactive_has_ext = match &self.inactive {
                Some(cells) => slice_has_ext_cells(cells),
                None => false,
            };
            let saved_has_rgb = match self.saved_cursor {
                Some(s) => pen_has_rgb(s.pen),
                None => false,
            };
            let alt_saved_has_rgb = match self.alt_saved_cursor {
                Some(s) => pen_has_rgb(s.pen),
                None => false,
            };
            if pen_has_rgb(self.pen)
                || saved_has_rgb
                || alt_saved_has_rgb
                || slice_has_ext_cells(&self.grid)
                || inactive_has_ext
            {
                out.extend_from_slice(&[2]);
                emit_opt_rgb(out, self.pen.fg_rgb);
                emit_opt_rgb(out, self.pen.bg_rgb);
                if let Some(s) = self.saved_cursor {
                    emit_opt_rgb(out, s.pen.fg_rgb);
                    emit_opt_rgb(out, s.pen.bg_rgb);
                }
                if let Some(s) = self.alt_saved_cursor {
                    emit_opt_rgb(out, s.pen.fg_rgb);
                    emit_opt_rgb(out, s.pen.bg_rgb);
                }
                emit_ext_cells(out, &self.grid);
                if let Some(cells) = &self.inactive {
                    emit_ext_cells(out, cells);
                }
            }
            // Tag-3 extension trailer for non-unit cell widths (`width != 1`, e.g. wide
            // CJK/emoji lead `width = 2` and spacer `width = 0`): emitted ONLY when some
            // cell carries `width != 1`, keeping every narrow screen byte-identical to its
            // pinned digest while preserving strict `Eq <=> serialize()` injectivity.
            let inactive_has_wide = match &self.inactive {
                Some(cells) => slice_has_wide_cells(cells),
                None => false,
            };
            if slice_has_wide_cells(&self.grid) || inactive_has_wide {
                out.extend_from_slice(&[3]);
                emit_wide_cells(out, &self.grid);
                if let Some(cells) = &self.inactive {
                    emit_wide_cells(out, cells);
                }
            }
            // Tag-4 extension trailer for session DEC private modes (`?1` DECCKM,
            // `?1004` focus reporting, `?2004` bracketed paste, `?2026` synchronized
            // output): emitted ONLY when at least one mode is set, preserving byte
            // identity for every reset-mode screen and strict `Eq <=> serialize()`
            // injectivity across `emit_ops`/`apply_ops` and raw `fold`.
            let ext_modes = (self.app_cursor_keys as u8)
                | ((self.focus_events as u8) << 1)
                | ((self.bracketed_paste as u8) << 2)
                | ((self.synchronized_output as u8) << 3)
                | ((self.joiner_open as u8) << 4)
                | ((self.stepped_onto_margin as u8) << 5);
            if ext_modes != 0 {
                out.extend_from_slice(&[4, ext_modes]);
            }
            // Tag-5 extension trailer for deep inline combining marks (`combining[4..16]` or
            // `combining_len > 4`): emitted ONLY when some cell carries more than 4 combining
            // marks, keeping every <=4-mark screen byte-identical to its pinned digest while
            // preserving strict `Eq <=> serialize()` injectivity up to `MAX_COMBINING = 16`.
            let inactive_has_deep = match &self.inactive {
                Some(cells) => slice_has_deep_combining_cells(cells),
                None => false,
            };
            if slice_has_deep_combining_cells(&self.grid) || inactive_has_deep {
                out.extend_from_slice(&[5]);
                emit_deep_combining_cells(out, &self.grid);
                if let Some(cells) = &self.inactive {
                    emit_deep_combining_cells(out, cells);
                }
            }
            // Tag-6 extension trailer for the underline beyond the attribute byte's
            // [`WIRE_UNDERLINE`] (a style other than none or single, an underline colour):
            // emitted ONLY when the pen, a saved pen or some cell has one, so every screen
            // whose underlines are single and uncoloured keeps the bytes it had when the
            // fold knew one underline, and `Eq <=> serialize()` stays strict. It names the
            // pen and each saved pen in full, then the cells that need it by index.
            let saved_ul = self.saved_cursor.is_some_and(|s| s.pen.underline_ext());
            let alt_saved_ul = self.alt_saved_cursor.is_some_and(|s| s.pen.underline_ext());
            let inactive_ul = self.inactive.as_ref().is_some_and(slice_has_underline_ext);
            if self.pen.underline_ext()
                || saved_ul
                || alt_saved_ul
                || slice_has_underline_ext(&self.grid)
                || inactive_ul
            {
                out.extend_from_slice(&[6]);
                emit_underline_pen(out, self.pen);
                if let Some(s) = self.saved_cursor {
                    emit_underline_pen(out, s.pen);
                }
                if let Some(s) = self.alt_saved_cursor {
                    emit_underline_pen(out, s.pen);
                }
                emit_underline_cells(out, &self.grid);
                if let Some(cells) = &self.inactive {
                    emit_underline_cells(out, cells);
                }
            }
        }
    }

    fn slice_has_underline_ext(cells: &Grid) -> bool {
        cells.any(cell_underline_ext)
    }

    fn emit_underline_cells<S: ByteSink>(out: &mut S, cells: &Grid) {
        let count = cells.count_if(cell_underline_ext);
        out.extend_from_slice(&encode_u32_le_bytes(count));
        cells.for_each_indexed(|idx, c| {
            if cell_underline_ext(c) {
                out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
                emit_underline(out, c.attrs, c.underline, c.ul, c.ul_rgb);
            }
        });
    }

    const fn cell_has_ext(c: &Cell) -> bool {
        c.fg_rgb.is_some()
            || c.bg_rgb.is_some()
            || c.combining_len != 0
            || c.combining[0] != '\0'
            || c.combining[1] != '\0'
            || c.combining[2] != '\0'
            || c.combining[3] != '\0'
    }

    fn slice_has_ext_cells(cells: &Grid) -> bool {
        cells.any(cell_has_ext)
    }

    fn emit_ext_cells<S: ByteSink>(out: &mut S, cells: &Grid) {
        let count = cells.count_if(cell_has_ext);
        out.extend_from_slice(&encode_u32_le_bytes(count));
        cells.for_each_indexed(|idx, c| {
            if cell_has_ext(c) {
                out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
                emit_opt_rgb(out, c.fg_rgb);
                emit_opt_rgb(out, c.bg_rgb);
                out.extend_from_slice(&[c.combining_len]);
                for &m in &c.combining[..4] {
                    out.extend_from_slice(&encode_u32_le_bytes(m as u32));
                }
            }
        });
    }

    const fn cell_has_deep_combining(c: &Cell) -> bool {
        if c.combining_len > 4 {
            return true;
        }
        let mut k = 4usize;
        while k < MAX_COMBINING {
            if c.combining[k] != '\0' {
                return true;
            }
            k += 1;
        }
        false
    }

    fn slice_has_deep_combining_cells(cells: &Grid) -> bool {
        cells.any(cell_has_deep_combining)
    }

    fn emit_deep_combining_cells<S: ByteSink>(out: &mut S, cells: &Grid) {
        let count = cells.count_if(cell_has_deep_combining);
        out.extend_from_slice(&encode_u32_le_bytes(count));
        cells.for_each_indexed(|idx, c| {
            if cell_has_deep_combining(c) {
                out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
                for &m in &c.combining[4..MAX_COMBINING] {
                    out.extend_from_slice(&encode_u32_le_bytes(m as u32));
                }
            }
        });
    }

    fn slice_has_wide_cells(cells: &Grid) -> bool {
        cells.any(|cell| cell.width != 1)
    }

    fn emit_wide_cells<S: ByteSink>(out: &mut S, cells: &Grid) {
        let count = cells.count_if(|cell| cell.width != 1);
        out.extend_from_slice(&encode_u32_le_bytes(count));
        cells.for_each_indexed(|idx, c| {
            if c.width != 1 {
                out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
                out.extend_from_slice(&[c.width]);
            }
        });
    }
}

struct ReferenceFnv1a(u64);

impl ByteSink for ReferenceFnv1a {
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        let mut rest = bytes;
        while let &[byte, ref tail @ ..] = rest {
            self.0 ^= byte as u64;
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
            rest = tail;
        }
    }
}

fn reference_hash(screen: &Screen) -> u64 {
    let mut hash = ReferenceFnv1a(0xcbf2_9ce4_8422_2325);
    screen.serialize_into_reference(&mut hash);
    hash.0
}

fn reference_bytes(screen: &Screen) -> Vec<u8> {
    let mut bytes = Vec::new();
    screen.serialize_into_reference(&mut bytes);
    bytes
}

fn compare(screen: &Screen) {
    assert_eq!(screen.serialize(), reference_bytes(screen));
    assert_eq!(frame_hash(screen), reference_hash(screen));
}

fn patterned_cell(marker: u64, kind: u8) -> Cell {
    let mut cell = Cell::BLANK;
    cell.ch = char::from(b'A' + (marker % 26) as u8);
    let kind = if kind == 1 {
        if marker % 257 != 0 {
            0
        } else {
            7
        }
    } else {
        kind
    };
    match kind {
        2 => {
            cell.fg_rgb = Some((marker as u8, 31, 42));
            cell.bg_rgb = Some((53, marker as u8, 64));
            cell.combining[0] = '\u{0301}';
            cell.combining_len = 1;
        }
        3 => cell.width = [0, 1, 2, 7, u8::MAX][marker as usize % 5],
        4 => {
            // Unused deep marks still belong to the encoding, even when tag2
            // has no reason to appear and combining_len remains zero.
            cell.combining[12] = '\u{200d}';
        }
        5 => {
            cell.attrs = marker as u8;
            cell.underline = Underline::Curly;
            cell.ul = Color::Indexed(marker as u8);
            cell.ul_rgb = Some((17, 28, marker as u8));
        }
        7 => {
            cell.fg = Color::Indexed(marker as u8);
            cell.bg = Color::Indexed((marker >> 8) as u8);
            cell.fg_rgb = Some((marker as u8, 31, 42));
            cell.bg_rgb = Some((53, marker as u8, 64));
            cell.attrs = marker as u8;
            cell.underline = [
                Underline::None,
                Underline::Single,
                Underline::Double,
                Underline::Curly,
                Underline::Dotted,
                Underline::Dashed,
            ][marker as usize % 6];
            cell.ul = Color::Indexed((marker >> 16) as u8);
            cell.ul_rgb = Some((17, 28, marker as u8));
            cell.width = [0, 1, 2, 7, u8::MAX][marker as usize % 5];
            cell.combining[0] = '\u{0301}';
            cell.combining[12] = '\u{200d}';
            cell.combining_len = [0, 1, 4, 5, MAX_COMBINING as u8, u8::MAX][marker as usize % 6];
        }
        _ => {}
    }
    cell
}

fn populate(screen: &mut Screen, kind: u8, seed: u64) {
    let (cols, rows) = screen.dims();
    for row in 0..rows {
        for col in 0..cols {
            let marker = seed + u64::from(row) * u64::from(cols) + u64::from(col);
            screen.set_cell(row, col, patterned_cell(marker, kind));
        }
    }
}

fn case(cols: u16, rows: u16, kind: u8, seed: u64, alternate: u8) -> Screen {
    let mut screen = Screen::new(cols, rows);
    if rows > 1 {
        screen.shift_up(0, 1);
    }
    populate(&mut screen, kind, seed);
    if kind == 8 {
        // Cell counts are all zero; only pens and saved slots request trailers.
        screen.pen.fg_rgb = Some((1, 2, 3));
        screen.pen.underline = Underline::Curly;
        screen.pen.ul_rgb = Some((4, 5, 6));
    }
    screen.save_cursor();
    if alternate > 0 {
        screen.enter_alt();
        if rows > 1 {
            screen.shift_down(0, rows - 1);
        }
        populate(&mut screen, kind, seed + 17);
        if kind == 8 {
            screen.pen.bg_rgb = Some((7, 8, 9));
            screen.pen.attrs = 0xff;
        }
        screen.save_cursor();
        if alternate == 2 {
            screen.leave_alt();
        }
    }
    screen
}

#[test]
fn serialization_matches_frozen_bytes_for_rotated_active_and_inactive_grids() {
    for (cols, rows) in [(1, 1), (2, 3), (9, 5), (17, 8)] {
        for kind in [0, 1, 2, 3, 4, 5, 7, 8] {
            for alternate in 0..3 {
                let mut screen = case(cols, rows, kind, 239, alternate);
                compare(&screen);
                screen.resize(cols.saturating_add(2), rows.saturating_add(1));
                compare(&screen);
                screen.enter_alt();
                compare(&screen);
                screen.leave_alt();
                compare(&screen);
            }
        }
    }
}

#[test]
fn raw_underline_bits_and_inactive_combining_slots_keep_exact_trailers() {
    for attrs in 0..=u8::MAX {
        for style in [
            Underline::None,
            Underline::Single,
            Underline::Double,
            Underline::Curly,
            Underline::Dotted,
            Underline::Dashed,
        ] {
            let mut screen = case(3, 2, 0, 1, 2);
            let mut cell = patterned_cell(u64::from(attrs), 7);
            cell.attrs = attrs;
            cell.underline = style;
            screen.set_cell(1, 2, cell);
            screen.pen.attrs = attrs;
            screen.pen.underline = style;
            screen.save_cursor();
            compare(&screen);
            screen.enter_alt();
            compare(&screen);
        }
    }
}

#[test]
fn zero_count_grids_keep_headers_when_only_the_other_grid_or_saved_pen_needs_a_tag() {
    for active in [false, true] {
        for mask in 0..16u8 {
            let mut screen = case(7, 4, 0, 1, 1);
            if active {
                screen.leave_alt();
            }
            let mut cell = Cell::BLANK;
            if mask & 1 != 0 {
                cell.fg_rgb = Some((1, 2, 3));
                cell.combining[0] = '\u{0301}';
            }
            if mask & 2 != 0 {
                cell.width = u8::MAX;
            }
            if mask & 4 != 0 {
                cell.combining[15] = '\u{200d}';
            }
            if mask & 8 != 0 {
                cell.attrs = WIRE_UNDERLINE;
            }
            screen.set_cell(2, 3, cell);
            compare(&screen);
            if active {
                screen.enter_alt();
            } else {
                screen.leave_alt();
            }
            compare(&screen);
        }
    }
    let mut screen = case(7, 4, 8, 1, 2);
    screen.pen = Pen::reset();
    compare(&screen);
}

fn measured_pair(
    repetitions: usize,
    mut previous: impl FnMut() -> u64,
    mut current: impl FnMut() -> u64,
) -> (u128, u128) {
    use std::hint::black_box;
    use std::time::Instant;
    let mut previous_times = [0; 8];
    let mut current_times = [0; 8];
    let measure = |f: &mut dyn FnMut() -> u64| {
        let start = Instant::now();
        let mut check = 0;
        for _ in 0..repetitions {
            check ^= black_box(f());
        }
        black_box(check);
        start.elapsed().as_nanos() / repetitions as u128
    };
    // Warm both variants before alternating their order within one process.
    black_box(previous());
    black_box(current());
    for run in 0..8 {
        if run % 2 == 0 {
            previous_times[run] = measure(&mut previous);
            current_times[run] = measure(&mut current);
        } else {
            current_times[run] = measure(&mut current);
            previous_times[run] = measure(&mut previous);
        }
    }
    previous_times.sort_unstable();
    current_times.sort_unstable();
    (
        (previous_times[3] + previous_times[4]) / 2,
        (current_times[3] + current_times[4]) / 2,
    )
}

#[test]
#[ignore = "manual alternating serialization, hash and fold-plus-hash CPU benchmark"]
fn serialization_count_scan_microbench() {
    use std::hint::black_box;
    for (cols, rows) in [(80, 24), (120, 50), (240, 100)] {
        for (kind, label) in [
            (0, "ordinary"),
            (1, "sparse"),
            (2, "extended"),
            (3, "wide"),
            (4, "deep"),
            (5, "underline"),
            (7, "malformed"),
            (8, "pen-only"),
        ] {
            for alternate in [0, 2] {
                let screen = case(cols, rows, kind, 239, alternate);
                compare(&screen);
                let cells = usize::from(cols) * usize::from(rows);
                let repetitions = (131_072 / cells).clamp(4, 64);
                let (previous, current) = measured_pair(
                    repetitions,
                    || black_box(reference_bytes(black_box(&screen))).len() as u64,
                    || black_box(black_box(&screen).serialize()).len() as u64,
                );
                println!("SERIALIZATION_COUNTS operation=serialize cols={cols} rows={rows} kind={label} inactive={} repetitions={repetitions} previous_ns={previous} current_ns={current} speedup={:.3}", alternate > 0, previous as f64 / current.max(1) as f64);
                let (previous, current) = measured_pair(
                    repetitions,
                    || reference_hash(black_box(&screen)),
                    || frame_hash(black_box(&screen)),
                );
                println!("SERIALIZATION_COUNTS operation=frame_hash cols={cols} rows={rows} kind={label} inactive={} repetitions={repetitions} previous_ns={previous} current_ns={current} speedup={:.3}", alternate > 0, previous as f64 / current.max(1) as f64);
            }
        }
        for (label, line) in [
            ("ordinary", "ordinary text and numbers 0123456789\r\n"),
            (
                "styled",
                "\x1b[38;2;1;2;3m\x1b[4:3mcoloured text\x1b[0m e\u{0301}界\r\n",
            ),
            ("alternate", "\x1b[?47hALT\r\n\x1b[?47lmain text\r\n"),
        ] {
            let records = [Record::Out(line.repeat(usize::from(rows) * 2).into_bytes())];
            let folded = fold(cols, rows, &records);
            compare(&folded);
            let repetitions = 16;
            let (previous, current) = measured_pair(
                repetitions,
                || {
                    let screen = fold(cols, rows, black_box(&records));
                    reference_hash(black_box(&screen))
                },
                || {
                    let screen = fold(cols, rows, black_box(&records));
                    frame_hash(black_box(&screen))
                },
            );
            println!("SERIALIZATION_COUNTS operation=fold_hash cols={cols} rows={rows} kind={label} inactive=varies repetitions={repetitions} previous_ns={previous} current_ns={current} speedup={:.3}", previous as f64 / current.max(1) as f64);
        }
    }
}
