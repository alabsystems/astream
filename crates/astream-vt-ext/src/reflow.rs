// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Soft-wrap logical-line terminal grid reflow (`Astream.Term.TlaGridReflow`).
//!
//! Reflows a flattened `old_cols * old_rows` [`Cell`] viewport into `(new_cols, new_rows)`
//! using soft-wrap row continuation flags (`wrapped_rows[r] == true` when row `r`
//! soft-wrapped into row `r + 1`), keeping East Asian wide glyphs (`width == 2` lead +
//! `width == 0` spacer) intact and preserving [`astream_term::Screen::serialize`] byte-for-byte
//! injectivity without altering [`astream_term::Screen`]'s serialized representation.

#![allow(clippy::manual_clamp)]

use astream_term::screen::Cell;

#[cfg(clean_islands)]
#[path = "reflow_island.rs"]
mod reflow_island;
#[cfg(clean_islands)]
pub use reflow_island::{reflow_col_clamp, reflow_row_clamp};

/// Clamp reflowed cursor column `col` to `0..=max_col` (`Astream.Term.TlaGridReflow`).
#[cfg(not(clean_islands))]
#[must_use]
pub const fn reflow_col_clamp(col: u64, max_col: u64) -> u64 {
    if col < max_col {
        col
    } else {
        max_col
    }
}

/// Clamp reflowed cursor row `row` to `0..=max_row` (`Astream.Term.TlaGridReflow`).
#[cfg(not(clean_islands))]
#[must_use]
pub const fn reflow_row_clamp(row: u64, max_row: u64) -> u64 {
    if row < max_row {
        row
    } else {
        max_row
    }
}

contract_fn! {
    /// Kernel-certified bounds check that reflowed cursor column `col` lies strictly
    /// within viewport width `cols` (`col < cols`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `reflow_cursor_in_grid_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn reflow_cursor_in_grid(col: u16, cols: u16) -> bool
    clauses [ensures result == (col < cols)]
    {
        col < cols
    }
}

/// Maximum viewport edge (`cols` or `rows`), matching `screen::MAX_DIM`.
pub const MAX_REFLOW_DIM: u16 = 512;

const MAX_REFLOW_GRID_CELLS: usize = (MAX_REFLOW_DIM as usize) * (MAX_REFLOW_DIM as usize);

fn blank_reflow_row(cols_cap: usize) -> Vec<Cell> {
    let cap = if cols_cap < (MAX_REFLOW_DIM as usize) {
        cols_cap
    } else {
        MAX_REFLOW_DIM as usize
    };
    let mut row = {
        let _ = cap;
        Vec::new()
    };
    let mut i = 0usize;
    while i < cap {
        row.push(Cell::BLANK);
        i = i.saturating_add(1);
    }
    row
}

fn blank_reflow_grid(cols: u16, rows: u16) -> Vec<Cell> {
    let raw_n = (cols as usize).saturating_mul(rows as usize);
    let n = if raw_n < MAX_REFLOW_GRID_CELLS {
        raw_n
    } else {
        MAX_REFLOW_GRID_CELLS
    };
    let mut grid = {
        let _ = n;
        Vec::new()
    };
    let mut i = 0usize;
    while i < n {
        grid.push(Cell::BLANK);
        i = i.saturating_add(1);
    }
    grid
}

fn row_used_len(cells: &[Cell], row: u16, cols: u16, is_wrapped: bool) -> usize {
    let row_start = (row as usize).saturating_mul(cols as usize);
    let row_end = row_start.saturating_add(cols as usize);
    let Some(slice) = cells.get(row_start..row_end) else {
        return 0;
    };
    if is_wrapped {
        return slice.len();
    }
    let mut rest = slice;
    while let [ref head @ .., ref last] = *rest {
        if *last == Cell::BLANK {
            rest = head;
        } else {
            break;
        }
    }
    rest.len()
}

fn slice_all_blank(mut cells: &[Cell]) -> bool {
    while let [ref cell, ref tail @ ..] = *cells {
        if *cell != Cell::BLANK {
            return false;
        }
        cells = tail;
    }
    true
}

/// Reflow `old` (`old_cols * old_rows`) into `(new_cols, new_rows)` using `wrapped_rows`
/// (`wrapped_rows.get(r) == Some(&true)` when row `r` soft-wrapped into row `r + 1`),
/// returning `(new_grid, new_wrapped_rows, new_cursor_row, new_cursor_col)`.
///
/// Wide glyphs (`width == 2` lead + `width == 0` spacer) are kept whole: if a wide glyph
/// reaches the last column of a destination row (`dst_col + 1 == new_cols` with `new_cols >= 2`),
/// the last column takes [`Cell::BLANK`] and the wide pair wraps onto the next row. When total
/// reflowed rows exceed `new_rows`, the bottom-most `new_rows` rows are retained.
#[must_use]
pub fn reflow_wrapped_grid(
    old: &[Cell],
    old_dims: (u16, u16),
    wrapped_rows: &[bool],
    cursor: (u16, u16),
    new_dims: (u16, u16),
) -> (Vec<Cell>, Vec<bool>, u16, u16) {
    let (old_cols, old_rows) = old_dims;
    let (cursor_row, cursor_col) = cursor;
    let (raw_cols, raw_rows) = new_dims;
    let new_cols = if raw_cols < 1 {
        1
    } else if raw_cols > MAX_REFLOW_DIM {
        MAX_REFLOW_DIM
    } else {
        raw_cols
    };
    let new_rows = if raw_rows < 1 {
        1
    } else if raw_rows > MAX_REFLOW_DIM {
        MAX_REFLOW_DIM
    } else {
        raw_rows
    };
    let cols_cap = if (new_cols as usize) < (MAX_REFLOW_DIM as usize) {
        new_cols as usize
    } else {
        MAX_REFLOW_DIM as usize
    };
    let rows_cap = if (new_rows as usize) < (MAX_REFLOW_DIM as usize) {
        new_rows as usize
    } else {
        MAX_REFLOW_DIM as usize
    };
    let old_cols_nonzero = if (old_cols as usize) < 1 {
        1
    } else {
        old_cols as usize
    };
    let prod_rows = (old_rows as usize).saturating_mul(old_cols_nonzero);
    let bounded_prod = if prod_rows < 4096 { prod_rows } else { 4096 };
    let init_cap = if bounded_prod > rows_cap {
        bounded_prod
    } else {
        rows_cap
    };

    let mut out_rows: Vec<Vec<Cell>> = {
        let _ = init_cap;
        Vec::new()
    };
    let mut out_wrapped: Vec<bool> = {
        let _ = init_cap;
        Vec::new()
    };
    let mut mapped_row: usize = 0;
    let mut mapped_col: u16 = 0;
    let mut cursor_mapped = false;

    let mut r = 0u16;
    while r < old_rows {
        let mut end_r = r;
        while (end_r as usize).saturating_add(1) < (old_rows as usize)
            && matches!(wrapped_rows.get(end_r as usize), Some(true))
        {
            end_r = end_r.saturating_add(1);
        }

        let mut cur_line: Vec<Cell> = blank_reflow_row(cols_cap);
        let mut dst_c: u16 = 0;

        let mut sr = r;
        while sr <= end_r {
            let is_cont = sr < end_r;
            let used = row_used_len(old, sr, old_cols, is_cont);
            let effective_used = if sr == cursor_row {
                let c_bound = if (cursor_col as usize) < (old_cols as usize) {
                    cursor_col as usize
                } else {
                    old_cols as usize
                };
                if used > c_bound {
                    used
                } else {
                    c_bound
                }
            } else {
                used
            };
            let row_base = (sr as usize).saturating_mul(old_cols as usize);

            if effective_used == 0 && sr == cursor_row && !cursor_mapped {
                mapped_row = out_rows.len();
                mapped_col = dst_c;
                cursor_mapped = true;
            }

            let mut sc = 0usize;
            while sc < effective_used {
                let Some(&cell) = old.get(row_base.saturating_add(sc)) else {
                    break;
                };
                if cell.width == 0 {
                    sc = sc.saturating_add(1);
                    continue;
                }
                let at_cursor = sr == cursor_row && (sc as u16) == cursor_col && !cursor_mapped;
                if cell.width == 2 {
                    if new_cols < 2 {
                        if dst_c >= new_cols {
                            out_rows.push(cur_line);
                            out_wrapped.push(true);
                            cur_line = blank_reflow_row(cols_cap);
                            dst_c = 0;
                        }
                        if at_cursor {
                            mapped_row = out_rows.len();
                            mapped_col = dst_c;
                            cursor_mapped = true;
                        }
                        if let Some(slot) = cur_line.get_mut(dst_c as usize) {
                            *slot = Cell::BLANK;
                        }
                        dst_c = dst_c.saturating_add(1);
                    } else {
                        if dst_c.saturating_add(1) >= new_cols {
                            if let Some(slot) = cur_line.get_mut(dst_c as usize) {
                                *slot = Cell::BLANK;
                            }
                            out_rows.push(cur_line);
                            out_wrapped.push(true);
                            cur_line = blank_reflow_row(cols_cap);
                            dst_c = 0;
                        }
                        if at_cursor {
                            mapped_row = out_rows.len();
                            mapped_col = dst_c;
                            cursor_mapped = true;
                        }
                        if let Some(slot) = cur_line.get_mut(dst_c as usize) {
                            *slot = cell;
                        }
                        let spacer_idx = row_base.saturating_add(sc).saturating_add(1);
                        let spacer = match old.get(spacer_idx) {
                            Some(&sp) if sp.width == 0 => sp,
                            _ => Cell {
                                ch: ' ',
                                width: 0,
                                ..cell
                            },
                        };
                        if let Some(slot) = cur_line.get_mut((dst_c as usize).saturating_add(1)) {
                            *slot = spacer;
                        }
                        dst_c = dst_c.saturating_add(2);
                    }
                    sc = sc.saturating_add(2);
                } else {
                    if dst_c >= new_cols {
                        out_rows.push(cur_line);
                        out_wrapped.push(true);
                        cur_line = blank_reflow_row(cols_cap);
                        dst_c = 0;
                    }
                    if at_cursor {
                        mapped_row = out_rows.len();
                        mapped_col = dst_c;
                        cursor_mapped = true;
                    }
                    if let Some(slot) = cur_line.get_mut(dst_c as usize) {
                        *slot = cell;
                    }
                    dst_c = dst_c.saturating_add(1);
                    sc = sc.saturating_add(1);
                }
            }

            if sr == cursor_row && !cursor_mapped {
                mapped_row = out_rows.len();
                let max_col = new_cols.saturating_sub(1);
                mapped_col = if dst_c < max_col { dst_c } else { max_col };
                cursor_mapped = true;
            }
            sr = sr.saturating_add(1);
        }

        out_rows.push(cur_line);
        out_wrapped.push(false);
        r = end_r.saturating_add(1);
    }

    while out_rows.len() > (new_rows as usize) && out_rows.len().saturating_sub(1) > mapped_row {
        let last_idx = out_rows.len().saturating_sub(1);
        let prev_wrapped =
            last_idx > 0 && matches!(out_wrapped.get(last_idx.saturating_sub(1)), Some(true));
        let all_blank = if prev_wrapped {
            false
        } else {
            match out_rows.get(last_idx) {
                Some(row_cells) => slice_all_blank(row_cells.as_slice()),
                None => false,
            }
        };
        if all_blank {
            out_rows.pop();
            out_wrapped.pop();
        } else {
            break;
        }
    }

    let drop_top = out_rows.len().saturating_sub(new_rows as usize);
    let mut flat = blank_reflow_grid(new_cols, new_rows);
    let mut final_wrapped = Vec::new();
    let mut wi = 0usize;
    while wi < rows_cap {
        final_wrapped.push(false);
        wi = wi.saturating_add(1);
    }

    let avail = out_rows.len().saturating_sub(drop_top);
    let kept = if avail < (new_rows as usize) {
        avail
    } else {
        new_rows as usize
    };
    let mut dr = 0usize;
    while dr < kept {
        let src_r = drop_top.saturating_add(dr);
        let dst_base = dr.saturating_mul(new_cols as usize);
        if let Some(src_row) = out_rows.get(src_r) {
            let mut dc = 0usize;
            while dc < (new_cols as usize) {
                if let (Some(&src_cell), Some(dst_slot)) =
                    (src_row.get(dc), flat.get_mut(dst_base.saturating_add(dc)))
                {
                    *dst_slot = src_cell;
                }
                dc = dc.saturating_add(1);
            }
        }
        if dr.saturating_add(1) < (new_rows as usize) {
            if let (Some(&w), Some(w_slot)) = (out_wrapped.get(src_r), final_wrapped.get_mut(dr)) {
                *w_slot = w;
            }
        }
        dr = dr.saturating_add(1);
    }

    let raw_row = mapped_row.saturating_sub(drop_top) as u64;
    let clamped_row = reflow_row_clamp(raw_row, new_rows.saturating_sub(1) as u64) as u16;
    let clamped_col = reflow_col_clamp(mapped_col as u64, new_cols.saturating_sub(1) as u64) as u16;
    let _ = reflow_cursor_in_grid(clamped_col, new_cols);
    (flat, final_wrapped, clamped_row, clamped_col)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ascii_cell(ch: char) -> Cell {
        Cell {
            ch,
            width: 1,
            ..Cell::BLANK
        }
    }

    #[test]
    fn reflow_narrow_then_widen_round_trips_logical_line() {
        let mut old = vec![Cell::BLANK; 10 * 2];
        for (i, ch) in "abcdefgh".chars().enumerate() {
            old[i] = ascii_cell(ch);
        }
        let (narrow, wrapped, nr, nc) =
            reflow_wrapped_grid(&old, (10, 2), &[false, false], (0, 6), (5, 3));
        assert_eq!(wrapped, vec![true, false, false]);
        assert_eq!((nr, nc), (1, 1));
        let row0: String = narrow[0..5].iter().map(|c| c.ch).collect();
        let row1: String = narrow[5..10].iter().map(|c| c.ch).collect();
        assert_eq!(row0, "abcde");
        assert_eq!(row1, "fgh  ");

        let (widened, wrapped2, wr, wc) =
            reflow_wrapped_grid(&narrow, (5, 3), &wrapped, (nr, nc), (10, 2));
        assert_eq!(wrapped2, vec![false, false]);
        assert_eq!((wr, wc), (0, 6));
        let wrow0: String = widened[0..10].iter().map(|c| c.ch).collect();
        assert_eq!(wrow0, "abcdefgh  ");
    }

    #[test]
    fn reflow_keeps_wide_glyph_intact_at_row_edge() {
        let mut old = vec![Cell::BLANK; 6];
        old[0] = ascii_cell('a');
        old[1] = ascii_cell('b');
        old[2] = Cell {
            ch: '漢',
            width: 2,
            ..Cell::BLANK
        };
        old[3] = Cell {
            ch: ' ',
            width: 0,
            ..Cell::BLANK
        };
        let (grid, wrapped, cr, cc) = reflow_wrapped_grid(&old, (6, 1), &[false], (0, 2), (3, 2));
        assert_eq!(wrapped, vec![true, false]);
        assert_eq!((cr, cc), (1, 0));
        assert_eq!(grid[0].ch, 'a');
        assert_eq!(grid[1].ch, 'b');
        assert_eq!(grid[2], Cell::BLANK);
        assert_eq!(grid[3].ch, '漢');
        assert_eq!(grid[3].width, 2);
        assert_eq!(grid[4].width, 0);
        assert!(reflow_cursor_in_grid(cc, 3));
    }
}
