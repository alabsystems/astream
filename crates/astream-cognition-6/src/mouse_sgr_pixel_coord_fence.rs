// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! HiDPI SGR-Pixels (`DECSET ?1016`) and SGR cell (`DECSET ?1006`) mouse coordinate fence
//! (`Astream.Term.TlaMouseSgrPixelFence`).
//!
//! Clamps 1-based terminal cell and Retina pixel mouse reports (`CSI < Cb ; Cx ; Cy M/m`) to the
//! active `aterm` pane viewport `(cols, rows, cell_px_w, cell_px_h)` without integer wraparound,
//! zero-origin underflow, or out-of-pane coordinate leakage during live window resizes.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "mouse_sgr_pixel_coord_fence_island.rs"]
mod mouse_sgr_pixel_coord_fence_island;
#[cfg(clean_islands)]
pub use mouse_sgr_pixel_coord_fence_island::{
    sgr_mouse_coord_clamp_b119, sgr_mouse_seq_advance_b119,
};

#[cfg(not(clean_islands))]
/// Clamp a 1-based mouse coordinate to `max_dim`.
#[must_use]
pub const fn sgr_mouse_coord_clamp_b119(cand_coord: u64, max_dim: u64) -> u64 {
    if cand_coord < max_dim {
        cand_coord
    } else {
        max_dim
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the mouse event sequence counter.
#[must_use]
pub const fn sgr_mouse_seq_advance_b119(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `coord <= max_dim`.
    #[must_use]
    pub const fn sgr_mouse_coord_valid_b119(coord: u64, max_dim: u64) -> bool
    clauses [ensures result == (coord <= max_dim)]
    {
        coord <= max_dim
    }
}

pub const MAX_PANE_CELLS: u64 = 4_096;
pub const MAX_CELL_PX: u64 = 128;

/// Clamped 1-based coordinate pair ready for `CSI < Cb ; X ; Y M/m` emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClampedMousePoint {
    pub x_one_based: u32,
    pub y_one_based: u32,
    pub event_seq: u64,
}

/// Viewport coordinate fence for `DECSET ?1006` (cells) and `DECSET ?1016` (HiDPI pixels).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MouseSgrPixelCoordFence {
    cols: u64,
    rows: u64,
    cell_px_w: u64,
    cell_px_h: u64,
    pixel_mode: bool,
    event_seq: u64,
}

impl Default for MouseSgrPixelCoordFence {
    fn default() -> Self {
        Self::new(80, 24, 10, 20)
    }
}

impl MouseSgrPixelCoordFence {
    #[must_use]
    pub const fn new(cols: u64, rows: u64, cell_px_w: u64, cell_px_h: u64) -> Self {
        let c = sgr_mouse_coord_clamp_b119(if cols == 0 { 1 } else { cols }, MAX_PANE_CELLS);
        let r = sgr_mouse_coord_clamp_b119(if rows == 0 { 1 } else { rows }, MAX_PANE_CELLS);
        let pw =
            sgr_mouse_coord_clamp_b119(if cell_px_w == 0 { 1 } else { cell_px_w }, MAX_CELL_PX);
        let ph =
            sgr_mouse_coord_clamp_b119(if cell_px_h == 0 { 1 } else { cell_px_h }, MAX_CELL_PX);
        Self {
            cols: c,
            rows: r,
            cell_px_w: pw,
            cell_px_h: ph,
            pixel_mode: false,
            event_seq: 0,
        }
    }

    pub fn set_pixel_mode(&mut self, enabled: bool) {
        self.pixel_mode = enabled;
    }

    pub fn resize_viewport(&mut self, cols: u64, rows: u64, cell_px_w: u64, cell_px_h: u64) {
        self.cols = sgr_mouse_coord_clamp_b119(if cols == 0 { 1 } else { cols }, MAX_PANE_CELLS);
        self.rows = sgr_mouse_coord_clamp_b119(if rows == 0 { 1 } else { rows }, MAX_PANE_CELLS);
        self.cell_px_w =
            sgr_mouse_coord_clamp_b119(if cell_px_w == 0 { 1 } else { cell_px_w }, MAX_CELL_PX);
        self.cell_px_h =
            sgr_mouse_coord_clamp_b119(if cell_px_h == 0 { 1 } else { cell_px_h }, MAX_CELL_PX);
    }

    /// Map 0-based pixel cursor `(px_x, px_y)` into 1-based `?1016` pixel or `?1006` cell coords.
    pub fn clamp_pointer(&mut self, px_x: u64, px_y: u64) -> ClampedMousePoint {
        let next_sq = self.event_seq.saturating_add(1);
        self.event_seq = sgr_mouse_seq_advance_b119(self.event_seq, next_sq);
        let (max_x, max_y, cand_x, cand_y) = if self.pixel_mode {
            let raw_mx = self.cols.saturating_mul(self.cell_px_w);
            let raw_my = self.rows.saturating_mul(self.cell_px_h);
            let mx = if raw_mx > 1 { raw_mx } else { 1 };
            let my = if raw_my > 1 { raw_my } else { 1 };
            (mx, my, px_x.saturating_add(1), px_y.saturating_add(1))
        } else {
            let cw = if self.cell_px_w == 0 {
                1
            } else {
                self.cell_px_w
            };
            let ch = if self.cell_px_h == 0 {
                1
            } else {
                self.cell_px_h
            };
            let qx = match px_x.checked_div(cw) {
                Some(v) => v,
                None => 0,
            };
            let qy = match px_y.checked_div(ch) {
                Some(v) => v,
                None => 0,
            };
            let cx = qx.saturating_add(1);
            let cy = qy.saturating_add(1);
            let cols_min = if self.cols > 1 { self.cols } else { 1 };
            let rows_min = if self.rows > 1 { self.rows } else { 1 };
            (cols_min, rows_min, cx, cy)
        };
        let raw_x = sgr_mouse_coord_clamp_b119(cand_x, max_x);
        let raw_y = sgr_mouse_coord_clamp_b119(cand_y, max_y);
        let x = if raw_x > 1 { raw_x } else { 1 };
        let y = if raw_y > 1 { raw_y } else { 1 };
        let _ = sgr_mouse_coord_valid_b119(x, max_x);
        let _ = sgr_mouse_coord_valid_b119(y, max_y);
        ClampedMousePoint {
            x_one_based: x as u32,
            y_one_based: y as u32,
            event_seq: self.event_seq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_hidpi_pixels_to_one_based_cells_and_pixels_within_shrunk_viewport() {
        let mut f = MouseSgrPixelCoordFence::new(100, 40, 12, 24);
        assert_eq!(
            f.clamp_pointer(0, 0),
            ClampedMousePoint {
                x_one_based: 1,
                y_one_based: 1,
                event_seq: 1
            }
        );
        // Overshoot clamps cleanly to (100, 40) in cell mode:
        assert_eq!(
            f.clamp_pointer(50_000, 50_000),
            ClampedMousePoint {
                x_one_based: 100,
                y_one_based: 40,
                event_seq: 2
            }
        );
        f.set_pixel_mode(true);
        assert_eq!(
            f.clamp_pointer(50_000, 50_000),
            ClampedMousePoint {
                x_one_based: 1200,
                y_one_based: 960,
                event_seq: 3
            }
        );
    }
}
