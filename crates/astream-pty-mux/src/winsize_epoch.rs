// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone `(resize_epoch, cols, rows)` `TIOCSWINSZ` barrier preventing stale-geometry `ASOP`
//! screen frames from overwriting newer terminal resizes (`Astream.PtyMux.TlaWinsizeEpoch`).

#[cfg(clean_islands)]
#[path = "winsize_epoch_island.rs"]
mod winsize_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ws_dim_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ws_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use winsize_epoch_island::{ws_dim_clamp, ws_epoch_advance};

/// Hard safety cap on PTY grid columns or rows (`1000`).
pub const MAX_PTY_DIMENSION: u64 = 1_000;

contract_fn! {
    /// Verified epoch currency check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ws_epoch_current_isl`.
    #[must_use]
    pub const fn ws_epoch_current(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyWinsize {
    pub epoch: u64,
    pub cols: u16,
    pub rows: u16,
}

/// Resize-epoch barrier fencing pre-resize render frames.
#[derive(Debug, Clone)]
pub struct WinsizeEpochBarrier {
    current: PtyWinsize,
}

impl WinsizeEpochBarrier {
    #[must_use]
    pub const fn new(cols: u16, rows: u16) -> Self {
        let c = ws_dim_clamp(cols as u64, MAX_PTY_DIMENSION) as u16;
        let r = ws_dim_clamp(rows as u64, MAX_PTY_DIMENSION) as u16;
        Self {
            current: PtyWinsize {
                epoch: 1,
                cols: if c == 0 { 80 } else { c },
                rows: if r == 0 { 24 } else { r },
            },
        }
    }

    pub fn apply_resize(&mut self, cols: u16, rows: u16) -> PtyWinsize {
        let raw_c = ws_dim_clamp(cols as u64, MAX_PTY_DIMENSION) as u16;
        let raw_r = ws_dim_clamp(rows as u64, MAX_PTY_DIMENSION) as u16;
        let c = if raw_c == 0 { 1 } else { raw_c };
        let r = if raw_r == 0 { 1 } else { raw_r };
        if c != self.current.cols || r != self.current.rows {
            let next_ep =
                ws_epoch_advance(self.current.epoch, self.current.epoch.saturating_add(1));
            self.current = PtyWinsize {
                epoch: next_ep,
                cols: c,
                rows: r,
            };
        }
        self.current
    }

    #[must_use]
    pub const fn accepts_frame_epoch(&self, frame_epoch: u64) -> bool {
        ws_epoch_current(frame_epoch, self.current.epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn winsize_barrier_advances_on_geometry_change_and_drops_stale_epoch_frames() {
        let mut b = WinsizeEpochBarrier::new(80, 24);
        assert!(b.accepts_frame_epoch(1));
        let ws = b.apply_resize(120, 40);
        assert_eq!(ws.epoch, 2);
        assert!(!b.accepts_frame_epoch(1));
        assert!(b.accepts_frame_epoch(2));
    }
}
