// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! POSIX `TIOCSWINSZ` / `SIGWINCH` terminal resize storm coalescer clamping `(rows, cols)` to
//! non-zero `[1, 1024]` bounds and eliding duplicate `ioctl` calls during live window drags
//! (`Astream.PtySig.TlaWinsizeCoalescer`).

#[cfg(clean_islands)]
#[path = "winsize_coalescer_island.rs"]
mod winsize_coalescer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_dim_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_win_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use winsize_coalescer_island::{pty_dim_clamp, pty_win_advance};

/// Maximum PTY grid dimension (`1_024` rows or columns).
pub const MAX_PTY_DIM: u64 = 1_024;

contract_fn! {
    /// Verified non-zero dimension bound (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_winsize_valid_isl`.
    #[must_use]
    pub const fn pty_winsize_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct WinsizeCoalescer {
    rows: u64,
    cols: u64,
    ioctls_issued: u64,
}

impl WinsizeCoalescer {
    #[must_use]
    pub const fn new(initial_rows: u64, initial_cols: u64) -> Self {
        let r = pty_dim_clamp(
            if initial_rows == 0 { 1 } else { initial_rows },
            MAX_PTY_DIM,
        );
        let c = pty_dim_clamp(
            if initial_cols == 0 { 1 } else { initial_cols },
            MAX_PTY_DIM,
        );
        Self {
            rows: r,
            cols: c,
            ioctls_issued: 0,
        }
    }

    pub fn propose_resize(&mut self, raw_rows: u64, raw_cols: u64) -> Option<(u64, u64)> {
        let r = pty_dim_clamp(if raw_rows == 0 { 1 } else { raw_rows }, MAX_PTY_DIM);
        let c = pty_dim_clamp(if raw_cols == 0 { 1 } else { raw_cols }, MAX_PTY_DIM);
        let _ = pty_winsize_valid(r, 1);
        let _ = pty_winsize_valid(c, 1);
        if r == self.rows && c == self.cols {
            return None;
        }
        self.rows = r;
        self.cols = c;
        self.ioctls_issued =
            pty_win_advance(self.ioctls_issued, self.ioctls_issued.saturating_add(1));
        Some((r, c))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesces_identical_dimensions_and_clamps_zero_to_one() {
        let mut w = WinsizeCoalescer::new(24, 80);
        assert_eq!(w.propose_resize(24, 80), None);
        assert_eq!(w.propose_resize(0, 120), Some((1, 120)));
        assert_eq!(w.propose_resize(1, 120), None);
    }
}
