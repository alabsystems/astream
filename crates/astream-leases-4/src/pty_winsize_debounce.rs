// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY `TIOCSWINSZ` / `SIGWINCH` live window-drag resize debouncer
//! (`Astream.Host.TlaWinsizeDebounce`).
//!
//! Coalesces high-frequency GUI drag-resize events (`120 Hz` macOS `NSWindow` live resize)
//! so child TUI applications and `astream` session logs receive an immediate initial size
//! followed by bounded-rate updates (`debounce_ms`, default `16 ms`) and a guaranteed
//! trailing-edge delivery of the final resting geometry.

#![allow(clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "pty_winsize_debounce_island.rs"]
mod pty_winsize_debounce_island;
#[cfg(clean_islands)]
pub use pty_winsize_debounce_island::{winsize_debounce_dim_clamp, winsize_debounce_epoch_advance};

/// Mirror of Clean's `winsize_debounce_dim_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn winsize_debounce_dim_clamp(raw_dim: u64, max_dim: u64) -> u64 {
    if raw_dim < max_dim {
        raw_dim
    } else {
        max_dim
    }
}

/// Mirror of Clean's `winsize_debounce_epoch_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn winsize_debounce_epoch_advance(cur_epoch: u64, next_epoch: u64) -> u64 {
    if cur_epoch < next_epoch {
        next_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// Kernel-certified check that `elapsed_ms` has reached `window_ms` (`window_ms <= elapsed_ms`),
    /// linked via `clean-kernel-defeq` to `winsize_debounce_ready_isl`.
    #[must_use]
    pub const fn winsize_debounce_ready(elapsed_ms: u64, window_ms: u64) -> bool
    clauses [ensures result == (window_ms <= elapsed_ms)]
    {
        window_ms <= elapsed_ms
    }
}

/// Maximum terminal cell dimension (`1..=MAX_PTY_WINSIZE_DIM`, matching `astream-term::Screen`).
pub const MAX_PTY_WINSIZE_DIM: u16 = 1024;

/// Default trailing-edge `TIOCSWINSZ` debounce interval in milliseconds (`16 ms`, ~60 Hz).
pub const DEFAULT_WINSIZE_DEBOUNCE_MS: u64 = 16;

/// Sanitized PTY window size (`cols`, `rows`, `xpixel`, `ypixel`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyWinSize {
    /// Columns (`1..=MAX_PTY_WINSIZE_DIM`).
    pub cols: u16,
    /// Rows (`1..=MAX_PTY_WINSIZE_DIM`).
    pub rows: u16,
    /// Horizontal pixel width (`0` if unknown).
    pub xpixel: u16,
    /// Vertical pixel height (`0` if unknown).
    pub ypixel: u16,
}

impl PtyWinSize {
    /// Sanitize raw `(cols, rows, xpixel, ypixel)` dimensions into `[1, MAX_PTY_WINSIZE_DIM]`.
    #[must_use]
    pub const fn sanitized(cols: u16, rows: u16, xpixel: u16, ypixel: u16) -> Self {
        let c = winsize_debounce_dim_clamp(cols as u64, MAX_PTY_WINSIZE_DIM as u64) as u16;
        let r = winsize_debounce_dim_clamp(rows as u64, MAX_PTY_WINSIZE_DIM as u64) as u16;
        Self {
            cols: if c == 0 { 1 } else { c },
            rows: if r == 0 { 1 } else { r },
            xpixel,
            ypixel,
        }
    }
}

/// Stateful trailing-edge PTY `TIOCSWINSZ` coalescer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WinsizeDebouncer {
    debounce_ms: u64,
    epoch: u64,
    applied: Option<PtyWinSize>,
    pending: Option<PtyWinSize>,
    last_emit_ms: u64,
}

impl WinsizeDebouncer {
    /// Construct a debouncer with `debounce_ms` window.
    #[must_use]
    pub const fn new(debounce_ms: u64) -> Self {
        Self {
            debounce_ms,
            epoch: 0,
            applied: None,
            pending: None,
            last_emit_ms: 0,
        }
    }

    /// Configured trailing-edge debounce interval in milliseconds.
    #[must_use]
    pub const fn debounce_ms(&self) -> u64 {
        self.debounce_ms
    }

    /// Monotone count of emitted `TIOCSWINSZ` updates.
    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Timestamp (`ms`) of the most recent emitted `TIOCSWINSZ`.
    #[must_use]
    pub const fn last_emit_ms(&self) -> u64 {
        self.last_emit_ms
    }

    /// Most recently emitted [`PtyWinSize`].
    #[must_use]
    pub const fn applied(&self) -> Option<PtyWinSize> {
        self.applied
    }

    /// Pending un-emitted trailing-edge [`PtyWinSize`], if any.
    #[must_use]
    pub const fn pending(&self) -> Option<PtyWinSize> {
        self.pending
    }

    /// Submit a candidate resize at monotonic timestamp `now_ms`.
    ///
    /// Returns `Some(size)` immediately when `applied` is `None` or the debounce window
    /// has elapsed and `size != applied`; otherwise stages `size` in `pending` (cancelling
    /// `pending` automatically if the user drags back to `applied`).
    pub fn on_resize(&mut self, raw: PtyWinSize, now_ms: u64) -> Option<PtyWinSize> {
        let clean = PtyWinSize::sanitized(raw.cols, raw.rows, raw.xpixel, raw.ypixel);
        let monotonic_now = if now_ms < self.last_emit_ms {
            self.last_emit_ms
        } else {
            now_ms
        };
        if self.applied == Some(clean) {
            self.pending = None;
            return None;
        }
        let elapsed = monotonic_now.saturating_sub(self.last_emit_ms);
        if self.applied.is_none() || winsize_debounce_ready(elapsed, self.debounce_ms) {
            self.applied = Some(clean);
            self.pending = None;
            self.last_emit_ms = monotonic_now;
            self.epoch = winsize_debounce_epoch_advance(self.epoch, self.epoch.saturating_add(1));
            Some(clean)
        } else {
            self.pending = Some(clean);
            None
        }
    }

    /// Poll at monotonic timestamp `now_ms` to flush any trailing-edge `pending` resize once
    /// `debounce_ms` has elapsed.
    pub fn poll_flush(&mut self, now_ms: u64) -> Option<PtyWinSize> {
        let Some(target) = self.pending else {
            return None;
        };
        let monotonic_now = if now_ms < self.last_emit_ms {
            self.last_emit_ms
        } else {
            now_ms
        };
        let elapsed = monotonic_now.saturating_sub(self.last_emit_ms);
        if winsize_debounce_ready(elapsed, self.debounce_ms) {
            self.pending = None;
            if self.applied != Some(target) {
                self.applied = Some(target);
                self.last_emit_ms = monotonic_now;
                self.epoch =
                    winsize_debounce_epoch_advance(self.epoch, self.epoch.saturating_add(1));
                return Some(target);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesces_rapid_drag_burst_and_flushes_final_trailing_geometry() {
        let mut d = WinsizeDebouncer::new(16);
        assert_eq!(d.debounce_ms(), 16);
        let init = d
            .on_resize(
                PtyWinSize {
                    cols: 80,
                    rows: 24,
                    xpixel: 800,
                    ypixel: 480,
                },
                100,
            )
            .expect("first resize emits immediately");
        assert_eq!((init.cols, init.rows, d.epoch()), (80, 24, 1));

        // Rapid burst within 16ms is coalesced into `pending`.
        assert!(d
            .on_resize(
                PtyWinSize {
                    cols: 90,
                    rows: 28,
                    xpixel: 900,
                    ypixel: 560,
                },
                104,
            )
            .is_none());
        assert!(d
            .on_resize(
                PtyWinSize {
                    cols: 120,
                    rows: 40,
                    xpixel: 1200,
                    ypixel: 800,
                },
                110,
            )
            .is_none());
        assert!(d.poll_flush(115).is_none());

        let flushed = d.poll_flush(116).expect("trailing edge flushes at +16ms");
        assert_eq!((flushed.cols, flushed.rows, d.epoch()), (120, 40, 2));
        assert_eq!(d.last_emit_ms(), 116);
        assert!(d.pending().is_none());
    }
}
