// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY `SIGWINCH` / `TIOCSWINSZ` Burst Coalescer (`Astream.Pump.TlaWinsizeCoalescer`).
//!
//! Live macOS window drags and `aterm` split-pane resizes emit up to 120 intermediate
//! `(cols, rows)` geometry events per second. Forwarding every intermediate step immediately
//! onto a PTY and session log forces full-screen TUIs (`vim`, `htop`, `claude`, `agy`) into
//! cascading redraw storms and bloats recorded logs with transient sizes.
//!
//! [`WinsizeCoalescer`] sanitizes and coalesces geometry bursts deterministically:
//! 1. Clamps `cols` and `rows` into `1..=max_dim` via Clean-origin [`winsize_dim_clamp`].
//! 2. Suppresses no-op updates equal to `last_emitted`.
//! 3. Emits the very first size immediately when uninitialized, then holds rapid follow-on
//!    drag updates inside `debounce_ticks` until either the quiet window elapses or
//!    [`WinsizeCoalescer::flush_pending`] is called, advancing `emit_epoch` monotonically via
//!    Clean-origin [`winsize_epoch_advance`].

#![allow(clippy::manual_map, clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "pty_resize_coalesce_island.rs"]
mod pty_resize_coalesce_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn winsize_dim_clamp(cand_dim: u64, max_dim: u64) -> u64 {
    if cand_dim < max_dim {
        cand_dim
    } else {
        max_dim
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn winsize_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use pty_resize_coalesce_island::{winsize_dim_clamp, winsize_epoch_advance};

/// Default maximum terminal columns/rows (`1024`).
pub const DEFAULT_MAX_WINSIZE_DIM: u16 = 1024;

/// Default quiet hold ticks for coalescing interactive drag bursts.
pub const DEFAULT_WINSIZE_DEBOUNCE_TICKS: u64 = 2;

contract_fn! {
    /// Kernel-certified check that `dim <= max_dim`, linked via `clean-kernel-defeq`
    /// to `winsize_dim_within_cap_isl`.
    #[must_use]
    pub const fn winsize_dim_within_cap(dim: u64, max_dim: u64) -> bool
    clauses [ensures result == (dim <= max_dim)]
    {
        dim <= max_dim
    }
}

/// Sanitized non-zero `(cols, rows)` terminal geometry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TerminalGeometry {
    pub cols: u16,
    pub rows: u16,
    pub emit_epoch: u64,
}

/// Action returned when submitting a resize event or advancing the tick clock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WinsizeAction {
    /// Redundant geometry identical to the currently active size; elided.
    SuppressedDuplicate,
    /// Latched inside the debounce window; will emit once `debounce_ticks` elapse or flushed.
    CoalescingPending {
        pending_cols: u16,
        pending_rows: u16,
    },
    /// Ready to apply via `TIOCSWINSZ` and append to the session log.
    Emit(TerminalGeometry),
}

/// Stateful PTY geometry coalescer backed by `Astream.Pump.TlaWinsizeCoalescer`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WinsizeCoalescer {
    max_dim: u16,
    debounce_ticks: u64,
    last_emitted: Option<(u16, u16)>,
    pending: Option<(u16, u16)>,
    pending_age_ticks: u64,
    emit_epoch: u64,
}

impl WinsizeCoalescer {
    /// Construct a coalescer with `max_dim` (`>= 1`) and `debounce_ticks` (`0` disables holdback).
    #[must_use]
    pub const fn new(max_dim: u16, debounce_ticks: u64) -> Self {
        let cap = if max_dim == 0 { 1 } else { max_dim };
        Self {
            max_dim: cap,
            debounce_ticks,
            last_emitted: None,
            pending: None,
            pending_age_ticks: 0,
            emit_epoch: 0,
        }
    }

    /// Construct a coalescer with [`DEFAULT_MAX_WINSIZE_DIM`] and
    /// [`DEFAULT_WINSIZE_DEBOUNCE_TICKS`].
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(DEFAULT_MAX_WINSIZE_DIM, DEFAULT_WINSIZE_DEBOUNCE_TICKS)
    }

    /// Monotone emission epoch count.
    #[must_use]
    pub const fn emit_epoch(&self) -> u64 {
        self.emit_epoch
    }

    /// Last emitted `(cols, rows)`, if any.
    #[must_use]
    pub const fn last_emitted(&self) -> Option<(u16, u16)> {
        self.last_emitted
    }

    fn sanitize_pair(&self, raw_cols: u16, raw_rows: u16) -> (u16, u16) {
        let c_clamped = winsize_dim_clamp(raw_cols as u64, self.max_dim as u64);
        let r_clamped = winsize_dim_clamp(raw_rows as u64, self.max_dim as u64);
        let cols = if c_clamped == 0 { 1 } else { c_clamped as u16 };
        let rows = if r_clamped == 0 { 1 } else { r_clamped as u16 };
        (cols, rows)
    }

    fn commit_emit(&mut self, cols: u16, rows: u16) -> TerminalGeometry {
        let cand_ep = self.emit_epoch.saturating_add(1);
        let next_ep = winsize_epoch_advance(self.emit_epoch, cand_ep);
        self.emit_epoch = next_ep;
        self.last_emitted = Some((cols, rows));
        self.pending = None;
        self.pending_age_ticks = 0;
        TerminalGeometry {
            cols,
            rows,
            emit_epoch: next_ep,
        }
    }

    /// Observe a raw `(cols, rows)` resize notification.
    pub fn observe_resize(&mut self, raw_cols: u16, raw_rows: u16) -> WinsizeAction {
        let (cols, rows) = self.sanitize_pair(raw_cols, raw_rows);
        if self.last_emitted == Some((cols, rows)) {
            // Dragged out and back to the already-active size before settling!
            self.pending = None;
            self.pending_age_ticks = 0;
            return WinsizeAction::SuppressedDuplicate;
        }
        if self.last_emitted.is_none() || self.debounce_ticks == 0 {
            return WinsizeAction::Emit(self.commit_emit(cols, rows));
        }
        self.pending = Some((cols, rows));
        self.pending_age_ticks = 0;
        WinsizeAction::CoalescingPending {
            pending_cols: cols,
            pending_rows: rows,
        }
    }

    /// Advance the debounce clock by one tick, emitting any pending geometry whose quiet window
    /// has elapsed.
    pub fn on_tick(&mut self) -> Option<TerminalGeometry> {
        let Some((cols, rows)) = self.pending else {
            return None;
        };
        self.pending_age_ticks = self.pending_age_ticks.saturating_add(1);
        if self.pending_age_ticks >= self.debounce_ticks {
            Some(self.commit_emit(cols, rows))
        } else {
            None
        }
    }

    /// Immediately flush any held geometry (e.g. before child exit or clean session close).
    pub fn flush_pending(&mut self) -> Option<TerminalGeometry> {
        match self.pending {
            Some((cols, rows)) => Some(self.commit_emit(cols, rows)),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emits_initial_immediately_coalesces_drag_burst_and_clamps_bounds() {
        let mut c = WinsizeCoalescer::new(500, 2);
        // Zero and oversize inputs clamp cleanly into 1..=500.
        assert_eq!(
            c.observe_resize(0, 999),
            WinsizeAction::Emit(TerminalGeometry {
                cols: 1,
                rows: 500,
                emit_epoch: 1,
            })
        );
        assert!(winsize_dim_within_cap(500, 500));

        // Duplicate is suppressed immediately.
        assert_eq!(c.observe_resize(0, 500), WinsizeAction::SuppressedDuplicate);

        // Rapid drag sequence: 90x30 -> 100x32 -> 120x40.
        assert_eq!(
            c.observe_resize(90, 30),
            WinsizeAction::CoalescingPending {
                pending_cols: 90,
                pending_rows: 30,
            }
        );
        assert_eq!(c.on_tick(), None);
        assert_eq!(
            c.observe_resize(100, 32),
            WinsizeAction::CoalescingPending {
                pending_cols: 100,
                pending_rows: 32,
            }
        );
        assert_eq!(
            c.observe_resize(120, 40),
            WinsizeAction::CoalescingPending {
                pending_cols: 120,
                pending_rows: 40,
            }
        );

        // Two quiet ticks settle on 120x40 as epoch 2!
        assert_eq!(c.on_tick(), None);
        assert_eq!(
            c.on_tick(),
            Some(TerminalGeometry {
                cols: 120,
                rows: 40,
                emit_epoch: 2,
            })
        );
        assert_eq!(c.on_tick(), None);
    }

    #[test]
    fn drag_returning_to_current_size_cancels_pending_without_spurious_emit() {
        let mut c = WinsizeCoalescer::with_defaults();
        assert!(matches!(c.observe_resize(80, 24), WinsizeAction::Emit(_)));
        assert!(matches!(
            c.observe_resize(85, 24),
            WinsizeAction::CoalescingPending { .. }
        ));
        assert_eq!(c.observe_resize(80, 24), WinsizeAction::SuppressedDuplicate);
        assert_eq!(c.flush_pending(), None);
        assert_eq!(c.emit_epoch(), 1);
    }
}
