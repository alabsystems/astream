// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC Mode `?2026` Synchronized Output freeze watchdog (`Astream.Term.TlaSyncOutputWatchdog`).
//!
//! Full-screen TUI agents (`claude`, `codex-alab`, `agy`) bracket redraws with
//! `CSI ? 2026 h` (begin synchronized update) and `CSI ? 2026 l` (end synchronized
//! update). If a child process hangs, hits SIGSTOP, or overflows the held byte cap
//! before closing `?2026l`, this watchdog auto-thaws rendering so the `aterm`
//! viewport never freezes indefinitely.

#[cfg(clean_islands)]
#[path = "sync_output_watchdog_island.rs"]
mod sync_output_watchdog_island;
#[cfg(clean_islands)]
pub use sync_output_watchdog_island::{sync_held_bytes_clamp, sync_thaw_epoch_advance};

/// Default maximum duration (`200 ms`) a `?2026h` synchronized frame may hold rendering.
pub const DEFAULT_MAX_SYNC_HOLD_MS: u64 = 200;

/// Default maximum bytes (`256 KiB`) buffered inside a single `?2026h` synchronized frame.
pub const DEFAULT_MAX_SYNC_HELD_BYTES: u64 = 262_144;

#[cfg(not(clean_islands))]
/// Monotonically advance the frame-thaw epoch.
#[must_use]
pub const fn sync_thaw_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp held synchronized-frame byte count to `max_held_bytes`.
#[must_use]
pub const fn sync_held_bytes_clamp(cand_bytes: u64, max_held_bytes: u64) -> u64 {
    if cand_bytes < max_held_bytes {
        cand_bytes
    } else {
        max_held_bytes
    }
}

contract_fn! {
    /// True iff `elapsed_ms` has reached or exceeded `max_hold_ms`.
    #[must_use]
    pub const fn sync_hold_expired(max_hold_ms: u64, elapsed_ms: u64) -> bool
    clauses [ensures result == (max_hold_ms <= elapsed_ms)]
    {
        max_hold_ms <= elapsed_ms
    }
}

/// Outcome of feeding bytes or a timer tick into the `?2026` watchdog.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncWatchdogAction {
    /// Normal immediate rendering (`?2026` inactive).
    RenderImmediate,
    /// Hold rendering inside active `?2026h` bracket.
    HoldFrame { held_bytes: u64 },
    /// Clean `CSI ? 2026 l` end-of-frame flush.
    FlushClean { thaw_epoch: u64 },
    /// Forced auto-thaw due to timeout, byte cap overflow, or child exit.
    ForceThaw { thaw_epoch: u64 },
}

/// Stateful DEC `?2026` synchronized output watchdog.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyncOutputWatchdog {
    active: bool,
    started_at_ms: u64,
    held_bytes: u64,
    thaw_epoch: u64,
    max_hold_ms: u64,
    max_held_bytes: u64,
}

impl Default for SyncOutputWatchdog {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_SYNC_HOLD_MS, DEFAULT_MAX_SYNC_HELD_BYTES)
    }
}

impl SyncOutputWatchdog {
    #[must_use]
    pub const fn new(max_hold_ms: u64, max_held_bytes: u64) -> Self {
        let hold_ms = if max_hold_ms == 0 {
            DEFAULT_MAX_SYNC_HOLD_MS
        } else {
            max_hold_ms
        };
        let hold_bytes = if max_held_bytes == 0 {
            DEFAULT_MAX_SYNC_HELD_BYTES
        } else {
            max_held_bytes
        };
        Self {
            active: false,
            started_at_ms: 0,
            held_bytes: 0,
            thaw_epoch: 0,
            max_hold_ms: hold_ms,
            max_held_bytes: hold_bytes,
        }
    }

    #[must_use]
    pub const fn is_holding(&self) -> bool {
        self.active
    }

    #[must_use]
    pub const fn held_bytes(&self) -> u64 {
        self.held_bytes
    }

    #[must_use]
    pub const fn thaw_epoch(&self) -> u64 {
        self.thaw_epoch
    }

    /// Enter `CSI ? 2026 h` synchronized hold mode (nested `h` preserves original `started_at_ms`).
    pub fn begin_sync(&mut self, now_ms: u64) {
        if !self.active {
            self.active = true;
            self.started_at_ms = now_ms;
            self.held_bytes = 0;
        }
    }

    /// Exit `CSI ? 2026 l` cleanly and flush held frame.
    pub fn end_sync(&mut self) -> SyncWatchdogAction {
        if !self.active {
            return SyncWatchdogAction::RenderImmediate;
        }
        self.active = false;
        self.held_bytes = 0;
        let cand = self.thaw_epoch.saturating_add(1);
        self.thaw_epoch = sync_thaw_epoch_advance(self.thaw_epoch, cand);
        SyncWatchdogAction::FlushClean {
            thaw_epoch: self.thaw_epoch,
        }
    }

    /// Account for `chunk_len` output bytes at `now_ms`, auto-thawing if byte cap or hold timer expires.
    pub fn on_output(&mut self, chunk_len: usize, now_ms: u64) -> SyncWatchdogAction {
        if !self.active {
            return SyncWatchdogAction::RenderImmediate;
        }
        let elapsed = now_ms.saturating_sub(self.started_at_ms);
        let cand_bytes = self.held_bytes.saturating_add(chunk_len as u64);
        if sync_hold_expired(self.max_hold_ms, elapsed) || cand_bytes >= self.max_held_bytes {
            return self.force_thaw();
        }
        self.held_bytes = sync_held_bytes_clamp(cand_bytes, self.max_held_bytes);
        SyncWatchdogAction::HoldFrame {
            held_bytes: self.held_bytes,
        }
    }

    /// Periodic timer check so an idle hung child thaws even when emitting 0 bytes.
    pub fn on_tick(&mut self, now_ms: u64) -> Option<SyncWatchdogAction> {
        if !self.active {
            return None;
        }
        let elapsed = now_ms.saturating_sub(self.started_at_ms);
        if sync_hold_expired(self.max_hold_ms, elapsed) {
            Some(self.force_thaw())
        } else {
            None
        }
    }

    /// Unconditionally thaw on child exit or reset.
    pub fn force_thaw(&mut self) -> SyncWatchdogAction {
        self.active = false;
        self.held_bytes = 0;
        let cand = self.thaw_epoch.saturating_add(1);
        self.thaw_epoch = sync_thaw_epoch_advance(self.thaw_epoch, cand);
        SyncWatchdogAction::ForceThaw {
            thaw_epoch: self.thaw_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_frame_until_end_sync_or_timeout_auto_thaw() {
        let mut wd = SyncOutputWatchdog::new(200, 4096);
        assert_eq!(wd.on_output(64, 1_000), SyncWatchdogAction::RenderImmediate);

        wd.begin_sync(1_000);
        assert_eq!(
            wd.on_output(512, 1_050),
            SyncWatchdogAction::HoldFrame { held_bytes: 512 }
        );
        assert_eq!(wd.on_tick(1_150), None);

        // Child hangs past 200 ms -> on_tick forces thaw!
        assert_eq!(
            wd.on_tick(1_200),
            Some(SyncWatchdogAction::ForceThaw { thaw_epoch: 1 })
        );
        assert!(!wd.is_holding());

        // Next clean frame flushes at epoch 2
        wd.begin_sync(2_000);
        assert_eq!(
            wd.on_output(128, 2_010),
            SyncWatchdogAction::HoldFrame { held_bytes: 128 }
        );
        assert_eq!(
            wd.end_sync(),
            SyncWatchdogAction::FlushClean { thaw_epoch: 2 }
        );
    }
}
