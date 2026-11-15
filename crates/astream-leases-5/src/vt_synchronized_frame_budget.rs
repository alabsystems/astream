// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC Mode `?2026` (`BSU`/`ESU` Synchronized Output) frame-byte & deadline watchdog
//! (`Astream.Term.TlaSynchronizedFrameBudget`).
//!
//! Protects `aterm` agent TUI tabs (Claude Code, `codex-alab`, `agy`, `Muse Code`) when a
//! child program enters synchronized-update mode (`CSI ? 2026 h`) and crashes or hangs before
//! emitting `CSI ? 2026 l`:
//! - Enforces `buffered_bytes <= max_sync_bytes` (default `1 MiB`) and `sync_elapsed_ms <= max_sync_ms`
//!   (default `100 ms`).
//! - Automatically fails open and flushes the held frame buffer when either cap is exceeded,
//!   preventing a wedged child TUI from freezing an `aterm` pane indefinitely.

#[cfg(clean_islands)]
#[path = "vt_synchronized_frame_budget_island.rs"]
mod vt_synchronized_frame_budget_island;
#[cfg(clean_islands)]
pub use vt_synchronized_frame_budget_island::{sync_bytes_clamp_b82, sync_elapsed_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn sync_bytes_clamp_b82(buffered: u64, max_bytes: u64) -> u64 {
    if buffered < max_bytes {
        buffered
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn sync_elapsed_clamp(elapsed: u64, max_ms: u64) -> u64 {
    if elapsed < max_ms {
        elapsed
    } else {
        max_ms
    }
}

contract_fn! {
    /// Verified check that buffered synchronized-output bytes sit within `max_sync_bytes`
    /// (`buffered_bytes <= max_sync_bytes`), linked via `clean-kernel-defeq` to
    /// `sync_frame_within_budget_isl`.
    #[must_use]
    pub const fn sync_frame_within_budget(buffered_bytes: u64, max_sync_bytes: u64) -> bool
    clauses [ensures result == (buffered_bytes <= max_sync_bytes)]
    {
        buffered_bytes <= max_sync_bytes
    }
}

/// Default maximum held bytes inside a single DEC `?2026` synchronized frame (`1 MiB`).
pub const DEFAULT_MAX_SYNC_FRAME_BYTES: usize = 1024 * 1024;
/// Default maximum hold duration before fail-open flush (`100 ms`).
pub const DEFAULT_MAX_SYNC_HOLD_MS: u64 = 100;

/// Action decided by [`SynchronizedFrameWatchdog`] on PTY output or timer tick.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyncFrameOutcome {
    /// Not in `?2026` mode: render `bytes` immediately.
    PassThrough,
    /// Holding bytes inside an active `?2026` transaction (`buffered_bytes <= max_sync_bytes`).
    Buffered {
        /// Current held byte count.
        buffered_bytes: usize,
    },
    /// Clean `ESU` (`CSI ? 2026 l`) or fail-open budget/timeout expiry: flush held bytes now.
    FlushHeld {
        /// Held frame bytes to apply atomically to the `Screen`.
        flushed_bytes: Vec<u8>,
        /// `true` if flushed due to byte-cap or deadline expiry rather than clean `ESU`.
        forced_fail_open: bool,
    },
}

/// Stateful DEC `?2026` synchronized-output frame buffer & fail-open watchdog.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SynchronizedFrameWatchdog {
    active: bool,
    started_at_ms: u64,
    elapsed_ms: u64,
    max_hold_ms: u64,
    max_sync_bytes: usize,
    buffered_len: u64,
    held: Vec<u8>,
}

impl SynchronizedFrameWatchdog {
    #[must_use]
    pub const fn new(max_sync_bytes: usize, max_hold_ms: u64) -> Self {
        let cap_b = if max_sync_bytes < 256 {
            256
        } else {
            max_sync_bytes
        };
        let cap_ms = if max_hold_ms < 1 { 1 } else { max_hold_ms };
        Self {
            active: false,
            started_at_ms: 0,
            elapsed_ms: 0,
            max_hold_ms: cap_ms,
            max_sync_bytes: cap_b,
            buffered_len: 0,
            held: Vec::new(),
        }
    }

    #[must_use]
    pub const fn is_active(&self) -> bool {
        self.active
    }

    #[must_use]
    pub const fn buffered_len(&self) -> u64 {
        self.buffered_len
    }

    /// Enter `BSU` (`CSI ? 2026 h`) at `now_ms`.
    pub fn begin_synchronized(&mut self, now_ms: u64) {
        if !self.active {
            self.active = true;
            self.started_at_ms = now_ms;
            self.elapsed_ms = 0;
        }
    }

    /// Exit `ESU` (`CSI ? 2026 l`) cleanly, flushing any held bytes.
    pub fn end_synchronized(&mut self) -> SyncFrameOutcome {
        self.active = false;
        self.elapsed_ms = 0;
        self.buffered_len = 0;
        let flushed = core::mem::take(&mut self.held);
        SyncFrameOutcome::FlushHeld {
            flushed_bytes: flushed,
            forced_fail_open: false,
        }
    }

    /// Feed a chunk of PTY bytes at monotonic `now_ms`, automatically failing open if
    /// `max_sync_bytes` or `max_hold_ms` is exceeded.
    pub fn push_pty_chunk(&mut self, chunk: &[u8], now_ms: u64) -> SyncFrameOutcome {
        if !self.active {
            return SyncFrameOutcome::PassThrough;
        }
        let raw_elapsed = now_ms.saturating_sub(self.started_at_ms);
        let proposed_len = (self.held.len() as u64).saturating_add(chunk.len() as u64);
        if raw_elapsed >= self.max_hold_ms
            || !sync_frame_within_budget(proposed_len, self.max_sync_bytes as u64)
        {
            self.active = false;
            self.elapsed_ms = sync_elapsed_clamp(raw_elapsed, self.max_hold_ms);
            self.buffered_len = 0;
            let mut flushed = core::mem::take(&mut self.held);
            flushed.extend_from_slice(chunk);
            return SyncFrameOutcome::FlushHeld {
                flushed_bytes: flushed,
                forced_fail_open: true,
            };
        }
        self.held.extend_from_slice(chunk);
        self.elapsed_ms = sync_elapsed_clamp(raw_elapsed, self.max_hold_ms);
        self.buffered_len =
            sync_bytes_clamp_b82(self.held.len() as u64, self.max_sync_bytes as u64);
        SyncFrameOutcome::Buffered {
            buffered_bytes: self.held.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buffers_clean_bsu_esu_frame_and_fails_open_on_wedged_tui_timeout_or_overflow() {
        let mut wd = SynchronizedFrameWatchdog::new(512, 100);
        assert_eq!(
            wd.push_pty_chunk(b"plain", 10),
            SyncFrameOutcome::PassThrough
        );

        // Clean BSU -> chunk -> ESU atomic flush.
        wd.begin_synchronized(1_000);
        assert_eq!(
            wd.push_pty_chunk(b"frame-part-1;", 1_020),
            SyncFrameOutcome::Buffered { buffered_bytes: 13 }
        );
        assert_eq!(
            wd.end_synchronized(),
            SyncFrameOutcome::FlushHeld {
                flushed_bytes: b"frame-part-1;".to_vec(),
                forced_fail_open: false,
            }
        );
        assert!(!wd.is_active());

        // Wedged child TUI exceeds 100ms hold -> automatic fail-open flush!
        wd.begin_synchronized(2_000);
        let _ = wd.push_pty_chunk(b"half-", 2_050);
        assert_eq!(
            wd.push_pty_chunk(b"hung", 2_120),
            SyncFrameOutcome::FlushHeld {
                flushed_bytes: b"half-hung".to_vec(),
                forced_fail_open: true,
            }
        );
        assert!(!wd.is_active());
        assert_eq!(wd.buffered_len(), 0);
    }
}
