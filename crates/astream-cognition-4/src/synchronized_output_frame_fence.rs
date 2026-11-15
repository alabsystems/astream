// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `DECSET ?2026` (`BSU`/`ESU`) synchronized-output frame watchdog
//! (`Astream.Term.TlaSynchronizedOutputFrameFence`).
//!
//! Prevents TUI tearing in `aterm` while ensuring a wedged child holding `CSI ? 2026 h` (`BSU`)
//! can never freeze screen rendering indefinitely: force-flushes if `buffered_bytes` reaches
//! `max_sync_bytes` or `held_ms` reaches `max_hold_ms`, advancing `frame_epoch` monotonically.

#[cfg(clean_islands)]
#[path = "synchronized_output_frame_fence_island.rs"]
mod synchronized_output_frame_fence_island;
#[cfg(clean_islands)]
pub use synchronized_output_frame_fence_island::{
    sync_frame_bytes_clamp_b116, sync_frame_epoch_advance_b116,
};

#[cfg(not(clean_islands))]
/// Clamp synchronized-output buffered byte count to `max_sync_bytes`.
#[must_use]
pub const fn sync_frame_bytes_clamp_b116(cand_bytes: u64, max_sync_bytes: u64) -> u64 {
    if cand_bytes < max_sync_bytes {
        cand_bytes
    } else {
        max_sync_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `frame_epoch`.
#[must_use]
pub const fn sync_frame_epoch_advance_b116(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `held_ms` has reached or exceeded `max_hold_ms`.
    #[must_use]
    pub const fn sync_frame_timed_out_b116(held_ms: u64, max_hold_ms: u64) -> bool
    clauses [ensures result == (max_hold_ms <= held_ms)]
    {
        max_hold_ms <= held_ms
    }
}

/// Render-flush verdict emitted by `SynchronizedOutputFrameFence`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncFrameVerdict {
    PassThroughImmediate {
        frame_epoch: u64,
    },
    HoldInBatch {
        buffered_bytes: u64,
    },
    FlushCompletedEsu {
        frame_epoch: u64,
        flushed_bytes: u64,
    },
    ForceFlushWatchdog {
        frame_epoch: u64,
        flushed_bytes: u64,
    },
}

/// `DECSET ?2026` synchronized-update frame accumulator and deadline watchdog.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SynchronizedOutputFrameFence {
    in_sync_batch: bool,
    start_ms: u64,
    buffered_bytes: u64,
    max_sync_bytes: u64,
    max_hold_ms: u64,
    frame_epoch: u64,
}

impl SynchronizedOutputFrameFence {
    #[must_use]
    pub const fn new(max_sync_bytes: u64, max_hold_ms: u64) -> Self {
        let bcap = if max_sync_bytes == 0 {
            1024 * 1024
        } else {
            max_sync_bytes
        };
        let tcap = if max_hold_ms == 0 { 100 } else { max_hold_ms };
        Self {
            in_sync_batch: false,
            start_ms: 0,
            buffered_bytes: 0,
            max_sync_bytes: bcap,
            max_hold_ms: tcap,
            frame_epoch: 0,
        }
    }

    #[must_use]
    pub const fn in_sync_batch(&self) -> bool {
        self.in_sync_batch
    }

    /// Enter `CSI ? 2026 h` (`BSU`) at `now_ms`.
    pub fn begin_sync_update(&mut self, now_ms: u64) {
        if !self.in_sync_batch {
            self.in_sync_batch = true;
            self.start_ms = now_ms;
            self.buffered_bytes = 0;
        }
    }

    /// Exit `CSI ? 2026 l` (`ESU`) and flush accumulated frame atomically.
    pub fn end_sync_update(&mut self) -> SyncFrameVerdict {
        let flushed = self.buffered_bytes;
        self.in_sync_batch = false;
        self.buffered_bytes = 0;
        let next_ep = self.frame_epoch.saturating_add(1);
        self.frame_epoch = sync_frame_epoch_advance_b116(self.frame_epoch, next_ep);
        SyncFrameVerdict::FlushCompletedEsu {
            frame_epoch: self.frame_epoch,
            flushed_bytes: flushed,
        }
    }

    /// Observe `chunk_bytes` of PTY output at `now_ms`.
    pub fn on_output_chunk(&mut self, chunk_bytes: u64, now_ms: u64) -> SyncFrameVerdict {
        if !self.in_sync_batch {
            let next_ep = self.frame_epoch.saturating_add(1);
            self.frame_epoch = sync_frame_epoch_advance_b116(self.frame_epoch, next_ep);
            return SyncFrameVerdict::PassThroughImmediate {
                frame_epoch: self.frame_epoch,
            };
        }
        let proposed = self.buffered_bytes.saturating_add(chunk_bytes);
        let held_ms = now_ms.saturating_sub(self.start_ms);
        if proposed >= self.max_sync_bytes || sync_frame_timed_out_b116(held_ms, self.max_hold_ms) {
            let flushed = sync_frame_bytes_clamp_b116(proposed, self.max_sync_bytes);
            self.in_sync_batch = false;
            self.buffered_bytes = 0;
            let next_ep = self.frame_epoch.saturating_add(1);
            self.frame_epoch = sync_frame_epoch_advance_b116(self.frame_epoch, next_ep);
            SyncFrameVerdict::ForceFlushWatchdog {
                frame_epoch: self.frame_epoch,
                flushed_bytes: flushed,
            }
        } else {
            self.buffered_bytes = sync_frame_bytes_clamp_b116(proposed, self.max_sync_bytes);
            SyncFrameVerdict::HoldInBatch {
                buffered_bytes: self.buffered_bytes,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_frame_until_esu_and_force_flushes_on_timeout() {
        let mut f = SynchronizedOutputFrameFence::new(65_536, 100);
        f.begin_sync_update(1_000);
        assert_eq!(
            f.on_output_chunk(2_048, 1_020),
            SyncFrameVerdict::HoldInBatch {
                buffered_bytes: 2_048
            }
        );
        assert_eq!(
            f.on_output_chunk(512, 1_150),
            SyncFrameVerdict::ForceFlushWatchdog {
                frame_epoch: 1,
                flushed_bytes: 2_560,
            }
        );
        assert!(!f.in_sync_batch());
    }
}
