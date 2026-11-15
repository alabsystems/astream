// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC private mode `?2026` synchronized-update frame batcher with hard deadline auto-flush so a
//! crashed or stalled TUI child cannot freeze terminal rendering indefinitely
//! (`Astream.OscProto.TlaSynchronizedOutputGate`).

#[cfg(clean_islands)]
#[path = "synchronized_output_gate_island.rs"]
mod synchronized_output_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_sync_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_frame_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use synchronized_output_gate_island::{osc_frame_advance, osc_sync_clamp};

/// Maximum `?2026` batch hold timeout (`200 ms`) before forced present.
pub const MAX_SYNC_HOLD_MS: u64 = 200;

contract_fn! {
    /// Verified frame-flush readiness predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `osc_flush_ready_isl`.
    #[must_use]
    pub const fn osc_flush_ready(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct SyncOutputGate {
    batching: bool,
    started_ms: u64,
    timeout_ms: u64,
    frames_flushed: u64,
}

impl SyncOutputGate {
    #[must_use]
    pub const fn new(timeout_ms: u64) -> Self {
        let clamped = osc_sync_clamp(timeout_ms, MAX_SYNC_HOLD_MS);
        Self {
            batching: false,
            started_ms: 0,
            timeout_ms: if clamped == 0 { 16 } else { clamped },
            frames_flushed: 0,
        }
    }

    pub fn begin_sync(&mut self, now_ms: u64) {
        self.batching = true;
        self.started_ms = now_ms;
    }

    pub fn end_sync(&mut self) {
        if self.batching {
            self.batching = false;
            self.frames_flushed =
                osc_frame_advance(self.frames_flushed, self.frames_flushed.saturating_add(1));
        }
    }

    pub fn should_present(&mut self, now_ms: u64) -> bool {
        if !self.batching {
            return true;
        }
        let deadline = self.started_ms.saturating_add(self.timeout_ms);
        if osc_flush_ready(now_ms, deadline) {
            self.batching = false;
            self.frames_flushed =
                osc_frame_advance(self.frames_flushed, self.frames_flushed.saturating_add(1));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_frame_during_sync_batch_and_auto_flushes_on_timeout() {
        let mut g = SyncOutputGate::new(100);
        g.begin_sync(1_000);
        assert!(!g.should_present(1_050));
        assert!(g.should_present(1_100));
    }
}
