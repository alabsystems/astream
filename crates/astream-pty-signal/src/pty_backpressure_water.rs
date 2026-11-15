// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-watermark (`low_water`, `high_water`) PTY master read throttle applying kernel PTY
//! backpressure against runaway output floods without starving interactive frames
//! (`Astream.PtySig.TlaPtyBackpressureWater`).

#[cfg(clean_islands)]
#[path = "pty_backpressure_water_island.rs"]
mod pty_backpressure_water_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_buf_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_pause_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pty_backpressure_water_island::{pty_buf_clamp, pty_pause_advance};

/// Maximum queued unrendered PTY bytes per tab (`4_194_304` = 4 MiB).
pub const MAX_QUEUED_PTY_BYTES: u64 = 4_194_304;

contract_fn! {
    /// Verified master-read headroom predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_can_read_master_isl`.
    #[must_use]
    pub const fn pty_can_read_master(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct PtyBackpressure {
    low_water: u64,
    high_water: u64,
    throttled: bool,
    throttle_epochs: u64,
}

impl PtyBackpressure {
    #[must_use]
    pub const fn new(low_water: u64, high_water: u64) -> Self {
        let hi = pty_buf_clamp(high_water, MAX_QUEUED_PTY_BYTES);
        let lo = pty_buf_clamp(low_water, hi);
        Self {
            low_water: lo,
            high_water: hi,
            throttled: false,
            throttle_epochs: 0,
        }
    }

    pub fn allow_master_read(&mut self, queued_bytes: u64) -> bool {
        let q = pty_buf_clamp(queued_bytes, MAX_QUEUED_PTY_BYTES);
        if self.throttled {
            if pty_can_read_master(self.low_water, q) {
                self.throttled = false;
                true
            } else {
                false
            }
        } else if pty_can_read_master(self.high_water, q) {
            true
        } else {
            self.throttled = true;
            self.throttle_epochs =
                pty_pause_advance(self.throttle_epochs, self.throttle_epochs.saturating_add(1));
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hysteresis_throttles_above_high_water_until_drained_to_low_water() {
        let mut bp = PtyBackpressure::new(64 * 1024, 256 * 1024);
        assert!(bp.allow_master_read(128 * 1024));
        assert!(!bp.allow_master_read(300 * 1024));
        assert!(!bp.allow_master_read(128 * 1024));
        assert!(bp.allow_master_read(32 * 1024));
    }
}
