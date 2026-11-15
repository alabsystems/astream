// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hysteresis high/low master-FD read-pause watermark applying natural kernel PTY backpressure
//! without injecting `XON`/`XOFF` bytes (`Astream.PtyMux.TlaPtyFlowWatermark`).

#[cfg(clean_islands)]
#[path = "pty_flow_watermark_island.rs"]
mod pty_flow_watermark_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flow_buffered_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flow_pause_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pty_flow_watermark_island::{flow_buffered_clamp, flow_pause_advance};

/// Hard cap on in-memory unconsumed PTY output per session (`8` MiB).
pub const MAX_PTY_FLOW_BUFFER_BYTES: u64 = 8 * 1024 * 1024;

contract_fn! {
    /// Verified resume check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `flow_below_low_mark_isl`.
    #[must_use]
    pub const fn flow_below_low_mark(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Hysteresis PTY master-read throttle (`paused` latches at `high_mark`, clears at `<= low_mark`).
#[derive(Debug, Clone)]
pub struct PtyFlowWatermark {
    low_mark: u64,
    high_mark: u64,
    buffered: u64,
    paused: bool,
    pause_events: u64,
}

impl PtyFlowWatermark {
    #[must_use]
    pub const fn new(low_mark: u64, high_mark: u64) -> Self {
        let hi = flow_buffered_clamp(high_mark, MAX_PTY_FLOW_BUFFER_BYTES);
        let lo = flow_buffered_clamp(low_mark, hi);
        Self {
            low_mark: lo,
            high_mark: if hi == 0 { 1 } else { hi },
            buffered: 0,
            paused: false,
            pause_events: 0,
        }
    }

    #[must_use]
    pub const fn is_master_read_paused(&self) -> bool {
        self.paused
    }

    pub fn on_enqueue(&mut self, bytes: u64) -> bool {
        let next = self.buffered.saturating_add(bytes);
        self.buffered = flow_buffered_clamp(next, MAX_PTY_FLOW_BUFFER_BYTES);
        if !self.paused && self.buffered >= self.high_mark {
            self.paused = true;
            self.pause_events =
                flow_pause_advance(self.pause_events, self.pause_events.saturating_add(1));
        }
        self.paused
    }

    pub fn on_drain(&mut self, bytes: u64) -> bool {
        self.buffered = self.buffered.saturating_sub(bytes);
        if self.paused && flow_below_low_mark(self.low_mark, self.buffered) {
            self.paused = false;
        }
        self.paused
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hysteresis_flow_watermark_pauses_at_high_mark_and_resumes_only_at_low_mark() {
        let mut fw = PtyFlowWatermark::new(4_096, 16_384);
        assert!(!fw.on_enqueue(10_000));
        assert!(fw.on_enqueue(8_000)); // 18_000 >= 16_384 -> paused!
        assert!(fw.on_drain(10_000)); // 8_000 > 4_096 -> stays paused (no thrash)!
        assert!(!fw.on_drain(4_000)); // 4_000 <= 4_096 -> resumed!
    }
}
