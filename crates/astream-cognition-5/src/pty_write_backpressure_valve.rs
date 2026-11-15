// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Non-blocking PTY master write-queue hysteresis backpressure valve
//! (`Astream.Pump.TlaPtyWriteBackpressureValve`).
//!
//! Prevents `aspump` or Autopilot prompt injection bursts from deadlocking PTY master writes
//! when a foreground child stops draining stdin: pauses new bus-to-PTY writes at `high_water_bytes`
//! and only re-opens admission once kernel PTY drain drops queued bytes to `<= low_water_bytes`.

#[cfg(clean_islands)]
#[path = "pty_write_backpressure_valve_island.rs"]
mod pty_write_backpressure_valve_island;
#[cfg(clean_islands)]
pub use pty_write_backpressure_valve_island::{
    pty_queued_bytes_clamp_b117, pty_written_total_advance_b117,
};

#[cfg(not(clean_islands))]
/// Clamp queued PTY write-buffer bytes to `max_queue_bytes`.
#[must_use]
pub const fn pty_queued_bytes_clamp_b117(cand_queued: u64, max_queue_bytes: u64) -> u64 {
    if cand_queued < max_queue_bytes {
        cand_queued
    } else {
        max_queue_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance cumulative `written_total` bytes drained into PTY master.
#[must_use]
pub const fn pty_written_total_advance_b117(cur_total: u64, cand_total: u64) -> u64 {
    if cur_total < cand_total {
        cand_total
    } else {
        cur_total
    }
}

contract_fn! {
    /// True iff `proposed_queued` fits within `max_queue_bytes`.
    #[must_use]
    pub const fn pty_write_fits_queue_b117(proposed_queued: u64, max_queue_bytes: u64) -> bool
    clauses [ensures result == (proposed_queued <= max_queue_bytes)]
    {
        proposed_queued <= max_queue_bytes
    }
}

/// Admission outcome for a proposed PTY master write chunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtyWriteAdmission {
    Admitted { queued_bytes: u64, throttled: bool },
    BackpressuredHoldBus { queued_bytes: u64 },
}

/// Hysteresis backpressure valve for non-blocking PTY master input queues.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyWriteBackpressureValve {
    queued_bytes: u64,
    low_water_bytes: u64,
    high_water_bytes: u64,
    max_queue_bytes: u64,
    throttled: bool,
    written_total: u64,
}

impl PtyWriteBackpressureValve {
    #[must_use]
    pub const fn new(low_water_bytes: u64, high_water_bytes: u64, max_queue_bytes: u64) -> Self {
        let max_q = if max_queue_bytes == 0 {
            65_536
        } else {
            max_queue_bytes
        };
        let hw = pty_queued_bytes_clamp_b117(
            if high_water_bytes == 0 {
                max_q
            } else {
                high_water_bytes
            },
            max_q,
        );
        let lw = pty_queued_bytes_clamp_b117(low_water_bytes, hw);
        Self {
            queued_bytes: 0,
            low_water_bytes: lw,
            high_water_bytes: hw,
            max_queue_bytes: max_q,
            throttled: false,
            written_total: 0,
        }
    }

    #[must_use]
    pub const fn queued_bytes(&self) -> u64 {
        self.queued_bytes
    }

    #[must_use]
    pub const fn is_throttled(&self) -> bool {
        self.throttled
    }

    /// Attempt to enqueue `chunk_bytes` for non-blocking PTY master write.
    pub fn try_enqueue(&mut self, chunk_bytes: u64) -> PtyWriteAdmission {
        if self.throttled {
            return PtyWriteAdmission::BackpressuredHoldBus {
                queued_bytes: self.queued_bytes,
            };
        }
        let proposed = self.queued_bytes.saturating_add(chunk_bytes);
        if !pty_write_fits_queue_b117(proposed, self.max_queue_bytes) {
            self.throttled = true;
            return PtyWriteAdmission::BackpressuredHoldBus {
                queued_bytes: self.queued_bytes,
            };
        }
        self.queued_bytes = pty_queued_bytes_clamp_b117(proposed, self.max_queue_bytes);
        if self.queued_bytes >= self.high_water_bytes {
            self.throttled = true;
        }
        PtyWriteAdmission::Admitted {
            queued_bytes: self.queued_bytes,
            throttled: self.throttled,
        }
    }

    /// Record `drained_bytes` written to the kernel PTY master fd.
    pub fn on_pty_drained(&mut self, drained_bytes: u64) -> bool {
        let actual = if drained_bytes > self.queued_bytes {
            self.queued_bytes
        } else {
            drained_bytes
        };
        self.queued_bytes = self.queued_bytes.saturating_sub(actual);
        let next_tot = self.written_total.saturating_add(actual);
        self.written_total = pty_written_total_advance_b117(self.written_total, next_tot);
        if self.throttled && self.queued_bytes <= self.low_water_bytes {
            self.throttled = false;
        }
        !self.throttled
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn throttles_at_high_water_and_resumes_at_low_water() {
        let mut v = PtyWriteBackpressureValve::new(2_000, 8_000, 16_000);
        assert_eq!(
            v.try_enqueue(9_000),
            PtyWriteAdmission::Admitted {
                queued_bytes: 9_000,
                throttled: true
            }
        );
        assert_eq!(
            v.try_enqueue(500),
            PtyWriteAdmission::BackpressuredHoldBus {
                queued_bytes: 9_000
            }
        );
        assert!(!v.on_pty_drained(5_000)); // 4_000 > low_water 2_000 -> still throttled
        assert!(v.on_pty_drained(2_500)); // 1_500 <= low_water -> resumed!
    }
}
