// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hysteresis PTY-to-broker backpressure valve (`aspump` RSS & kernel PTY flow control).
//!
//! When a child process inside an `aterm` tab writes faster than a WAN/congested broker
//! connection acknowledges `Publish` frames, unbounded buffering inflates `aspump` memory
//! while single-threshold throttling causes `POLLIN` thrashing.
//!
//! `PtyBackpressureValve` enforces dual-watermark hysteresis bounded by `max_inflight_bytes`:
//! - `Flowing` while `inflight_bytes < high_water_bytes`: `aspump` polls PTY master `POLLIN`
//!   for up to `readable_budget_bytes()`.
//! - Transitions to `Paused { pause_epoch }` at `inflight_bytes >= high_water_bytes` so
//!   kernel PTY buffer backpressure naturally blocks the producer's `write(2)` without
//!   dropping a single terminal byte.
//! - Resumes `Flowing` only once broker acks drain `inflight_bytes <= low_water_bytes`.
//!
//! Clean specification: `pump_backpressure_valve_island.rs` (`Astream.Pump.TlaPtyBackpressureValve`).

#[cfg(clean_islands)]
#[path = "pump_backpressure_valve_island.rs"]
mod pump_backpressure_valve_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn valve_inflight_clamp(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn valve_pause_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use pump_backpressure_valve_island::{valve_inflight_clamp, valve_pause_epoch_advance};

/// Default low-water resume threshold (`256 KiB`).
pub const DEFAULT_LOW_WATER_BYTES: u64 = 256 * 1024;
/// Default high-water pause threshold (`1 MiB`).
pub const DEFAULT_HIGH_WATER_BYTES: u64 = 1024 * 1024;
/// Default hard cap on unacknowledged PTY bytes (`2 MiB`).
pub const DEFAULT_MAX_INFLIGHT_BYTES: u64 = 2 * 1024 * 1024;

contract_fn! {
    /// Kernel-certified check that `inflight_bytes <= max_bytes`, linked via
    /// `clean-kernel-defeq` to `valve_inflight_within_max_isl`.
    #[must_use]
    pub const fn valve_inflight_within_max(inflight_bytes: u64, max_bytes: u64) -> bool
    clauses [ensures result == (inflight_bytes <= max_bytes)]
    {
        inflight_bytes <= max_bytes
    }
}

/// Current PTY master read-polling state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValvePollState {
    /// Poll PTY master `POLLIN` for up to `budget_bytes`.
    Flowing { budget_bytes: u64 },
    /// Omit PTY master `POLLIN` until broker acks drain `inflight_bytes <= low_water_bytes`.
    Paused { pause_epoch: u64 },
}

/// Dual-watermark hysteresis flow-control valve for `aspump`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PtyBackpressureValve {
    inflight_bytes: u64,
    low_water_bytes: u64,
    high_water_bytes: u64,
    max_inflight_bytes: u64,
    paused: bool,
    pause_epoch: u64,
}

impl PtyBackpressureValve {
    /// Construct a valve with `low_water <= high_water <= max_inflight`.
    #[must_use]
    pub fn new(low_water_bytes: u64, high_water_bytes: u64, max_inflight_bytes: u64) -> Self {
        let max_b = if max_inflight_bytes == 0 {
            DEFAULT_MAX_INFLIGHT_BYTES
        } else {
            max_inflight_bytes
        };
        let high_b = if high_water_bytes == 0 || high_water_bytes > max_b {
            max_b
        } else {
            high_water_bytes
        };
        let low_b = if low_water_bytes > high_b {
            high_b / 2
        } else {
            low_water_bytes
        };
        Self {
            inflight_bytes: 0,
            low_water_bytes: low_b,
            high_water_bytes: high_b,
            max_inflight_bytes: max_b,
            paused: false,
            pause_epoch: 0,
        }
    }

    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(
            DEFAULT_LOW_WATER_BYTES,
            DEFAULT_HIGH_WATER_BYTES,
            DEFAULT_MAX_INFLIGHT_BYTES,
        )
    }

    #[must_use]
    pub const fn inflight_bytes(&self) -> u64 {
        self.inflight_bytes
    }

    #[must_use]
    pub const fn is_paused(&self) -> bool {
        self.paused
    }

    #[must_use]
    pub const fn pause_epoch(&self) -> u64 {
        self.pause_epoch
    }

    /// Current poll decision before calling `poll(2)` on the PTY master fd.
    #[must_use]
    pub fn poll_state(&self) -> ValvePollState {
        if self.paused {
            ValvePollState::Paused {
                pause_epoch: self.pause_epoch,
            }
        } else {
            let rem = self.max_inflight_bytes.saturating_sub(self.inflight_bytes);
            ValvePollState::Flowing { budget_bytes: rem }
        }
    }

    /// Record `enqueued_bytes` read from PTY master and queued for broker `Publish`.
    pub fn on_pty_read(&mut self, enqueued_bytes: u64) -> ValvePollState {
        let cand = self.inflight_bytes.saturating_add(enqueued_bytes);
        let clamped = valve_inflight_clamp(cand, self.max_inflight_bytes);
        let _ = valve_inflight_within_max(clamped, self.max_inflight_bytes);
        self.inflight_bytes = clamped;

        if !self.paused && self.inflight_bytes >= self.high_water_bytes {
            self.paused = true;
            self.pause_epoch =
                valve_pause_epoch_advance(self.pause_epoch, self.pause_epoch.saturating_add(1));
        }
        self.poll_state()
    }

    /// Record `acked_bytes` confirmed by broker `Ack` frames.
    pub fn on_broker_ack(&mut self, acked_bytes: u64) -> ValvePollState {
        let reduced = self.inflight_bytes.saturating_sub(acked_bytes);
        let clamped = valve_inflight_clamp(reduced, self.max_inflight_bytes);
        let _ = valve_inflight_within_max(clamped, self.max_inflight_bytes);
        self.inflight_bytes = clamped;

        if self.paused && self.inflight_bytes <= self.low_water_bytes {
            self.paused = false;
        }
        self.poll_state()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hysteresis_pauses_at_high_water_and_stays_paused_until_low_water() {
        let mut valve = PtyBackpressureValve::new(256, 1_024, 2_048);
        assert_eq!(
            valve.poll_state(),
            ValvePollState::Flowing {
                budget_bytes: 2_048
            }
        );

        // Read 900 bytes (< 1024 high-water) -> still Flowing.
        assert_eq!(
            valve.on_pty_read(900),
            ValvePollState::Flowing {
                budget_bytes: 1_148
            }
        );

        // Read 200 more bytes (1100 >= 1024 high-water) -> transitions to Paused (epoch 1).
        assert_eq!(
            valve.on_pty_read(200),
            ValvePollState::Paused { pause_epoch: 1 }
        );
        assert!(valve.is_paused());

        // Partial ack (500 bytes -> 600 remaining > 256 low-water) -> stays Paused (no thrashing!).
        assert_eq!(
            valve.on_broker_ack(500),
            ValvePollState::Paused { pause_epoch: 1 }
        );

        // Drain to 200 bytes (<= 256 low-water) -> resumes Flowing!
        assert_eq!(
            valve.on_broker_ack(400),
            ValvePollState::Flowing {
                budget_bytes: 1_848
            }
        );
        assert!(!valve.is_paused());
    }
}
