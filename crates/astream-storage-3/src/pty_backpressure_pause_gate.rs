// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hysteretic PTY master read-pause / resume backpressure gate
//! (`Astream.Pump.TlaPtyBackpressurePauseGate`).
//!
//! Protects `aspump` and `aterm` tabs when a child process floods stdout (`yes`,
//! `cat /dev/zero`, huge build logs) faster than the broker or remote link drains:
//! pauses PTY reads at `high_watermark` (`in_flight <= hard_cap`) and resumes only
//! once acknowledged drain drops `in_flight <= low_watermark`, preventing both OOM
//! and single-byte pause/resume oscillation.

#[cfg(clean_islands)]
#[path = "pty_backpressure_pause_gate_island.rs"]
mod pty_backpressure_pause_gate_island;
#[cfg(clean_islands)]
pub use pty_backpressure_pause_gate_island::{pty_inflight_clamp, pty_pause_seq_advance};

#[cfg(not(clean_islands))]
/// Clamp in-flight unacked PTY byte tally to `hard_cap`.
#[must_use]
pub const fn pty_inflight_clamp(cand_bytes: u64, hard_cap: u64) -> u64 {
    if cand_bytes < hard_cap {
        cand_bytes
    } else {
        hard_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of PTY backpressure pause episodes.
#[must_use]
pub const fn pty_pause_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// Hysteretic pause transition: pause at `>= high_wm`; stay paused until `<= low_wm`.
    #[must_use]
    pub const fn pty_next_paused(
        was_paused: bool,
        in_flight: u64,
        low_wm: u64,
        high_wm: u64,
    ) -> bool
    clauses [ensures result == ((was_paused && low_wm < in_flight) || (!was_paused && high_wm <= in_flight))]
    {
        (was_paused && low_wm < in_flight) || (!was_paused && high_wm <= in_flight)
    }
}

/// Hysteretic PTY read-pause gate for `aspump`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtyBackpressurePauseGate {
    low_watermark: u64,
    high_watermark: u64,
    hard_cap: u64,
    in_flight_bytes: u64,
    paused: bool,
    pause_episodes: u64,
}

impl PtyBackpressurePauseGate {
    #[must_use]
    pub const fn new(low_watermark: u64, high_watermark: u64, hard_cap: u64) -> Self {
        let hi = if high_watermark == 0 {
            65_536
        } else {
            high_watermark
        };
        let lo = if low_watermark < hi {
            low_watermark
        } else {
            hi / 2
        };
        let cap = if hard_cap < hi { hi } else { hard_cap };
        Self {
            low_watermark: lo,
            high_watermark: hi,
            hard_cap: cap,
            in_flight_bytes: 0,
            paused: false,
            pause_episodes: 0,
        }
    }

    #[must_use]
    pub const fn is_paused(&self) -> bool {
        self.paused
    }

    #[must_use]
    pub const fn in_flight_bytes(&self) -> u64 {
        self.in_flight_bytes
    }

    #[must_use]
    pub const fn pause_episodes(&self) -> u64 {
        self.pause_episodes
    }

    /// Maximum PTY read chunk allowed right now (`0` while paused).
    #[must_use]
    pub const fn readable_budget(&self) -> u64 {
        if self.paused {
            0
        } else {
            self.hard_cap.saturating_sub(self.in_flight_bytes)
        }
    }

    /// Record `n` bytes read from the PTY master and queued toward the broker.
    pub fn on_pty_read(&mut self, n: u64) -> bool {
        let next_bytes = self.in_flight_bytes.saturating_add(n);
        self.in_flight_bytes = pty_inflight_clamp(next_bytes, self.hard_cap);
        let next_paused = pty_next_paused(
            self.paused,
            self.in_flight_bytes,
            self.low_watermark,
            self.high_watermark,
        );
        if !self.paused && next_paused {
            let cand = self.pause_episodes.saturating_add(1);
            self.pause_episodes = pty_pause_seq_advance(self.pause_episodes, cand);
        }
        self.paused = next_paused;
        self.paused
    }

    /// Record `acked` bytes durably flushed to the broker.
    pub fn on_broker_ack(&mut self, acked: u64) -> bool {
        let next_bytes = self.in_flight_bytes.saturating_sub(acked);
        self.in_flight_bytes = pty_inflight_clamp(next_bytes, self.hard_cap);
        self.paused = pty_next_paused(
            self.paused,
            self.in_flight_bytes,
            self.low_watermark,
            self.high_watermark,
        );
        self.paused
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hysteresis_prevents_pause_resume_thrashing() {
        let mut gate = PtyBackpressurePauseGate::new(4_096, 16_384, 32_768);
        assert!(!gate.on_pty_read(10_000));
        // Crossing high_watermark (16_384) pauses PTY reads:
        assert!(gate.on_pty_read(8_000));
        assert_eq!(gate.readable_budget(), 0);
        assert_eq!(gate.pause_episodes(), 1);

        // Draining to 8_000 (> low_watermark 4_096) keeps PTY paused (no thrashing!):
        assert!(gate.on_broker_ack(10_000));
        assert_eq!(gate.in_flight_bytes(), 8_000);

        // Draining to <= 4_096 cleanly resumes PTY reads:
        assert!(!gate.on_broker_ack(4_000));
        assert_eq!(gate.in_flight_bytes(), 4_000);
        assert!(gate.readable_budget() > 0);
    }
}
