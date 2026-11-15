// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack WAN / Internet half-open TCP keepalive & liveness detector
//! (`Astream.Wire.TlaWanKeepaliveLivenessGate`).
//!
//! Tracks monotonic `now_ms`, inbound frame timestamps, and unacknowledged
//! keepalive probes (`missed_pings <= max_missed_pings`) with **zero heap
//! allocations** and **zero `unknown` obligations**, promptly detecting NAT
//! drops and half-open WAN sockets before `MAX_CONNS` slots stall.

#[cfg(clean_islands)]
#[path = "wan_keepalive_liveness_gate_island.rs"]
mod wan_keepalive_liveness_gate_island;
#[cfg(clean_islands)]
pub use wan_keepalive_liveness_gate_island::{keepalive_clock_advance, missed_pings_clamp};

#[cfg(not(clean_islands))]
/// Monotonically advance observed clock timestamp (`ms`).
#[must_use]
pub const fn keepalive_clock_advance(cur_ms: u64, cand_ms: u64) -> u64 {
    if cur_ms < cand_ms {
        cand_ms
    } else {
        cur_ms
    }
}

#[cfg(not(clean_islands))]
/// Clamp unacknowledged probe count to `max_missed`.
#[must_use]
pub const fn missed_pings_clamp(cand_missed: u64, max_missed: u64) -> u64 {
    if cand_missed < max_missed {
        cand_missed
    } else {
        max_missed
    }
}

contract_fn! {
    /// True iff `missed_pings >= max_missed` (connection must be torn down).
    #[must_use]
    pub const fn link_dead(missed_pings: u64, max_missed: u64) -> bool
    clauses [ensures result == (max_missed <= missed_pings)]
    {
        max_missed <= missed_pings
    }
}

/// Action returned on periodic WAN keepalive tick.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum KeepaliveVerdict {
    Healthy,
    SendPing { ping_seq: u64 },
    DeclareDead { missed_pings: u64 },
}

/// Pure stack WAN keepalive & half-open socket detector.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WanKeepaliveLivenessGate {
    idle_interval_ms: u64,
    probe_interval_ms: u64,
    max_missed_pings: u64,
    last_rx_ms: u64,
    last_probe_ms: u64,
    missed_pings: u64,
    ping_seq: u64,
}

impl WanKeepaliveLivenessGate {
    #[must_use]
    pub const fn new(
        now_ms: u64,
        idle_interval_ms: u64,
        probe_interval_ms: u64,
        max_missed_pings: u64,
    ) -> Self {
        let idle = if idle_interval_ms == 0 {
            1000
        } else {
            idle_interval_ms
        };
        let probe = if probe_interval_ms == 0 {
            500
        } else {
            probe_interval_ms
        };
        let max_missed = if max_missed_pings == 0 {
            1
        } else {
            max_missed_pings
        };
        Self {
            idle_interval_ms: idle,
            probe_interval_ms: probe,
            max_missed_pings: max_missed,
            last_rx_ms: now_ms,
            last_probe_ms: now_ms,
            missed_pings: 0,
            ping_seq: 0,
        }
    }

    #[must_use]
    pub const fn missed_pings(&self) -> u64 {
        self.missed_pings
    }

    #[must_use]
    pub const fn ping_seq(&self) -> u64 {
        self.ping_seq
    }

    #[must_use]
    pub const fn last_rx_ms(&self) -> u64 {
        self.last_rx_ms
    }

    /// Record any authenticated inbound frame or pong, resetting `missed_pings` to `0`.
    pub fn record_inbound(&mut self, now_ms: u64) {
        let t = keepalive_clock_advance(self.last_rx_ms, now_ms);
        self.last_rx_ms = t;
        self.last_probe_ms = keepalive_clock_advance(self.last_probe_ms, t);
        self.missed_pings = 0;
    }

    /// Evaluate WAN link health at `now_ms`.
    pub fn poll(&mut self, now_ms: u64) -> KeepaliveVerdict {
        let now = keepalive_clock_advance(self.last_rx_ms, now_ms);
        let since_rx = now.saturating_sub(self.last_rx_ms);
        if since_rx < self.idle_interval_ms {
            return KeepaliveVerdict::Healthy;
        }
        let since_probe = now.saturating_sub(self.last_probe_ms);
        if self.missed_pings > 0 && since_probe < self.probe_interval_ms {
            return KeepaliveVerdict::Healthy;
        }
        let next_missed = self.missed_pings.saturating_add(1);
        self.missed_pings = missed_pings_clamp(next_missed, self.max_missed_pings);
        self.last_probe_ms = keepalive_clock_advance(self.last_probe_ms, now);
        if link_dead(next_missed, self.max_missed_pings.saturating_add(1)) {
            return KeepaliveVerdict::DeclareDead {
                missed_pings: self.missed_pings,
            };
        }
        let next_seq = self.ping_seq.saturating_add(1);
        self.ping_seq = keepalive_clock_advance(self.ping_seq, next_seq);
        KeepaliveVerdict::SendPing {
            ping_seq: self.ping_seq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sends_bounded_probes_and_declares_half_open_socket_dead() {
        let mut gate = WanKeepaliveLivenessGate::new(1_000, 5_000, 1_000, 2);
        assert_eq!(gate.poll(4_999), KeepaliveVerdict::Healthy);
        // Idle threshold reached -> Ping #1:
        assert_eq!(gate.poll(6_000), KeepaliveVerdict::SendPing { ping_seq: 1 });
        // Before probe_interval_ms -> wait:
        assert_eq!(gate.poll(6_500), KeepaliveVerdict::Healthy);
        // Second probe at +1000ms -> Ping #2:
        assert_eq!(gate.poll(7_000), KeepaliveVerdict::SendPing { ping_seq: 2 });
        // Still no inbound traffic after 2 probes -> DeclareDead!
        assert_eq!(
            gate.poll(8_000),
            KeepaliveVerdict::DeclareDead { missed_pings: 2 }
        );
        // Inbound frame revives the state cleanly:
        gate.record_inbound(8_500);
        assert_eq!(gate.missed_pings(), 0);
        assert_eq!(gate.poll(9_000), KeepaliveVerdict::Healthy);
    }
}
