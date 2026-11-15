// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure-stack WAN/NAT half-open TCP keepalive probe detector for `aterm-link`
//! (`Astream.Wire.TlaWanKeepaliveLivenessProbe`).
//!
//! Detects silent NAT-table drops and half-open WAN links without false positives during large
//! frame transfers: any inbound byte progress resets `missed_probes = 0`, idle intervals emit
//! monotone `probe_epoch` pings, and reaching `max_missed_probes` triggers immediate reconnect
//! failover with `0 unknown` obligations in `astream-wire`.

#[cfg(clean_islands)]
#[path = "wan_keepalive_liveness_probe_island.rs"]
mod wan_keepalive_liveness_probe_island;
#[cfg(clean_islands)]
pub use wan_keepalive_liveness_probe_island::{
    wan_missed_probes_clamp_b120, wan_probe_epoch_advance_b120,
};

#[cfg(not(clean_islands))]
/// Clamp `cand_missed` to `max_missed`.
#[must_use]
pub const fn wan_missed_probes_clamp_b120(cand_missed: u64, max_missed: u64) -> u64 {
    if cand_missed < max_missed {
        cand_missed
    } else {
        max_missed
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `probe_epoch`.
#[must_use]
pub const fn wan_probe_epoch_advance_b120(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `missed_probes >= max_missed`.
    #[must_use]
    pub const fn wan_peer_dead_b120(missed_probes: u64, max_missed: u64) -> bool
    clauses [ensures result == (max_missed <= missed_probes)]
    {
        max_missed <= missed_probes
    }
}

pub const DEFAULT_PROBE_INTERVAL_MS: u64 = 5_000;
pub const DEFAULT_MAX_MISSED_PROBES: u64 = 3;

/// Keepalive tick outcome on a WAN `aterm-link` transport.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WanProbeAction {
    HealthyIdle,
    SendPing {
        probe_epoch: u64,
        missed_so_far: u64,
    },
    DeclareHalfOpenDead {
        missed_probes: u64,
    },
}

/// Pure-stack half-open TCP detector (`0` heap allocations, `0` non-test `Debug` derives).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WanKeepaliveLivenessProbe {
    probe_interval_ms: u64,
    max_missed: u64,
    last_rx_ms: u64,
    last_probe_ms: u64,
    missed_probes: u64,
    probe_epoch: u64,
}

impl Default for WanKeepaliveLivenessProbe {
    fn default() -> Self {
        Self::new(DEFAULT_PROBE_INTERVAL_MS, DEFAULT_MAX_MISSED_PROBES, 0)
    }
}

impl WanKeepaliveLivenessProbe {
    #[must_use]
    pub const fn new(probe_interval_ms: u64, max_missed: u64, now_ms: u64) -> Self {
        Self {
            probe_interval_ms: if probe_interval_ms == 0 {
                1
            } else {
                probe_interval_ms
            },
            max_missed: if max_missed == 0 { 1 } else { max_missed },
            last_rx_ms: now_ms,
            last_probe_ms: now_ms,
            missed_probes: 0,
            probe_epoch: 0,
        }
    }

    #[must_use]
    pub const fn missed_probes(&self) -> u64 {
        self.missed_probes
    }

    #[must_use]
    pub const fn probe_epoch(&self) -> u64 {
        self.probe_epoch
    }

    /// Record inbound bytes or Pong receipt at `now_ms`, resetting `missed_probes` to `0`.
    pub fn on_inbound_activity(&mut self, now_ms: u64) {
        if now_ms > self.last_rx_ms {
            self.last_rx_ms = now_ms;
        }
        if now_ms > self.last_probe_ms {
            self.last_probe_ms = now_ms;
        }
        self.missed_probes = 0;
    }

    /// Evaluate periodic timer at `now_ms`.
    pub fn poll_tick(&mut self, now_ms: u64) -> WanProbeAction {
        let anchor = if self.last_rx_ms > self.last_probe_ms {
            self.last_rx_ms
        } else {
            self.last_probe_ms
        };
        if now_ms.saturating_sub(anchor) < self.probe_interval_ms {
            return WanProbeAction::HealthyIdle;
        }
        self.last_probe_ms = now_ms;
        let next_missed =
            wan_missed_probes_clamp_b120(self.missed_probes.saturating_add(1), self.max_missed);
        self.missed_probes = next_missed;
        if wan_peer_dead_b120(self.missed_probes, self.max_missed) {
            return WanProbeAction::DeclareHalfOpenDead {
                missed_probes: self.missed_probes,
            };
        }
        let next_ep = self.probe_epoch.saturating_add(1);
        self.probe_epoch = wan_probe_epoch_advance_b120(self.probe_epoch, next_ep);
        WanProbeAction::SendPing {
            probe_epoch: self.probe_epoch,
            missed_so_far: self.missed_probes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn emits_pings_resets_on_rx_and_declares_half_open_dead_on_third_miss() {
        let mut p = WanKeepaliveLivenessProbe::new(5_000, 3, 1_000);
        assert_eq!(p.poll_tick(4_000), WanProbeAction::HealthyIdle);
        assert_eq!(
            p.poll_tick(6_000),
            WanProbeAction::SendPing {
                probe_epoch: 1,
                missed_so_far: 1
            }
        );
        // Inbound frame bytes reset missed count without requiring a separate Pong!
        p.on_inbound_activity(7_000);
        assert_eq!(p.missed_probes(), 0);
        assert_eq!(
            p.poll_tick(12_000),
            WanProbeAction::SendPing {
                probe_epoch: 2,
                missed_so_far: 1
            }
        );
        assert_eq!(
            p.poll_tick(17_000),
            WanProbeAction::SendPing {
                probe_epoch: 3,
                missed_so_far: 2
            }
        );
        assert_eq!(
            p.poll_tick(22_000),
            WanProbeAction::DeclareHalfOpenDead { missed_probes: 3 }
        );
    }
}
