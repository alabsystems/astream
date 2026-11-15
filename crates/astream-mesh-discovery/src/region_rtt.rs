// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RFC 6298 Jacobson/Karels integer SRTT + RTTVAR estimator and lowest-cost cross-region
//! gateway selector (`ROADMAP.md` line 124, `Astream.Mesh.TlaRegionRtt`).
//!
//! Uses pure unsigned integer bit-shifts (`>> 3` for `1/8`, `>> 2` for `1/4`) with zero
//! floating-point non-determinism across platforms, clamps hostile RTT spikes via Clean-origin
//! `rtt_sample_clamp`, advances routing epochs via `rtt_epoch_advance`, and selects the
//! lowest-cost (`srtt_ms + 2 * rttvar_ms`) gateway meeting the configured SLA ceiling.

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "region_rtt_island.rs"]
mod region_rtt_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rtt_sample_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rtt_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use region_rtt_island::{rtt_epoch_advance, rtt_sample_clamp};

/// Upper clamp on individual RTT probe samples (`30` seconds in milliseconds).
pub const MAX_RTT_SAMPLE_MS: u64 = 30_000;

contract_fn! {
    /// Verified SLA check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `rtt_within_sla_isl`. Used as `rtt_within_sla(sla_ceiling_ms, gateway_cost_ms)`.
    #[must_use]
    pub const fn rtt_within_sla(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Per-gateway RFC 6298 smoothed RTT state (stored in microseconds for sub-ms precision).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GatewayRttStats {
    pub srtt_us: u64,
    pub rttvar_us: u64,
    pub samples: u64,
}

impl GatewayRttStats {
    /// Composite routing score in milliseconds: `(srtt_us + 2 * rttvar_us) / 1000`.
    #[must_use]
    pub const fn routing_cost_ms(&self) -> u64 {
        self.srtt_us
            .saturating_add(self.rttvar_us.saturating_mul(2))
            / 1000
    }
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Maximum distinct regional gateways tracked in one RTT table.
pub const MAX_RTT_GATEWAYS: usize = 256;

/// Multi-region gateway RTT estimator and selector.
#[derive(Debug, Clone)]
pub struct RegionRttTable {
    sla_ceiling_ms: u64,
    epoch: u64,
    gateways: BTreeMap<String, GatewayRttStats>,
}

impl Default for RegionRttTable {
    fn default() -> Self {
        Self::new()
    }
}

impl RegionRttTable {
    #[must_use]
    pub fn new() -> Self {
        Self::with_sla_ms(500)
    }

    #[must_use]
    pub fn with_sla_ms(sla_ceiling_ms: u64) -> Self {
        Self {
            sla_ceiling_ms: rtt_sample_clamp(sla_ceiling_ms, MAX_RTT_SAMPLE_MS),
            epoch: 0,
            gateways: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.gateways.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.gateways.is_empty()
    }

    /// Records an RTT sample in milliseconds for `gateway_id` using RFC 6298 Jacobson/Karels smoothing.
    #[allow(clippy::manual_map)]
    pub fn record_sample_ms(&mut self, gateway_id: &str, raw_sample_ms: u64) -> GatewayRttStats {
        let clamped_ms = rtt_sample_clamp(raw_sample_ms, MAX_RTT_SAMPLE_MS);
        let sample_us = clamped_ms.saturating_mul(1000);
        if gateway_id.is_empty() {
            return GatewayRttStats {
                srtt_us: sample_us,
                rttvar_us: sample_us >> 1,
                samples: 0,
            };
        }

        let prev_opt = match self.gateways.get(gateway_id) {
            Some(&p) => Some(p),
            None => None,
        };
        if prev_opt.is_none() && self.gateways.len() >= MAX_RTT_GATEWAYS {
            return GatewayRttStats {
                srtt_us: sample_us,
                rttvar_us: sample_us >> 1,
                samples: 0,
            };
        }

        self.epoch = rtt_epoch_advance(self.epoch, self.epoch.saturating_add(1));

        let next = match prev_opt {
            None => GatewayRttStats {
                srtt_us: sample_us,
                rttvar_us: sample_us >> 1,
                samples: 1,
            },
            Some(prev) => {
                let abs_err = if prev.srtt_us >= sample_us {
                    prev.srtt_us.saturating_sub(sample_us)
                } else {
                    sample_us.saturating_sub(prev.srtt_us)
                };
                // rttvar = (3 * rttvar + |srtt - sample|) / 4
                let rttvar_us = (prev.rttvar_us.saturating_mul(3).saturating_add(abs_err)) >> 2;
                // srtt = (7 * srtt + sample) / 8
                let srtt_us = (prev.srtt_us.saturating_mul(7).saturating_add(sample_us)) >> 3;
                GatewayRttStats {
                    srtt_us,
                    rttvar_us,
                    samples: prev.samples.saturating_add(1),
                }
            }
        };
        self.gateways.insert(clone_str(gateway_id), next);
        next
    }

    /// Picks the lowest-cost `(gateway_id, cost_ms)` within `sla_ceiling_ms` (lexicographic tie-break).
    #[must_use]
    #[allow(clippy::manual_map)]
    pub fn best_gateway_within_sla(&self) -> Option<(String, u64)> {
        let mut best: Option<(&str, u64)> = None;
        for (gw, st) in &self.gateways {
            let cost = st.routing_cost_ms();
            if !rtt_within_sla(self.sla_ceiling_ms, cost) {
                continue;
            }
            match best {
                None => best = Some((gw.as_str(), cost)),
                Some((_, best_cost)) if cost < best_cost => best = Some((gw.as_str(), cost)),
                _ => {}
            }
        }
        match best {
            Some((g, c)) => Some((clone_str(g), c)),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc6298_rtt_smoothing_picks_lowest_cost_gateway_and_rejects_over_sla() {
        let mut tbl = RegionRttTable::with_sla_ms(200);
        for _ in 0..8 {
            tbl.record_sample_ms("gw-us-west", 24);
            tbl.record_sample_ms("gw-eu-central", 110);
            tbl.record_sample_ms("gw-sat-link", 650);
        }
        let (winner, cost) = tbl.best_gateway_within_sla().unwrap();
        assert_eq!(winner, "gw-us-west");
        assert!(cost <= 35);

        let mut strict = RegionRttTable::with_sla_ms(50);
        strict.record_sample_ms("gw-far", 400);
        assert!(strict.best_gateway_within_sla().is_none());
    }
}
