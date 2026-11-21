// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autonomous replica leader-lease TTL clock for a background lease-heartbeat failover daemon,
//! enforcing bounded lease durations and guard-band expiry before candidate election
//! (`Astream.LeaseFail.TlaLeaderLeaseTtl`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "leader_lease_ttl_island.rs"]
mod leader_lease_ttl_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_ttl_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_renew_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use leader_lease_ttl_island::{lhf_renew_advance, lhf_ttl_clamp};

/// Maximum leader lease duration (`30_000` ms).
pub const MAX_LEADER_LEASE_MS: u64 = 30_000;

contract_fn! {
    /// Verified lease expiry past guard band (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_lease_expired_isl`.
    #[must_use]
    pub const fn lhf_lease_expired(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct LeaderLeaseClock {
    ttl_ms: u64,
    guard_band_ms: u64,
    lease_deadline_ms: u64,
}

impl LeaderLeaseClock {
    #[must_use]
    pub const fn new(ttl_ms: u64, guard_band_ms: u64) -> Self {
        Self {
            ttl_ms: lhf_ttl_clamp(ttl_ms, MAX_LEADER_LEASE_MS),
            guard_band_ms: lhf_ttl_clamp(guard_band_ms, MAX_LEADER_LEASE_MS),
            lease_deadline_ms: 0,
        }
    }

    pub fn renew(&mut self, now_ms: u64) -> u64 {
        let cand = now_ms.saturating_add(self.ttl_ms);
        self.lease_deadline_ms = lhf_renew_advance(self.lease_deadline_ms, cand);
        self.lease_deadline_ms
    }

    #[must_use]
    pub const fn election_eligible(&self, now_ms: u64) -> bool {
        match self.lease_deadline_ms.checked_add(self.guard_band_ms) {
            Some(threshold) => lhf_lease_expired(now_ms, threshold),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn waits_for_ttl_plus_guard_band_before_triggering_election() {
        let mut c = LeaderLeaseClock::new(2_000, 250);
        assert_eq!(c.renew(1_000), 3_000);
        assert!(!c.election_eligible(3_200));
        assert!(c.election_eligible(3_250));
    }
}
