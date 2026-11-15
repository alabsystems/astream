// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Restart-durable first-seen record timestamp (`bt_ms`) tracker truncating stamps above
//! `recovered_head` on crash recovery so replacement records never inherit stale ages
//! (`Astream.HeldComp.TlaFirstSeenAgeStamp`).

#[cfg(clean_islands)]
#[path = "first_seen_age_stamp_island.rs"]
mod first_seen_age_stamp_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_stmp_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_age_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use first_seen_age_stamp_island::{hc_age_advance, hc_stmp_clamp};

/// Maximum tracked retention age (`2_592_000_000 ms` = 30 days).
pub const MAX_RETENTION_AGE_MS: u64 = 2_592_000_000;

contract_fn! {
    /// Verified age-expiry check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `hc_expired_by_age_isl`.
    #[must_use]
    pub const fn hc_expired_by_age(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct DurableStampHorizon {
    stamped_head: u64,
    last_tick_ms: u64,
}

impl DurableStampHorizon {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            stamped_head: 0,
            last_tick_ms: 0,
        }
    }

    pub fn clamp_to_recovered_head(&mut self, recovered_head: u64) {
        self.stamped_head = hc_stmp_clamp(self.stamped_head, recovered_head);
    }

    pub fn is_record_expired(&mut self, first_seen_ms: u64, now_ms: u64, max_age_ms: u64) -> bool {
        self.last_tick_ms = hc_age_advance(self.last_tick_ms, now_ms);
        let cap_age = hc_stmp_clamp(max_age_ms, MAX_RETENTION_AGE_MS);
        let age = self.last_tick_ms.saturating_sub(first_seen_ms);
        hc_expired_by_age(age, cap_age)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncates_unflushed_stamps_on_recovery_and_cuts_past_seven_day_age() {
        let mut h = DurableStampHorizon {
            stamped_head: 50,
            last_tick_ms: 1_000,
        };
        h.clamp_to_recovered_head(42);
        assert_eq!(h.stamped_head, 42);
        let week_ms = 7 * 24 * 3_600 * 1_000;
        assert!(!h.is_record_expired(1_000, 1_000 + week_ms - 1, week_ms));
        assert!(h.is_record_expired(1_000, 1_000 + week_ms, week_ms));
    }
}
