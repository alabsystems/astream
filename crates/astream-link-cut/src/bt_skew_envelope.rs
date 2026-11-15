// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone broker-time (`0xB6 bt_ms`, `REQUIREMENTS R3`) cross-shard skew verifier bounding wall
//! drift across `ShardedBroker` instances when ordering multi-shard cuts (`Astream.LinkCut.TlaBtSkewEnvelope`).

#[cfg(clean_islands)]
#[path = "bt_skew_envelope_island.rs"]
mod bt_skew_envelope_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_skew_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_bt_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bt_skew_envelope_island::{lc_bt_advance, lc_skew_clamp};

/// Maximum tolerated inter-shard `bt_ms` skew (`5_000 ms`).
pub const MAX_BT_SKEW_MS: u64 = 5_000;

contract_fn! {
    /// Verified inter-shard skew bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lc_skew_within_bound_isl`.
    #[must_use]
    pub const fn lc_skew_within_bound(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct BtSkewGuard {
    max_skew_ms: u64,
    high_bt_ms: u64,
}

impl BtSkewGuard {
    #[must_use]
    pub const fn new(max_skew_ms: u64) -> Self {
        Self {
            max_skew_ms: lc_skew_clamp(max_skew_ms, MAX_BT_SKEW_MS),
            high_bt_ms: 0,
        }
    }

    pub fn observe_bt(&mut self, shard_bt_ms: u64) -> bool {
        self.high_bt_ms = lc_bt_advance(self.high_bt_ms, shard_bt_ms);
        let skew = self.high_bt_ms.saturating_sub(shard_bt_ms);
        lc_skew_within_bound(self.max_skew_ms, skew)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_bounded_shard_bt_skew_and_flags_runaway_lag() {
        let mut g = BtSkewGuard::new(500);
        assert!(g.observe_bt(10_000));
        assert!(g.observe_bt(9_700));
        assert!(!g.observe_bt(9_000));
    }
}
