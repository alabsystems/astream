// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Logarithmic `O(log N)` binary-search divergence locator pinpointing the exact first tampered
//! or divergent log offset between two replicas (`Astream.Audit.TlaTamperBisect`).

#[cfg(clean_islands)]
#[path = "tamper_bisect_island.rs"]
mod tamper_bisect_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bisect_probes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bisect_low_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use tamper_bisect_island::{bisect_low_advance, bisect_probes_clamp};

/// 64 probes suffice to bisect the entire `u64` offset space!
pub const MAX_BISECT_PROBES: u64 = 64;

contract_fn! {
    /// Verified convergence check (`threshold <= observed`, i.e. `high <= low`),
    /// linked via `clean-kernel-defeq` to `bisect_converged_isl`.
    #[must_use]
    pub const fn bisect_converged(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Interactive `O(log N)` bisection state locating the earliest offset where digests disagree.
#[derive(Debug, Clone)]
pub struct TamperBisectSession {
    low: u64,
    high: u64,
    probes: u64,
}

impl TamperBisectSession {
    #[must_use]
    pub const fn new(total_records: u64) -> Self {
        Self {
            low: 0,
            high: total_records,
            probes: 0,
        }
    }

    #[must_use]
    pub const fn next_probe_offset(&self) -> Option<u64> {
        if bisect_converged(self.low, self.high) || self.probes >= MAX_BISECT_PROBES {
            return None;
        }
        let span = self.high.saturating_sub(self.low);
        Some(self.low.saturating_add(span >> 1))
    }

    pub fn record_probe_result(&mut self, probed_offset: u64, prefix_matches: bool) {
        if probed_offset < self.low || probed_offset >= self.high {
            return;
        }
        self.probes = bisect_probes_clamp(self.probes.saturating_add(1), MAX_BISECT_PROBES);
        if prefix_matches {
            let next_lo = probed_offset.saturating_add(1);
            self.low = bisect_low_advance(self.low, next_lo);
        } else {
            self.high = probed_offset;
        }
    }

    #[must_use]
    pub const fn pinpointed_corrupt_offset(&self) -> Option<u64> {
        if bisect_converged(self.low, self.high) {
            Some(self.low)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bisect_pinpoints_exact_corrupted_offset_in_million_record_log_within_20_probes() {
        let mut b = TamperBisectSession::new(1_000_000);
        let corrupt_at = 731_419u64;
        while let Some(probe) = b.next_probe_offset() {
            b.record_probe_result(probe, probe < corrupt_at);
        }
        assert_eq!(b.pinpointed_corrupt_offset(), Some(corrupt_at));
        assert!(b.probes <= 20);
    }
}
