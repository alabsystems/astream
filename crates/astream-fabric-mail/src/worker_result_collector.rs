// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Worker completion report collector tracking `aterm ctl @<sid> result` across revision-gated
//! `aterm ctl await task @<sid>:<rev>` wakeups (`Astream.FabMail.TlaWorkerResultCollector`).

use astream_digest::Sha256;

#[cfg(clean_islands)]
#[path = "worker_result_collector_island.rs"]
mod worker_result_collector_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_res_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_rev_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use worker_result_collector_island::{fm_res_clamp, fm_rev_advance};

/// Maximum report summary bytes stored per spawned worker (`16_384`).
pub const MAX_RESULT_BYTES: u64 = 16_384;

contract_fn! {
    /// Verified revision freshness check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `fm_result_fresh_isl`.
    #[must_use]
    pub const fn fm_result_fresh(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct WorkerResultSlot {
    last_rev: u64,
    last_digest: [u8; 32],
    stored_bytes: u64,
}

impl WorkerResultSlot {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            last_rev: 0,
            last_digest: [0u8; 32],
            stored_bytes: 0,
        }
    }

    pub fn ingest_result(&mut self, rev: u64, report: &[u8]) -> bool {
        let min_rev = self.last_rev.saturating_add(1);
        if !fm_result_fresh(rev, min_rev) {
            return false;
        }
        self.last_rev = fm_rev_advance(self.last_rev, rev);
        self.stored_bytes = fm_res_clamp(report.len() as u64, MAX_RESULT_BYTES);
        let stored_slice = match report.get(..self.stored_bytes as usize) {
            Some(s) => s,
            None => report,
        };
        self.last_digest = Sha256::digest_slice(stored_slice);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_newer_worker_revision_and_rejects_stale_duplicate() {
        let mut s = WorkerResultSlot::new();
        assert!(s.ingest_result(1, b"landed commit abc1234"));
        assert!(!s.ingest_result(1, b"duplicate"));
        assert!(s.ingest_result(2, b"follow-up check green"));
    }
}
