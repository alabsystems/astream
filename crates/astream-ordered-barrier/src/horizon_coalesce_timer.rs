// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Ordered { horizon }` (`100ms` in `aterm-broker.escalate`) full-flush coalescer skipping
//! redundant `sync_full` syscalls whenever `durable_head >= target_offset`
//! (`Astream.OrdBar.TlaHorizonCoalesceTimer`).

#[cfg(clean_islands)]
#[path = "horizon_coalesce_timer_island.rs"]
mod horizon_coalesce_timer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_hor_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_sync_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use horizon_coalesce_timer_island::{ob_hor_clamp, ob_sync_advance};

/// Maximum `Ordered` horizon (`10_000 ms`).
pub const MAX_ORDERED_HORIZON_MS: u64 = 10_000;

contract_fn! {
    /// Verified durable-coverage skip check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ob_flush_covered_isl`.
    #[must_use]
    pub const fn ob_flush_covered(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct HorizonFlushCoalescer {
    horizon_ms: u64,
    durable_head: u64,
    flushes_run: u64,
}

impl HorizonFlushCoalescer {
    #[must_use]
    pub const fn new(horizon_ms: u64) -> Self {
        Self {
            horizon_ms: ob_hor_clamp(horizon_ms, MAX_ORDERED_HORIZON_MS),
            durable_head: 0,
            flushes_run: 0,
        }
    }

    #[must_use]
    pub const fn horizon_ms(&self) -> u64 {
        self.horizon_ms
    }

    pub fn needs_sync_full(&mut self, target_offset: u64, newly_flushed_to: Option<u64>) -> bool {
        if let Some(d) = newly_flushed_to {
            self.durable_head = ob_sync_advance(self.durable_head, d);
            self.flushes_run = self.flushes_run.saturating_add(1);
        }
        !ob_flush_covered(self.durable_head, target_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_sync_full_when_target_offset_is_already_covered_by_durable_head() {
        let mut c = HorizonFlushCoalescer::new(100);
        assert!(c.needs_sync_full(10, None));
        assert!(!c.needs_sync_full(10, Some(15)));
        assert!(!c.needs_sync_full(15, None));
    }
}
