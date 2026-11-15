// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Permanent failed-flush poison latch (`broker.ordered-tier`: a failed deferred full flush marks
//! `<log>.id` `Lossy` and permanently poisons the open handle because a later `fsync` returning `0`
//! says nothing about dirty pages dropped by the failed flush; `Astream.OrdBar.TlaFailedFlushPoison`).

#[cfg(clean_islands)]
#[path = "failed_flush_poison_island.rs"]
mod failed_flush_poison_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_psn_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_lossy_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use failed_flush_poison_island::{ob_lossy_advance, ob_psn_clamp};

/// Poison state ceiling (`1 = PoisonedLossy`).
pub const POISONED_STATE: u64 = 1;

contract_fn! {
    /// Verified unpoisoned handle predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ob_log_healthy_isl`.
    #[must_use]
    pub const fn ob_log_healthy(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct FlushPoisonState {
    poisoned: u64,
    lossy_marks: u64,
}

impl FlushPoisonState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            poisoned: 0,
            lossy_marks: 0,
        }
    }

    pub fn on_deferred_flush_result(&mut self, ok: bool) -> bool {
        if !ok {
            self.poisoned = ob_psn_clamp(POISONED_STATE, POISONED_STATE);
            self.lossy_marks =
                ob_lossy_advance(self.lossy_marks, self.lossy_marks.saturating_add(1));
        }
        self.allow_operation()
    }

    #[must_use]
    pub const fn allow_operation(&self) -> bool {
        ob_log_healthy(0, self.poisoned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_flush_permanently_poisons_handle_even_if_subsequent_flush_succeeds() {
        let mut p = FlushPoisonState::new();
        assert!(p.on_deferred_flush_result(true));
        assert!(!p.on_deferred_flush_result(false));
        assert!(!p.on_deferred_flush_result(true));
        assert!(!p.allow_operation());
    }
}
