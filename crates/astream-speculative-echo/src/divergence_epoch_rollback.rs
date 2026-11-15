// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Speculative overlay rollback verifier checking `reconciled == authoritative` via SHA-256 screen
//! serialization equality (`s1 == s2 <=> s1.serialize() == s2.serialize()`;
//! `Astream.SpecEcho.TlaDivergenceEpochRollback`).

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

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "divergence_epoch_rollback_island.rs"]
mod divergence_epoch_rollback_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_dirty_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_rb_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use divergence_epoch_rollback_island::{se_dirty_clamp, se_rb_advance};

/// Maximum cells rolled back in a single divergence reconciliation (`65_536`).
pub const MAX_ROLLBACK_CELLS: u64 = 65_536;

contract_fn! {
    /// Verified full-screen convergence (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `se_converged_equal_isl`.
    #[must_use]
    pub const fn se_converged_equal(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct RollbackReconciler {
    rollback_epochs: u64,
}

impl RollbackReconciler {
    #[must_use]
    pub const fn new() -> Self {
        Self { rollback_epochs: 0 }
    }

    pub fn verify_rollback(
        &mut self,
        reconciled_serialized: &[u8],
        authoritative_serialized: &[u8],
        dirty_cells_restored: u64,
    ) -> bool {
        let clamped_dirty = se_dirty_clamp(dirty_cells_restored, MAX_ROLLBACK_CELLS);
        self.rollback_epochs =
            se_rb_advance(self.rollback_epochs, self.rollback_epochs.saturating_add(1));
        if reconciled_serialized.is_empty()
            || authoritative_serialized.is_empty()
            || clamped_dirty != dirty_cells_restored
            || reconciled_serialized.len() != authoritative_serialized.len()
        {
            return false;
        }
        let d1 = Sha256::digest_slice(reconciled_serialized);
        let d2 = Sha256::digest_slice(authoritative_serialized);
        let eq = ct_eq(&d1, &d2);
        se_converged_equal(if eq { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn confirms_serialized_screen_equality_after_divergence_rollback() {
        let mut r = RollbackReconciler::new();
        assert!(r.verify_rollback(b"ASTREAM_SCR_V1:80x24:ok", b"ASTREAM_SCR_V1:80x24:ok", 12));
        assert!(!r.verify_rollback(
            b"ASTREAM_SCR_V1:80x24:stale",
            b"ASTREAM_SCR_V1:80x24:ok",
            12
        ));
    }
}
