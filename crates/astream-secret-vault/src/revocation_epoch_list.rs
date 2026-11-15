// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone capability revocation epoch watermark (`REQUIREMENTS R6`) rejecting tokens minted at
//! or below `revoked_through_epoch` (`token_epoch > revoked_through_epoch`;
//! `Astream.SecVault.TlaRevocationEpochList`).

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
#[path = "revocation_epoch_list_island.rs"]
mod revocation_epoch_list_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_rev_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use revocation_epoch_list_island::{sv_epoch_advance, sv_rev_clamp};

/// Maximum tracked revocation epoch (`1_000_000_000`).
pub const MAX_REVOCATION_EPOCH: u64 = 1_000_000_000;

contract_fn! {
    /// Verified unrevoked token-epoch predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sv_token_unrevoked_isl`.
    #[must_use]
    pub const fn sv_token_unrevoked(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct RevocationWatermark {
    revoked_through: u64,
}

impl RevocationWatermark {
    #[must_use]
    pub const fn new() -> Self {
        Self { revoked_through: 0 }
    }

    pub fn revoke_up_to(&mut self, epoch: u64) {
        let clamped = sv_rev_clamp(epoch, MAX_REVOCATION_EPOCH);
        self.revoked_through = sv_epoch_advance(self.revoked_through, clamped);
    }

    #[must_use]
    pub const fn is_token_live(&self, token_mint_epoch: u64) -> bool {
        if token_mint_epoch == 0 || token_mint_epoch > MAX_REVOCATION_EPOCH {
            return false;
        }
        let min_live = self.revoked_through.saturating_add(1);
        sv_token_unrevoked(token_mint_epoch, min_live)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_capabilities_at_or_below_revocation_epoch() {
        let mut w = RevocationWatermark::new();
        w.revoke_up_to(10);
        assert!(!w.is_token_live(10));
        assert!(w.is_token_live(11));
    }
}
