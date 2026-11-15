// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-tier capability revocation floor & stack 16-token ring guard
//! (`Astream.Cap.TlaCapRevocationEpochBloom`).
//!
//! Enforces R6 capability revocation in `O(1)` stack memory without heap allocation:
//! combines a monotonically advancing `min_valid_epoch` floor (bulk key-rotation
//! revocation) with a bounded 16-entry stack ring of individual revoked token tags.

#[cfg(clean_islands)]
#[path = "cap_revocation_epoch_bloom_island.rs"]
mod cap_revocation_epoch_bloom_island;
#[cfg(clean_islands)]
pub use cap_revocation_epoch_bloom_island::{cap_epoch_floor_advance, revoked_count_clamp_b101};

/// Fixed stack ring capacity for individual revoked capability tags (`16`).
pub const REVOKED_RING_CAP: usize = 16;

#[cfg(not(clean_islands))]
/// Monotonically advance minimum accepted capability epoch floor.
#[must_use]
pub const fn cap_epoch_floor_advance(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}

#[cfg(not(clean_islands))]
/// Clamp ring cursor / entry count to `max_entries`.
#[must_use]
pub const fn revoked_count_clamp_b101(cand_count: u64, max_entries: u64) -> u64 {
    if cand_count < max_entries {
        cand_count
    } else {
        max_entries
    }
}

contract_fn! {
    /// True iff `token_epoch >= min_valid_epoch`.
    #[must_use]
    pub const fn cap_epoch_admissible(token_epoch: u64, min_valid_epoch: u64) -> bool
    clauses [ensures result == (min_valid_epoch <= token_epoch)]
    {
        min_valid_epoch <= token_epoch
    }
}

/// Reason a capability token failed revocation admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapRevocationRefusal {
    ZeroTokenTag,
    EpochRevoked {
        token_epoch: u64,
        min_valid_epoch: u64,
    },
    TokenExplicitlyRevoked {
        token_tag: u64,
    },
}

/// Pure stack R6 capability revocation guard (`min_valid_epoch` + 16-tag ring).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapRevocationEpochBloom {
    min_valid_epoch: u64,
    revoked_tags: [u64; REVOKED_RING_CAP],
    count: usize,
    write_cursor: usize,
}

impl Default for CapRevocationEpochBloom {
    fn default() -> Self {
        Self::new(1)
    }
}

impl CapRevocationEpochBloom {
    #[must_use]
    pub const fn new(min_valid_epoch: u64) -> Self {
        Self {
            min_valid_epoch,
            revoked_tags: [0u64; REVOKED_RING_CAP],
            count: 0,
            write_cursor: 0,
        }
    }

    #[must_use]
    pub const fn min_valid_epoch(&self) -> u64 {
        self.min_valid_epoch
    }

    #[must_use]
    pub const fn revoked_count(&self) -> usize {
        self.count
    }

    /// Ratchet `min_valid_epoch` upward, revoking all older-epoch capabilities at once.
    pub fn ratchet_epoch_floor(&mut self, next_floor: u64) -> u64 {
        self.min_valid_epoch = cap_epoch_floor_advance(self.min_valid_epoch, next_floor);
        self.min_valid_epoch
    }

    /// Revoke a specific `token_tag` (`!= 0`). If the 16-entry ring is full, before
    /// evicting an entry the caller can also ratchet `min_valid_epoch` so evicted older
    /// tokens remain covered by the epoch floor.
    pub fn revoke_token(&mut self, token_tag: u64, fallback_floor_on_wrap: u64) {
        if token_tag == 0 {
            return;
        }
        for &existing in &self.revoked_tags {
            if existing == token_tag {
                return;
            }
        }
        if self.count >= REVOKED_RING_CAP {
            self.min_valid_epoch =
                cap_epoch_floor_advance(self.min_valid_epoch, fallback_floor_on_wrap);
        }
        let idx = self.write_cursor % REVOKED_RING_CAP;
        if let Some(slot) = self.revoked_tags.get_mut(idx) {
            *slot = token_tag;
        }
        self.write_cursor = idx.saturating_add(1) % REVOKED_RING_CAP;
        let next_count = (self.count as u64).saturating_add(1);
        self.count = revoked_count_clamp_b101(next_count, REVOKED_RING_CAP as u64) as usize;
    }

    /// Check whether `(token_tag, token_epoch)` is admissible.
    pub fn check(&self, token_tag: u64, token_epoch: u64) -> Result<(), CapRevocationRefusal> {
        if token_tag == 0 {
            return Err(CapRevocationRefusal::ZeroTokenTag);
        }
        if !cap_epoch_admissible(token_epoch, self.min_valid_epoch) {
            return Err(CapRevocationRefusal::EpochRevoked {
                token_epoch,
                min_valid_epoch: self.min_valid_epoch,
            });
        }
        for &revoked in &self.revoked_tags {
            if revoked == token_tag {
                return Err(CapRevocationRefusal::TokenExplicitlyRevoked { token_tag });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_individual_revocation_and_epoch_floor_wrap_fail_closed() {
        let mut guard = CapRevocationEpochBloom::new(5);
        assert_eq!(guard.check(0xAA01, 5), Ok(()));
        assert_eq!(
            guard.check(0xAA01, 4),
            Err(CapRevocationRefusal::EpochRevoked {
                token_epoch: 4,
                min_valid_epoch: 5,
            })
        );

        guard.revoke_token(0xAA01, 5);
        assert_eq!(
            guard.check(0xAA01, 5),
            Err(CapRevocationRefusal::TokenExplicitlyRevoked { token_tag: 0xAA01 })
        );

        // Wrapping past 16 entries ratchets `min_valid_epoch` to `fallback_floor_on_wrap` (6),
        // so even an evicted epoch-5 token stays revoked!
        for t in 1..=17u64 {
            guard.revoke_token(0xBB00 + t, 6);
        }
        assert_eq!(guard.min_valid_epoch(), 6);
        assert_eq!(
            guard.check(0xAA01, 5),
            Err(CapRevocationRefusal::EpochRevoked {
                token_epoch: 5,
                min_valid_epoch: 6,
            })
        );
    }
}
