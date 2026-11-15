// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Offline Macaroon `via=<hex>` delegation attenuation verifier
//! (`Astream.Cap.TlaMacaroonViaAttenuator`).
//!
//! Verifies monotonic attenuation along offline bearer delegation chains:
//! 1. Delegation hop depth never exceeds `MAX_VIA_DELEGATION_HOPS` (`8`).
//! 2. Child verb bitmask is a subset of parent verb bitmask (`(child & !parent) == 0`).
//! 3. Child subject namespace sits equal to or strictly inside parent subject prefix
//!    on a `/` segment boundary (preventing `/a/inbox/s1` -> `/a/inbox/s10` confusion!).
//! 4. Child expiry `exp_ms` never exceeds parent expiry (`child_exp <= parent_exp`).

#[cfg(clean_islands)]
#[path = "macaroon_via_attenuator_island.rs"]
mod macaroon_via_attenuator_island;
#[cfg(clean_islands)]
pub use macaroon_via_attenuator_island::{via_exp_attenuate_clamp, via_hop_advance};

/// Hard upper bound on `via=` offline delegation hops.
pub const MAX_VIA_DELEGATION_HOPS: u64 = 8;

#[cfg(not(clean_islands))]
/// Monotonically advance verified delegation chain hop depth.
#[must_use]
pub const fn via_hop_advance(cur_hop: u64, cand_hop: u64) -> u64 {
    if cur_hop < cand_hop {
        cand_hop
    } else {
        cur_hop
    }
}

#[cfg(not(clean_islands))]
/// Clamp attenuated child expiry so it never exceeds `parent_exp`.
#[must_use]
pub const fn via_exp_attenuate_clamp(child_exp: u64, parent_exp: u64) -> u64 {
    if child_exp < parent_exp {
        child_exp
    } else {
        parent_exp
    }
}

contract_fn! {
    /// True iff `hop_count <= max_hops`.
    #[must_use]
    pub const fn via_hop_within_cap(hop_count: u64, max_hops: u64) -> bool
    clauses [ensures result == (hop_count <= max_hops)]
    {
        hop_count <= max_hops
    }
}

/// Refusal reasons when a delegated caveat attempts privilege amplification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ViaAttenuationError {
    HopDepthExceeded {
        max_hops: u64,
    },
    VerbAmplification {
        parent_verbs: u32,
        child_verbs: u32,
    },
    ExpiryAmplification {
        parent_exp_ms: u64,
        child_exp_ms: u64,
    },
    SubjectEscape,
}

/// True iff `child_prefix` is equal to `parent_prefix` or strictly nested under it on a `/` boundary.
#[must_use]
pub fn is_valid_subprefix(parent_prefix: &[u8], child_prefix: &[u8]) -> bool {
    if parent_prefix == b"/" {
        return child_prefix.starts_with(b"/");
    }
    if child_prefix == parent_prefix {
        return true;
    }
    if !child_prefix.starts_with(parent_prefix) {
        return false;
    }
    if parent_prefix.ends_with(b"/") {
        return true;
    }
    matches!(child_prefix.get(parent_prefix.len()), Some(&b'/'))
}

/// Stateful delegation chain verifier starting from a root capability scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacaroonViaChain {
    hop_depth: u64,
    verbs_mask: u32,
    effective_exp_ms: u64,
    subject_prefix: Vec<u8>,
}

impl MacaroonViaChain {
    #[must_use]
    pub fn from_root(verbs_mask: u32, root_exp_ms: u64, root_prefix: &[u8]) -> Self {
        let mut p = Vec::new();
        p.extend_from_slice(root_prefix);
        Self {
            hop_depth: 0,
            verbs_mask,
            effective_exp_ms: root_exp_ms,
            subject_prefix: p,
        }
    }

    #[must_use]
    pub const fn hop_depth(&self) -> u64 {
        self.hop_depth
    }

    #[must_use]
    pub const fn verbs_mask(&self) -> u32 {
        self.verbs_mask
    }

    #[must_use]
    pub const fn effective_exp_ms(&self) -> u64 {
        self.effective_exp_ms
    }

    #[must_use]
    pub fn subject_prefix(&self) -> &[u8] {
        &self.subject_prefix
    }

    /// Apply and verify one offline attenuation caveat hop.
    pub fn apply_hop(
        &mut self,
        child_verbs: u32,
        child_exp_ms: u64,
        child_prefix: &[u8],
    ) -> Result<(), ViaAttenuationError> {
        let next_hop = self.hop_depth.saturating_add(1);
        if !via_hop_within_cap(next_hop, MAX_VIA_DELEGATION_HOPS) {
            return Err(ViaAttenuationError::HopDepthExceeded {
                max_hops: MAX_VIA_DELEGATION_HOPS,
            });
        }
        if (child_verbs & !self.verbs_mask) != 0 {
            return Err(ViaAttenuationError::VerbAmplification {
                parent_verbs: self.verbs_mask,
                child_verbs,
            });
        }
        if child_exp_ms > self.effective_exp_ms {
            return Err(ViaAttenuationError::ExpiryAmplification {
                parent_exp_ms: self.effective_exp_ms,
                child_exp_ms,
            });
        }
        if !is_valid_subprefix(&self.subject_prefix, child_prefix) {
            return Err(ViaAttenuationError::SubjectEscape);
        }

        self.hop_depth = via_hop_advance(self.hop_depth, next_hop);
        self.verbs_mask = child_verbs;
        self.effective_exp_ms = via_exp_attenuate_clamp(child_exp_ms, self.effective_exp_ms);
        self.subject_prefix.clear();
        self.subject_prefix.extend_from_slice(child_prefix);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_segment_boundary_subprefix_verb_subset_and_expiry_reduction() {
        let mut chain = MacaroonViaChain::from_root(0b0111, 10_000, b"/a/inbox");
        assert_eq!(chain.apply_hop(0b0011, 5_000, b"/a/inbox/s1"), Ok(()));
        assert_eq!(chain.hop_depth(), 1);
        assert_eq!(chain.verbs_mask(), 0b0011);
        assert_eq!(chain.effective_exp_ms(), 5_000);
        assert_eq!(chain.subject_prefix(), b"/a/inbox/s1");

        // Segment-boundary sibling confusion (/a/inbox/s1 -> /a/inbox/s10) MUST fail!
        assert_eq!(
            chain.apply_hop(0b0011, 4_000, b"/a/inbox/s10"),
            Err(ViaAttenuationError::SubjectEscape)
        );
        // Verb amplification MUST fail!
        assert_eq!(
            chain.apply_hop(0b0111, 4_000, b"/a/inbox/s1/sub"),
            Err(ViaAttenuationError::VerbAmplification {
                parent_verbs: 0b0011,
                child_verbs: 0b0111,
            })
        );
        // Expiry amplification MUST fail!
        assert_eq!(
            chain.apply_hop(0b0001, 6_000, b"/a/inbox/s1/sub"),
            Err(ViaAttenuationError::ExpiryAmplification {
                parent_exp_ms: 5_000,
                child_exp_ms: 6_000,
            })
        );
    }
}
