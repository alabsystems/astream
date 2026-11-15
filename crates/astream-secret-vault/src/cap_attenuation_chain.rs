// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Delegated capability attenuation verifier confirming child sub-capabilities never widen right
//! masks (`child_rights & !parent_rights == 0`) or extend `exp=` deadlines (`child_exp <= parent_exp`;
//! `Astream.SecVault.TlaCapAttenuationChain`).

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
#[path = "cap_attenuation_chain_island.rs"]
mod cap_attenuation_chain_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_hops_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_att_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cap_attenuation_chain_island::{sv_att_advance, sv_hops_clamp};

/// Maximum delegation chain depth (`8` hops).
pub const MAX_DELEGATION_HOPS: u64 = 8;

contract_fn! {
    /// Verified monotone expiry attenuation (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sv_attenuation_narrower_isl`.
    #[must_use]
    pub const fn sv_attenuation_narrower(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct AttenuationVerifier {
    chains_checked: u64,
}

impl AttenuationVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { chains_checked: 0 }
    }

    pub fn verify_child(
        &mut self,
        parent_rights: u64,
        parent_exp_ms: u64,
        child_rights: u64,
        child_exp_ms: u64,
        hop_depth: u64,
    ) -> bool {
        self.chains_checked =
            sv_att_advance(self.chains_checked, self.chains_checked.saturating_add(1));
        if parent_exp_ms == 0 || child_exp_ms == 0 || child_rights == 0 {
            return false;
        }
        let hops = sv_hops_clamp(hop_depth, MAX_DELEGATION_HOPS);
        if hops != hop_depth {
            return false;
        }
        let rights_subset = (child_rights & !parent_rights) == 0;
        rights_subset && sv_attenuation_narrower(parent_exp_ms, child_exp_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_rights_subset_and_non_extended_expiry_on_delegated_cap() {
        let mut v = AttenuationVerifier::new();
        assert!(v.verify_child(0b111, 50_000, 0b011, 30_000, 2));
        assert!(!v.verify_child(0b011, 50_000, 0b111, 30_000, 2));
        assert!(!v.verify_child(0b111, 50_000, 0b011, 60_000, 2));
    }
}
