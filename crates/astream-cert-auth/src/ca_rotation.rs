// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-root CA trust bundle rollover and retired-authority grace-horizon fence
//! (`ROADMAP.md` lines 12-14, `Astream.CertAuth.TlaCaRotation`).
//!
//! Enables zero-downtime rotation of Ed25519 SSH/identity CAs across fleets:
//! - `Active` roots verify newly issued and existing certificates unconditionally.
//! - `Retiring { grace_until_ms }` roots verify certificates while `now_ms < grace_until_ms`
//!   so in-flight sessions survive CA rollover without mass disconnects.
//! - `Revoked` roots fail closed immediately, and `bundle_gen` advances monotonically via
//!   Clean-origin `ca_bundle_gen_advance`.

use astream_digest::ct_eq;

#[cfg(clean_islands)]
#[path = "ca_rotation_island.rs"]
mod ca_rotation_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ca_roots_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ca_bundle_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ca_rotation_island::{ca_bundle_gen_advance, ca_roots_clamp};

/// Maximum CA public keys held simultaneously in a trust bundle.
pub const MAX_TRUSTED_CA_ROOTS: u64 = 8;

contract_fn! {
    /// Verified grace-window check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ca_key_trusted_isl`.
    #[must_use]
    pub const fn ca_key_trusted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Lifecycle state of an Ed25519 CA root inside [`CaTrustBundle`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaRootState {
    Active,
    Retiring { grace_until_ms: u64 },
    Revoked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CaRootEntry {
    pub public_key: [u8; 32],
    pub state: CaRootState,
}

/// Constant-time verified multi-root CA trust bundle.
#[derive(Debug, Clone)]
pub struct CaTrustBundle {
    bundle_gen: u64,
    roots: Vec<CaRootEntry>,
}

impl Default for CaTrustBundle {
    fn default() -> Self {
        Self::new()
    }
}

impl CaTrustBundle {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bundle_gen: 0,
            roots: Vec::new(),
        }
    }

    #[must_use]
    pub const fn bundle_gen(&self) -> u64 {
        self.bundle_gen
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.roots.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }

    /// Installs a strictly newer `next_gen` root set (`<= MAX_TRUSTED_CA_ROOTS`).
    pub fn install_bundle(
        &mut self,
        next_gen: u64,
        entries: Vec<CaRootEntry>,
    ) -> Result<u64, &'static str> {
        if next_gen <= self.bundle_gen {
            return Err("stale ca bundle generation refused");
        }
        let max_r = ca_roots_clamp(MAX_TRUSTED_CA_ROOTS, MAX_TRUSTED_CA_ROOTS) as usize;
        if entries.len() > max_r {
            return Err("too many ca roots in bundle");
        }
        self.bundle_gen = ca_bundle_gen_advance(self.bundle_gen, next_gen);
        self.roots = entries;
        Ok(self.bundle_gen)
    }

    /// Evaluates whether `candidate_ca_pk` is trusted at `now_ms` using constant-time key comparison.
    #[must_use]
    pub fn is_ca_trusted(&self, candidate_ca_pk: &[u8; 32], now_ms: u64) -> bool {
        let mut matched_trust = false;
        for entry in &self.roots {
            if ct_eq(&entry.public_key, candidate_ca_pk) {
                let state_ok = match entry.state {
                    CaRootState::Active => true,
                    CaRootState::Retiring { grace_until_ms } => {
                        now_ms < grace_until_ms && ca_key_trusted(grace_until_ms, now_ms)
                    }
                    CaRootState::Revoked => false,
                };
                if state_ok {
                    matched_trust = true;
                }
            }
        }
        matched_trust
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dual_root_ca_rollover_honors_grace_period_and_rejects_downgrade_or_revoked() {
        let old_ca = [0x11; 32];
        let new_ca = [0x22; 32];
        let rogue = [0x99; 32];
        let mut bundle = CaTrustBundle::new();
        bundle
            .install_bundle(
                1,
                vec![
                    CaRootEntry {
                        public_key: old_ca,
                        state: CaRootState::Retiring {
                            grace_until_ms: 10_000,
                        },
                    },
                    CaRootEntry {
                        public_key: new_ca,
                        state: CaRootState::Active,
                    },
                ],
            )
            .unwrap();
        assert!(bundle.install_bundle(1, vec![]).is_err());
        assert!(bundle.is_ca_trusted(&old_ca, 9_999));
        assert!(!bundle.is_ca_trusted(&old_ca, 10_000));
        assert!(bundle.is_ca_trusted(&new_ca, 50_000));
        assert!(!bundle.is_ca_trusted(&rogue, 5_000));
    }
}
