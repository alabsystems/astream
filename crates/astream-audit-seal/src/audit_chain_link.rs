// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Domain-separated SHA-256 hash-chain link (`H("ASTREAM-AUDIT-V1\0" || prev || off || bt || sha)`)
//! (`Astream.Audit.TlaAuditChainLink`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "audit_chain_link_island.rs"]
mod audit_chain_link_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn chain_batch_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn chain_height_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use audit_chain_link_island::{chain_batch_clamp, chain_height_advance};

/// Maximum links verified in one batch slice.
pub const MAX_AUDIT_VERIFY_BATCH: u64 = 4_096;

contract_fn! {
    /// Verified contiguity check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `chain_contiguous_isl`.
    #[must_use]
    pub const fn chain_contiguous(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditChainEntry {
    pub offset: u64,
    pub bt_ms: u64,
    pub payload_sha256: [u8; 32],
    pub link_hash: [u8; 32],
}

fn link_digest(prev: &[u8; 32], offset: u64, bt_ms: u64, payload_sha: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-AUDIT-V1\0");
    h.update_slice(prev);
    h.update_slice(&offset.to_le_bytes());
    h.update_slice(&bt_ms.to_le_bytes());
    h.update_slice(payload_sha);
    h.finalize()
}

/// Append-only SHA-256 audit hash-chain accumulator.
#[derive(Debug, Clone)]
pub struct AuditHashChain {
    head_hash: [u8; 32],
    next_offset: u64,
}

impl Default for AuditHashChain {
    fn default() -> Self {
        Self::new()
    }
}

impl AuditHashChain {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            head_hash: [0u8; 32],
            next_offset: 0,
        }
    }

    pub fn append(&mut self, bt_ms: u64, payload: &[u8]) -> AuditChainEntry {
        let payload_sha256 = Sha256::digest_slice(payload);
        let off = self.next_offset;
        let link_hash = link_digest(&self.head_hash, off, bt_ms, &payload_sha256);
        self.head_hash = link_hash;
        self.next_offset = chain_height_advance(self.next_offset, off.saturating_add(1));
        AuditChainEntry {
            offset: off,
            bt_ms,
            payload_sha256,
            link_hash,
        }
    }

    #[must_use]
    pub fn verify_slice(genesis: [u8; 32], base_off: u64, slice: &[AuditChainEntry]) -> bool {
        let lim = chain_batch_clamp(slice.len() as u64, MAX_AUDIT_VERIFY_BATCH) as usize;
        if lim != slice.len() {
            return false;
        }
        let mut prev = genesis;
        let mut exp_off = base_off;
        for e in slice {
            if e.offset != exp_off || !chain_contiguous(e.offset, exp_off) {
                return false;
            }
            let calc = link_digest(&prev, e.offset, e.bt_ms, &e.payload_sha256);
            if !ct_eq(&calc, &e.link_hash) {
                return false;
            }
            prev = e.link_hash;
            exp_off = exp_off.saturating_add(1);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn audit_hash_chain_detects_any_reordering_or_timestamp_tampering() {
        let mut c = AuditHashChain::new();
        let e0 = c.append(1_000, b"login h-alice");
        let mut e1 = c.append(1_005, b"mint cap");
        assert!(AuditHashChain::verify_slice(
            [0u8; 32],
            0,
            &[e0.clone(), e1.clone()]
        ));
        e1.bt_ms = 1_006;
        assert!(!AuditHashChain::verify_slice([0u8; 32], 0, &[e0, e1]));
    }
}
