// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! M-of-N witness checkpoint cosigner binding `(log_id, generation, head_offset, root_hash)`
//! (`Astream.Audit.TlaCheckpointCosign`).

use astream_digest::ct_eq;
use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "checkpoint_cosign_island.rs"]
mod checkpoint_cosign_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cosign_sigs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cosign_ckpt_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use checkpoint_cosign_island::{cosign_ckpt_advance, cosign_sigs_clamp};

/// Maximum witness nodes in a checkpoint cosigning committee.
pub const MAX_COSIGN_WITNESSES: u64 = 32;

contract_fn! {
    /// Verified quorum threshold check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cosign_quorum_met_isl`.
    #[must_use]
    pub const fn cosign_quorum_met(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Committee witness cosignature accumulator.
#[derive(Debug, Clone)]
pub struct CheckpointCosignCollector {
    allowed_witnesses: BTreeSet<String>,
    quorum: u64,
    checkpoint_head: u64,
    root_hash: [u8; 32],
    signed_by: BTreeSet<String>,
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

impl CheckpointCosignCollector {
    #[must_use]
    pub fn new(witnesses: &[&str], quorum: u64, checkpoint_head: u64, root_hash: [u8; 32]) -> Self {
        let cap = cosign_sigs_clamp(witnesses.len() as u64, MAX_COSIGN_WITNESSES) as usize;
        let mut allowed: BTreeSet<String> = BTreeSet::new();
        let mut idx = 0usize;
        while idx < cap {
            if let Some(&w) = witnesses.get(idx) {
                if !w.is_empty() {
                    allowed.insert(clone_str(w));
                }
            }
            idx = idx.saturating_add(1);
        }
        let q = if allowed.is_empty() {
            1
        } else {
            let clamped = cosign_sigs_clamp(quorum, allowed.len() as u64);
            if clamped == 0 {
                1
            } else {
                clamped
            }
        };
        Self {
            allowed_witnesses: allowed,
            quorum: q,
            checkpoint_head: cosign_ckpt_advance(0, checkpoint_head),
            root_hash,
            signed_by: BTreeSet::new(),
        }
    }

    pub fn add_cosignature(
        &mut self,
        witness_id: &str,
        head: u64,
        root: &[u8; 32],
    ) -> Result<bool, &'static str> {
        if !self.allowed_witnesses.contains(witness_id) {
            return Err("unrecognized witness");
        }
        if head != self.checkpoint_head || !ct_eq(root, &self.root_hash) {
            return Err("equivocating checkpoint root or head");
        }
        self.signed_by.insert(clone_str(witness_id));
        Ok(self.has_quorum())
    }

    #[must_use]
    pub fn has_quorum(&self) -> bool {
        cosign_quorum_met(self.signed_by.len() as u64, self.quorum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkpoint_cosigner_requires_distinct_authorized_witnesses_for_exact_root() {
        let mut c = CheckpointCosignCollector::new(&["w1", "w2", "w3"], 2, 500, [0xAA; 32]);
        assert!(!c.add_cosignature("w1", 500, &[0xAA; 32]).unwrap());
        assert!(!c.add_cosignature("w1", 500, &[0xAA; 32]).unwrap()); // duplicate w1!
        assert!(c.add_cosignature("w1", 500, &[0xBB; 32]).is_err()); // wrong root!
        assert!(c.add_cosignature("w2", 500, &[0xAA; 32]).unwrap());
    }
}
