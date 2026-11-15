// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RFC 6962 Certificate-Transparency-style SHA-256 Merkle audit & consistency proofs.
//!
//! Enables `aterm` evidence verifiers and remote session auditors to verify in `O(log N)`
//! hashes that:
//! 1. A specific receipt, terminal step, or broker record `leaf` is committed at `leaf_index`
//!    under `root_hash` of a log of size `tree_size` ([`verify_inclusion_proof`]), with
//!    RFC 6962 §2.1 domain separation (`0x00` leaf prefix vs `0x01` interior node prefix)
//!    defeating second-preimage tree-height confusion attacks.
//! 2. An append-only log snapshot of `old_size` (`old_root`) is a strict prefix of a newer
//!    snapshot of `new_size` (`new_root`) ([`verify_consistency_proof`]), detecting split-view
//!    or equivocating log truncation immediately.
//!
//! Constant-time final root comparison via [`astream_digest::ct_eq`], bounded proof depth
//! (`<= MAX_MERKLE_PROOF_DEPTH`), zero closures, and zero unsafe code.
//! Backed by Clean TLA+ island `Astream.Digest.TlaMerkleAuditProof` (`merkle_proof_island.rs`).

#![allow(clippy::assign_op_pattern, clippy::question_mark)]

use astream_digest::{ct_eq, Sha256, OUTPUT_LEN};

#[cfg(clean_islands)]
#[path = "merkle_proof_island.rs"]
mod merkle_proof_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn merkle_proof_depth_clamp(depth: u64, max_depth: u64) -> u64 {
    if depth < max_depth {
        depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn merkle_tree_size_advance(prev_size: u64, cand_size: u64) -> u64 {
    if prev_size < cand_size {
        cand_size
    } else {
        prev_size
    }
}
#[cfg(clean_islands)]
pub use merkle_proof_island::{merkle_proof_depth_clamp, merkle_tree_size_advance};

/// Maximum Merkle audit/consistency proof depth (`64` levels covers up to `2^64` leaves).
pub const MAX_MERKLE_PROOF_DEPTH: usize = 64;

/// Maximum leaves built in an in-memory batch tree (`65_536` leaves).
pub const MAX_IN_MEMORY_LEAVES: usize = 65_536;

const LEAF_DOMAIN_PREFIX: u8 = 0x00;
const NODE_DOMAIN_PREFIX: u8 = 0x01;

contract_fn! {
    /// Verified bounds predicate (`leaf_idx < leaf_count`), linked via `clean-kernel-defeq`
    /// to `merkle_leaf_in_range_isl`.
    #[must_use]
    pub const fn merkle_leaf_in_range(leaf_idx: usize, leaf_count: usize) -> bool
    clauses [ensures result == (leaf_idx < leaf_count)]
    {
        leaf_idx < leaf_count
    }
}

/// RFC 6962 §2.1 domain-separated leaf hash: `SHA-256(0x00 || data)`.
#[must_use]
pub fn merkle_leaf_hash(data: &[u8]) -> [u8; OUTPUT_LEN] {
    let mut h = Sha256::new();
    h.update_slice(&[LEAF_DOMAIN_PREFIX]);
    h.update_slice(data);
    h.finalize()
}

/// RFC 6962 §2.1 domain-separated interior node hash: `SHA-256(0x01 || left || right)`.
#[must_use]
pub fn merkle_node_hash(left: &[u8; OUTPUT_LEN], right: &[u8; OUTPUT_LEN]) -> [u8; OUTPUT_LEN] {
    let mut h = Sha256::new();
    h.update_slice(&[NODE_DOMAIN_PREFIX]);
    h.update_slice(left);
    h.update_slice(right);
    h.finalize()
}

/// Largest power of two strictly less than `n` (for `n >= 2`).
#[must_use]
const fn largest_pow2_lt(n: usize) -> usize {
    if n <= 1 {
        return 0;
    }
    let prev = n.saturating_sub(1);
    let lz = prev.leading_zeros();
    let shift = (usize::BITS - 1).saturating_sub(lz);
    if shift < usize::BITS {
        1usize << (shift & (usize::BITS - 1))
    } else {
        0
    }
}

#[must_use]
const fn clamp_usize(val: usize, cap: usize) -> usize {
    if val < cap {
        val
    } else {
        cap
    }
}

/// Compute the RFC 6962 §2.1 Merkle Tree Hash (`MTH`) over pre-hashed leaves.
///
/// For empty `leaf_hashes`, returns `SHA-256("")` per RFC 6962 §2.1.
#[must_use]
pub fn merkle_root_from_leaf_hashes(leaf_hashes: &[[u8; OUTPUT_LEN]]) -> [u8; OUTPUT_LEN] {
    let capped = clamp_usize(leaf_hashes.len(), MAX_IN_MEMORY_LEAVES);
    let Some(hashes) = leaf_hashes.get(..capped) else {
        return Sha256::digest_slice(b"");
    };
    mth_slice(hashes, 0)
}

fn mth_slice(hashes: &[[u8; OUTPUT_LEN]], depth: usize) -> [u8; OUTPUT_LEN] {
    if depth > MAX_MERKLE_PROOF_DEPTH || hashes.is_empty() {
        return Sha256::digest_slice(b"");
    }
    if let &[single] = hashes {
        return single;
    }
    let k = largest_pow2_lt(hashes.len());
    let (Some(left_part), Some(right_part)) = (hashes.get(..k), hashes.get(k..)) else {
        return Sha256::digest_slice(b"");
    };
    let left = mth_slice(left_part, depth.saturating_add(1));
    let right = mth_slice(right_part, depth.saturating_add(1));
    merkle_node_hash(&left, &right)
}

/// Inclusion proof (`PATH(m, D[n])` in RFC 6962 §2.1.1), stack-allocated with zero heap.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MerkleInclusionProof {
    pub leaf_index: usize,
    pub tree_size: usize,
    pub audit_path: [[u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH],
    pub path_len: usize,
}

/// Consistency proof (`PROOF(m, D[n])` in RFC 6962 §2.1.2), stack-allocated with zero heap.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MerkleConsistencyProof {
    pub old_size: usize,
    pub new_size: usize,
    pub nodes: [[u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH],
    pub nodes_len: usize,
}

/// Build an RFC 6962 §2.1.1 inclusion proof for `leaf_index` in `leaf_hashes`.
#[must_use]
pub fn build_inclusion_proof(
    leaf_hashes: &[[u8; OUTPUT_LEN]],
    leaf_index: usize,
) -> Option<MerkleInclusionProof> {
    let n = clamp_usize(leaf_hashes.len(), MAX_IN_MEMORY_LEAVES);
    if !merkle_leaf_in_range(leaf_index, n) {
        return None;
    }
    let Some(hashes) = leaf_hashes.get(..n) else {
        return None;
    };
    let mut path = [[0u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH];
    let mut path_len = 0usize;
    build_path_into(hashes, leaf_index, &mut path, &mut path_len, 0);
    Some(MerkleInclusionProof {
        leaf_index,
        tree_size: n,
        audit_path: path,
        path_len,
    })
}

fn build_path_into(
    hashes: &[[u8; OUTPUT_LEN]],
    m: usize,
    out: &mut [[u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH],
    out_len: &mut usize,
    depth: usize,
) {
    if hashes.len() <= 1 || depth >= MAX_MERKLE_PROOF_DEPTH {
        return;
    }
    let k = largest_pow2_lt(hashes.len());
    let (Some(left), Some(right)) = (hashes.get(..k), hashes.get(k..)) else {
        return;
    };
    if m < k {
        build_path_into(left, m, out, out_len, depth.saturating_add(1));
        if let Some(slot) = out.get_mut(*out_len) {
            *slot = mth_slice(right, depth.saturating_add(1));
            *out_len = out_len.saturating_add(1);
        }
    } else {
        build_path_into(
            right,
            m.saturating_sub(k),
            out,
            out_len,
            depth.saturating_add(1),
        );
        if let Some(slot) = out.get_mut(*out_len) {
            *slot = mth_slice(left, depth.saturating_add(1));
            *out_len = out_len.saturating_add(1);
        }
    }
}

/// Verify an RFC 6962 §2.1.1 Merkle inclusion proof in `O(log N)` hashes.
#[must_use]
pub fn verify_inclusion_proof(
    leaf_hash: &[u8; OUTPUT_LEN],
    proof: &MerkleInclusionProof,
    expected_root: &[u8; OUTPUT_LEN],
) -> bool {
    if !merkle_leaf_in_range(proof.leaf_index, proof.tree_size) {
        return false;
    }
    let clamped_depth =
        merkle_proof_depth_clamp(proof.path_len as u64, MAX_MERKLE_PROOF_DEPTH as u64) as usize;
    if proof.path_len != clamped_depth {
        return false;
    }

    let mut fn_idx = proof.leaf_index;
    let mut sn = proof.tree_size.saturating_sub(1);
    let mut cur = *leaf_hash;
    let mut pos = 0usize;

    while pos < proof.path_len {
        let Some(p) = proof.audit_path.get(pos) else {
            return false;
        };
        if sn == 0 {
            return false;
        }
        if (fn_idx & 1) == 1 || fn_idx == sn {
            cur = merkle_node_hash(p, &cur);
            while (fn_idx & 1) == 0 && fn_idx != 0 {
                fn_idx = fn_idx >> (1);
                sn = sn >> (1);
            }
        } else {
            cur = merkle_node_hash(&cur, p);
        }
        fn_idx = fn_idx >> (1);
        sn = sn >> (1);
        pos = pos.saturating_add(1);
    }

    sn == 0 && ct_eq(&cur, expected_root)
}

/// Build an RFC 6962 §2.1.2 consistency proof between `old_size` and `leaf_hashes.len()`.
#[must_use]
pub fn build_consistency_proof(
    leaf_hashes: &[[u8; OUTPUT_LEN]],
    old_size: usize,
) -> Option<MerkleConsistencyProof> {
    let n = clamp_usize(leaf_hashes.len(), MAX_IN_MEMORY_LEAVES);
    let advanced_n = merkle_tree_size_advance(old_size as u64, n as u64) as usize;
    if old_size == 0 || old_size > n || advanced_n != n {
        return None;
    }
    let Some(hashes) = leaf_hashes.get(..n) else {
        return None;
    };
    let mut nodes = [[0u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH];
    let mut nodes_len = 0usize;
    if old_size < n {
        subproof_into(old_size, hashes, true, &mut nodes, &mut nodes_len, 0);
    }
    Some(MerkleConsistencyProof {
        old_size,
        new_size: n,
        nodes,
        nodes_len,
    })
}

fn subproof_into(
    m: usize,
    hashes: &[[u8; OUTPUT_LEN]],
    complete_subtree: bool,
    out: &mut [[u8; OUTPUT_LEN]; MAX_MERKLE_PROOF_DEPTH],
    out_len: &mut usize,
    depth: usize,
) {
    let n = hashes.len();
    if m == 0 || m > n || depth >= MAX_MERKLE_PROOF_DEPTH {
        return;
    }
    if m == n {
        if !complete_subtree {
            if let Some(slot) = out.get_mut(*out_len) {
                *slot = mth_slice(hashes, depth.saturating_add(1));
                *out_len = out_len.saturating_add(1);
            }
        }
        return;
    }
    let k = largest_pow2_lt(n);
    let (Some(left), Some(right)) = (hashes.get(..k), hashes.get(k..)) else {
        return;
    };
    if m <= k {
        subproof_into(
            m,
            left,
            complete_subtree,
            out,
            out_len,
            depth.saturating_add(1),
        );
        if let Some(slot) = out.get_mut(*out_len) {
            *slot = mth_slice(right, depth.saturating_add(1));
            *out_len = out_len.saturating_add(1);
        }
    } else {
        subproof_into(
            m.saturating_sub(k),
            right,
            false,
            out,
            out_len,
            depth.saturating_add(1),
        );
        if let Some(slot) = out.get_mut(*out_len) {
            *slot = mth_slice(left, depth.saturating_add(1));
            *out_len = out_len.saturating_add(1);
        }
    }
}

/// Verify an RFC 6962 §2.1.2 Merkle consistency proof between `(old_size, old_root)`
/// and `(new_size, new_root)`.
#[must_use]
pub fn verify_consistency_proof(
    proof: &MerkleConsistencyProof,
    old_root: &[u8; OUTPUT_LEN],
    new_root: &[u8; OUTPUT_LEN],
) -> bool {
    if proof.old_size == 0 || proof.old_size > proof.new_size {
        return false;
    }
    let advanced = merkle_tree_size_advance(proof.old_size as u64, proof.new_size as u64) as usize;
    if advanced != proof.new_size {
        return false;
    }
    if proof.old_size == proof.new_size {
        return proof.nodes_len == 0 && ct_eq(old_root, new_root);
    }
    let clamped_depth =
        merkle_proof_depth_clamp(proof.nodes_len as u64, MAX_MERKLE_PROOF_DEPTH as u64) as usize;
    if proof.nodes_len == 0 || proof.nodes_len != clamped_depth {
        return false;
    }

    let mut fn_idx = proof.old_size.saturating_sub(1);
    let mut sn = proof.new_size.saturating_sub(1);
    while (fn_idx & 1) == 1 {
        fn_idx = fn_idx >> (1);
        sn = sn >> (1);
    }

    let is_pow2 = proof.old_size.is_power_of_two();
    let (mut fr, mut sr, mut pos) = if is_pow2 {
        (*old_root, *old_root, 0usize)
    } else {
        let Some(first) = proof.nodes.first() else {
            return false;
        };
        (*first, *first, 1usize)
    };

    while pos < proof.nodes_len {
        let Some(c) = proof.nodes.get(pos) else {
            return false;
        };
        if sn == 0 {
            return false;
        }
        if (fn_idx & 1) == 1 || fn_idx == sn {
            fr = merkle_node_hash(c, &fr);
            sr = merkle_node_hash(c, &sr);
            while (fn_idx & 1) == 0 && fn_idx != 0 {
                fn_idx = fn_idx >> (1);
                sn = sn >> (1);
            }
        } else {
            sr = merkle_node_hash(&sr, c);
        }
        fn_idx = fn_idx >> (1);
        sn = sn >> (1);
        pos = pos.saturating_add(1);
    }

    sn == 0 && ct_eq(&fr, old_root) && ct_eq(&sr, new_root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(merkle_proof_depth_clamp(10, 64), 10);
        assert_eq!(merkle_proof_depth_clamp(99, 64), 64);
        assert_eq!(merkle_tree_size_advance(12, 20), 20);
        assert_eq!(merkle_tree_size_advance(20, 12), 20);
        assert!(merkle_leaf_in_range(0, 1));
        assert!(!merkle_leaf_in_range(1, 1));
    }

    #[test]
    fn inclusion_and_consistency_proofs_verify_across_all_tree_shapes() {
        let leaves: Vec<[u8; OUTPUT_LEN]> = (0..19u8)
            .map(|i| merkle_leaf_hash(&[b'r', b'e', b'c', i]))
            .collect();

        for n in 1..=leaves.len() {
            let sub = &leaves[..n];
            let root_n = merkle_root_from_leaf_hashes(sub);

            for idx in 0..n {
                let proof = build_inclusion_proof(sub, idx).unwrap();
                assert!(verify_inclusion_proof(&sub[idx], &proof, &root_n));

                // Wrong leaf or tampered root MUST fail closed!
                let wrong_leaf = merkle_leaf_hash(b"forged");
                assert!(!verify_inclusion_proof(&wrong_leaf, &proof, &root_n));
            }

            for m in 1..=n {
                let root_m = merkle_root_from_leaf_hashes(&leaves[..m]);
                let cproof = build_consistency_proof(sub, m).unwrap();
                assert!(
                    verify_consistency_proof(&cproof, &root_m, &root_n),
                    "consistency failed for m={m}, n={n}"
                );
                if m < n {
                    let mut forged_old = root_m;
                    forged_old[0] ^= 0x01;
                    assert!(!verify_consistency_proof(&cproof, &forged_old, &root_n));
                }
            }
        }
    }
}
