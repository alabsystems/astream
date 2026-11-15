// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Release tag + `evidence/manifest.toml` SHA-256 attestation builder binding a Git commit OID to
//! its verified claim count and manifest digest (`Astream.GitAlign.TlaSignedTagManifest`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "signed_tag_manifest_island.rs"]
mod signed_tag_manifest_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_claims_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_tag_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use signed_tag_manifest_island::{git_claims_clamp, git_tag_advance};

/// Maximum evidence claims bound into a single release tag attestation.
pub const MAX_ATTESTED_CLAIMS: u64 = 4_096;

contract_fn! {
    /// Verified claim floor (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `git_manifest_pinned_isl`.
    #[must_use]
    pub const fn git_manifest_pinned(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReleaseAttestation {
    pub tag_name: String,
    pub commit_oid: String,
    pub claim_count: u64,
    pub sequence: u64,
    pub sha256: [u8; 32],
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn compute_tag_sha(tag: &str, oid: &str, claims: u64, seq: u64, manifest_bytes: &[u8]) -> [u8; 32] {
    let tag_len = (tag.len() as u64).to_le_bytes();
    let oid_len = (oid.len() as u64).to_le_bytes();
    let claims_le = claims.to_le_bytes();
    let seq_le = seq.to_le_bytes();
    let mf_len = (manifest_bytes.len() as u64).to_le_bytes();
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-RELEASE-ATTEST-V1\0");
    h.update_slice(&tag_len);
    h.update_slice(tag.as_bytes());
    h.update_slice(&oid_len);
    h.update_slice(oid.as_bytes());
    h.update_slice(&claims_le);
    h.update_slice(&seq_le);
    h.update_slice(&mf_len);
    h.update_slice(manifest_bytes);
    h.finalize()
}

impl ReleaseAttestation {
    #[must_use]
    pub fn seal(tag: &str, oid: &str, claims: u64, prev_seq: u64, manifest_bytes: &[u8]) -> Self {
        let clamped_claims = git_claims_clamp(claims, MAX_ATTESTED_CLAIMS);
        let seq = git_tag_advance(prev_seq, prev_seq.saturating_add(1));
        let sha256 = compute_tag_sha(tag, oid, clamped_claims, seq, manifest_bytes);
        Self {
            tag_name: copy_str(tag),
            commit_oid: copy_str(oid),
            claim_count: clamped_claims,
            sequence: seq,
            sha256,
        }
    }

    #[must_use]
    pub fn verify(&self, min_claims: u64, manifest_bytes: &[u8]) -> bool {
        if self.tag_name.is_empty()
            || self.commit_oid.is_empty()
            || !git_manifest_pinned(self.claim_count, min_claims)
        {
            return false;
        }
        let expected = compute_tag_sha(
            &self.tag_name,
            &self.commit_oid,
            self.claim_count,
            self.sequence,
            manifest_bytes,
        );
        ct_eq(&expected, &self.sha256)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_attestation_binds_commit_oid_and_manifest_digest() {
        let mf = b"[[claim]]\nid = \"wire.frame\"";
        let att = ReleaseAttestation::seal("v0.2.1", "2c42a8d", 120, 0, mf);
        assert!(att.verify(100, mf));
        assert!(!att.verify(100, b"tampered"));
    }
}
