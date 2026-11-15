// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SHA-256 subagent handoff commitment binding `(conv_id, head_commit_oid, summary)`
//! (`Astream.Subagent.TlaHandoffDigestPin`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "handoff_digest_pin_island.rs"]
mod handoff_digest_pin_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_summary_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_handoff_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use handoff_digest_pin_island::{sub_handoff_advance, sub_summary_clamp};

/// Maximum handoff report bytes (`64` KiB).
pub const MAX_HANDOFF_BYTES: u64 = 65_536;

contract_fn! {
    /// Verified handoff revision check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sub_handoff_verified_isl`.
    #[must_use]
    pub const fn sub_handoff_verified(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedSubagentHandoff {
    pub conv_id: String,
    pub git_oid: String,
    pub revision: u64,
    pub summary: String,
    pub sha256: [u8; 32],
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

#[allow(clippy::manual_unwrap_or_default)]
fn utf8_prefix_str(s: &str, max_bytes: usize) -> &str {
    if s.len() <= max_bytes {
        return s;
    }
    let mut end = max_bytes;
    while end > 0 && !s.is_char_boundary(end) {
        end = end.saturating_sub(1);
    }
    match s.get(..end) {
        Some(sub) => sub,
        None => "",
    }
}

fn handoff_sha(conv_id: &str, git_oid: &str, rev: u64, summary: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-HANDOFF-V1\0");
    h.update_slice(&(conv_id.len() as u64).to_le_bytes());
    h.update_slice(conv_id.as_bytes());
    h.update_slice(&(git_oid.len() as u64).to_le_bytes());
    h.update_slice(git_oid.as_bytes());
    h.update_slice(&rev.to_le_bytes());
    h.update_slice(&(summary.len() as u64).to_le_bytes());
    h.update_slice(summary.as_bytes());
    h.finalize()
}

impl PinnedSubagentHandoff {
    #[must_use]
    pub fn seal(conv_id: &str, git_oid: &str, prev_rev: u64, summary: &str) -> Self {
        let keep = sub_summary_clamp(summary.len() as u64, MAX_HANDOFF_BYTES) as usize;
        let rev = sub_handoff_advance(prev_rev, prev_rev.saturating_add(1));
        let clipped = copy_str(utf8_prefix_str(summary, keep));
        let sha256 = handoff_sha(conv_id, git_oid, rev, &clipped);
        Self {
            conv_id: copy_str(conv_id),
            git_oid: copy_str(git_oid),
            revision: rev,
            summary: clipped,
            sha256,
        }
    }

    #[must_use]
    pub fn verify(&self, min_rev: u64) -> bool {
        if self.conv_id.is_empty()
            || self.git_oid.is_empty()
            || (self.summary.len() as u64) > MAX_HANDOFF_BYTES
        {
            return false;
        }
        if !sub_handoff_verified(self.revision, min_rev) {
            return false;
        }
        let calc = handoff_sha(&self.conv_id, &self.git_oid, self.revision, &self.summary);
        ct_eq(&calc, &self.sha256)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handoff_pin_binds_git_commit_oid_and_detects_tampering() {
        let mut h = PinnedSubagentHandoff::seal("conv-1", "2c42a8d", 0, "all tests green");
        assert!(h.verify(1));
        h.git_oid = "deadbeef".to_owned();
        assert!(!h.verify(1));
    }
}
