// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC protected-folder fence blocking unprompted agent probes into `Documents`, `Desktop`,
//! `Downloads`, `/Volumes/*`, or cloud-synced folders when Full Disk Access is absent
//! (`Astream.MacTcc.TlaProtectedFolderFence`).

#[cfg(clean_islands)]
#[path = "protected_folder_fence_island.rs"]
mod protected_folder_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_zone_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_probe_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use protected_folder_fence_island::{tcc_probe_advance, tcc_zone_clamp};

/// Highest path sensitivity class (`0 = workspace`, `1 = fda_guarded`, `2 = always_modal_container`).
pub const MAX_TCC_ZONE: u64 = 2;

contract_fn! {
    /// Verified clearance check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tcc_lookup_safe_isl`.
    #[must_use]
    pub const fn tcc_lookup_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ProtectedFolderFence {
    fda_granted: bool,
    checks: u64,
}

fn has_nul_or_dotdot(bytes: &[u8]) -> bool {
    let mut idx = 0usize;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if b == 0 {
            return true;
        }
        if b == b'.' && bytes.get(idx.saturating_add(1)) == Some(&b'.') {
            let prev_ok = idx == 0 || bytes.get(idx.saturating_sub(1)) == Some(&b'/');
            let next_b = bytes.get(idx.saturating_add(2));
            let next_ok = next_b.is_none() || next_b == Some(&b'/');
            if prev_ok && next_ok {
                return true;
            }
        }
        idx = idx.saturating_add(1);
    }
    false
}

fn starts_with_segment_ci(bytes: &[u8], seg: &[u8]) -> bool {
    let Some(head) = bytes.get(..seg.len()) else {
        return false;
    };
    if !head.eq_ignore_ascii_case(seg) {
        return false;
    }
    let after = bytes.get(seg.len());
    after.is_none() || after == Some(&b'/')
}

fn has_segment_prefix_ci(bytes: &[u8], seg: &[u8]) -> bool {
    let mut idx = 0usize;
    while idx.saturating_add(seg.len()) <= bytes.len() {
        if let Some(sub) = bytes.get(idx..idx.saturating_add(seg.len())) {
            if sub.eq_ignore_ascii_case(seg) {
                let after = bytes.get(idx.saturating_add(seg.len()));
                if after.is_none() || after == Some(&b'/') {
                    return true;
                }
            }
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl ProtectedFolderFence {
    #[must_use]
    pub const fn new(fda_granted: bool) -> Self {
        Self {
            fda_granted,
            checks: 0,
        }
    }

    #[must_use]
    pub fn classify_path(path: &str) -> u64 {
        let bytes = path.trim().as_bytes();
        if bytes.is_empty() || has_nul_or_dotdot(bytes) {
            return 2;
        }
        if has_segment_prefix_ci(bytes, b"/Library/Containers")
            || has_segment_prefix_ci(bytes, b"/Library/Group Containers")
            || has_segment_prefix_ci(bytes, b"/Library/CloudStorage")
            || has_segment_prefix_ci(bytes, b"/Music")
            || has_segment_prefix_ci(bytes, b"/Pictures")
        {
            2
        } else if has_segment_prefix_ci(bytes, b"/Documents")
            || has_segment_prefix_ci(bytes, b"/Desktop")
            || has_segment_prefix_ci(bytes, b"/Downloads")
            || starts_with_segment_ci(bytes, b"/Volumes")
        {
            1
        } else {
            0
        }
    }

    pub fn allow_lookup(&mut self, path: &str) -> bool {
        let zone = tcc_zone_clamp(Self::classify_path(path), MAX_TCC_ZONE);
        let clearance = if self.fda_granted { 1u64 } else { 0u64 };
        self.checks = tcc_probe_advance(self.checks, self.checks.saturating_add(1));
        tcc_lookup_safe(clearance, zone)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fda_allows_downloads_and_volumes_but_still_blocks_other_app_containers() {
        let mut no_fda = ProtectedFolderFence::new(false);
        assert!(no_fda.allow_lookup("/fixture-home/astream/Cargo.toml"));
        assert!(!no_fda.allow_lookup("/fixture-home/Downloads/archive.tar"));

        let mut with_fda = ProtectedFolderFence::new(true);
        assert!(with_fda.allow_lookup("/fixture-home/Downloads/archive.tar"));
        assert!(with_fda.allow_lookup("/Volumes/Scratch/build"));
        assert!(!with_fda.allow_lookup("/fixture-home/Library/Containers/com.apple.mail/Data"));
    }
}
