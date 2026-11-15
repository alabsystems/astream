// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` archive unpack confinement guard ensuring every extracted tar/zip entry resolves
//! strictly inside `atpkg`'s managed prefix and never writes `/opt/homebrew` or `..` escapes
//! (`Astream.Abrew.TlaPrefixConfinementGate`).

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
#[path = "prefix_confinement_gate_island.rs"]
mod prefix_confinement_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_seg_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_path_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use prefix_confinement_gate_island::{ab_path_advance, ab_seg_clamp};

/// Maximum relative archive path depth (`64` components).
pub const MAX_ARCHIVE_DEPTH: u64 = 64;

contract_fn! {
    /// Verified confinement predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ab_inside_prefix_isl`.
    #[must_use]
    pub const fn ab_inside_prefix(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct PrefixConfinementGate {
    entries_checked: u64,
}

impl PrefixConfinementGate {
    #[must_use]
    pub const fn new() -> Self {
        Self { entries_checked: 0 }
    }

    pub fn validate_archive_entry(&mut self, rel_path: &str) -> bool {
        self.entries_checked =
            ab_path_advance(self.entries_checked, self.entries_checked.saturating_add(1));
        if rel_path.is_empty() || rel_path.starts_with('/') {
            return false;
        }
        let mut idx = 0usize;
        let bytes = rel_path.as_bytes();
        while idx < bytes.len() {
            let Some(&b) = bytes.get(idx) else {
                break;
            };
            if b == b'\\' || b == 0 || b == b':' {
                return false;
            }
            idx = idx.saturating_add(1);
        }
        let mut depth = 0u64;
        let mut escapes = 0u64;
        for seg in rel_path.split('/') {
            if seg == ".." {
                escapes = escapes.saturating_add(1);
            } else if !seg.is_empty() && seg != "." {
                depth = depth.saturating_add(1);
            }
        }
        let clamped_depth = ab_seg_clamp(depth, MAX_ARCHIVE_DEPTH);
        escapes == 0 && clamped_depth == depth && ab_inside_prefix(clamped_depth, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_confined_cellar_paths_and_rejects_dotdot_or_root_paths() {
        let mut g = PrefixConfinementGate::new();
        assert!(g.validate_archive_entry("ripgrep/14.1.0/bin/rg"));
        assert!(!g.validate_archive_entry("../../opt/homebrew/bin/rg"));
        assert!(!g.validate_archive_entry("/usr/local/bin/rg"));
    }
}
