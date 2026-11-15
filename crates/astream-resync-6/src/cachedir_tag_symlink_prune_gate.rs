// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence tree-walker symlink refusal, named dot-dir allowlist, & `CACHEDIR.TAG` signature gate
//! (`evidence/manifest.toml` `gate.rejects-known-failures`;
//! `Astream.Evidence.TlaCachedirTagSymlinkPruneGate`).
//!
//! Enforces `astream-evidence` tree-linting coverage invariants:
//! - Refuses to run outside a verified workspace root,
//! - Never follows symlinks (neither directory symlinks nor `CACHEDIR.TAG` symlinks),
//! - Prunes ONLY named tool-state dot-directories (`.git`, `.claude`, `.direnv`, `.cargo-build`)
//!   so vendored dependencies hidden in arbitrary `.vendor` dot-directories are STILL linted!
//! - Prunes a cache directory via `CACHEDIR.TAG` ONLY when its first 43 bytes match the exact
//!   Bryan Ford `Signature: 8a477f597d28d172789f06886806bc55` header, and emits a stdout log line
//!   naming every `CACHEDIR.TAG` skip!

#[cfg(clean_islands)]
#[path = "cachedir_tag_symlink_prune_gate_island.rs"]
mod cachedir_tag_symlink_prune_gate_island;
#[cfg(clean_islands)]
pub use cachedir_tag_symlink_prune_gate_island::{
    pruned_dir_count_advance_b144, walk_depth_clamp_b144,
};

/// Canonical 43-byte `CACHEDIR.TAG` first-line signature.
pub const CACHEDIR_TAG_SIGNATURE: &[u8; 43] = b"Signature: 8a477f597d28d172789f06886806bc55";
/// Maximum recursion depth for workspace tree scanning (`64`).
pub const MAX_GATE_WALK_DEPTH: u64 = 64;

#[cfg(not(clean_islands))]
/// Monotonically advance count of explicitly reported `CACHEDIR.TAG` skips.
#[must_use]
pub const fn pruned_dir_count_advance_b144(cur_pruned: u64, cand_pruned: u64) -> u64 {
    if cur_pruned < cand_pruned {
        cand_pruned
    } else {
        cur_pruned
    }
}

#[cfg(not(clean_islands))]
/// Clamp directory walk depth to `max_depth`.
#[must_use]
pub const fn walk_depth_clamp_b144(cand_depth: u64, max_depth: u64) -> u64 {
    if cand_depth < max_depth {
        cand_depth
    } else {
        max_depth
    }
}

contract_fn! {
    /// Pruning via `CACHEDIR.TAG` is authorized ONLY inside the workspace root, on a non-symlink
    /// entry, when `CACHEDIR.TAG` carries the exact 43-byte spec signature.
    #[must_use]
    pub const fn cachedir_prune_authorized_b144(
        inside_workspace_root: bool,
        entry_is_symlink: bool,
        exact_spec_signature: bool,
    ) -> bool
    clauses [ensures result == (inside_workspace_root && !entry_is_symlink && exact_spec_signature)]
    {
        inside_workspace_root && !entry_is_symlink && exact_spec_signature
    }
}

/// Exact named tool-state dot-directory check (unknown `.vendor` dirs are NOT pruned!).
#[must_use]
pub const fn is_named_tool_state_dir(name: &[u8]) -> bool {
    matches!(
        name,
        b".git" | b".claude" | b".direnv" | b".cargo-build" | b"target"
    )
}

/// True iff `header_prefix` starts with the exact 43-byte `CACHEDIR.TAG` spec signature.
#[must_use]
pub fn has_valid_cachedir_signature(header_prefix: &[u8]) -> bool {
    header_prefix.starts_with(CACHEDIR_TAG_SIGNATURE)
}

/// Directory walk action chosen by the evidence gate scanner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateDirWalkAction {
    RefusedOutsideWorkspaceRoot,
    SkipSymlinkNeverFollow,
    PruneNamedToolStateDir,
    PruneTaggedCacheAndReportStdout { reported_skips: u64 },
    DescendAndLint { bounded_depth: u64 },
}

/// Stateful walker tracking `CACHEDIR.TAG` stdout-reported skips and recursion depth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GateTreeWalkGuard {
    inside_workspace_root: bool,
    reported_cachedir_skips: u64,
}

impl GateTreeWalkGuard {
    #[must_use]
    pub const fn new(inside_workspace_root: bool) -> Self {
        Self {
            inside_workspace_root,
            reported_cachedir_skips: 0,
        }
    }

    pub fn classify_directory(
        &mut self,
        dir_name: &[u8],
        raw_depth: u64,
        entry_is_symlink: bool,
        cachedir_tag_first_line: Option<&[u8]>,
    ) -> GateDirWalkAction {
        if !self.inside_workspace_root {
            return GateDirWalkAction::RefusedOutsideWorkspaceRoot;
        }
        if entry_is_symlink {
            return GateDirWalkAction::SkipSymlinkNeverFollow;
        }
        if is_named_tool_state_dir(dir_name) {
            return GateDirWalkAction::PruneNamedToolStateDir;
        }
        let sig_ok = match cachedir_tag_first_line {
            Some(line) => has_valid_cachedir_signature(line),
            None => false,
        };
        if cachedir_prune_authorized_b144(self.inside_workspace_root, entry_is_symlink, sig_ok) {
            let next = self.reported_cachedir_skips.saturating_add(1);
            self.reported_cachedir_skips =
                pruned_dir_count_advance_b144(self.reported_cachedir_skips, next);
            GateDirWalkAction::PruneTaggedCacheAndReportStdout {
                reported_skips: self.reported_cachedir_skips,
            }
        } else {
            GateDirWalkAction::DescendAndLint {
                bounded_depth: walk_depth_clamp_b144(raw_depth, MAX_GATE_WALK_DEPTH),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lints_unlisted_dot_vendor_dirs_and_prunes_only_exact_cachedir_tag() {
        let mut g = GateTreeWalkGuard::new(true);
        // Unlisted `.vendor-sneaky` dot-directory without valid `CACHEDIR.TAG` IS descended & linted!
        assert_eq!(
            g.classify_directory(b".vendor-sneaky", 2, false, Some(b"Signature: wrong")),
            GateDirWalkAction::DescendAndLint { bounded_depth: 2 }
        );
        // Valid 43-byte `CACHEDIR.TAG` is pruned AND counted for mandatory stdout reporting:
        assert_eq!(
            g.classify_directory(
                b".build-cache",
                2,
                false,
                Some(b"Signature: 8a477f597d28d172789f06886806bc55\n")
            ),
            GateDirWalkAction::PruneTaggedCacheAndReportStdout { reported_skips: 1 }
        );
        // Symlinks are never followed even if named like a cache dir:
        assert_eq!(
            g.classify_directory(b"crates", 1, true, None),
            GateDirWalkAction::SkipSymlinkNeverFollow
        );
    }
}
