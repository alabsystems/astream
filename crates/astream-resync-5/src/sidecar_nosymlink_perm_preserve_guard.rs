// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sidecar planted-symlink refusal & compaction permission-mode preservation guard
//! (`Astream.Broker.TlaSidecarNosymlinkPermPreserveGuard`).
//!
//! Enforces the filesystem staging security invariants:
//! 1. Staging and destination paths for `.hw`, `.base`, `.replica`, `.compact`, `.state`, `.held`,
//!    and `--seq-file` MUST refuse planted symlinks (`O_NOFOLLOW | O_CREAT | O_EXCL`),
//! 2. Retention/compaction staging MUST `fchmod` the staged file to the source log's exact mode
//!    (never widening e.g. `0o600` to process umask `0o644`) BEFORE atomic `rename`!

#[cfg(clean_islands)]
#[path = "sidecar_nosymlink_perm_preserve_guard_island.rs"]
mod sidecar_nosymlink_perm_preserve_guard_island;
#[cfg(clean_islands)]
pub use sidecar_nosymlink_perm_preserve_guard_island::{
    log_mode_bits_clamp_b142, sidecar_write_seq_advance_b142,
};

#[cfg(not(clean_islands))]
/// Clamp staged permission mode so it never exceeds `source_log_mode`.
#[must_use]
pub const fn log_mode_bits_clamp_b142(raw_mode: u64, source_log_mode: u64) -> u64 {
    if raw_mode < source_log_mode {
        raw_mode
    } else {
        source_log_mode
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the atomic sidecar staging sequence number.
#[must_use]
pub const fn sidecar_write_seq_advance_b142(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// Atomic `rename(stage, dest)` is admissible ONLY when `dest` is not a symlink, `stage` was
    /// opened `O_CREAT | O_EXCL | O_NOFOLLOW`, and `fchmod` preserved the log's permission mode.
    #[must_use]
    pub const fn sidecar_stage_admissible_b142(
        dest_is_symlink: bool,
        stage_opened_excl_nofollow: bool,
        fchmod_matched_log_mode: bool,
    ) -> bool
    clauses [ensures result == (!dest_is_symlink && stage_opened_excl_nofollow && fchmod_matched_log_mode)]
    {
        !dest_is_symlink && stage_opened_excl_nofollow && fchmod_matched_log_mode
    }
}

/// Verdict for staging and atomically renaming a broker sidecar or compacted log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SidecarStageVerdict {
    AdmittedAtomicRename {
        applied_mode: u64,
        write_seq: u64,
    },
    RefusedPlantedSymlink,
    RefusedNonExclStageOpen,
    RefusedPermissionWidening {
        candidate_mode: u64,
        source_log_mode: u64,
    },
}

/// Permission-preserving, symlink-refusing sidecar commit gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SidecarStageGuard {
    source_log_mode: u64,
    write_seq: u64,
}

impl SidecarStageGuard {
    #[must_use]
    pub const fn new(source_log_mode: u64) -> Self {
        Self {
            source_log_mode: source_log_mode & 0o777,
            write_seq: 0,
        }
    }

    pub fn verify_before_rename(
        &mut self,
        cand_seq: u64,
        dest_is_symlink: bool,
        stage_opened_excl_nofollow: bool,
        staged_mode: u64,
    ) -> SidecarStageVerdict {
        if dest_is_symlink {
            return SidecarStageVerdict::RefusedPlantedSymlink;
        }
        if !stage_opened_excl_nofollow {
            return SidecarStageVerdict::RefusedNonExclStageOpen;
        }
        let clean_mode = staged_mode & 0o777;
        // Reject any mode bit present in `clean_mode` that was NOT present in `source_log_mode`!
        let fchmod_ok = clean_mode == self.source_log_mode;
        if !sidecar_stage_admissible_b142(dest_is_symlink, stage_opened_excl_nofollow, fchmod_ok) {
            return SidecarStageVerdict::RefusedPermissionWidening {
                candidate_mode: clean_mode,
                source_log_mode: self.source_log_mode,
            };
        }
        self.write_seq = sidecar_write_seq_advance_b142(self.write_seq, cand_seq);
        SidecarStageVerdict::AdmittedAtomicRename {
            applied_mode: log_mode_bits_clamp_b142(clean_mode, self.source_log_mode),
            write_seq: self.write_seq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_planted_symlink_and_umask_permission_widening_on_retention() {
        let mut g = SidecarStageGuard::new(0o600);
        assert_eq!(
            g.verify_before_rename(1, true, true, 0o600),
            SidecarStageVerdict::RefusedPlantedSymlink
        );
        // Umask default `0o644` widens `0o600` -> refused before rename!
        assert_eq!(
            g.verify_before_rename(1, false, true, 0o644),
            SidecarStageVerdict::RefusedPermissionWidening {
                candidate_mode: 0o644,
                source_log_mode: 0o600
            }
        );
        assert_eq!(
            g.verify_before_rename(1, false, true, 0o600),
            SidecarStageVerdict::AdmittedAtomicRename {
                applied_mode: 0o600,
                write_seq: 1
            }
        );
    }
}
