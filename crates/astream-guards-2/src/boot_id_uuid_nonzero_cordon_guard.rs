// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Boot-session UUID non-zero parser & ACL-before-mode owner-privacy cordon guard
//! (`evidence/manifest.toml` `os.cordon`;
//! `Astream.Host.TlaBootIdUuidNonzeroCordonGuard`).
//!
//! Enforces two load-bearing `os.cordon` contracts shared across `aterm-link`, `aterm-agent`,
//! `aterm-uds`, `aterm-release`, and `astream-broker`:
//! 1. `parse_boot_id` accepts exactly `32` hex nybbles (`16` bytes) and STRICTLY REFUSES the
//!    reserved all-zero UUID (`hi_u64 == 0 && lo_u64 == 0`),
//! 2. `owner_private` evaluates owner UID match -> file-vs-dir kind -> Apple allow-ACL BEFORE
//!    checking `(mode & 0o077) == 0`, so `Mode` is reported ONLY when no allow-ACL is present
//!    (`aterm-uds` narrows `Mode` directories in place and must never mistake an ACL leak for `Mode`).

#[cfg(clean_islands)]
#[path = "boot_id_uuid_nonzero_cordon_guard_island.rs"]
mod boot_id_uuid_nonzero_cordon_guard_island;
#[cfg(clean_islands)]
pub use boot_id_uuid_nonzero_cordon_guard_island::{
    boot_nybble_count_clamp_b148, cordon_check_epoch_advance_b148,
};

/// Required hex nybble count for a 128-bit boot UUID (`32`).
pub const BOOT_UUID_HEX_NYBBLES: u64 = 32;

/// Group/other permission mask (`0o077`) forbidden on owner-private files/dirs.
pub const GROUP_OTHER_MODE_MASK: u64 = 0o077;

#[cfg(not(clean_islands))]
/// Clamp scanned hex nybble count to `max_nybbles`.
#[must_use]
pub const fn boot_nybble_count_clamp_b148(cand_nybbles: u64, max_nybbles: u64) -> u64 {
    if cand_nybbles < max_nybbles {
        cand_nybbles
    } else {
        max_nybbles
    }
}

#[cfg(not(clean_islands))]
/// Advance validated cordon check epoch monotonically.
#[must_use]
pub const fn cordon_check_epoch_advance_b148(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `nybbles == 32` and the 128-bit UUID `(hi, lo)` is non-zero.
    #[must_use]
    pub const fn boot_uuid_valid_nonzero_b148(nybbles: u64, hi: u64, lo: u64) -> bool
    clauses [ensures result == (nybbles == 32 && (hi != 0 || lo != 0))]
    {
        nybbles == 32 && (hi != 0 || lo != 0)
    }
}

/// Verdict for `os.cordon` boot-UUID validation and ACL-before-mode privacy check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OsCordonDecision {
    ValidBootId { hi: u64, lo: u64, epoch: u64 },
    RefusedAllZeroBootId,
    RefusedInvalidBootIdLength { nybbles: u64 },
    OwnerPrivatePassed { epoch: u64 },
    RefusedForeignOwner { file_uid: u64, euid: u64 },
    RefusedWrongFileKind,
    RefusedAllowAclPresent,
    RefusedOpenGroupOtherMode { mode_bits: u64 },
}

/// Stateful `os.cordon` validator tracking monotonic check epoch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BootAndPrivacyCordonGuard {
    check_epoch: u64,
}

impl BootAndPrivacyCordonGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { check_epoch: 0 }
    }

    #[must_use]
    pub const fn check_epoch(&self) -> u64 {
        self.check_epoch
    }

    /// Validate parsed `(nybbles, hi, lo)` from a candidate boot-session UUID string.
    pub fn validate_boot_uuid(&mut self, nybbles: u64, hi: u64, lo: u64) -> OsCordonDecision {
        let clamped_nybbles = boot_nybble_count_clamp_b148(nybbles, 64);
        if clamped_nybbles != BOOT_UUID_HEX_NYBBLES {
            return OsCordonDecision::RefusedInvalidBootIdLength {
                nybbles: clamped_nybbles,
            };
        }
        if !boot_uuid_valid_nonzero_b148(clamped_nybbles, hi, lo) {
            return OsCordonDecision::RefusedAllZeroBootId;
        }
        let next = self.check_epoch.saturating_add(1);
        self.check_epoch = cordon_check_epoch_advance_b148(self.check_epoch, next);
        OsCordonDecision::ValidBootId {
            hi,
            lo,
            epoch: self.check_epoch,
        }
    }

    /// Evaluate owner-privacy clauses in strict `Owner -> Kind -> AllowAcl -> Mode` order!
    pub fn check_owner_private(
        &mut self,
        file_uid: u64,
        euid: u64,
        kind_matches: bool,
        has_allow_acl: bool,
        mode: u64,
    ) -> OsCordonDecision {
        if file_uid != euid {
            return OsCordonDecision::RefusedForeignOwner { file_uid, euid };
        }
        if !kind_matches {
            return OsCordonDecision::RefusedWrongFileKind;
        }
        // CRITICAL (`os.cordon`): ACL is judged BEFORE mode bits so `0644` + allow-ACL is `Acl`, never `Mode`!
        if has_allow_acl {
            return OsCordonDecision::RefusedAllowAclPresent;
        }
        let leaked_bits = mode & GROUP_OTHER_MODE_MASK;
        if leaked_bits != 0 {
            return OsCordonDecision::RefusedOpenGroupOtherMode {
                mode_bits: mode & 0o777,
            };
        }
        let next = self.check_epoch.saturating_add(1);
        self.check_epoch = cordon_check_epoch_advance_b148(self.check_epoch, next);
        OsCordonDecision::OwnerPrivatePassed {
            epoch: self.check_epoch,
        }
    }
}

impl Default for BootAndPrivacyCordonGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_all_zero_uuid_and_judges_allow_acl_before_open_mode_bits() {
        let mut g = BootAndPrivacyCordonGuard::new();
        assert_eq!(
            g.validate_boot_uuid(32, 0, 0),
            OsCordonDecision::RefusedAllZeroBootId
        );
        assert_eq!(
            g.validate_boot_uuid(32, 0, 1),
            OsCordonDecision::ValidBootId {
                hi: 0,
                lo: 1,
                epoch: 1,
            }
        );
        // 0644 with allow-ACL MUST report `RefusedAllowAclPresent`, never `Mode`!
        assert_eq!(
            g.check_owner_private(501, 501, true, true, 0o644),
            OsCordonDecision::RefusedAllowAclPresent
        );
        // Once `chmod -N` clears allow-ACL, the same 0644 reports `RefusedOpenGroupOtherMode`!
        assert_eq!(
            g.check_owner_private(501, 501, true, false, 0o644),
            OsCordonDecision::RefusedOpenGroupOtherMode { mode_bits: 0o644 }
        );
        assert_eq!(
            g.check_owner_private(501, 501, true, false, 0o600),
            OsCordonDecision::OwnerPrivatePassed { epoch: 2 }
        );
    }
}
