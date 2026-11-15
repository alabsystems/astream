// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Single-fd `read_secret_at` vs `read_secret_at_narrowed` (`aterm fabric on --dry-run`) gate
//! (`evidence/manifest.toml` `cap.secret-file-owner-only`;
//! `Astream.Cap.TlaSecretFileSingleFdNarrowedGate`).
//!
//! Models the shared `astream-cap::capfile` / `aterm-link` secret-file contract:
//! - Judges the already-opened non-blocking descriptor (`O_NONBLOCK | O_NOFOLLOW`) rather than a
//!   separate `stat(path)` call, eliminating path-swap TOCTOU,
//! - Requires regular file (refusing FIFO and directory without blocking), `uid == euid`,
//!   `file_mode & 0o077 == 0`, no macOS `allow` ACL entry, `nlink == 1`, and `len >= SECRET_MIN` (`32`),
//! - `read_secret_at` additionally requires `dir_mode & 0o077 == 0`, whereas
//!   `read_secret_at_narrowed` (`aterm fabric on --dry-run`) relaxes ONLY the directory's mode bits
//!   while still refusing symlinked/foreign/ACL-allowing directories and exposed files!

#[cfg(clean_islands)]
#[path = "secret_file_single_fd_narrowed_gate_island.rs"]
mod secret_file_single_fd_narrowed_gate_island;
#[cfg(clean_islands)]
pub use secret_file_single_fd_narrowed_gate_island::{
    fd_hardlink_cap_clamp_b145, secret_min_floor_advance_b145,
};

/// Minimum mint-secret byte length (`SECRET_MIN = 32`).
pub const SECRET_MIN_BYTES: u64 = 32;
/// Maximum allowed hard-link count for `read_secret_in` / `read_secret_at` (`1`).
pub const SINGLE_HARDLINK_CAP: u64 = 1;

#[cfg(not(clean_islands))]
/// Ensure accepted secret byte length is at least `min_secret_bytes`.
#[must_use]
pub const fn secret_min_floor_advance_b145(min_secret_bytes: u64, raw_secret_bytes: u64) -> u64 {
    if min_secret_bytes < raw_secret_bytes {
        raw_secret_bytes
    } else {
        min_secret_bytes
    }
}

#[cfg(not(clean_islands))]
/// Clamp accepted hard-link count to `max_nlink` (`1`).
#[must_use]
pub const fn fd_hardlink_cap_clamp_b145(cand_nlink: u64, max_nlink: u64) -> u64 {
    if cand_nlink < max_nlink {
        cand_nlink
    } else {
        max_nlink
    }
}

contract_fn! {
    /// True iff file descriptor, directory ownership/ACL, directory mode (or narrowed dry-run),
    /// single hard-link count, and `secret_len >= min_secret_bytes` all hold.
    #[must_use]
    pub const fn secret_at_admissible_b145(
        file_owner_private: bool,
        nlink_is_one: bool,
        dir_owner_no_acl: bool,
        dir_mode_private_or_narrowed: bool,
        secret_len: u64,
        min_secret_bytes: u64,
    ) -> bool
    clauses [ensures result == (file_owner_private && nlink_is_one && dir_owner_no_acl && dir_mode_private_or_narrowed && min_secret_bytes <= secret_len)]
    {
        file_owner_private
            && nlink_is_one
            && dir_owner_no_acl
            && dir_mode_private_or_narrowed
            && min_secret_bytes <= secret_len
    }
}

/// Kind of open file descriptor inspected by `fstat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecretFdKind {
    RegularFile,
    Fifo,
    Directory,
    Symlink,
}

/// Verdict for `read_secret_at` / `read_secret_at_narrowed`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecretFileVerdict {
    AdmittedSecret {
        secret_bytes: u64,
        accepted_nlink: u64,
    },
    RefusedNotRegularFile {
        kind: SecretFdKind,
    },
    RefusedDirectoryOwnerOrAcl,
    RefusedDirectoryGroupOtherMode {
        dir_mode: u64,
    },
    RefusedFileOwnerModeOrAcl,
    RefusedMultipleHardLinks {
        nlink: u64,
    },
    RefusedSecretTooShort {
        secret_len: u64,
    },
}

/// Evaluate single-fd metadata for `read_secret_at` (`narrowed_dry_run = false`) or
/// `read_secret_at_narrowed` (`narrowed_dry_run = true`).
#[must_use]
#[allow(clippy::too_many_arguments)]
pub const fn evaluate_secret_fd(
    fd_kind: SecretFdKind,
    file_owned_by_euid: bool,
    file_mode: u64,
    file_has_allow_acl: bool,
    nlink: u64,
    dir_not_symlink_and_owned_by_euid: bool,
    dir_has_allow_acl: bool,
    dir_mode: u64,
    narrowed_dry_run: bool,
    secret_len: u64,
) -> SecretFileVerdict {
    if !matches!(fd_kind, SecretFdKind::RegularFile) {
        return SecretFileVerdict::RefusedNotRegularFile { kind: fd_kind };
    }
    let dir_owner_no_acl = dir_not_symlink_and_owned_by_euid && !dir_has_allow_acl;
    if !dir_owner_no_acl {
        return SecretFileVerdict::RefusedDirectoryOwnerOrAcl;
    }
    let dir_mode_ok = (dir_mode & 0o077) == 0 || narrowed_dry_run;
    if !dir_mode_ok {
        return SecretFileVerdict::RefusedDirectoryGroupOtherMode {
            dir_mode: dir_mode & 0o777,
        };
    }
    let file_owner_private = file_owned_by_euid && (file_mode & 0o077) == 0 && !file_has_allow_acl;
    if !file_owner_private {
        return SecretFileVerdict::RefusedFileOwnerModeOrAcl;
    }
    let nlink_is_one = nlink == 1;
    if !nlink_is_one {
        return SecretFileVerdict::RefusedMultipleHardLinks { nlink };
    }
    if !secret_at_admissible_b145(
        file_owner_private,
        nlink_is_one,
        dir_owner_no_acl,
        dir_mode_ok,
        secret_len,
        SECRET_MIN_BYTES,
    ) {
        return SecretFileVerdict::RefusedSecretTooShort { secret_len };
    }
    SecretFileVerdict::AdmittedSecret {
        secret_bytes: secret_min_floor_advance_b145(SECRET_MIN_BYTES, secret_len),
        accepted_nlink: fd_hardlink_cap_clamp_b145(nlink, SINGLE_HARDLINK_CAP),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn narrowed_dry_run_relaxes_only_dir_mode_while_enforcing_acl_nlink_and_secret_min() {
        // 0600 file in 0755 dir: refused by `read_secret_at`, admitted by `read_secret_at_narrowed`!
        assert_eq!(
            evaluate_secret_fd(
                SecretFdKind::RegularFile,
                true,
                0o600,
                false,
                1,
                true,
                false,
                0o755,
                false,
                32
            ),
            SecretFileVerdict::RefusedDirectoryGroupOtherMode { dir_mode: 0o755 }
        );
        assert_eq!(
            evaluate_secret_fd(
                SecretFdKind::RegularFile,
                true,
                0o600,
                false,
                1,
                true,
                false,
                0o755,
                true,
                32
            ),
            SecretFileVerdict::AdmittedSecret {
                secret_bytes: 32,
                accepted_nlink: 1
            }
        );
        // macOS `everyone allow` ACL on 0755 dir is STILL refused under `narrowed_dry_run`!
        assert_eq!(
            evaluate_secret_fd(
                SecretFdKind::RegularFile,
                true,
                0o600,
                false,
                1,
                true,
                true,
                0o755,
                true,
                32
            ),
            SecretFileVerdict::RefusedDirectoryOwnerOrAcl
        );
    }
}
