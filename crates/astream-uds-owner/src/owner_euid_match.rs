// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Descriptor `st_uid == geteuid()` ownership verifier (`os.cordon`: `/` owned by `0` is refused
//! as `Owner(0)` for unprivileged callers before inspecting mode bits;
//! `Astream.UdsOwn.TlaOwnerEuidMatch`).

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
#[path = "owner_euid_match_island.rs"]
mod owner_euid_match_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_uid_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_own_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use owner_euid_match_island::{uo_own_advance, uo_uid_clamp};

/// Maximum 32-bit POSIX `uid_t` (`0xFFFF_FFFF`).
pub const MAX_POSIX_UID: u64 = 0xFFFF_FFFF;

contract_fn! {
    /// Verified `st_uid == euid` match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `uo_owned_by_self_isl`.
    #[must_use]
    pub const fn uo_owned_by_self(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct EuidOwnerChecker {
    verified: u64,
}

impl EuidOwnerChecker {
    #[must_use]
    pub const fn new() -> Self {
        Self { verified: 0 }
    }

    pub fn verify_owner(&mut self, file_uid: u64, caller_euid: u64) -> Result<(), u64> {
        self.verified = uo_own_advance(self.verified, self.verified.saturating_add(1));
        if file_uid > MAX_POSIX_UID || caller_euid > MAX_POSIX_UID {
            return Err(file_uid);
        }
        let f = uo_uid_clamp(file_uid, MAX_POSIX_UID);
        let e = uo_uid_clamp(caller_euid, MAX_POSIX_UID);
        if uo_owned_by_self(if f == e { 1 } else { 0 }, 1) {
            Ok(())
        } else {
            Err(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_root_owned_path_for_non_root_euid_naming_owner_zero() {
        let mut c = EuidOwnerChecker::new();
        assert_eq!(c.verify_owner(501, 501), Ok(()));
        assert_eq!(c.verify_owner(0, 501), Err(0));
    }
}
