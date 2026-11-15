// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `astream-sys` `owner_private` evaluation-order guard (`os.cordon`: judging macOS ACL allow
//! entries BEFORE POSIX mode bits so a `Mode` refusal guarantees `aterm-uds` can safely `chmod` the
//! directory with no hidden ACL allow entry remaining; `Astream.UdsOwn.TlaAclBeforeModeOrder`).

#[cfg(clean_islands)]
#[path = "acl_before_mode_order_island.rs"]
mod acl_before_mode_order_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_acl_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_ord_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use acl_before_mode_order_island::{uo_acl_clamp, uo_ord_advance};

/// Maximum tracked ACL allow entries (`64`).
pub const MAX_ACL_ALLOWS: u64 = 64;

contract_fn! {
    /// Verified zero-ACL-allows invariant (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `uo_mode_means_no_acl_isl`.
    #[must_use]
    pub const fn uo_mode_means_no_acl(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnerCheckFinding {
    PrivateOk,
    RefusedAcl,
    RefusedMode(u32),
}

#[derive(Debug, Clone, Default)]
pub struct AclFirstJudge {
    judged: u64,
}

impl AclFirstJudge {
    #[must_use]
    pub const fn new() -> Self {
        Self { judged: 0 }
    }

    pub fn judge(&mut self, acl_allow_entries: u64, mode_bits: u32) -> OwnerCheckFinding {
        let allows = uo_acl_clamp(acl_allow_entries, MAX_ACL_ALLOWS);
        self.judged = uo_ord_advance(self.judged, self.judged.saturating_add(1));
        if !uo_mode_means_no_acl(0, allows) {
            return OwnerCheckFinding::RefusedAcl;
        }
        if (mode_bits & 0o077) != 0 {
            OwnerCheckFinding::RefusedMode(mode_bits & 0o777)
        } else {
            OwnerCheckFinding::PrivateOk
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_acl_before_mode_on_0755_directory_with_macos_allow_acl() {
        let mut j = AclFirstJudge::new();
        assert_eq!(j.judge(1, 0o755), OwnerCheckFinding::RefusedAcl);
        assert_eq!(j.judge(0, 0o755), OwnerCheckFinding::RefusedMode(0o755));
        assert_eq!(j.judge(0, 0o700), OwnerCheckFinding::PrivateOk);
    }
}
