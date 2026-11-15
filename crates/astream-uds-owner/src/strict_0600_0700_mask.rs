// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Owner-only POSIX permission bitmask verifier (`os.cordon`: passing `0600`, `0400`, `0700` and
//! refusing `0640`, `0604`, `0644`, `0660`, `0755` whenever `(mode & 0o077) != 0`;
//! `Astream.UdsOwn.TlaStrict06000700Mask`).

#[cfg(clean_islands)]
#[path = "strict_0600_0700_mask_island.rs"]
mod strict_0600_0700_mask_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_perm_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_mod_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use strict_0600_0700_mask_island::{uo_mod_advance, uo_perm_clamp};

/// Nine-bit POSIX permission mask (`0o777`).
pub const MAX_PERM_BITS: u64 = 0o777;

contract_fn! {
    /// Verified zero group/other bits (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `uo_group_other_zero_isl`.
    #[must_use]
    pub const fn uo_group_other_zero(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct StrictModeMask {
    checked: u64,
}

impl StrictModeMask {
    #[must_use]
    pub const fn new() -> Self {
        Self { checked: 0 }
    }

    pub fn is_owner_private_mode(&mut self, st_mode: u64) -> bool {
        let perms = uo_perm_clamp(st_mode & MAX_PERM_BITS, MAX_PERM_BITS);
        let group_other = perms & 0o077;
        self.checked = uo_mod_advance(self.checked, self.checked.saturating_add(1));
        uo_group_other_zero(0, group_other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn passes_0600_0400_0700_and_refuses_any_group_or_world_permission_bit() {
        let mut m = StrictModeMask::new();
        assert!(m.is_owner_private_mode(0o600));
        assert!(m.is_owner_private_mode(0o400));
        assert!(m.is_owner_private_mode(0o700));
        assert!(!m.is_owner_private_mode(0o640));
        assert!(!m.is_owner_private_mode(0o604));
        assert!(!m.is_owner_private_mode(0o755));
    }
}
