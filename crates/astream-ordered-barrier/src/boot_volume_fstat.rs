// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Opened-descriptor `fstat` `st_dev` boot-volume matcher (`broker.ordered-tier`: judging by the
//! opened file's own device so `/dev/fd/N` on the boot volume passes while `/dev/null` on `devfs`
//! is served `Strict`; `Astream.OrdBar.TlaBootVolumeFstat`).

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
#[path = "boot_volume_fstat_island.rs"]
mod boot_volume_fstat_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_dev_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_stat_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use boot_volume_fstat_island::{ob_dev_clamp, ob_stat_advance};

/// Maximum 32-bit Darwin `dev_t` (`0xFFFF_FFFF`).
pub const MAX_DARWIN_DEV_T: u64 = 0xFFFF_FFFF;

contract_fn! {
    /// Verified boot-volume match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ob_on_boot_vol_isl`.
    #[must_use]
    pub const fn ob_on_boot_vol(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct BootVolumeMatcher {
    root_st_dev: u64,
    root_valid: bool,
    probes: u64,
}

impl BootVolumeMatcher {
    #[must_use]
    pub const fn new(root_st_dev: u64) -> Self {
        Self {
            root_st_dev: ob_dev_clamp(root_st_dev, MAX_DARWIN_DEV_T),
            root_valid: root_st_dev != 0 && root_st_dev <= MAX_DARWIN_DEV_T,
            probes: 0,
        }
    }

    pub fn is_boot_volume_fd(&mut self, fd_st_dev: u64, is_apple: bool) -> bool {
        self.probes = ob_stat_advance(self.probes, self.probes.saturating_add(1));
        if !self.root_valid || fd_st_dev == 0 || fd_st_dev > MAX_DARWIN_DEV_T {
            return false;
        }
        let dev = ob_dev_clamp(fd_st_dev, MAX_DARWIN_DEV_T);
        let ok = is_apple && dev == self.root_st_dev;
        ob_on_boot_vol(if ok { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_boot_volume_by_fd_device_and_rejects_devfs_or_non_apple() {
        let mut m = BootVolumeMatcher::new(16_777_234);
        assert!(m.is_boot_volume_fd(16_777_234, true));
        assert!(!m.is_boot_volume_fd(553_648_128, true)); // devfs
        assert!(!m.is_boot_volume_fd(16_777_234, false));
    }
}
