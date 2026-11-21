// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `seccomp-bpf` 5-syscall `SECCOMP_RET_TRACE` pre-filter classifier: the filter traces only the
//! intercepted set (`clock_gettime`, `getrandom`, `openat`, `read`, `close`), so the tracer costs
//! O(intercepted) rather than O(all) syscalls
//! (`Astream.SecReplay.TlaSeccompFiveMask`).

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
#[path = "seccomp_five_mask_island.rs"]
mod seccomp_five_mask_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_nr_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_traced_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use seccomp_five_mask_island::{sec_nr_clamp, sec_traced_advance};

/// Maximum Linux x86_64/aarch64 syscall number inspected (`1024`).
pub const MAX_SYSCALL_NR: u64 = 1024;

/// x86_64 Linux syscall numbers for the 5 intercepted deterministic-effect syscalls.
pub const NR_READ: u64 = 0;
pub const NR_CLOSE: u64 = 3;
pub const NR_CLOCK_GETTIME: u64 = 228;
pub const NR_OPENAT: u64 = 257;
pub const NR_GETRANDOM: u64 = 318;

contract_fn! {
    /// Verified BPF trace action (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sec_is_intercepted_isl`.
    #[must_use]
    pub const fn sec_is_intercepted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SeccompFiveFilter {
    traced_stops: u64,
    fast_allowed: u64,
}

impl SeccompFiveFilter {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            traced_stops: 0,
            fast_allowed: 0,
        }
    }

    pub fn eval_syscall(&mut self, nr: u64) -> bool {
        let clamped = sec_nr_clamp(nr, MAX_SYSCALL_NR);
        let hit = nr <= MAX_SYSCALL_NR
            && matches!(
                clamped,
                NR_READ | NR_CLOSE | NR_CLOCK_GETTIME | NR_OPENAT | NR_GETRANDOM
            );
        let code = u64::from(hit);
        if sec_is_intercepted(code, 1) {
            self.traced_stops =
                sec_traced_advance(self.traced_stops, self.traced_stops.saturating_add(1));
            true
        } else {
            self.fast_allowed = self.fast_allowed.saturating_add(1);
            false
        }
    }

    #[must_use]
    pub const fn traced_stops(&self) -> u64 {
        self.traced_stops
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traces_only_the_five_effect_syscalls_and_allows_others_in_kernel() {
        let mut f = SeccompFiveFilter::new();
        assert!(f.eval_syscall(NR_CLOCK_GETTIME));
        assert!(f.eval_syscall(NR_GETRANDOM));
        assert!(!f.eval_syscall(1)); // write
        assert!(!f.eval_syscall(9)); // mmap
        assert_eq!(f.traced_stops(), 2);
    }
}
