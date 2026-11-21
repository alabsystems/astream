// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Replay-time syscall no-op neutralization gate: rewrite the syscall to a no-op at the seccomp
//! stop, then inject the taped return value and buffer, so no real syscall reaches the kernel
//! (`Astream.SecReplay.TlaSyscallNoopNeutralize`).

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
#[path = "syscall_noop_neutralize_island.rs"]
mod syscall_noop_neutralize_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_arg_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_neut_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use syscall_noop_neutralize_island::{sec_arg_clamp, sec_neut_advance};

/// Harmless side-effect-free `getpid` / `-1` neutralization slot ceiling (`1024`).
pub const MAX_NEUTRALIZED_NR: u64 = 1024;
/// Linux `orig_rax = u64::MAX` (`-1`) skips kernel syscall dispatch and yields `-ENOSYS`.
pub const NEUTRALIZED_ORIG_NR: i64 = -1;

contract_fn! {
    /// Verified neutralized stop before return injection (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sec_kernel_bypassed_isl`.
    #[must_use]
    pub const fn sec_kernel_bypassed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SyscallNeutralizer {
    neutralized_count: u64,
    in_neutralized_stop: bool,
    desynced: bool,
}

impl SyscallNeutralizer {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            neutralized_count: 0,
            in_neutralized_stop: false,
            desynced: false,
        }
    }

    pub fn on_seccomp_entry(&mut self, orig_nr: u64) -> i64 {
        let _nr = sec_arg_clamp(orig_nr, MAX_NEUTRALIZED_NR);
        if self.in_neutralized_stop || orig_nr > MAX_NEUTRALIZED_NR {
            self.desynced = true;
            self.in_neutralized_stop = false;
            return NEUTRALIZED_ORIG_NR;
        }
        self.in_neutralized_stop = true;
        NEUTRALIZED_ORIG_NR
    }

    pub fn inject_return_on_exit(&mut self, taped_ret: i64) -> Option<i64> {
        if self.desynced {
            return None;
        }
        let bypassed = u64::from(self.in_neutralized_stop);
        if !sec_kernel_bypassed(bypassed, 1) {
            return None;
        }
        self.in_neutralized_stop = false;
        self.neutralized_count = sec_neut_advance(
            self.neutralized_count,
            self.neutralized_count.saturating_add(1),
        );
        Some(taped_ret)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewrites_entry_to_minus_one_before_injecting_taped_return() {
        let mut n = SyscallNeutralizer::new();
        assert_eq!(n.inject_return_on_exit(32), None);
        assert_eq!(n.on_seccomp_entry(318), -1);
        assert_eq!(n.inject_return_on_exit(32), Some(32));
    }
}
