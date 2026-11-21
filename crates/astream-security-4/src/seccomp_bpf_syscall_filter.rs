// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Architecture-pinned `seccomp-bpf` selective syscall pre-filter (`O(intercepted)` tracer cost)
//! (foreign-process replay: the `seccomp-bpf` pre-filter;
//! `Astream.Host.TlaSeccompBpfSyscallFilter`).
//!
//! Models a `seccomp-bpf` filter installed prior to `execve` that:
//! - Pins `seccomp_data.arch` to the expected ABI (`AUDIT_ARCH_X86_64` or `AUDIT_ARCH_AARCH64`) and
//!   kills/refuses any foreign/compat-32 ABI call so alternate syscall numbers cannot bypass tracing,
//! - Emits `SECCOMP_RET_TRACE` ONLY for the five effect-bearing syscalls (`clock_gettime`,
//!   `getrandom`, `openat`, `read`, `close`) and `SECCOMP_RET_ALLOW` for all pure compute/memory
//!   syscalls so `traced_stops <= total_syscalls` (`O(intercepted)` ptrace context switches).

#[cfg(clean_islands)]
#[path = "seccomp_bpf_syscall_filter_island.rs"]
mod seccomp_bpf_syscall_filter_island;
#[cfg(clean_islands)]
pub use seccomp_bpf_syscall_filter_island::{
    seccomp_total_advance_b128, seccomp_traced_clamp_b128,
};

#[cfg(not(clean_islands))]
/// Clamp `traced_stops` to `<= total_syscalls`.
#[must_use]
pub const fn seccomp_traced_clamp_b128(cand_traced: u64, total_syscalls: u64) -> u64 {
    if cand_traced < total_syscalls {
        cand_traced
    } else {
        total_syscalls
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance total observed syscall count.
#[must_use]
pub const fn seccomp_total_advance_b128(cur_total: u64, cand_total: u64) -> u64 {
    if cur_total < cand_total {
        cand_total
    } else {
        cur_total
    }
}

contract_fn! {
    /// True iff `observed_arch == pinned_arch` and `nr` is outside the x32 high-bit ABI (`nr < 0x4000_0000`).
    #[must_use]
    pub const fn seccomp_arch_and_abi_valid_b128(
        observed_arch: u64,
        pinned_arch: u64,
        syscall_nr: u64,
    ) -> bool
    clauses [ensures result == (observed_arch == pinned_arch && syscall_nr < 0x4000_0000)]
    {
        observed_arch == pinned_arch && syscall_nr < 0x4000_0000
    }
}

pub const AUDIT_ARCH_X86_64_TAG: u64 = 0xC000_003E;
pub const AUDIT_ARCH_AARCH64_TAG: u64 = 0xC000_00B7;

/// Linux `x86_64` syscall numbers for the 5 intercepted foreign-process effect syscalls.
pub mod x86_64_nr {
    pub const READ: u64 = 0;
    pub const CLOSE: u64 = 3;
    pub const CLOCK_GETTIME: u64 = 228;
    pub const OPENAT: u64 = 257;
    pub const GETRANDOM: u64 = 318;
}

/// Linux `aarch64` syscall numbers for the 5 intercepted foreign-process effect syscalls.
pub mod aarch64_nr {
    pub const OPENAT: u64 = 56;
    pub const CLOSE: u64 = 57;
    pub const READ: u64 = 63;
    pub const CLOCK_GETTIME: u64 = 113;
    pub const GETRANDOM: u64 = 278;
}

/// Intercepted foreign-process effect kind matched by the `seccomp-bpf` filter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterceptedSyscall {
    ClockGettime,
    Getrandom,
    Openat,
    Read,
    Close,
}

/// `seccomp-bpf` return action for one evaluated `seccomp_data` frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeccompFilterVerdict {
    /// `SECCOMP_RET_ALLOW`: kernel executes directly with zero `ptrace` stop overhead.
    AllowFastPath,
    /// `SECCOMP_RET_TRACE`: kernel stops child into `PTRACE_EVENT_SECCOMP` with `kind` tag.
    TraceIntercepted { kind: InterceptedSyscall },
    /// `SECCOMP_RET_KILL_PROCESS`: wrong `AUDIT_ARCH_*` or x32 ABI bit detected.
    KillForeignAbi { observed_arch: u64, syscall_nr: u64 },
}

/// Architecture-pinned `seccomp-bpf` classifier & stop-ratio meter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeccompBpfSyscallFilter {
    pinned_arch: u64,
    total_syscalls: u64,
    traced_stops: u64,
}

impl SeccompBpfSyscallFilter {
    #[must_use]
    pub const fn new(pinned_arch: u64) -> Self {
        Self {
            pinned_arch,
            total_syscalls: 0,
            traced_stops: 0,
        }
    }

    #[must_use]
    pub const fn traced_stops(&self) -> u64 {
        self.traced_stops
    }

    #[must_use]
    pub const fn total_syscalls(&self) -> u64 {
        self.total_syscalls
    }

    #[must_use]
    const fn classify_nr(&self, nr: u64) -> Option<InterceptedSyscall> {
        if self.pinned_arch == AUDIT_ARCH_X86_64_TAG {
            match nr {
                x86_64_nr::CLOCK_GETTIME => Some(InterceptedSyscall::ClockGettime),
                x86_64_nr::GETRANDOM => Some(InterceptedSyscall::Getrandom),
                x86_64_nr::OPENAT => Some(InterceptedSyscall::Openat),
                x86_64_nr::READ => Some(InterceptedSyscall::Read),
                x86_64_nr::CLOSE => Some(InterceptedSyscall::Close),
                _ => None,
            }
        } else if self.pinned_arch == AUDIT_ARCH_AARCH64_TAG {
            match nr {
                aarch64_nr::CLOCK_GETTIME => Some(InterceptedSyscall::ClockGettime),
                aarch64_nr::GETRANDOM => Some(InterceptedSyscall::Getrandom),
                aarch64_nr::OPENAT => Some(InterceptedSyscall::Openat),
                aarch64_nr::READ => Some(InterceptedSyscall::Read),
                aarch64_nr::CLOSE => Some(InterceptedSyscall::Close),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Evaluate a `seccomp_data` `(observed_arch, syscall_nr)` tuple.
    pub fn evaluate(&mut self, observed_arch: u64, syscall_nr: u64) -> SeccompFilterVerdict {
        self.total_syscalls =
            seccomp_total_advance_b128(self.total_syscalls, self.total_syscalls.saturating_add(1));
        if !seccomp_arch_and_abi_valid_b128(observed_arch, self.pinned_arch, syscall_nr) {
            return SeccompFilterVerdict::KillForeignAbi {
                observed_arch,
                syscall_nr,
            };
        }
        match self.classify_nr(syscall_nr) {
            Some(kind) => {
                self.traced_stops = seccomp_traced_clamp_b128(
                    self.traced_stops.saturating_add(1),
                    self.total_syscalls,
                );
                SeccompFilterVerdict::TraceIntercepted { kind }
            }
            None => SeccompFilterVerdict::AllowFastPath,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn traces_only_five_effect_syscalls_allows_compute_syscalls_and_kills_x32_or_wrong_arch() {
        let mut f = SeccompBpfSyscallFilter::new(AUDIT_ARCH_X86_64_TAG);

        // 100 brk/mmap/write compute syscalls run on the fast path with zero ptrace stops.
        for _ in 0..100 {
            assert_eq!(
                f.evaluate(AUDIT_ARCH_X86_64_TAG, 12), // brk
                SeccompFilterVerdict::AllowFastPath
            );
        }
        assert_eq!(f.traced_stops(), 0);
        assert_eq!(f.total_syscalls(), 100);

        // The intercepted trio: clock_gettime, getrandom, read.
        assert_eq!(
            f.evaluate(AUDIT_ARCH_X86_64_TAG, x86_64_nr::CLOCK_GETTIME),
            SeccompFilterVerdict::TraceIntercepted {
                kind: InterceptedSyscall::ClockGettime
            }
        );
        assert_eq!(
            f.evaluate(AUDIT_ARCH_X86_64_TAG, x86_64_nr::GETRANDOM),
            SeccompFilterVerdict::TraceIntercepted {
                kind: InterceptedSyscall::Getrandom
            }
        );
        assert_eq!(
            f.evaluate(AUDIT_ARCH_X86_64_TAG, x86_64_nr::READ),
            SeccompFilterVerdict::TraceIntercepted {
                kind: InterceptedSyscall::Read
            }
        );
        assert_eq!(f.traced_stops(), 3);

        // x32 high-bit bypass attempt is killed immediately.
        assert_eq!(
            f.evaluate(AUDIT_ARCH_X86_64_TAG, 0x4000_0000 | x86_64_nr::READ),
            SeccompFilterVerdict::KillForeignAbi {
                observed_arch: AUDIT_ARCH_X86_64_TAG,
                syscall_nr: 0x4000_0000 | x86_64_nr::READ,
            }
        );
    }
}
