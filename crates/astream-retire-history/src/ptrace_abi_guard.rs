// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Foreign-process `ptrace` tracee scratch-page arena and non-wrapping pointer bounds verifier
//! (`effects.foreign-process.record-replay`, `Astream.Retire.TlaPtraceAbiGuard`).

#[cfg(clean_islands)]
#[path = "ptrace_abi_guard_island.rs"]
mod ptrace_abi_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn abi_len_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn abi_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ptrace_abi_guard_island::{abi_len_clamp, abi_seq_advance};

/// Size of one dedicated tracee scratch page (`4096` bytes).
pub const MAX_SCRATCH_PAGE_BYTES: u64 = 4096;

contract_fn! {
    /// Verified bounds predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `abi_in_bounds_isl`.
    #[must_use]
    pub const fn abi_in_bounds(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Verified non-wrapping `(tracee_addr, byte_len)` write span for `PTRACE_POKEDATA` / `process_vm_writev`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifiedSyscallFrame {
    pub tracee_addr: u64,
    pub byte_len: u64,
    pub word_aligned: bool,
    pub step_seq: u64,
}

/// Verifier guarding tracee buffer writes against null pointers, kernel-space addresses,
/// `u64` address wrap-around, and scratch-page overrun.
#[derive(Debug, Clone)]
pub struct PtraceAbiVerifier {
    min_user_addr: u64,
    max_user_addr: u64,
    step_seq: u64,
}

impl Default for PtraceAbiVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl PtraceAbiVerifier {
    /// Default 48-bit canonical Linux user-space range `[0x1000 ..= 0x0000_7FFF_FFFF_FFFF]`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            min_user_addr: 0x1000,
            max_user_addr: 0x0000_7FFF_FFFF_FFFF,
            step_seq: 0,
        }
    }

    #[must_use]
    pub const fn step_seq(&self) -> u64 {
        self.step_seq
    }

    /// Validates `(ptr, len)` before injecting taped output bytes into tracee memory.
    pub fn verify_user_slice(
        &mut self,
        ptr: u64,
        len: u64,
    ) -> Result<VerifiedSyscallFrame, &'static str> {
        let clamped_len = abi_len_clamp(len, MAX_SCRATCH_PAGE_BYTES);
        if clamped_len != len {
            return Err("injection slice exceeds MAX_SCRATCH_PAGE_BYTES");
        }
        if !abi_in_bounds(ptr, self.min_user_addr) {
            return Err("null or zero-page tracee pointer refused");
        }
        let end = match ptr.checked_add(clamped_len) {
            Some(e) => e,
            None => return Err("tracee pointer + len wraps u64"),
        };
        if !abi_in_bounds(self.max_user_addr, end) {
            return Err("tracee slice crosses above canonical user-space ceiling");
        }
        self.step_seq = abi_seq_advance(self.step_seq, self.step_seq.saturating_add(1));
        Ok(VerifiedSyscallFrame {
            tracee_addr: ptr,
            byte_len: clamped_len,
            word_aligned: (ptr & 7) == 0,
            step_seq: self.step_seq,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ptrace_abi_guard_rejects_null_kernel_wrap_and_oversized_slices() {
        let mut v = PtraceAbiVerifier::new();
        assert!(v.verify_user_slice(0, 8).is_err());
        assert!(v.verify_user_slice(u64::MAX - 4, 16).is_err());
        assert!(v.verify_user_slice(0x0000_8000_0000_0000, 8).is_err());
        assert!(v.verify_user_slice(0x4000_0000, 8192).is_err());

        let ok = v.verify_user_slice(0x7FFF_0000_1000, 64).unwrap();
        assert!(ok.word_aligned);
        assert_eq!(ok.step_seq, 1);
    }
}
