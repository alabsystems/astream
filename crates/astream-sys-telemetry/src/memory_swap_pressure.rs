// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `phys_footprint` (`fp_bytes`), compressor, and swap pressure concurrency step-down
//! controller preventing `rust-lld` / Z3 OOM swap storms (`Astream.SysTel.TlaMemorySwapPressure`).

#[cfg(clean_islands)]
#[path = "memory_swap_pressure_island.rs"]
mod memory_swap_pressure_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn w15_sys_jobs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_throttle_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use memory_swap_pressure_island::{sys_throttle_advance, w15_sys_jobs_clamp};

/// Maximum parallel build/solver workers (`-j`).
pub const MAX_BUILD_JOBS: u64 = 32;

contract_fn! {
    /// Verified memory headroom check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_mem_headroom_isl`.
    #[must_use]
    pub const fn sys_mem_headroom(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Recommends safe `-j` parallelism from free RAM MiB and swap growth MiB.
#[derive(Debug, Clone)]
pub struct MemoryPressureStepDown {
    nominal_jobs: u64,
    throttle_events: u64,
}

impl MemoryPressureStepDown {
    #[must_use]
    pub const fn new(nominal_jobs: u64) -> Self {
        let clamped = w15_sys_jobs_clamp(nominal_jobs, MAX_BUILD_JOBS);
        Self {
            nominal_jobs: if clamped == 0 { 1 } else { clamped },
            throttle_events: 0,
        }
    }

    pub fn recommended_jobs(&mut self, available_mb: u64, swap_used_mb: u64) -> u64 {
        if sys_mem_headroom(available_mb, 8_192) && swap_used_mb < 1_024 {
            return self.nominal_jobs;
        }
        self.throttle_events =
            sys_throttle_advance(self.throttle_events, self.throttle_events.saturating_add(1));
        if !sys_mem_headroom(available_mb, 2_048) {
            1
        } else {
            let half = self.nominal_jobs >> 1;
            if half == 0 {
                1
            } else {
                half
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_controller_halves_or_serializes_jobs_under_low_ram_or_swap() {
        let mut c = MemoryPressureStepDown::new(8);
        assert_eq!(c.recommended_jobs(16_384, 0), 8);
        assert_eq!(c.recommended_jobs(4_096, 512), 4);
        assert_eq!(c.recommended_jobs(1_024, 4_096), 1);
    }
}
