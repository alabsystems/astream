// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Metal terminal renderer `gpu_ppm` (`0..=1_000_000` parts-per-million GPU residency) governor
//! throttling background tab glyph-atlas animation when GPU utilization exceeds cap
//! (`aterm ctl @self sys`, `Astream.SysTel.TlaGpuPpmBudget`).

#[cfg(clean_islands)]
#[path = "gpu_ppm_budget_island.rs"]
mod gpu_ppm_budget_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_ppm_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_frame_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use gpu_ppm_budget_island::{sys_frame_advance, sys_ppm_clamp};

/// Full-device GPU residency in parts per million (`1_000_000 ppm == 100%`).
pub const MAX_GPU_PPM: u64 = 1_000_000;

contract_fn! {
    /// Verified GPU budget check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_gpu_within_cap_isl`.
    #[must_use]
    pub const fn sys_gpu_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Governs background-tab Metal redraw cadence from `gpu_ppm` residency telemetry.
#[derive(Debug, Clone)]
pub struct MetalGpuBudgetGovernor {
    ceiling_ppm: u64,
    frames_evaluated: u64,
}

impl MetalGpuBudgetGovernor {
    #[must_use]
    pub const fn new(ceiling_ppm: u64) -> Self {
        Self {
            ceiling_ppm: sys_ppm_clamp(ceiling_ppm, MAX_GPU_PPM),
            frames_evaluated: 0,
        }
    }

    pub fn allow_background_redraw(&mut self, observed_gpu_ppm: u64) -> bool {
        let clamped = sys_ppm_clamp(observed_gpu_ppm, MAX_GPU_PPM);
        self.frames_evaluated = sys_frame_advance(
            self.frames_evaluated,
            self.frames_evaluated.saturating_add(1),
        );
        sys_gpu_within_cap(self.ceiling_ppm, clamped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gpu_governor_allows_redraw_within_ppm_budget_and_defers_under_gpu_saturation() {
        let mut g = MetalGpuBudgetGovernor::new(250_000);
        assert!(g.allow_background_redraw(80_000));
        assert!(!g.allow_background_redraw(420_000));
    }
}
