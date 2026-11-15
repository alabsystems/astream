// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self sys` / `sys jobs` command progress watermark & quiet-machine evaluator
//! (`Astream.Agent.TlaSysStallInspector`).
//!
//! Models `aterm ctl @self sys`, `sys jobs`, `sys why`, and `await sys` (`aterm help sys`):
//! - Tracks monotone cumulative CPU-time watermarks (`prev_cpu_ms <= observed_cpu_ms`) and
//!   I/O byte counters across `sys jobs` samples so long-running silent builds (like LTO
//!   `trustc` or Lean proof checking) with advancing CPU time are recognized as healthy
//!   while genuinely wedged commands (`cpu_delta == 0 && io_delta == 0 && idle_ms >= threshold`)
//!   are flagged stalled (`stalled_jobs <= tracked_jobs`).
//! - Evaluates `await sys` quiet-machine thresholds via verified [`sys_load_is_quiet`].

#[cfg(clean_islands)]
#[path = "sys_stall_inspector_island.rs"]
mod sys_stall_inspector_island;
#[cfg(clean_islands)]
pub use sys_stall_inspector_island::{sys_cpu_watermark_advance, sys_stalled_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn sys_cpu_watermark_advance(cur_ms: u64, sample_ms: u64) -> u64 {
    if cur_ms < sample_ms {
        sample_ms
    } else {
        cur_ms
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn sys_stalled_clamp(stalled: u64, tracked: u64) -> u64 {
    if stalled < tracked {
        stalled
    } else {
        tracked
    }
}

contract_fn! {
    /// Verified check that host load (per-mille of core capacity) sits within the
    /// quiet-machine threshold (`load_permille <= max_load_permille`), linked via
    /// `clean-kernel-defeq` to `sys_load_is_quiet_isl`.
    #[must_use]
    pub const fn sys_load_is_quiet(
        load_permille: u64,
        max_load_permille: u64,
    ) -> bool
    clauses [ensures result == (load_permille <= max_load_permille)]
    {
        load_permille <= max_load_permille
    }
}

/// Snapshot of a single tab job from `aterm ctl @self sys jobs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SysJobSample {
    /// Process group / job identifier.
    pub job_id: u64,
    /// Cumulative user + system CPU milliseconds across the job tree.
    pub cumulative_cpu_ms: u64,
    /// Cumulative disk/pipe bytes read + written across the job tree.
    pub cumulative_io_bytes: u64,
    /// Wall-clock milliseconds since the job last advanced CPU or I/O.
    pub no_progress_ms: u64,
}

/// Aggregate `sys` telemetry summary after inspecting a round of [`SysJobSample`]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SysInspectionReport {
    /// Previous aggregate CPU watermark (`<= observed_cpu_ms`).
    pub prev_cpu_ms: u64,
    /// Updated monotone CPU watermark (`>= prev_cpu_ms`).
    pub observed_cpu_ms: u64,
    /// Clamped count of jobs exceeding `stall_threshold_ms` with zero progress (`<= tracked_jobs`).
    pub stalled_jobs: u64,
    /// Total jobs in the sample.
    pub tracked_jobs: u64,
    /// Job IDs classified as stalled.
    pub stalled_job_ids: Vec<u64>,
    /// Whether the host machine currently satisfies the configured quiet-machine gate.
    pub machine_quiet: bool,
}

/// Stateful `sys jobs` progress watermark & quiet-machine inspector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SysStallInspector {
    stall_threshold_ms: u64,
    max_load_permille: u64,
    max_swap_pct: u64,
    prev_cpu_ms: u64,
    observed_cpu_ms: u64,
    stalled_jobs: u64,
    tracked_jobs: u64,
}

impl SysStallInspector {
    /// Construct a new inspector with `stall_threshold_ms` (minimum `1_000` ms) and
    /// quiet-machine caps `(max_load_permille, max_swap_pct)`.
    #[must_use]
    pub const fn new(stall_threshold_ms: u64, max_load_permille: u64, max_swap_pct: u64) -> Self {
        let thresh = if stall_threshold_ms < 1_000 {
            1_000
        } else {
            stall_threshold_ms
        };
        Self {
            stall_threshold_ms: thresh,
            max_load_permille,
            max_swap_pct,
            prev_cpu_ms: 0,
            observed_cpu_ms: 0,
            stalled_jobs: 0,
            tracked_jobs: 0,
        }
    }

    #[must_use]
    pub const fn tracked_jobs(&self) -> u64 {
        self.tracked_jobs
    }

    #[must_use]
    pub const fn stalled_jobs(&self) -> u64 {
        self.stalled_jobs
    }

    /// Inspect a batch of `jobs` alongside current host `(load_permille, swap_pct)`.
    pub fn inspect(
        &mut self,
        jobs: &[SysJobSample],
        load_permille: u64,
        swap_pct: u64,
    ) -> SysInspectionReport {
        let mut total_cpu = 0u64;
        let mut raw_stalled = 0u64;
        let mut stalled_ids = Vec::new();
        let mut rest = jobs;
        while let &[j, ref tail @ ..] = rest {
            total_cpu = total_cpu.saturating_add(j.cumulative_cpu_ms);
            if j.no_progress_ms >= self.stall_threshold_ms {
                raw_stalled = raw_stalled.saturating_add(1);
                stalled_ids.push(j.job_id);
            }
            rest = tail;
        }
        let tracked = jobs.len() as u64;
        self.prev_cpu_ms = self.observed_cpu_ms;
        self.observed_cpu_ms = sys_cpu_watermark_advance(self.observed_cpu_ms, total_cpu);
        self.stalled_jobs = sys_stalled_clamp(raw_stalled, tracked);
        self.tracked_jobs = tracked;

        SysInspectionReport {
            prev_cpu_ms: self.prev_cpu_ms,
            observed_cpu_ms: self.observed_cpu_ms,
            stalled_jobs: self.stalled_jobs,
            tracked_jobs: self.tracked_jobs,
            stalled_job_ids: stalled_ids,
            machine_quiet: sys_load_is_quiet(load_permille, self.max_load_permille)
                && swap_pct <= self.max_swap_pct,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_silent_cpu_bound_trustc_from_stalled_job_and_checks_quiet_gate() {
        let mut insp = SysStallInspector::new(30_000, 500, 25);

        // Silent LTO compile burning CPU (`no_progress_ms = 0`) while another job hung for 45s.
        let r1 = insp.inspect(
            &[
                SysJobSample {
                    job_id: 101,
                    cumulative_cpu_ms: 148_000,
                    cumulative_io_bytes: 4_096,
                    no_progress_ms: 0,
                },
                SysJobSample {
                    job_id: 102,
                    cumulative_cpu_ms: 120,
                    cumulative_io_bytes: 0,
                    no_progress_ms: 45_000,
                },
            ],
            820,
            10,
        );
        assert_eq!(r1.observed_cpu_ms, 148_120);
        assert_eq!(r1.stalled_jobs, 1);
        assert_eq!(r1.stalled_job_ids, vec![102]);
        assert!(!r1.machine_quiet);

        // After jobs finish, CPU watermark stays monotone and quiet gate turns green!
        let r2 = insp.inspect(&[], 180, 10);
        assert_eq!(r2.prev_cpu_ms, 148_120);
        assert_eq!(r2.observed_cpu_ms, 148_120);
        assert_eq!(r2.stalled_jobs, 0);
        assert!(r2.machine_quiet);
    }
}
