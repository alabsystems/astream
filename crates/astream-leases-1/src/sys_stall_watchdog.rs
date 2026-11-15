// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self sys jobs` command progress & stall watchdog
//! (`Astream.Host.TlaSysStallWatchdog`, Island #284).
//!
//! Models how `aterm ctl @self sys jobs` identifies commands in a tab that stopped making
//! progress:
//! - Cumulative work `(cpu_ns + io_bytes + pty_out_bytes)` advances monotonically via
//!   [`sys_progress_advance`].
//! - Whenever a sample observes strictly higher work (`prev_work < next_work`), `silent_ms`
//!   resets to `0`; otherwise `silent_ms` accumulates up to `MAX_SILENT_WINDOW_MS`.
//! - Only a running, non-timer job with `threshold_ms <= silent_ms` is reported `Stalled`.

#[cfg(clean_islands)]
#[path = "sys_stall_watchdog_island.rs"]
mod sys_stall_watchdog_island;
#[cfg(clean_islands)]
pub use sys_stall_watchdog_island::{sys_progress_advance, sys_silent_ms_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_progress_advance(prev_work: u64, cur_work: u64) -> u64 {
    if prev_work < cur_work {
        cur_work
    } else {
        prev_work
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_silent_ms_clamp(silent_ms: u64, max_ms: u64) -> u64 {
    if silent_ms < max_ms {
        silent_ms
    } else {
        max_ms
    }
}

/// Default stall threshold (`60_000` ms = 60 seconds with zero CPU, I/O, or PTY output).
pub const DEFAULT_STALL_THRESHOLD_MS: u64 = 60_000;

/// Maximum clamped silent duration (`24` hours = `86_400_000` ms).
pub const MAX_SILENT_WINDOW_MS: u64 = 86_400_000;

contract_fn! {
    /// Verified check `threshold_ms <= silent_ms`, linked via `clean-kernel-defeq` to
    /// `sys_silence_past_threshold_isl`.
    #[must_use]
    pub const fn sys_silence_past_threshold(silent_ms: u64, threshold_ms: u64) -> bool
    clauses [ensures result == (threshold_ms <= silent_ms)]
    {
        threshold_ms <= silent_ms
    }
}

/// Check `threshold_ms <= silent_ms && running_flag != 0`.
#[inline]
#[must_use]
pub const fn sys_job_is_stalled(silent_ms: u64, threshold_ms: u64, running_flag: u64) -> bool {
    sys_silence_past_threshold(silent_ms, threshold_ms) && running_flag != 0
}

/// Liveness verdict reported for one foreground/background tab job.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JobLiveness {
    /// Job made CPU, disk/socket I/O, or PTY progress within `threshold_ms`.
    MakingProgress { work_units: u64, silent_ms: u64 },
    /// Job is still running with zero progress for `silent_ms >= threshold_ms`.
    Stalled { work_units: u64, silent_ms: u64 },
    /// Job has already exited with `exit_code`; never reported stalled.
    Exited { exit_code: i32 },
}

/// Per-job progress watchdog (`sys jobs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SysJobWatchdog {
    work_units: u64,
    silent_ms: u64,
    threshold_ms: u64,
    exit_code: Option<i32>,
}

impl SysJobWatchdog {
    #[must_use]
    pub const fn new(initial_work: u64, threshold_ms: u64) -> Self {
        let thresh = if threshold_ms == 0 {
            1
        } else {
            sys_silent_ms_clamp(threshold_ms, MAX_SILENT_WINDOW_MS)
        };
        Self {
            work_units: initial_work,
            silent_ms: 0,
            threshold_ms: thresh,
            exit_code: None,
        }
    }

    #[must_use]
    pub const fn work_units(&self) -> u64 {
        self.work_units
    }

    #[must_use]
    pub const fn silent_ms(&self) -> u64 {
        self.silent_ms
    }

    #[must_use]
    pub const fn threshold_ms(&self) -> u64 {
        self.threshold_ms
    }

    #[must_use]
    pub const fn exit_code(&self) -> Option<i32> {
        self.exit_code
    }

    /// Mark the job as exited so subsequent `sys jobs` sweeps never report it stalled.
    pub fn mark_exited(&mut self, code: i32) {
        self.exit_code = Some(code);
        self.silent_ms = 0;
    }

    /// Feed a periodic sample (`observed_work`, `delta_ms` elapsed since previous sample).
    pub fn sample(&mut self, observed_work: u64, delta_ms: u64) -> JobLiveness {
        if let Some(code) = self.exit_code {
            return JobLiveness::Exited { exit_code: code };
        }
        let next_work = sys_progress_advance(self.work_units, observed_work);
        if next_work > self.work_units {
            self.work_units = next_work;
            self.silent_ms = 0;
        } else {
            self.silent_ms = sys_silent_ms_clamp(
                self.silent_ms.saturating_add(delta_ms),
                MAX_SILENT_WINDOW_MS,
            );
        }
        if sys_job_is_stalled(self.silent_ms, self.threshold_ms, 1) {
            JobLiveness::Stalled {
                work_units: self.work_units,
                silent_ms: self.silent_ms,
            }
        } else {
            JobLiveness::MakingProgress {
                work_units: self.work_units,
                silent_ms: self.silent_ms,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_stalled_command_resets_on_io_and_ignores_exited_jobs() {
        let mut w = SysJobWatchdog::new(100, DEFAULT_STALL_THRESHOLD_MS);
        assert_eq!(
            w.sample(100, 30_000),
            JobLiveness::MakingProgress {
                work_units: 100,
                silent_ms: 30_000,
            }
        );
        // Zero new CPU/IO for 60s -> Stalled!
        assert_eq!(
            w.sample(100, 30_000),
            JobLiveness::Stalled {
                work_units: 100,
                silent_ms: 60_000,
            }
        );
        // 1 byte of new output resets `silent_ms` immediately!
        assert_eq!(
            w.sample(101, 5_000),
            JobLiveness::MakingProgress {
                work_units: 101,
                silent_ms: 0,
            }
        );
        w.mark_exited(0);
        assert_eq!(w.sample(101, 120_000), JobLiveness::Exited { exit_code: 0 });
    }
}
