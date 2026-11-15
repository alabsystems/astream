// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-Signal Subprocess Stall Detector (`aterm ctl @self sys jobs`,
//! `Astream.Host.TlaStalledJobDetector`).
//!
//! Naive stdout-only inactivity timers falsely declare quiet CPU-bound proof runs (`trustc`,
//! `z4`, `cargo build`) "hung" while they burn cores silently, whereas deadlocked child processes
//! waiting on a closed pipe or unheld lock advance neither PTY bytes, redirected log bytes, nor
//! cumulative user+system CPU milliseconds.
//!
//! [`SubprocessProgressMonitor`] fuses `(pty_out_bytes, log_file_bytes, cpu_time_ms)` into a
//! monotone composite progress watermark via Clean-origin [`job_progress_advance`], counting
//! consecutive zero-delta samples via Clean-origin [`job_stall_ticks_clamp`] and flagging
//! [`JobLiveness::StalledNoProgress`] iff [`job_stall_threshold_reached`] holds.

#[cfg(clean_islands)]
#[path = "stalled_job_detector_island.rs"]
mod stalled_job_detector_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn job_stall_ticks_clamp(cand_ticks: u64, stall_cap: u64) -> u64 {
    if cand_ticks < stall_cap {
        cand_ticks
    } else {
        stall_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn job_progress_advance(cur_prog: u64, cand_prog: u64) -> u64 {
    if cur_prog < cand_prog {
        cand_prog
    } else {
        cur_prog
    }
}
#[cfg(clean_islands)]
pub use stalled_job_detector_island::{job_progress_advance, job_stall_ticks_clamp};

/// Default consecutive zero-progress samples before classifying a job as stalled (`6` samples).
pub const DEFAULT_JOB_STALL_CAP: u64 = 6;

contract_fn! {
    /// Kernel-certified check that `stall_ticks >= stall_cap`, linked via
    /// `clean-kernel-defeq` to `job_stall_threshold_reached_isl`.
    #[must_use]
    pub const fn job_stall_threshold_reached(stall_ticks: u64, stall_cap: u64) -> bool
    clauses [ensures result == (stall_cap <= stall_ticks)]
    {
        stall_cap <= stall_ticks
    }
}

/// Telemetry sample collected for a running child process tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobActivitySample {
    pub pty_out_bytes: u64,
    pub log_file_bytes: u64,
    pub cpu_time_ms: u64,
}

impl JobActivitySample {
    /// Saturating composite work score across output, log growth, and CPU execution.
    #[must_use]
    pub const fn composite_score(&self) -> u64 {
        self.pty_out_bytes
            .saturating_add(self.log_file_bytes)
            .saturating_add(self.cpu_time_ms)
    }
}

/// Liveness classification returned by [`SubprocessProgressMonitor::observe_sample`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JobLiveness {
    /// At least one of PTY output, log size, or CPU runtime advanced since the last sample.
    ActiveMakingProgress { progress_mark: u64 },
    /// No progress on this sample, still inside grace window (`idle_ticks < stall_cap`).
    QuietWithinGrace { idle_ticks: u64, stall_cap: u64 },
    /// Zero progress across `>= stall_cap` consecutive samples.
    StalledNoProgress {
        idle_ticks: u64,
        last_progress_mark: u64,
    },
}

/// Stateful subprocess progress monitor backed by `Astream.Host.TlaStalledJobDetector`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubprocessProgressMonitor {
    stall_ticks: u64,
    stall_cap: u64,
    progress_mark: u64,
    initialized: bool,
}

impl SubprocessProgressMonitor {
    /// Construct a monitor with `stall_cap` (`>= 1`).
    #[must_use]
    pub const fn new(stall_cap: u64) -> Self {
        let cap = if stall_cap == 0 { 1 } else { stall_cap };
        Self {
            stall_ticks: 0,
            stall_cap: cap,
            progress_mark: 0,
            initialized: false,
        }
    }

    /// Construct a monitor with [`DEFAULT_JOB_STALL_CAP`].
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(DEFAULT_JOB_STALL_CAP)
    }

    /// Consecutive zero-progress ticks (`<= stall_cap`).
    #[must_use]
    pub const fn stall_ticks(&self) -> u64 {
        self.stall_ticks
    }

    /// Monotone highest composite progress watermark observed.
    #[must_use]
    pub const fn progress_mark(&self) -> u64 {
        self.progress_mark
    }

    /// Observe a fresh [`JobActivitySample`] and classify liveness.
    pub fn observe_sample(&mut self, sample: JobActivitySample) -> JobLiveness {
        let score = sample.composite_score();
        if !self.initialized {
            self.initialized = true;
            self.progress_mark = job_progress_advance(self.progress_mark, score);
            self.stall_ticks = 0;
            return JobLiveness::ActiveMakingProgress {
                progress_mark: self.progress_mark,
            };
        }

        let next_mark = job_progress_advance(self.progress_mark, score);
        if next_mark > self.progress_mark {
            self.progress_mark = next_mark;
            self.stall_ticks = 0;
            return JobLiveness::ActiveMakingProgress {
                progress_mark: next_mark,
            };
        }

        let cand_ticks = self.stall_ticks.saturating_add(1);
        let next_ticks = job_stall_ticks_clamp(cand_ticks, self.stall_cap);
        self.stall_ticks = next_ticks;
        if job_stall_threshold_reached(next_ticks, self.stall_cap) {
            JobLiveness::StalledNoProgress {
                idle_ticks: next_ticks,
                last_progress_mark: self.progress_mark,
            }
        } else {
            JobLiveness::QuietWithinGrace {
                idle_ticks: next_ticks,
                stall_cap: self.stall_cap,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cpu_progress_without_stdout_prevents_false_stall_and_deadlock_trips_at_cap() {
        let mut mon = SubprocessProgressMonitor::new(3);
        assert_eq!(
            mon.observe_sample(JobActivitySample {
                pty_out_bytes: 100,
                log_file_bytes: 0,
                cpu_time_ms: 50,
            }),
            JobLiveness::ActiveMakingProgress { progress_mark: 150 }
        );

        // Silent SMT solver: 0 stdout bytes, but CPU ms advances -> ActiveMakingProgress!
        assert_eq!(
            mon.observe_sample(JobActivitySample {
                pty_out_bytes: 100,
                log_file_bytes: 0,
                cpu_time_ms: 950,
            }),
            JobLiveness::ActiveMakingProgress {
                progress_mark: 1050
            }
        );

        // True deadlock: neither stdout, log, nor CPU moves across 3 samples.
        let frozen = JobActivitySample {
            pty_out_bytes: 100,
            log_file_bytes: 0,
            cpu_time_ms: 950,
        };
        assert_eq!(
            mon.observe_sample(frozen),
            JobLiveness::QuietWithinGrace {
                idle_ticks: 1,
                stall_cap: 3,
            }
        );
        assert_eq!(
            mon.observe_sample(frozen),
            JobLiveness::QuietWithinGrace {
                idle_ticks: 2,
                stall_cap: 3,
            }
        );
        assert_eq!(
            mon.observe_sample(frozen),
            JobLiveness::StalledNoProgress {
                idle_ticks: 3,
                last_progress_mark: 1050,
            }
        );
    }
}
