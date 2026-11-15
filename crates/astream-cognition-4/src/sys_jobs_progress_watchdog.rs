// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self sys jobs` stalled-command progress watchdog
//! (`Astream.Host.TlaSysJobsProgressWatchdog`).
//!
//! Tracks CPU-time, I/O-byte, and PTY-output tick progress for commands running inside an `aterm`
//! tab (`aterm help sys`): resets `stall_ticks` whenever cumulative progress advances and flags a
//! job as stalled once `stall_ticks >= stall_threshold` across monotone `sample_epoch`.

#[cfg(clean_islands)]
#[path = "sys_jobs_progress_watchdog_island.rs"]
mod sys_jobs_progress_watchdog_island;
#[cfg(clean_islands)]
pub use sys_jobs_progress_watchdog_island::{
    sys_job_sample_epoch_advance_b116, sys_job_stall_ticks_clamp_b116,
};

#[cfg(not(clean_islands))]
/// Clamp consecutive zero-progress `stall_ticks` to `stall_threshold`.
#[must_use]
pub const fn sys_job_stall_ticks_clamp_b116(cand_ticks: u64, stall_threshold: u64) -> u64 {
    if cand_ticks < stall_threshold {
        cand_ticks
    } else {
        stall_threshold
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `sample_epoch`.
#[must_use]
pub const fn sys_job_sample_epoch_advance_b116(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `stall_ticks` has reached `stall_threshold`.
    #[must_use]
    pub const fn sys_job_is_stalled_b116(stall_ticks: u64, stall_threshold: u64) -> bool
    clauses [ensures result == (stall_threshold <= stall_ticks)]
    {
        stall_threshold <= stall_ticks
    }
}

/// Progress verdict for a supervised tab job (`aterm ctl @self sys jobs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SysJobProgressVerdict {
    MakingProgress {
        sample_epoch: u64,
        cumulative_units: u64,
    },
    QuietBelowThreshold {
        sample_epoch: u64,
        stall_ticks: u64,
    },
    StalledNoProgress {
        sample_epoch: u64,
        stall_ticks: u64,
    },
}

/// Watchdog tracking cumulative CPU+IO+PTY work units for a tab command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SysJobsProgressWatchdog {
    last_cumulative_units: u64,
    stall_ticks: u64,
    stall_threshold: u64,
    sample_epoch: u64,
}

impl SysJobsProgressWatchdog {
    #[must_use]
    pub const fn new(stall_threshold: u64) -> Self {
        let thresh = if stall_threshold == 0 {
            6
        } else {
            stall_threshold
        };
        Self {
            last_cumulative_units: 0,
            stall_ticks: 0,
            stall_threshold: thresh,
            sample_epoch: 0,
        }
    }

    #[must_use]
    pub const fn stall_ticks(&self) -> u64 {
        self.stall_ticks
    }

    /// Record a periodic `sys` telemetry sample (`cpu_ms + io_kb + pty_bytes`).
    pub fn record_sample(&mut self, cumulative_units: u64) -> SysJobProgressVerdict {
        let next_ep = self.sample_epoch.saturating_add(1);
        self.sample_epoch = sys_job_sample_epoch_advance_b116(self.sample_epoch, next_ep);

        if cumulative_units > self.last_cumulative_units {
            self.last_cumulative_units = cumulative_units;
            self.stall_ticks = 0;
            return SysJobProgressVerdict::MakingProgress {
                sample_epoch: self.sample_epoch,
                cumulative_units,
            };
        }
        let cand = self.stall_ticks.saturating_add(1);
        self.stall_ticks = sys_job_stall_ticks_clamp_b116(cand, self.stall_threshold);
        if sys_job_is_stalled_b116(self.stall_ticks, self.stall_threshold) {
            SysJobProgressVerdict::StalledNoProgress {
                sample_epoch: self.sample_epoch,
                stall_ticks: self.stall_ticks,
            }
        } else {
            SysJobProgressVerdict::QuietBelowThreshold {
                sample_epoch: self.sample_epoch,
                stall_ticks: self.stall_ticks,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags_job_that_stops_making_cpu_or_io_progress() {
        let mut w = SysJobsProgressWatchdog::new(2);
        assert_eq!(
            w.record_sample(100),
            SysJobProgressVerdict::MakingProgress {
                sample_epoch: 1,
                cumulative_units: 100
            }
        );
        assert_eq!(
            w.record_sample(100),
            SysJobProgressVerdict::QuietBelowThreshold {
                sample_epoch: 2,
                stall_ticks: 1
            }
        );
        assert_eq!(
            w.record_sample(100),
            SysJobProgressVerdict::StalledNoProgress {
                sample_epoch: 3,
                stall_ticks: 2
            }
        );
    }
}
