// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self sys jobs` zero-progress stall detector identifying background commands whose
//! CPU time, child exits, and PTY/log byte counters all stopped advancing (`Astream.SysTel.TlaStalledJobDetector`).

#[cfg(clean_islands)]
#[path = "stalled_job_detector_island.rs"]
mod stalled_job_detector_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_idle_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_alert_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use stalled_job_detector_island::{sys_alert_advance, sys_idle_clamp};

/// Maximum stall window tracked (`86_400` seconds == 24h).
pub const MAX_STALL_WINDOW_SECS: u64 = 86_400;

contract_fn! {
    /// Verified stall threshold check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_job_stalled_isl`.
    #[must_use]
    pub const fn sys_job_stalled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Tracks `(cpu_ns, output_bytes)` progress for a supervised command.
#[derive(Debug, Clone)]
pub struct JobProgressMonitor {
    stall_after_secs: u64,
    last_cpu_ns: u64,
    last_output_bytes: u64,
    idle_secs: u64,
    alerts: u64,
}

impl JobProgressMonitor {
    #[must_use]
    pub const fn new(stall_after_secs: u64) -> Self {
        let clamped = sys_idle_clamp(stall_after_secs, MAX_STALL_WINDOW_SECS);
        Self {
            stall_after_secs: if clamped == 0 { 1 } else { clamped },
            last_cpu_ns: 0,
            last_output_bytes: 0,
            idle_secs: 0,
            alerts: 0,
        }
    }

    pub fn poll(&mut self, dt_secs: u64, cpu_ns: u64, output_bytes: u64) -> bool {
        if cpu_ns > self.last_cpu_ns || output_bytes > self.last_output_bytes {
            if cpu_ns > self.last_cpu_ns {
                self.last_cpu_ns = cpu_ns;
            }
            if output_bytes > self.last_output_bytes {
                self.last_output_bytes = output_bytes;
            }
            self.idle_secs = 0;
            return false;
        }
        self.idle_secs = sys_idle_clamp(
            self.idle_secs.saturating_add(dt_secs),
            MAX_STALL_WINDOW_SECS,
        );
        if sys_job_stalled(self.idle_secs, self.stall_after_secs) {
            self.alerts = sys_alert_advance(self.alerts, self.alerts.saturating_add(1));
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stall_detector_resets_on_cpu_progress_and_trips_when_frozen() {
        let mut m = JobProgressMonitor::new(60);
        assert!(!m.poll(30, 1_000, 0));
        assert!(!m.poll(40, 1_000, 0));
        assert!(m.poll(25, 1_000, 0));
        assert!(!m.poll(30, 2_000, 0));
    }
}
