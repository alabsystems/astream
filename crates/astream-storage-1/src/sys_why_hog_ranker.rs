// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack `aterm ctl @self sys why` resource-hog ranker & `await sys` quiet gate
//! (`Astream.Host.TlaSysWhyHogRanker`).
//!
//! Ranks active `aterm` session tabs by weighted `(cpu_mcores, rss_mb)` pressure
//! in a fixed `[SysHogSample; 4]` stack leaderboard with **zero heap allocations**,
//! and evaluates whether the machine meets the `await sys` quiet ceiling.

#![allow(clippy::manual_swap)]

#[cfg(clean_islands)]
#[path = "sys_why_hog_ranker_island.rs"]
mod sys_why_hog_ranker_island;
#[cfg(clean_islands)]
pub use sys_why_hog_ranker_island::{sys_sample_epoch_advance_b97, sys_top_k_clamp};

/// Fixed stack leaderboard capacity for `sys why` top offenders.
pub const SYS_WHY_TOP_K: usize = 4;

#[cfg(not(clean_islands))]
/// Monotonically advance the `sys` telemetry sample epoch.
#[must_use]
pub const fn sys_sample_epoch_advance_b97(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp populated top-K hog entries to `max_top_k`.
#[must_use]
pub const fn sys_top_k_clamp(cand_count: u64, max_top_k: u64) -> u64 {
    if cand_count < max_top_k {
        cand_count
    } else {
        max_top_k
    }
}

contract_fn! {
    /// True iff `load_mcores <= quiet_ceiling_mcores`.
    #[must_use]
    pub const fn sys_machine_quiet(load_mcores: u64, quiet_ceiling_mcores: u64) -> bool
    clauses [ensures result == (load_mcores <= quiet_ceiling_mcores)]
    {
        load_mcores <= quiet_ceiling_mcores
    }
}

/// Resource attribution sample for one session/process tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SysHogSample {
    pub sid: u64,
    pub cpu_mcores: u64,
    pub rss_mb: u64,
}

impl SysHogSample {
    pub const EMPTY: Self = Self {
        sid: 0,
        cpu_mcores: 0,
        rss_mb: 0,
    };

    /// Combined pressure score (`1 core = 1000 mcores` weighted equal to `4 GiB = 4096 MiB` RSS).
    #[must_use]
    pub const fn pressure_score(self) -> u64 {
        self.cpu_mcores
            .saturating_mul(4)
            .saturating_add(self.rss_mb)
    }
}

/// Ranked `sys why` snapshot + quiet verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SysWhyReport {
    pub sample_epoch: u64,
    pub top_hogs: [SysHogSample; SYS_WHY_TOP_K],
    pub populated: usize,
    pub total_cpu_mcores: u64,
    pub total_rss_mb: u64,
    pub is_quiet: bool,
}

/// Pure stack `sys why` evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SysWhyHogRanker {
    sample_epoch: u64,
    quiet_cpu_ceiling_mcores: u64,
    quiet_swap_ceiling_mb: u64,
}

impl SysWhyHogRanker {
    #[must_use]
    pub const fn new(quiet_cpu_ceiling_mcores: u64, quiet_swap_ceiling_mb: u64) -> Self {
        Self {
            sample_epoch: 0,
            quiet_cpu_ceiling_mcores,
            quiet_swap_ceiling_mb,
        }
    }

    #[must_use]
    pub const fn sample_epoch(&self) -> u64 {
        self.sample_epoch
    }

    /// Rank `samples` into a fixed top-4 stack array and evaluate `is_quiet`.
    pub fn evaluate(&mut self, samples: &[SysHogSample], swap_used_mb: u64) -> SysWhyReport {
        let cand_ep = self.sample_epoch.saturating_add(1);
        self.sample_epoch = sys_sample_epoch_advance_b97(self.sample_epoch, cand_ep);

        let mut top = [SysHogSample::EMPTY; SYS_WHY_TOP_K];
        let mut count = 0usize;
        let mut total_cpu = 0u64;
        let mut total_rss = 0u64;

        let mut rest = samples;
        while let &[item, ref tail @ ..] = rest {
            total_cpu = total_cpu.saturating_add(item.cpu_mcores);
            total_rss = total_rss.saturating_add(item.rss_mb);

            // Insert `item` into sorted `top[0..SYS_WHY_TOP_K]` descending by `pressure_score()`
            let mut carry = item;
            let mut k = 0usize;
            let limit = if count < SYS_WHY_TOP_K {
                count.saturating_add(1)
            } else {
                SYS_WHY_TOP_K
            };
            while k < limit {
                if let Some(slot) = top.get_mut(k) {
                    if k >= count || carry.pressure_score() > slot.pressure_score() {
                        let displaced = *slot;
                        *slot = carry;
                        carry = displaced;
                    }
                }
                k = k.saturating_add(1);
            }
            if count < SYS_WHY_TOP_K {
                count = count.saturating_add(1);
            }
            rest = tail;
        }

        let clamped_count = sys_top_k_clamp(count as u64, SYS_WHY_TOP_K as u64) as usize;
        let is_quiet = sys_machine_quiet(total_cpu, self.quiet_cpu_ceiling_mcores)
            && swap_used_mb <= self.quiet_swap_ceiling_mb;

        SysWhyReport {
            sample_epoch: self.sample_epoch,
            top_hogs: top,
            populated: clamped_count,
            total_cpu_mcores: total_cpu,
            total_rss_mb: total_rss,
            is_quiet,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ranks_top_offenders_descending_and_evaluates_quiet_machine() {
        let mut ranker = SysWhyHogRanker::new(2_000, 512);
        let samples = [
            SysHogSample {
                sid: 1,
                cpu_mcores: 200,
                rss_mb: 500,
            },
            SysHogSample {
                sid: 2,
                cpu_mcores: 3_500,
                rss_mb: 8_000,
            },
            SysHogSample {
                sid: 3,
                cpu_mcores: 1_000,
                rss_mb: 2_000,
            },
        ];

        let rep = ranker.evaluate(&samples, 128);
        assert_eq!(rep.populated, 3);
        assert_eq!(rep.top_hogs[0].sid, 2);
        assert_eq!(rep.top_hogs[1].sid, 3);
        assert_eq!(rep.top_hogs[2].sid, 1);
        assert!(!rep.is_quiet);

        let quiet_rep = ranker.evaluate(&samples[..1], 128);
        assert!(quiet_rep.is_quiet);
    }
}
