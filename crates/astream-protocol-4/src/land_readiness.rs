// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autopilot `land` Zero-Residual Repository Readiness Gate
//! (`Astream.Evidence.TlaLandReadinessGate`).
//!
//! Under `aterm` Autopilot `land`, a session completes only when every piece of session work is
//! merged and pushed on remote `main` — zero uncommitted edits, zero untracked leftovers, zero
//! unpushed local commits, zero un-rebased remote `main` commits, zero parked stashes, zero
//! parked local branches, and a green verification run at the current epoch — defended by a
//! canonical `Nothing left:` summary.
//!
//! [`LandReadinessEvaluator`] tracks monotone verified epochs via Clean-origin
//! [`land_epoch_advance`], bounds aggregate residual debt via Clean-origin [`land_debt_clamp`],
//! checks zero residual debt via contract-verified [`land_debt_is_zero`], and returns either
//! [`LandVerdict::LandedClean`] (with its formatted `Nothing left:` defense) or the exact list
//! of [`LandBlocker`] items still open.

#[cfg(clean_islands)]
#[path = "land_readiness_island.rs"]
mod land_readiness_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_debt_clamp(raw_debt: u64, debt_cap: u64) -> u64 {
    if raw_debt < debt_cap {
        raw_debt
    } else {
        debt_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn land_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use land_readiness_island::{land_debt_clamp, land_epoch_advance};

/// Default upper bound used to clamp saturated debt summaries.
pub const DEFAULT_LAND_DEBT_CAP: u64 = 1_000_000;

contract_fn! {
    /// Kernel-certified check that aggregate residual repository debt is zero
    /// (`total_debt == 0`), linked via `clean-kernel-defeq` to `land_debt_is_zero_isl`.
    #[must_use]
    pub const fn land_debt_is_zero(total_debt: u64) -> bool
    clauses [ensures result == (total_debt == 0)]
    {
        total_debt == 0
    }
}

/// Snapshot of workspace repository state inspected before declaring `Nothing left:`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RepoLandSnapshot {
    pub dirty_tracked_files: u64,
    pub untracked_files: u64,
    pub unpushed_commits: u64,
    pub behind_remote_commits: u64,
    pub stash_entries: u64,
    pub unmerged_local_branches: u64,
    pub verify_passed: bool,
    pub commit_epoch: u64,
}

impl RepoLandSnapshot {
    /// Saturating sum of all six git-visible residual debt counters.
    #[must_use]
    pub const fn raw_total_debt(&self) -> u64 {
        self.dirty_tracked_files
            .saturating_add(self.untracked_files)
            .saturating_add(self.unpushed_commits)
            .saturating_add(self.behind_remote_commits)
            .saturating_add(self.stash_entries)
            .saturating_add(self.unmerged_local_branches)
    }
}

/// Specific residual item preventing an Autopilot `land` session from concluding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LandBlocker {
    DirtyWorkingTree {
        count: u64,
    },
    UntrackedFiles {
        count: u64,
    },
    UnpushedCommits {
        count: u64,
    },
    BehindRemoteMain {
        count: u64,
    },
    ParkedStashes {
        count: u64,
    },
    ParkedBranches {
        count: u64,
    },
    VerificationNotPassed,
    StaleCommitEpoch {
        observed: u64,
        required_at_least: u64,
    },
}

/// Outcome of evaluating [`RepoLandSnapshot`] against [`LandReadinessEvaluator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LandVerdict {
    /// Every debt counter is zero, verification passed at the monotone head epoch, and the
    /// session may emit the returned `Nothing left:` defense string.
    LandedClean {
        verified_epoch: u64,
        defense_line: String,
    },
    /// Work remains before landing is complete.
    Incomplete {
        bounded_debt: u64,
        blockers: Vec<LandBlocker>,
    },
}

/// Stateful evaluator enforcing monotone `verified_epoch` progression and bounded debt reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LandReadinessEvaluator {
    bounded_debt: u64,
    debt_cap: u64,
    verified_epoch: u64,
}

impl LandReadinessEvaluator {
    /// Create a new evaluator with `debt_cap` (clamped to `>= 1`).
    #[must_use]
    pub const fn new(debt_cap: u64) -> Self {
        let cap = if debt_cap == 0 { 1 } else { debt_cap };
        Self {
            bounded_debt: 0,
            debt_cap: cap,
            verified_epoch: 0,
        }
    }

    /// Create an evaluator with [`DEFAULT_LAND_DEBT_CAP`].
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(DEFAULT_LAND_DEBT_CAP)
    }

    /// Last clamped debt total (`<= debt_cap`).
    #[must_use]
    pub const fn bounded_debt(&self) -> u64 {
        self.bounded_debt
    }

    /// Highest verified commit epoch observed so far.
    #[must_use]
    pub const fn verified_epoch(&self) -> u64 {
        self.verified_epoch
    }

    /// Evaluate `snap` and update monotone readiness state.
    pub fn evaluate(&mut self, snap: RepoLandSnapshot, head_sha_short: &str) -> LandVerdict {
        let raw_debt = snap.raw_total_debt();
        self.bounded_debt = land_debt_clamp(raw_debt, self.debt_cap);

        let mut blockers = Vec::new();
        if snap.dirty_tracked_files > 0 {
            blockers.push(LandBlocker::DirtyWorkingTree {
                count: snap.dirty_tracked_files,
            });
        }
        if snap.untracked_files > 0 {
            blockers.push(LandBlocker::UntrackedFiles {
                count: snap.untracked_files,
            });
        }
        if snap.unpushed_commits > 0 {
            blockers.push(LandBlocker::UnpushedCommits {
                count: snap.unpushed_commits,
            });
        }
        if snap.behind_remote_commits > 0 {
            blockers.push(LandBlocker::BehindRemoteMain {
                count: snap.behind_remote_commits,
            });
        }
        if snap.stash_entries > 0 {
            blockers.push(LandBlocker::ParkedStashes {
                count: snap.stash_entries,
            });
        }
        if snap.unmerged_local_branches > 0 {
            blockers.push(LandBlocker::ParkedBranches {
                count: snap.unmerged_local_branches,
            });
        }
        if !snap.verify_passed {
            blockers.push(LandBlocker::VerificationNotPassed);
        }
        if snap.commit_epoch < self.verified_epoch {
            blockers.push(LandBlocker::StaleCommitEpoch {
                observed: snap.commit_epoch,
                required_at_least: self.verified_epoch,
            });
        }

        if land_debt_is_zero(raw_debt) && blockers.is_empty() {
            let next_epoch = land_epoch_advance(self.verified_epoch, snap.commit_epoch);
            self.verified_epoch = next_epoch;
            let sha_label = if head_sha_short.is_empty() {
                "HEAD"
            } else {
                head_sha_short
            };
            let mut defense_line = String::new();
            defense_line.push_str("Nothing left: origin/main aligned at ");
            defense_line.push_str(sha_label);
            defense_line.push_str(" (epoch ");
            push_dec_u64(&mut defense_line, next_epoch);
            defense_line.push_str(
                "), 0 uncommitted/untracked/unpushed/stashed/unmerged items, verification green.",
            );
            LandVerdict::LandedClean {
                verified_epoch: next_epoch,
                defense_line,
            }
        } else {
            LandVerdict::Incomplete {
                bounded_debt: self.bounded_debt,
                blockers,
            }
        }
    }
}

fn push_dec_u64(out: &mut String, mut n: u64) {
    if n == 0 {
        out.push('0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while n > 0 && len < digits.len() {
        let d = (n % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add(d);
        }
        len = len.saturating_add(1);
        n /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&b) = digits.get(len) {
            out.push(b as char);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_any_residual_debt_or_missing_verification_with_exact_blockers() {
        let mut eval = LandReadinessEvaluator::new(10);
        let dirty = RepoLandSnapshot {
            dirty_tracked_files: 3,
            untracked_files: 1,
            unpushed_commits: 2,
            behind_remote_commits: 0,
            stash_entries: 8,
            unmerged_local_branches: 1,
            verify_passed: false,
            commit_epoch: 5,
        };
        let verdict = eval.evaluate(dirty, "6c4174c");
        assert_eq!(
            verdict,
            LandVerdict::Incomplete {
                bounded_debt: 10,
                blockers: vec![
                    LandBlocker::DirtyWorkingTree { count: 3 },
                    LandBlocker::UntrackedFiles { count: 1 },
                    LandBlocker::UnpushedCommits { count: 2 },
                    LandBlocker::ParkedStashes { count: 8 },
                    LandBlocker::ParkedBranches { count: 1 },
                    LandBlocker::VerificationNotPassed,
                ],
            }
        );
        assert_eq!(eval.bounded_debt(), 10);
        assert_eq!(eval.verified_epoch(), 0);
    }

    #[test]
    fn clean_verified_snapshot_advances_epoch_and_blocks_rollback() {
        let mut eval = LandReadinessEvaluator::with_defaults();
        let clean = RepoLandSnapshot {
            dirty_tracked_files: 0,
            untracked_files: 0,
            unpushed_commits: 0,
            behind_remote_commits: 0,
            stash_entries: 0,
            unmerged_local_branches: 0,
            verify_passed: true,
            commit_epoch: 17,
        };
        let ok = eval.evaluate(clean, "6c4174c");
        match ok {
            LandVerdict::LandedClean {
                verified_epoch,
                defense_line,
            } => {
                assert_eq!(verified_epoch, 17);
                assert!(defense_line.starts_with("Nothing left:"));
                assert!(defense_line.contains("6c4174c"));
            }
            LandVerdict::Incomplete { .. } => panic!("expected LandedClean"),
        }
        assert_eq!(eval.bounded_debt(), 0);
        assert_eq!(eval.verified_epoch(), 17);

        let rolled_back = RepoLandSnapshot {
            commit_epoch: 16,
            ..clean
        };
        let stale = eval.evaluate(rolled_back, "5503f3c");
        assert_eq!(
            stale,
            LandVerdict::Incomplete {
                bounded_debt: 0,
                blockers: vec![LandBlocker::StaleCommitEpoch {
                    observed: 16,
                    required_at_least: 17,
                }],
            }
        );
    }
}
