// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Autopilot Land` clean-tree & remote-main completion fence (`Astream.Agent.TlaLandCleanTreeFence`).
//!
//! Enforces `aterm`'s `autopilot=land` rule: a worker session ends ONLY when
//! `git` finds zero uncommitted files, zero unpushed commits, zero unmerged local
//! branches, zero stashes, HEAD is on `main`, AND the final report starts with
//! `"Nothing left:"` in a concise multi-line defense (`1..=MAX_DEFENSE_LINES`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "land_clean_tree_fence_island.rs"]
mod land_clean_tree_fence_island;
#[cfg(clean_islands)]
pub use land_clean_tree_fence_island::{land_audit_epoch_advance, land_residuals_clamp};

/// Required opening prefix for a terminal `Autopilot Land` defense reply.
pub const NOTHING_LEFT_PREFIX: &[u8] = b"Nothing left:";

/// Upper bound on tracked residual items across `git` status checks.
pub const MAX_TRACKED_RESIDUALS: u64 = 10_000;

/// Maximum concise lines permitted in a terminal `Nothing left:` defense.
pub const MAX_DEFENSE_LINES: usize = 8;

#[cfg(not(clean_islands))]
/// Monotonically advance the `Autopilot Land` audit epoch.
#[must_use]
pub const fn land_audit_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp total residual git items (`dirty + unpushed + unmerged + stashes`) to `max_residuals`.
#[must_use]
pub const fn land_residuals_clamp(cand_residuals: u64, max_residuals: u64) -> u64 {
    if cand_residuals < max_residuals {
        cand_residuals
    } else {
        max_residuals
    }
}

contract_fn! {
    /// True iff `residuals == zero_floor` (`0`).
    #[must_use]
    pub const fn land_zero_residuals(residuals: u64, zero_floor: u64) -> bool
    clauses [ensures result == (residuals == zero_floor)]
    {
        residuals == zero_floor
    }
}

/// Snapshot of `git` cleanliness in the worker session's folder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GitLandAudit {
    pub dirty_paths: u64,
    pub unpushed_commits: u64,
    pub unmerged_branches: u64,
    pub stash_entries: u64,
    pub on_remote_main: bool,
}

impl GitLandAudit {
    #[must_use]
    pub const fn total_residuals(self) -> u64 {
        let r = self
            .dirty_paths
            .saturating_add(self.unpushed_commits)
            .saturating_add(self.unmerged_branches)
            .saturating_add(self.stash_entries);
        if self.on_remote_main {
            r
        } else {
            r.saturating_add(1)
        }
    }
}

/// Verdict of evaluating a turn end under `autopilot=land`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LandTurnVerdict {
    /// All work is on remote `main` and defended by `Nothing left:`; stop typing.
    ParkComplete { audit_epoch: u64 },
    /// Work remains in `git` (`residuals > 0`); continue prompting the worker.
    ContinueGitResiduals { audit_epoch: u64, residuals: u64 },
    /// `git` is clean, but reply lacked a concise `Nothing left:` defense; prompt for defense.
    ContinueNeedsDefense { audit_epoch: u64 },
}

#[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
fn has_valid_nothing_left_defense(reply: &[u8]) -> bool {
    // Trim leading ASCII whitespace
    let mut trimmed = reply;
    while let &[b, ref tail @ ..] = trimmed {
        if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
            trimmed = tail;
        } else {
            break;
        }
    }
    if !trimmed.starts_with(NOTHING_LEFT_PREFIX) {
        return false;
    }
    let after = match trimmed.get(NOTHING_LEFT_PREFIX.len()..) {
        Some(s) => s,
        None => &[],
    };
    // Require non-empty explanation after "Nothing left:"
    let mut non_space = false;
    let mut lines = 1usize;
    let mut scan = after;
    while let &[b, ref tail @ ..] = scan {
        if b == b'\n' {
            if !tail.is_empty() {
                lines = lines.saturating_add(1);
            }
        } else if b != b' ' && b != b'\t' && b != b'\r' {
            non_space = true;
        }
        scan = tail;
    }
    non_space && lines <= MAX_DEFENSE_LINES
}

/// Stateful `Autopilot Land` turn-end completion fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LandCleanTreeFence {
    audit_epoch: u64,
    last_residuals: u64,
}

impl Default for LandCleanTreeFence {
    fn default() -> Self {
        Self::new()
    }
}

impl LandCleanTreeFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            audit_epoch: 0,
            last_residuals: 0,
        }
    }

    #[must_use]
    pub const fn audit_epoch(&self) -> u64 {
        self.audit_epoch
    }

    #[must_use]
    pub const fn last_residuals(&self) -> u64 {
        self.last_residuals
    }

    /// Evaluate a worker turn end against `git` reality and the reply text.
    pub fn evaluate_turn_end(&mut self, git: GitLandAudit, reply: &[u8]) -> LandTurnVerdict {
        let cand_ep = self.audit_epoch.saturating_add(1);
        self.audit_epoch = land_audit_epoch_advance(self.audit_epoch, cand_ep);
        let clamped_res = land_residuals_clamp(git.total_residuals(), MAX_TRACKED_RESIDUALS);
        self.last_residuals = clamped_res;

        if !land_zero_residuals(clamped_res, 0) {
            return LandTurnVerdict::ContinueGitResiduals {
                audit_epoch: self.audit_epoch,
                residuals: clamped_res,
            };
        }
        if !has_valid_nothing_left_defense(reply) {
            return LandTurnVerdict::ContinueNeedsDefense {
                audit_epoch: self.audit_epoch,
            };
        }
        LandTurnVerdict::ParkComplete {
            audit_epoch: self.audit_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_false_nothing_left_when_git_has_unpushed_or_stash() {
        let mut fence = LandCleanTreeFence::new();
        let dirty = GitLandAudit {
            dirty_paths: 0,
            unpushed_commits: 1,
            unmerged_branches: 0,
            stash_entries: 1,
            on_remote_main: true,
        };
        assert_eq!(
            fence.evaluate_turn_end(dirty, b"Nothing left: everything pushed to origin/main."),
            LandTurnVerdict::ContinueGitResiduals {
                audit_epoch: 1,
                residuals: 2,
            }
        );

        let clean = GitLandAudit {
            dirty_paths: 0,
            unpushed_commits: 0,
            unmerged_branches: 0,
            stash_entries: 0,
            on_remote_main: true,
        };
        assert_eq!(
            fence.evaluate_turn_end(clean, b"All done!"),
            LandTurnVerdict::ContinueNeedsDefense { audit_epoch: 2 }
        );
        assert_eq!(
            fence.evaluate_turn_end(
                clean,
                b"Nothing left: HEAD matches origin/main, git status/stash/branch all empty.\nVerified make ci exit 0."
            ),
            LandTurnVerdict::ParkComplete { audit_epoch: 3 }
        );
    }
}
