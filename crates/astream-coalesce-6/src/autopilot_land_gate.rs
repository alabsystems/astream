// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` `Autopilot=Land` completion verifier (`Astream.Agent.TlaAutopilotLandGate`).
//!
//! Enforces the `aterm` `land` autopilot invariant:
//! under `land`, the harness continues every turn end until 100% of the session's work is
//! on the remote `main` branch (zero uncommitted files, zero untracked files, zero stashes,
//! zero unpushed commits, zero unmerged local branches, and HEAD on `main`) AND the agent's
//! reply defends that in a few concise lines starting with `Nothing left:`.

#![allow(
    clippy::absurd_extreme_comparisons,
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
#[path = "autopilot_land_gate_island.rs"]
mod autopilot_land_gate_island;
#[cfg(clean_islands)]
pub use autopilot_land_gate_island::{land_nonzero_bit, land_turn_clamp, land_zero_gate_select};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn land_turn_clamp(turns: u64, max_turns: u64) -> u64 {
    if turns < max_turns {
        turns
    } else {
        max_turns
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn land_nonzero_bit(val: u64) -> u64 {
    if val < 1 {
        0
    } else {
        1
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn land_zero_gate_select(unlanded_items: u64, when_clean: u64) -> u64 {
    if unlanded_items < 1 {
        when_clean
    } else {
        0
    }
}

/// Park flag composed over Clean-origin [`land_zero_gate_select`] and [`land_nonzero_bit`]:
/// returns `1` iff `unlanded_items == 0` and `defense_valid > 0`.
#[must_use]
pub const fn land_park_flag(unlanded_items: u64, defense_valid: u64) -> u64 {
    land_zero_gate_select(unlanded_items, land_nonzero_bit(defense_valid))
}

/// Check that git dirty, unpushed, and unmerged counts are all zero.
#[must_use]
pub const fn land_git_is_clean(dirty: u64, unpushed: u64, unmerged: u64) -> bool {
    let sum = dirty.saturating_add(unpushed).saturating_add(unmerged);
    land_unlanded_is_zero(sum)
}

contract_fn! {
    /// Verified check that total unlanded repository obligations equal zero (`unlanded <= 0`),
    /// linked via `clean-kernel-defeq` to `land_unlanded_is_zero_isl`.
    #[must_use]
    pub const fn land_unlanded_is_zero(unlanded: u64) -> bool
    clauses [ensures result == (unlanded <= 0)]
    {
        unlanded <= 0
    }
}

/// Snapshot of `git` repository state in the session's working folder at turn end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GitLandSnapshot {
    /// Whether `HEAD` is attached to `main` (or `master` when configured as primary).
    pub on_main_branch: bool,
    /// Modified or staged tracked files (`git status --porcelain`).
    pub dirty_tracked_files: u64,
    /// Untracked non-ignored files (`??` in `git status --porcelain`).
    pub untracked_files: u64,
    /// Commits ahead of `origin/main` (`git rev-list --count origin/main..HEAD`).
    pub unpushed_commits: u64,
    /// Local feature/parked branches not yet merged into `origin/main`.
    pub unmerged_branches: u64,
    /// Entries in `git stash list`.
    pub stash_entries: u64,
}

impl GitLandSnapshot {
    /// Total count of unlanded repository obligations (`0` iff 100% landed on `origin/main`).
    #[must_use]
    pub const fn unlanded_item_count(&self) -> u64 {
        let off_main = if self.on_main_branch { 0u64 } else { 1u64 };
        off_main
            .saturating_add(self.dirty_tracked_files)
            .saturating_add(self.untracked_files)
            .saturating_add(self.unpushed_commits)
            .saturating_add(self.unmerged_branches)
            .saturating_add(self.stash_entries)
    }

    /// True iff `on_main_branch` holds and every git obligation counter is zero.
    #[must_use]
    pub const fn is_fully_landed(&self) -> bool {
        let dirty_all = self
            .dirty_tracked_files
            .saturating_add(self.untracked_files)
            .saturating_add(self.stash_entries);
        self.on_main_branch
            && land_git_is_clean(dirty_all, self.unpushed_commits, self.unmerged_branches)
    }
}

/// Decision emitted by [`AutopilotLandGate::evaluate_turn_end`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LandTurnDecision {
    /// All work is on `origin/main` and the reply validly starts with `Nothing left:`;
    /// stop typing until a person's turn.
    ParkSessionDone,
    /// Work remains unlanded or the closing defense is missing/bloated; continue driving.
    ContinueLanding {
        /// Number of unlanded git obligations detected.
        unlanded_items: u64,
        /// Clamped continuation index (`<= max_turns`).
        continuation_turn: u64,
        /// Specific reason why parking was refused.
        reason: &'static str,
    },
}

/// Stateful `Autopilot=Land` turn-end gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutopilotLandGate {
    max_defense_lines: usize,
    max_turns: u64,
    continuations: u64,
    parked: bool,
}

impl AutopilotLandGate {
    /// Create a new `Autopilot=Land` gate allowing up to `max_defense_lines` non-empty lines
    /// in a `Nothing left:` defense (clamped to `1..=16`) and tracking up to `max_turns`.
    #[must_use]
    pub const fn new(max_defense_lines: usize, max_turns: u64) -> Self {
        let lines = if max_defense_lines < 1 {
            1
        } else if max_defense_lines > 16 {
            16
        } else {
            max_defense_lines
        };
        Self {
            max_defense_lines: lines,
            max_turns,
            continuations: 0,
            parked: false,
        }
    }

    /// Whether the session has cleanly parked on a verified `Nothing left:` reply.
    #[must_use]
    pub const fn is_parked(&self) -> bool {
        self.parked
    }

    /// Clamped continuation count (`<= max_turns`).
    #[must_use]
    pub const fn continuations(&self) -> u64 {
        self.continuations
    }

    /// Validate that `reply` starts (after trimming leading blank lines) with `"Nothing left:"`
    /// and spans `1..=self.max_defense_lines` non-empty lines without deferral markers.
    #[must_use]
    pub fn is_valid_nothing_left_defense(&self, reply: &str) -> bool {
        let trimmed = reply.trim();
        if !trimmed.starts_with("Nothing left:") {
            return false;
        }
        let body_after_prefix = trimmed.trim_start_matches("Nothing left:").trim();
        if body_after_prefix.is_empty() {
            return false;
        }
        let mut non_empty_lines = 0usize;
        for line in trimmed.split('\n') {
            let l = line.trim();
            if !l.is_empty() {
                non_empty_lines = non_empty_lines.saturating_add(1);
                if l.starts_with("NEEDS YOU:") {
                    return false;
                }
            }
        }
        non_empty_lines >= 1 && non_empty_lines <= self.max_defense_lines
    }

    /// Evaluate a turn-end `(reply, git_snapshot)` pair under `Autopilot=Land`.
    pub fn evaluate_turn_end(&mut self, reply: &str, git: &GitLandSnapshot) -> LandTurnDecision {
        let unlanded = git.unlanded_item_count();
        let defense_ok = self.is_valid_nothing_left_defense(reply);
        let park_flag = land_park_flag(unlanded, if defense_ok { 1 } else { 0 });
        if park_flag == 1 && git.is_fully_landed() {
            self.parked = true;
            LandTurnDecision::ParkSessionDone
        } else {
            self.parked = false;
            let raw_next = self.continuations.saturating_add(1);
            self.continuations = land_turn_clamp(raw_next, self.max_turns);
            let reason = if !git.on_main_branch {
                "HEAD is not on main branch"
            } else if git.dirty_tracked_files > 0 || git.untracked_files > 0 {
                "working tree has uncommitted or untracked files"
            } else if git.unpushed_commits > 0 {
                "local commits are not yet pushed to origin/main"
            } else if git.unmerged_branches > 0 || git.stash_entries > 0 {
                "parked local branch or git stash remains unmerged"
            } else {
                "reply does not defend completion in concise lines starting with 'Nothing left:'"
            };
            LandTurnDecision::ContinueLanding {
                unlanded_items: unlanded,
                continuation_turn: self.continuations,
                reason,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_parking_until_git_is_100_percent_clean_on_origin_main_with_concise_defense() {
        let mut gate = AutopilotLandGate::new(6, 100);
        let clean_git = GitLandSnapshot {
            on_main_branch: true,
            dirty_tracked_files: 0,
            untracked_files: 0,
            unpushed_commits: 0,
            unmerged_branches: 0,
            stash_entries: 0,
        };

        // 1. Agent claims "Nothing left:" while 1 commit is still unpushed -> MUST continue!
        let mut unpushed = clean_git;
        unpushed.unpushed_commits = 1;
        assert_eq!(
            gate.evaluate_turn_end("Nothing left: everything tested and committed.", &unpushed,),
            LandTurnDecision::ContinueLanding {
                unlanded_items: 1,
                continuation_turn: 1,
                reason: "local commits are not yet pushed to origin/main",
            }
        );
        assert!(!gate.is_parked());

        // 2. Git is clean, but reply does not start with "Nothing left:" -> MUST continue!
        assert!(matches!(
            gate.evaluate_turn_end("All done! Pushed to main.", &clean_git),
            LandTurnDecision::ContinueLanding {
                unlanded_items: 0,
                continuation_turn: 2,
                ..
            }
        ));
        assert!(!gate.is_parked());

        // 3. Git is clean AND concise `Nothing left:` defense -> parks cleanly!
        assert_eq!(
            gate.evaluate_turn_end(
                "Nothing left: pushed 6c4174c to origin/main; git status/branch/stash empty; make ci passed.",
                &clean_git,
            ),
            LandTurnDecision::ParkSessionDone
        );
        assert!(gate.is_parked());
    }
}
