// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Autopilot Land` 10-minute direct-person-reply yield gate
//! (`Astream.Agent.TlaLandHumanTurnYield`).
//!
//! Enforces `aterm`'s `autopilot=land` conversational ownership rule:
//! *"Under `land`, a reply to a person's own question or message, outside a job
//! the harness is continuing (answered within 10 minutes), is theirs: nothing
//! is typed after it."*

#[cfg(clean_islands)]
#[path = "land_human_turn_yield_island.rs"]
mod land_human_turn_yield_island;
#[cfg(clean_islands)]
pub use land_human_turn_yield_island::{human_elapsed_clamp, human_yield_epoch_advance};

/// Exact 10-minute conversational reply window (`600_000 ms`).
pub const DEFAULT_HUMAN_REPLY_WINDOW_MS: u64 = 10 * 60 * 1_000;

#[cfg(not(clean_islands))]
/// Monotonically advance the human-turn yield evaluation epoch.
#[must_use]
pub const fn human_yield_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp observed reply latency within `window_ms`.
#[must_use]
pub const fn human_elapsed_clamp(cand_elapsed_ms: u64, window_ms: u64) -> u64 {
    if cand_elapsed_ms < window_ms {
        cand_elapsed_ms
    } else {
        window_ms
    }
}

contract_fn! {
    /// True iff `elapsed_ms <= window_ms` (`<= 10 minutes`).
    #[must_use]
    pub const fn reply_within_human_window(elapsed_ms: u64, window_ms: u64) -> bool
    clauses [ensures result == (elapsed_ms <= window_ms)]
    {
        elapsed_ms <= window_ms
    }
}

/// Who initiated the turn that just completed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnInitiator {
    PersonDirect { sent_at_ms: u64 },
    HarnessContinuation,
}

/// Ownership decision at turn end under `autopilot=land`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LandOwnership {
    /// Direct reply to the person within 10 minutes outside an active harness job -> type nothing!
    PersonOwnsTurn { yield_epoch: u64 },
    /// Long-running (>10 min) or harness-continued job -> Autopilot Land continues!
    HarnessContinuesJob { yield_epoch: u64 },
}

/// Stateful `autopilot=land` human-reply yield tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LandHumanTurnYield {
    window_ms: u64,
    harness_job_active: bool,
    yield_epoch: u64,
    last_clamped_elapsed_ms: u64,
}

impl Default for LandHumanTurnYield {
    fn default() -> Self {
        Self::new(DEFAULT_HUMAN_REPLY_WINDOW_MS)
    }
}

impl LandHumanTurnYield {
    #[must_use]
    pub const fn new(window_ms: u64) -> Self {
        let win = if window_ms == 0 {
            DEFAULT_HUMAN_REPLY_WINDOW_MS
        } else {
            window_ms
        };
        Self {
            window_ms: win,
            harness_job_active: false,
            yield_epoch: 0,
            last_clamped_elapsed_ms: 0,
        }
    }

    #[must_use]
    pub const fn yield_epoch(&self) -> u64 {
        self.yield_epoch
    }

    #[must_use]
    pub const fn is_harness_job_active(&self) -> bool {
        self.harness_job_active
    }

    pub fn set_harness_job_active(&mut self, active: bool) {
        self.harness_job_active = active;
    }

    /// Decide whether Autopilot Land must stay silent after a reply finishes at `reply_at_ms`.
    pub fn evaluate_turn_end(
        &mut self,
        initiator: TurnInitiator,
        reply_at_ms: u64,
    ) -> LandOwnership {
        let cand_ep = self.yield_epoch.saturating_add(1);
        self.yield_epoch = human_yield_epoch_advance(self.yield_epoch, cand_ep);

        match initiator {
            TurnInitiator::HarnessContinuation => {
                self.harness_job_active = true;
                LandOwnership::HarnessContinuesJob {
                    yield_epoch: self.yield_epoch,
                }
            }
            TurnInitiator::PersonDirect { sent_at_ms } => {
                let elapsed = reply_at_ms.saturating_sub(sent_at_ms);
                self.last_clamped_elapsed_ms = human_elapsed_clamp(elapsed, self.window_ms);
                if !self.harness_job_active && reply_within_human_window(elapsed, self.window_ms) {
                    LandOwnership::PersonOwnsTurn {
                        yield_epoch: self.yield_epoch,
                    }
                } else {
                    self.harness_job_active = true;
                    LandOwnership::HarnessContinuesJob {
                        yield_epoch: self.yield_epoch,
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yields_quick_direct_person_replies_and_continues_long_or_harness_jobs() {
        let mut gate = LandHumanTurnYield::default();

        // Person asks a quick question answered in 45s outside a job -> theirs, type nothing!
        assert_eq!(
            gate.evaluate_turn_end(TurnInitiator::PersonDirect { sent_at_ms: 1_000 }, 46_000),
            LandOwnership::PersonOwnsTurn { yield_epoch: 1 }
        );
        assert!(!gate.is_harness_job_active());

        // Person launches a 15-minute job (900_000 ms > 600_000 ms) -> harness carries it to land!
        assert_eq!(
            gate.evaluate_turn_end(
                TurnInitiator::PersonDirect {
                    sent_at_ms: 100_000,
                },
                1_000_001,
            ),
            LandOwnership::HarnessContinuesJob { yield_epoch: 2 }
        );
        assert!(gate.is_harness_job_active());
    }
}
