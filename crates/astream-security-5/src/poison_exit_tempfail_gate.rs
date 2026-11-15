// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Poisoned-log `EX_TEMPFAIL` (`75`) exit & bridge `outcome unknown` vs `reason=poisoned` classifier
//! (`docs/DESIGN-aterm-fabric.md` §3 lines 413–456; `Astream.Broker.TlaPoisonExitTempfailGate`).
//!
//! Models the exact two-sided poison protocol between `astream-broker` and `aterm-link`:
//! - On Ordered full-flush failure over uncovered acks, the triggering op returns
//!   [`BridgePoisonView::OutcomeUnknownHoldPinned`] (`fabric=connected`, holds post at pinned `seq`),
//! - Subsequent writes arriving inside the `<= 2_000ms` health poll return
//!   [`BridgePoisonView::StalledPoisonedDrop`] (`fabric=stalled reason=poisoned`, drops socket),
//! - Every `POISON_HEALTH_POLL_MS` (`2_000ms`), unless `stay_seam` (`ATERM_LINK_BROKER_FAULT=stay`)
//!   is armed for negative-control testing, the serving loop drops listeners and exits `75`
//!   (`EX_TEMPFAIL`) so `launchd` / `systemd` reopens the Lossy log at `generation + 1`.

#[cfg(clean_islands)]
#[path = "poison_exit_tempfail_gate_island.rs"]
mod poison_exit_tempfail_gate_island;
#[cfg(clean_islands)]
pub use poison_exit_tempfail_gate_island::{
    poison_gen_advance_b130, poison_poll_elapsed_clamp_b130,
};

/// POSIX `<sysexits.h>` `EX_TEMPFAIL` exit status (`75`) signaling supervisor reopen.
pub const EX_TEMPFAIL_STATUS: u8 = 75;

/// Default serving-loop poison poll cadence (`2_000ms`).
pub const POISON_HEALTH_POLL_MS: u64 = 2_000;

#[cfg(not(clean_islands))]
/// Clamp elapsed poll interval to `poll_budget_ms`.
#[must_use]
pub const fn poison_poll_elapsed_clamp_b130(cand_elapsed_ms: u64, poll_budget_ms: u64) -> u64 {
    if cand_elapsed_ms < poll_budget_ms {
        cand_elapsed_ms
    } else {
        poll_budget_ms
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance reopened log generation after Lossy poison exit.
#[must_use]
pub const fn poison_gen_advance_b130(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// True iff the log is poisoned and the `stay` negative-control seam is off.
    #[must_use]
    pub const fn poison_should_exit_75_b130(is_poisoned: bool, stay_seam: bool) -> bool
    clauses [ensures result == (is_poisoned && !stay_seam)]
    {
        is_poisoned && !stay_seam
    }
}

/// Bridge-side classification of a write reply during or after a poison transition.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BridgePoisonView {
    /// Healthy write committed normally.
    Committed,
    /// Triggering op whose own full flush failed (`outcome unknown`): keep `fabric=connected` and hold pinned `seq`.
    OutcomeUnknownHoldPinned { pinned_seq: u64 },
    /// Subsequent write hitting `BrokerRefusal::is_poisoned` before exit: set `fabric=stalled reason=poisoned` and drop link.
    StalledPoisonedDrop,
}

/// Serving-loop poll verdict.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PoisonPollAction {
    /// Keep serving normally (or under `stay` dev seam).
    KeepServing,
    /// Drop listeners and exit `75` (`EX_TEMPFAIL`) so supervisor reopens at `next_gen`.
    ExitTempfail {
        status: u8,
        expected_reopen_gen: u64,
    },
}

/// Stateful Ordered poison-exit and bridge-classification gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PoisonExitTempfailGate {
    poisoned: bool,
    stay_seam: bool,
    poll_budget_ms: u64,
    last_poll_elapsed_ms: u64,
    cur_generation: u64,
}

impl PoisonExitTempfailGate {
    #[must_use]
    pub const fn new(initial_generation: u64, stay_seam: bool) -> Self {
        Self {
            poisoned: false,
            stay_seam,
            poll_budget_ms: POISON_HEALTH_POLL_MS,
            last_poll_elapsed_ms: 0,
            cur_generation: initial_generation,
        }
    }

    #[must_use]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    #[must_use]
    pub const fn cur_generation(&self) -> u64 {
        self.cur_generation
    }

    /// Observe an Ordered full-flush outcome on `pinned_seq`.
    pub fn on_write_attempt(
        &mut self,
        pinned_seq: u64,
        full_flush_failed: bool,
    ) -> BridgePoisonView {
        if self.poisoned {
            return BridgePoisonView::StalledPoisonedDrop;
        }
        if full_flush_failed {
            self.poisoned = true;
            return BridgePoisonView::OutcomeUnknownHoldPinned { pinned_seq };
        }
        BridgePoisonView::Committed
    }

    /// Run one `broker_health::POLL` check; if exiting 75, advances expected reopen generation by 1.
    pub fn poll_health(&mut self, elapsed_ms: u64) -> PoisonPollAction {
        self.last_poll_elapsed_ms = poison_poll_elapsed_clamp_b130(elapsed_ms, self.poll_budget_ms);
        if poison_should_exit_75_b130(self.poisoned, self.stay_seam) {
            let cand_gen = self.cur_generation.saturating_add(1);
            let next_gen = poison_gen_advance_b130(self.cur_generation, cand_gen);
            self.cur_generation = next_gen;
            self.poisoned = false;
            PoisonPollAction::ExitTempfail {
                status: EX_TEMPFAIL_STATUS,
                expected_reopen_gen: next_gen,
            }
        } else {
            PoisonPollAction::KeepServing
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn triggering_flush_holds_pinned_next_write_stalls_and_poll_exits_75_unless_stay() {
        let mut gate = PoisonExitTempfailGate::new(4, false);
        assert_eq!(
            gate.on_write_attempt(10, false),
            BridgePoisonView::Committed
        );
        assert_eq!(
            gate.on_write_attempt(11, true),
            BridgePoisonView::OutcomeUnknownHoldPinned { pinned_seq: 11 }
        );
        assert_eq!(
            gate.on_write_attempt(12, false),
            BridgePoisonView::StalledPoisonedDrop
        );
        assert_eq!(
            gate.poll_health(2_000),
            PoisonPollAction::ExitTempfail {
                status: EX_TEMPFAIL_STATUS,
                expected_reopen_gen: 5,
            }
        );
        // Resend of pinned seq 11 on reopened generation 5 now commits!
        assert_eq!(
            gate.on_write_attempt(11, false),
            BridgePoisonView::Committed
        );

        // Negative control: `stay_seam = true` keeps serving and stays poisoned.
        let mut stay = PoisonExitTempfailGate::new(1, true);
        let _ = stay.on_write_attempt(1, true);
        assert_eq!(stay.poll_health(2_000), PoisonPollAction::KeepServing);
        assert_eq!(
            stay.on_write_attempt(2, false),
            BridgePoisonView::StalledPoisonedDrop
        );
    }
}
