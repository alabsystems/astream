// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Critic item B08 held-inbox-commit piggyback & `IDLE_ACK_GRACE` (`5ms`) burst coalescer, and
//! critic item C13's session-log mirror burst (`docs/DESIGN-aterm-fabric.md` §2.1, "The
//! bridge's loop reads its acks without parking"; `Astream.Broker.TlaB08HeldCommitPiggyback`).
//!
//! An independent sketch of the invariants of aterm's `Bridge::hold_inbox_commit`,
//! `Bridge::take_commit_for_the_mirror` and `Link::send_burst` (one `Client::send_pipelined`
//! write, the commit first). Like every crate of agy's verification cohort, nothing binds it to
//! aterm's code: aterm runs none of it, and no aterm test checks the bridge against it. It has
//! no fence input either, so it does not state the D06 pass that sends the commit ahead of the
//! mirror pin's fence. What it sketches:
//! - A due inbox group commit is clamped strictly to `<= session_owed_floor` (a record still
//!   owed to a session is never committed past),
//! - If a commit stopped by a session-owed record leaves nothing new above `flushed_commit`,
//!   nothing is held (`NoCommitDue`) so the bridge loop parks its full wait,
//! - Otherwise the commit is held up to `IDLE_ACK_GRACE_MS` (`5ms`) so the session's push-lane
//!   reply carries `(Commit, Publish)` in one pipelined write behind one broker flush,
//! - An off-bus item or `elapsed_ms >= IDLE_ACK_GRACE_MS` flushes the held commit alone first,
//! - The mirror's burst of `N` slots carries the held commit, or, with no inbox record queued,
//!   the commit that is due and not yet held (the one the round's settle would hold), ahead of
//!   its slots in the same write: `(Commit, Publish × N)`. With an inbox record queued and no
//!   commit held, the commit waits for that record's delivery and the slots go alone. After a
//!   burst with no inbox record queued, no commit is due.

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
#[path = "b08_held_commit_piggyback_island.rs"]
mod b08_held_commit_piggyback_island;
#[cfg(clean_islands)]
pub use b08_held_commit_piggyback_island::{
    b08_commit_clamp_below_owed_b130, b08_flushed_commit_advance_b130,
};

/// Maximum grace window (`5ms`) a round holds an uncarried inbox commit (`IDLE_ACK_GRACE`).
pub const IDLE_ACK_GRACE_MS: u64 = 5;

#[cfg(not(clean_islands))]
/// Clamp candidate group commit cursor to `owed_floor` (never commit past a record still owed to a session).
#[must_use]
pub const fn b08_commit_clamp_below_owed_b130(cand_commit: u64, owed_floor: u64) -> u64 {
    if cand_commit < owed_floor {
        cand_commit
    } else {
        owed_floor
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance flushed inbox group commit cursor.
#[must_use]
pub const fn b08_flushed_commit_advance_b130(cur_flushed: u64, cand_flushed: u64) -> u64 {
    if cur_flushed < cand_flushed {
        cand_flushed
    } else {
        cur_flushed
    }
}

contract_fn! {
    /// True iff `held_elapsed_ms >= grace_ms`.
    #[must_use]
    pub const fn b08_grace_expired_b130(held_elapsed_ms: u64, grace_ms: u64) -> bool
    clauses [ensures result == (held_elapsed_ms >= grace_ms)]
    {
        held_elapsed_ms >= grace_ms
    }
}

/// Wire burst emitted by the B08 held-commit scheduler.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum B08Emission {
    /// Nothing due (or still within grace awaiting push-lane reply).
    Park,
    /// Send standalone `Commit(cursor)` before handling an off-bus item or on grace expiry.
    SendStandaloneCommit { commit_upto: u64 },
    /// Send `(Commit(cursor), Publish)` together in one `Client::send_pipelined` write!
    SendPipelinedCommitAndPublish { commit_upto: u64, publish_seq: u64 },
    /// No held commit due: send `Publish` alone.
    SendPublishAlone { publish_seq: u64 },
    /// The session-log mirror's burst: `(Commit(cursor), Publish × slots)` in one
    /// `Client::send_pipelined` write (aterm `Link::send_burst`), the commit first, or the
    /// `slots` publishes from `first_seq` alone when `commit_upto` is `None`.
    SendPipelinedBurst {
        commit_upto: Option<u64>,
        first_seq: u64,
        slots: u64,
    },
}

/// Stateful B08 held-inbox-commit coalescer.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct B08HeldCommitPiggyback {
    flushed_commit: u64,
    held_commit: Option<(u64, u64)>, // (commit_upto, held_at_ms)
    grace_ms: u64,
}

impl Default for B08HeldCommitPiggyback {
    fn default() -> Self {
        Self::new()
    }
}

impl B08HeldCommitPiggyback {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            flushed_commit: 0,
            held_commit: None,
            grace_ms: IDLE_ACK_GRACE_MS,
        }
    }

    #[must_use]
    pub const fn flushed_commit(&self) -> u64 {
        self.flushed_commit
    }

    #[must_use]
    pub const fn has_held_commit(&self) -> bool {
        self.held_commit.is_some()
    }

    /// Hold a candidate inbox commit `cand_upto` clamped by `session_owed_floor` (`u64::MAX` if none owed).
    pub fn hold_round_commit(
        &mut self,
        cand_upto: u64,
        session_owed_floor: u64,
        now_ms: u64,
    ) -> bool {
        let clamped = b08_commit_clamp_below_owed_b130(cand_upto, session_owed_floor);
        if clamped <= self.flushed_commit {
            return false;
        }
        let held_since = match self.held_commit {
            Some((_, t0)) => t0,
            None => now_ms,
        };
        self.held_commit = Some((clamped, held_since));
        true
    }

    /// Carry any held commit ahead of a push-lane `Publish(publish_seq)` in one pipelined write.
    pub fn on_push_publish(&mut self, publish_seq: u64) -> B08Emission {
        match core::mem::take(&mut self.held_commit) {
            Some((commit_upto, _)) => {
                self.flushed_commit =
                    b08_flushed_commit_advance_b130(self.flushed_commit, commit_upto);
                B08Emission::SendPipelinedCommitAndPublish {
                    commit_upto,
                    publish_seq,
                }
            }
            None => B08Emission::SendPublishAlone { publish_seq },
        }
    }

    /// Whether a commit is due: `cand_upto` clamped by `session_owed_floor` lies above what is
    /// flushed, so a round's settle would hold it ([`Self::hold_round_commit`]).
    #[must_use]
    pub const fn commit_due(&self, cand_upto: u64, session_owed_floor: u64) -> bool {
        b08_commit_clamp_below_owed_b130(cand_upto, session_owed_floor) > self.flushed_commit
    }

    /// The session-log mirror's burst of `slots` publishes from `first_seq` (critic item C13,
    /// aterm `Bridge::take_commit_for_the_mirror` and `Link::send_burst`): it carries the held
    /// commit (at the latest offset due, as aterm's `Bridge::take_held_commit` takes it), or,
    /// with no inbox record queued, the commit that is due and not yet held, the one the
    /// round's settle would hold for the loop's next write ([`Self::commit_due`]), ahead of its
    /// slots in one pipelined write. With an inbox record queued and nothing held, the commit
    /// waits for that record's delivery and the slots go alone.
    pub fn on_mirror_burst(
        &mut self,
        cand_upto: u64,
        session_owed_floor: u64,
        inbox_queued: bool,
        first_seq: u64,
        slots: u64,
    ) -> B08Emission {
        let commit_upto = match core::mem::take(&mut self.held_commit) {
            // The held commit rides at the latest offset due: a delivery since the hold moved it.
            Some((held, _)) => Some(b08_flushed_commit_advance_b130(
                held,
                b08_commit_clamp_below_owed_b130(cand_upto, session_owed_floor),
            )),
            None if !inbox_queued && self.commit_due(cand_upto, session_owed_floor) => Some(
                b08_commit_clamp_below_owed_b130(cand_upto, session_owed_floor),
            ),
            None => None,
        };
        if let Some(upto) = commit_upto {
            self.flushed_commit = b08_flushed_commit_advance_b130(self.flushed_commit, upto);
        }
        B08Emission::SendPipelinedBurst {
            commit_upto,
            first_seq,
            slots,
        }
    }

    /// Flush held commit standalone if an off-bus item arrives or `IDLE_ACK_GRACE_MS` has elapsed.
    pub fn poll_or_flush_before_off_bus(&mut self, now_ms: u64, off_bus_item: bool) -> B08Emission {
        let Some((commit_upto, held_since)) = self.held_commit else {
            return B08Emission::Park;
        };
        let elapsed = now_ms.saturating_sub(held_since);
        if off_bus_item || b08_grace_expired_b130(elapsed, self.grace_ms) {
            self.held_commit = None;
            self.flushed_commit = b08_flushed_commit_advance_b130(self.flushed_commit, commit_upto);
            B08Emission::SendStandaloneCommit { commit_upto }
        } else {
            B08Emission::Park
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rides_reply_clamps_below_owed_flushes_off_bus_and_expires_grace() {
        let mut b08 = B08HeldCommitPiggyback::new();
        // Delivery at 10 stopped by session-owed record at 10 -> clamped to 10; if 0 flushed, holds 10!
        // Next delivery at 11 while 10 is still owed -> clamped to 10 == flushed once 10 lands!
        assert!(b08.hold_round_commit(15, 12, 1_000));
        assert_eq!(
            b08.on_push_publish(1),
            B08Emission::SendPipelinedCommitAndPublish {
                commit_upto: 12,
                publish_seq: 1,
            }
        );
        assert_eq!(b08.flushed_commit(), 12);
        // Stopped at 12 when 12 is already flushed -> NOT held!
        assert!(!b08.hold_round_commit(15, 12, 1_002));
        assert!(!b08.has_held_commit());

        // Off-bus item flushes immediately before grace expires.
        assert!(b08.hold_round_commit(15, u64::MAX, 2_000));
        assert_eq!(
            b08.poll_or_flush_before_off_bus(2_002, false),
            B08Emission::Park
        );
        assert_eq!(
            b08.poll_or_flush_before_off_bus(2_002, true),
            B08Emission::SendStandaloneCommit { commit_upto: 15 }
        );

        // Grace expiry at +5ms sends standalone commit.
        assert!(b08.hold_round_commit(20, u64::MAX, 3_000));
        assert_eq!(
            b08.poll_or_flush_before_off_bus(3_005, false),
            B08Emission::SendStandaloneCommit { commit_upto: 20 }
        );
    }

    /// A model whose flushed commit is `flushed` and whose held commit is `held`, built through
    /// its own steps.
    fn model(flushed: u64, held: Option<u64>) -> B08HeldCommitPiggyback {
        let mut b08 = B08HeldCommitPiggyback::new();
        if flushed > 0 {
            assert!(b08.hold_round_commit(flushed, u64::MAX, 0));
            b08.poll_or_flush_before_off_bus(0, true);
        }
        if let Some(h) = held {
            assert!(b08.hold_round_commit(h, u64::MAX, 0));
        }
        assert_eq!(b08.flushed_commit(), flushed);
        b08
    }

    /// The mirror burst's law, of one burst from `before` with the round's candidate `cand`,
    /// its owed floor `owed` and `inbox_queued`: it is one write with the commit first; a held
    /// commit rides; no commit nothing held rides past the owed floor, or ahead of a queued
    /// inbox record's delivery; and with no inbox record queued no commit is due after it.
    fn burst_law(
        before: &B08HeldCommitPiggyback,
        after: &B08HeldCommitPiggyback,
        emitted: B08Emission,
        (cand, owed, inbox_queued): (u64, u64, bool),
    ) -> Result<(), &'static str> {
        let B08Emission::SendPipelinedBurst { commit_upto, .. } = emitted else {
            return Err("the burst is not one pipelined write");
        };
        if before.has_held_commit() && commit_upto.is_none() {
            return Err("a held commit stayed behind");
        }
        if after.has_held_commit() {
            return Err("a commit is still held");
        }
        if !before.has_held_commit() {
            if commit_upto.is_some_and(|c| c > owed) {
                return Err("a commit past a record still owed to a session");
            }
            if inbox_queued && commit_upto.is_some() {
                return Err("a commit ahead of a queued inbox record's delivery");
            }
        }
        if !inbox_queued && after.commit_due(cand, owed) {
            return Err("a due commit left for a write of its own");
        }
        Ok(())
    }

    /// aterm's `Mutant::MirrorRidesOnlyAHeldCommit`: the burst takes the held commit alone.
    fn rides_only_a_held_commit(
        b08: &mut B08HeldCommitPiggyback,
        first_seq: u64,
        slots: u64,
    ) -> B08Emission {
        let commit_upto = match b08.on_push_publish(first_seq) {
            B08Emission::SendPipelinedCommitAndPublish { commit_upto, .. } => Some(commit_upto),
            _ => None,
        };
        B08Emission::SendPipelinedBurst {
            commit_upto,
            first_seq,
            slots,
        }
    }

    /// C13: the mirror's burst carries a held commit, or a due one nothing holds yet, ahead of
    /// its slots, over a grid of flushed and held commits, candidates, owed floors and queued
    /// inbox records. NEGATIVE CONTROL: the burst that rides only a held commit breaks the law
    /// exactly where a commit is due, unheld, with no inbox record queued.
    #[test]
    fn the_mirror_burst_carries_a_due_commit_ahead_of_its_slots() {
        let mut unheld_due = 0;
        for flushed in [0u64, 5] {
            for held in [None, Some(9u64)] {
                for cand in [3u64, 8, 12] {
                    for owed in [u64::MAX, 7, 10] {
                        for inbox_queued in [false, true] {
                            let case = (cand, owed, inbox_queued);
                            let before = model(flushed, held);
                            let mut after = before;
                            let emitted = after.on_mirror_burst(cand, owed, inbox_queued, 40, 3);
                            assert_eq!(
                                burst_law(&before, &after, emitted, case),
                                Ok(()),
                                "{before:?} {case:?} -> {emitted:?}"
                            );
                            let mut mutant = before;
                            let wrong = rides_only_a_held_commit(&mut mutant, 40, 3);
                            let due =
                                held.is_none() && !inbox_queued && before.commit_due(cand, owed);
                            if due {
                                assert!(
                                    burst_law(&before, &mutant, wrong, case).is_err(),
                                    "NEGATIVE CONTROL {before:?} {case:?} -> {wrong:?}"
                                );
                            }
                            unheld_due += usize::from(due);
                        }
                    }
                }
            }
        }
        assert!(unheld_due > 0, "the grid holds a due commit nothing held");
        let mut b08 = model(5, None);
        assert_eq!(
            b08.on_mirror_burst(12, 10, false, 40, 3),
            B08Emission::SendPipelinedBurst {
                commit_upto: Some(10),
                first_seq: 40,
                slots: 3,
            },
            "the due commit, clamped below the owed record, rides first"
        );
        assert_eq!(b08.flushed_commit(), 10);
    }
}
