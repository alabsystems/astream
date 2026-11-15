// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Ordered` / `Relaxed` Broker Escalation Hold-and-Release Planner.
//!
//! Models the `astream-broker` escalation table (`OpenOptions::escalation`):
//! when a record matching an escalated subject filter is appended on an `Ordered` or
//! `Relaxed` log, the broker holds `visible_head` at or below the earliest un-flushed
//! escalated record offset (`held_floor`) and withholds the producer `Ack` until an
//! out-of-lock full fsync advances `durable_head` strictly past that offset
//! (`held_offset < durable_head`).
//!
//! Backed by Clean TLA+ Island `Astream.Broker.TlaEscalationHoldPlanner`
//! (`escalation_table_planner_island.rs`), proving `visibleHead <= heldFloor` and
//! `durableHead <= logHead`.

#[cfg(clean_islands)]
#[path = "escalation_table_planner_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{esc_durable_clamp, esc_visible_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn esc_visible_clamp(proposed_vis: u64, held_floor: u64) -> u64 {
    if proposed_vis < held_floor {
        proposed_vis
    } else {
        held_floor
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn esc_durable_clamp(flushed_upto: u64, log_head: u64) -> u64 {
    if flushed_upto < log_head {
        flushed_upto
    } else {
        log_head
    }
}

contract_fn! {
    /// Kernel-certified check that an escalated record at `held_offset` is covered by
    /// `durable_head` (`held_offset < durable_head`).
    #[must_use]
    #[inline]
    pub const fn esc_hold_satisfied(held_offset: u64, durable_head: u64) -> bool
    clauses [ensures result == (held_offset < durable_head)]
    {
        held_offset < durable_head
    }
}

/// Maximum concurrent escalated batches tracked inline without heap allocation.
pub const MAX_HELD_ESCALATIONS: usize = 32;

/// Held escalated batch waiting on an out-of-lock full flush.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HeldBatchSpan {
    /// First escalated record offset in this batch (blocks `visible_head` from passing it).
    pub first_escalated_offset: u64,
    /// Highest record offset in this batch (`durable_head` must reach `last_offset + 1` to ack).
    pub last_offset: u64,
    pub active: bool,
}

impl HeldBatchSpan {
    const EMPTY: Self = Self {
        first_escalated_offset: 0,
        last_offset: 0,
        active: false,
    };
}

/// Snapshot of heads after an append or full-flush completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EscalationStateSnapshot {
    pub visible_head: u64,
    pub held_floor: u64,
    pub durable_head: u64,
    pub log_head: u64,
    pub released_batches: usize,
}

/// Deterministic escalation hold-and-release state machine certified by `TlaEscalationHoldPlanner`.
#[derive(Debug, Clone)]
pub struct EscalationHoldPlanner {
    visible_head: u64,
    held_floor: u64,
    durable_head: u64,
    log_head: u64,
    held: [HeldBatchSpan; MAX_HELD_ESCALATIONS],
}

impl Default for EscalationHoldPlanner {
    fn default() -> Self {
        Self::new()
    }
}

impl EscalationHoldPlanner {
    #[inline]
    pub const fn new() -> Self {
        Self {
            visible_head: 0,
            held_floor: 0,
            durable_head: 0,
            log_head: 0,
            held: [HeldBatchSpan::EMPTY; MAX_HELD_ESCALATIONS],
        }
    }

    #[inline]
    pub const fn visible_head(&self) -> u64 {
        self.visible_head
    }

    #[inline]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    #[inline]
    pub const fn log_head(&self) -> u64 {
        self.log_head
    }

    #[inline]
    pub const fn held_floor(&self) -> u64 {
        self.held_floor
    }

    fn recompute_held_floor(&self, next_log_head: u64) -> u64 {
        let mut floor = next_log_head;
        let mut rest: &[HeldBatchSpan] = &self.held;
        while let &[span, ref tail @ ..] = rest {
            if span.active && span.first_escalated_offset < floor {
                floor = span.first_escalated_offset;
            }
            rest = tail;
        }
        floor
    }

    /// Appends a batch ending at `new_log_head` (`> self.log_head`), optionally carrying its
    /// earliest escalated record offset `first_escalated_offset`.
    pub fn record_batch_append(
        &mut self,
        new_log_head: u64,
        first_escalated_offset: Option<u64>,
    ) -> Result<EscalationStateSnapshot, &'static str> {
        if new_log_head < self.log_head {
            return Err("log_head cannot regress");
        }
        if let Some(esc_off) = first_escalated_offset {
            if esc_off >= new_log_head {
                return Err("escalated offset must be < new_log_head");
            }
            if !esc_hold_satisfied(new_log_head.saturating_sub(1), self.durable_head) {
                let mut placed = false;
                let mut rest: &mut [HeldBatchSpan] = &mut self.held;
                while let [slot, tail @ ..] = rest {
                    if !slot.active {
                        *slot = HeldBatchSpan {
                            first_escalated_offset: esc_off,
                            last_offset: new_log_head.saturating_sub(1),
                            active: true,
                        };
                        placed = true;
                        break;
                    }
                    rest = tail;
                }
                if !placed {
                    return Err("held escalation table full");
                }
            }
        }

        let next_held = self.recompute_held_floor(new_log_head);
        self.log_head = new_log_head;
        self.held_floor = next_held;
        self.durable_head = esc_durable_clamp(self.durable_head, new_log_head);
        self.visible_head = esc_visible_clamp(new_log_head, next_held);

        Ok(EscalationStateSnapshot {
            visible_head: self.visible_head,
            held_floor: self.held_floor,
            durable_head: self.durable_head,
            log_head: self.log_head,
            released_batches: 0,
        })
    }

    /// Records completion of an out-of-lock full flush through `flushed_head`, releasing all
    /// held batches whose `last_offset < durable_head` and advancing `visible_head`.
    pub fn complete_full_flush(&mut self, flushed_head: u64) -> EscalationStateSnapshot {
        let dur_cand = if flushed_head > self.durable_head {
            flushed_head
        } else {
            self.durable_head
        };
        let next_dur = esc_durable_clamp(dur_cand, self.log_head);
        let mut released = 0usize;
        let mut rest: &mut [HeldBatchSpan] = &mut self.held;
        while let [slot, tail @ ..] = rest {
            if slot.active && esc_hold_satisfied(slot.last_offset, next_dur) {
                *slot = HeldBatchSpan::EMPTY;
                released = released.saturating_add(1);
            }
            rest = tail;
        }
        let next_held = self.recompute_held_floor(self.log_head);
        self.durable_head = next_dur;
        self.held_floor = next_held;
        self.visible_head = esc_visible_clamp(self.log_head, next_held);

        EscalationStateSnapshot {
            visible_head: self.visible_head,
            held_floor: self.held_floor,
            durable_head: self.durable_head,
            log_head: self.log_head,
            released_batches: released,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escalated_batch_holds_visibility_until_out_of_lock_full_flush_completes() {
        let mut planner = EscalationHoldPlanner::new();

        // Non-escalated batch 0..4 is immediately visible on Ordered/Relaxed!
        let s1 = planner.record_batch_append(4, None).unwrap();
        assert_eq!(s1.visible_head, 4);
        assert_eq!(s1.durable_head, 0);

        // Batch 4..8 has an escalated record at offset 5 -> visible_head advances to 5 (4 fits!),
        // while 5..8 is held unseen!
        let s2 = planner.record_batch_append(8, Some(5)).unwrap();
        assert_eq!(s2.visible_head, 5);
        assert_eq!(s2.held_floor, 5);
        assert_eq!(s2.log_head, 8);

        // Subsequent non-escalated batch 8..10 ALSO stays behind held_floor=5 to preserve gapless order!
        let s3 = planner.record_batch_append(10, None).unwrap();
        assert_eq!(s3.visible_head, 5);

        // Partial flush to 7 does not yet cover last_offset=7 (`!(7 < 7)`).
        let f_partial = planner.complete_full_flush(7);
        assert_eq!(f_partial.released_batches, 0);
        assert_eq!(f_partial.visible_head, 5);

        // Full flush through 8 covers offset 7 (`7 < 8`) -> releases held batch AND unblocks 8..10!
        let f_done = planner.complete_full_flush(8);
        assert_eq!(f_done.released_batches, 1);
        assert_eq!(f_done.durable_head, 8);
        assert_eq!(f_done.visible_head, 10);
        assert_eq!(f_done.held_floor, 10);
    }
}
