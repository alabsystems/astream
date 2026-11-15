// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Asker-judged relative `dl=<span_ms>` deadline & `late=1` reply classifier
//! (`docs/REQUIREMENTS-fabric-operations-2026-09-14.md` R8 lines 373–400,
//! `docs/DESIGN-aterm-fabric.md` §6.4 line 4042, aterm `478963013`;
//! `Astream.Wire.TlaAskerRelativeDeadlineJudge`).
//!
//! Covers the exact bus invariant R8 lines 399–400 noted `TlaFabricReceipts` left open:
//! - `dl=<span_ms>` is a RELATIVE span counted exclusively on the asker's own monotonic clock
//!   from `ask_local_start_ms` (`elapsed = now_local_ms.saturating_sub(ask_local_start_ms)`),
//!   never converted into a cross-host wall-clock instant,
//! - Any `answer`, `report`, or `ack` (with OR without `verdict=`) on the asker's `in` lane
//!   carrying `re == ask_offset` settles the ask (`SettledOnTime`) if observed before `expired`,
//! - When `elapsed >= dl_span_ms` before any settling reply, the asker's bridge emits `kind=expired`
//!   carrying `re=<ask_offset> dl=<dl_span_ms>` at most ONCE,
//! - Any reply arriving AFTER `expired` was emitted is still delivered to the asker stamped `late=1`!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "asker_relative_deadline_judge_island.rs"]
mod asker_relative_deadline_judge_island;
#[cfg(clean_islands)]
pub use asker_relative_deadline_judge_island::{asker_clock_advance_b138, relative_dl_clamp_b138};

/// Maximum relative deadline span (`7` days in milliseconds = `604_800_000` ms).
pub const MAX_RELATIVE_DL_SPAN_MS: u64 = 604_800_000;

#[cfg(not(clean_islands))]
/// Clamp relative `dl=` span to `span_cap` (`MAX_RELATIVE_DL_SPAN_MS`).
#[must_use]
pub const fn relative_dl_clamp_b138(cand_span_ms: u64, span_cap: u64) -> u64 {
    if cand_span_ms < span_cap {
        cand_span_ms
    } else {
        span_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the asker's local monotonic clock reading (`ms`).
#[must_use]
pub const fn asker_clock_advance_b138(cur_ms: u64, cand_ms: u64) -> u64 {
    if cur_ms < cand_ms {
        cand_ms
    } else {
        cur_ms
    }
}

contract_fn! {
    /// True iff `!already_settled && !already_expired && elapsed_ms >= dl_span_ms`.
    #[must_use]
    pub const fn relative_deadline_due_b138(
        already_settled: bool,
        already_expired: bool,
        elapsed_ms: u64,
        dl_span_ms: u64,
    ) -> bool
    clauses [ensures result == (!already_settled && !already_expired && elapsed_ms >= dl_span_ms)]
    {
        !already_settled && !already_expired && elapsed_ms >= dl_span_ms
    }
}

/// Disposition of a reply or timer tick for a tracked `ask` carrying `dl=<span_ms>`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RelativeDeadlineEvent {
    /// Still waiting within `dl_span_ms` on the asker's clock.
    StillPending { remaining_ms: u64 },
    /// Emit `v=1 t=<ms> re=<ask_off> dl=<dl_span_ms>` (`kind=expired`) once on the asker's lane!
    EmitExpiredOnce { ask_offset: u64, dl_span_ms: u64 },
    /// Settled before expiry by `answer`, `report`, or `ack` (with or without `verdict=`)!
    SettledOnTime,
    /// Arrived after `expired` was recorded: deliver to inbox stamped `late=1`!
    DeliverReplyLate,
    /// Unrelated `re=` or non-settling face (e.g. `pub/<node>/node/ack` halt ack is NOT a receipt!).
    IgnoredNonMatchingRecord,
}

/// Asker-side relative deadline state machine for a single outbound `ask`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AskerRelativeDeadline {
    ask_offset: u64,
    ask_local_start_ms: u64,
    asker_now_ms: u64,
    dl_span_ms: u64,
    settled_on_time: bool,
    expired_emitted: bool,
}

impl AskerRelativeDeadline {
    #[must_use]
    pub const fn new(ask_offset: u64, ask_local_start_ms: u64, raw_dl_span_ms: u64) -> Self {
        let span = relative_dl_clamp_b138(raw_dl_span_ms, MAX_RELATIVE_DL_SPAN_MS);
        Self {
            ask_offset,
            ask_local_start_ms,
            asker_now_ms: ask_local_start_ms,
            dl_span_ms: span,
            settled_on_time: false,
            expired_emitted: false,
        }
    }

    #[must_use]
    pub const fn dl_span_ms(&self) -> u64 {
        relative_dl_clamp_b138(self.dl_span_ms, MAX_RELATIVE_DL_SPAN_MS)
    }

    #[must_use]
    pub const fn elapsed_local_ms(&self) -> u64 {
        self.asker_now_ms.saturating_sub(self.ask_local_start_ms)
    }

    /// Observe an `in`-lane record `(is_in_lane_answer_report_or_ack, re_offset)`.
    /// Note (R8 line 377): `pub/.../ack` halt/barrier rows pass `false` and never settle an ask!
    pub fn on_inbound_record(
        &mut self,
        is_in_lane_answer_report_or_ack: bool,
        re_offset: u64,
    ) -> RelativeDeadlineEvent {
        if !is_in_lane_answer_report_or_ack || re_offset != self.ask_offset {
            return RelativeDeadlineEvent::IgnoredNonMatchingRecord;
        }
        if self.expired_emitted {
            return RelativeDeadlineEvent::DeliverReplyLate;
        }
        self.settled_on_time = true;
        RelativeDeadlineEvent::SettledOnTime
    }

    /// Poll the asker's monotonic clock at `cand_now_ms` (completely independent of peer wall clock `t=`!).
    pub fn poll_asker_clock(&mut self, cand_now_ms: u64) -> RelativeDeadlineEvent {
        self.asker_now_ms = asker_clock_advance_b138(self.asker_now_ms, cand_now_ms);
        if self.settled_on_time {
            return RelativeDeadlineEvent::SettledOnTime;
        }
        let elapsed = self.elapsed_local_ms();
        if relative_deadline_due_b138(false, self.expired_emitted, elapsed, self.dl_span_ms) {
            self.expired_emitted = true;
            return RelativeDeadlineEvent::EmitExpiredOnce {
                ask_offset: self.ask_offset,
                dl_span_ms: self.dl_span_ms,
            };
        }
        if self.expired_emitted {
            RelativeDeadlineEvent::StillPending { remaining_ms: 0 }
        } else {
            RelativeDeadlineEvent::StillPending {
                remaining_ms: self.dl_span_ms.saturating_sub(elapsed),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relative_span_emits_expired_once_and_stamps_subsequent_reply_late() {
        let mut d = AskerRelativeDeadline::new(90_312, 1_000, 5_000);
        // Non-`in` face (`pub/<node>/node/ack`) with matching `re=` is NOT a receipt!
        assert_eq!(
            d.on_inbound_record(false, 90_312),
            RelativeDeadlineEvent::IgnoredNonMatchingRecord
        );
        assert_eq!(
            d.poll_asker_clock(5_999),
            RelativeDeadlineEvent::StillPending { remaining_ms: 1 }
        );
        // At `1_000 + 5_000 = 6_000` ms on the asker's monotonic clock, `expired` fires ONCE:
        assert_eq!(
            d.poll_asker_clock(6_000),
            RelativeDeadlineEvent::EmitExpiredOnce {
                ask_offset: 90_312,
                dl_span_ms: 5_000
            }
        );
        assert_eq!(
            d.poll_asker_clock(7_000),
            RelativeDeadlineEvent::StillPending { remaining_ms: 0 }
        );
        // Reply arriving at 7_500 ms is delivered `late=1`!
        assert_eq!(
            d.on_inbound_record(true, 90_312),
            RelativeDeadlineEvent::DeliverReplyLate
        );
    }
}
