// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-source `1_024` records / `8 MiB` mailbox subscription pause & half-drain resume valve
//! (`docs/DESIGN-aterm-fabric.md` §5.6 lines 1503–1507, aterm `14b515f83`;
//! `Astream.Pump.TlaMailboxSourcePauseValve`).
//!
//! Prevents one flooded bus face (`say`, `fleet`, or `inbox`) from exhausting bridge RAM or
//! blocking sibling faces:
//! - When a source reaches `MAX_MAILBOX_SOURCE_RECORDS` (`1_024`) OR `MAX_MAILBOX_SOURCE_BYTES`
//!   (`8 MiB`), its reader closes ONLY that subscription (`PauseCloseSubscription`) recording
//!   `resume_next_offset = offset + 1`,
//! - Once the main loop drains BOTH `queued_records <= 512` AND `queued_bytes <= 4 MiB`, the
//!   source re-subscribes cleanly from `resume_next_offset` (`ResumeFrom(resume_next_offset)`).

#[cfg(clean_islands)]
#[path = "mailbox_source_pause_valve_island.rs"]
mod mailbox_source_pause_valve_island;
#[cfg(clean_islands)]
pub use mailbox_source_pause_valve_island::{
    mbox_queued_recs_clamp_b133, mbox_resume_offset_advance_b133,
};

/// Maximum queued records per bridge input face (`1_024`).
pub const MAX_MAILBOX_SOURCE_RECORDS: u64 = 1_024;
/// Half-watermark record threshold to resume a paused face (`512`).
pub const HALF_MAILBOX_SOURCE_RECORDS: u64 = 512;

/// Maximum queued bytes per bridge input face (`8 MiB`).
pub const MAX_MAILBOX_SOURCE_BYTES: u64 = 8 * 1024 * 1024;
/// Half-watermark byte threshold to resume a paused face (`4 MiB`).
pub const HALF_MAILBOX_SOURCE_BYTES: u64 = 4 * 1024 * 1024;

#[cfg(not(clean_islands))]
/// Clamp queued record count to `max_recs`.
#[must_use]
pub const fn mbox_queued_recs_clamp_b133(cand_recs: u64, max_recs: u64) -> u64 {
    if cand_recs < max_recs {
        cand_recs
    } else {
        max_recs
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `resume_next_offset` across deliveries.
#[must_use]
pub const fn mbox_resume_offset_advance_b133(cur_next_off: u64, cand_next_off: u64) -> u64 {
    if cur_next_off < cand_next_off {
        cand_next_off
    } else {
        cur_next_off
    }
}

contract_fn! {
    /// True iff `queued_recs <= half_recs && queued_bytes <= half_bytes`.
    #[must_use]
    pub const fn mbox_drained_to_half_b133(
        queued_recs: u64,
        half_recs: u64,
        queued_bytes: u64,
        half_bytes: u64,
    ) -> bool
    clauses [ensures result == (queued_recs <= half_recs && queued_bytes <= half_bytes)]
    {
        queued_recs <= half_recs && queued_bytes <= half_bytes
    }
}

/// Subscription transition for a single bridge input face.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MailboxValveTransition {
    /// Subscription stays in its current state (`paused` or `flowing`).
    Steady,
    /// Queue hit `1_024` records or `8 MiB`: close this face's subscription until half-drained!
    PauseCloseSubscription { resume_from: u64 },
    /// Queue drained to `<= 512` records AND `<= 4 MiB`: re-subscribe from `resume_from`!
    ResumeSubscription { resume_from: u64 },
}

/// Stateful per-face mailbox pause/resume valve.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MailboxSourcePauseValve {
    paused: bool,
    queued_records: u64,
    queued_bytes: u64,
    resume_next_offset: u64,
}

impl Default for MailboxSourcePauseValve {
    fn default() -> Self {
        Self::new()
    }
}

impl MailboxSourcePauseValve {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            paused: false,
            queued_records: 0,
            queued_bytes: 0,
            resume_next_offset: 0,
        }
    }

    #[must_use]
    pub const fn is_paused(&self) -> bool {
        self.paused
    }

    /// Enqueue one record at `offset` of `payload_bytes`.
    pub fn on_enqueue(&mut self, offset: u64, payload_bytes: u64) -> MailboxValveTransition {
        let next_off = offset.saturating_add(1);
        self.resume_next_offset =
            mbox_resume_offset_advance_b133(self.resume_next_offset, next_off);
        self.queued_records = mbox_queued_recs_clamp_b133(
            self.queued_records.saturating_add(1),
            MAX_MAILBOX_SOURCE_RECORDS,
        );
        self.queued_bytes = self.queued_bytes.saturating_add(payload_bytes);
        if !self.paused
            && (self.queued_records >= MAX_MAILBOX_SOURCE_RECORDS
                || self.queued_bytes >= MAX_MAILBOX_SOURCE_BYTES)
        {
            self.paused = true;
            MailboxValveTransition::PauseCloseSubscription {
                resume_from: self.resume_next_offset,
            }
        } else {
            MailboxValveTransition::Steady
        }
    }

    /// Account drained records/bytes; resumes once BOTH drop to or below half-watermark.
    pub fn on_drain(&mut self, drained_records: u64, drained_bytes: u64) -> MailboxValveTransition {
        self.queued_records = self.queued_records.saturating_sub(drained_records);
        self.queued_bytes = self.queued_bytes.saturating_sub(drained_bytes);
        if self.paused
            && mbox_drained_to_half_b133(
                self.queued_records,
                HALF_MAILBOX_SOURCE_RECORDS,
                self.queued_bytes,
                HALF_MAILBOX_SOURCE_BYTES,
            )
        {
            self.paused = false;
            MailboxValveTransition::ResumeSubscription {
                resume_from: self.resume_next_offset,
            }
        } else {
            MailboxValveTransition::Steady
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pauses_at_byte_or_record_cap_and_resumes_only_at_half_watermark() {
        let mut v = MailboxSourcePauseValve::new();
        assert_eq!(
            v.on_enqueue(41, MAX_MAILBOX_SOURCE_BYTES),
            MailboxValveTransition::PauseCloseSubscription { resume_from: 42 }
        );
        assert!(v.is_paused());
        // Draining only 3 MiB leaves 5 MiB > 4 MiB -> stays paused!
        assert_eq!(
            v.on_drain(0, 3 * 1024 * 1024),
            MailboxValveTransition::Steady
        );
        assert!(v.is_paused());
        // Draining another 1 MiB + 1 record drops to (0, 4 MiB) -> resumes at 42!
        assert_eq!(
            v.on_drain(1, 1024 * 1024),
            MailboxValveTransition::ResumeSubscription { resume_from: 42 }
        );
        assert!(!v.is_paused());
    }
}
