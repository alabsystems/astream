// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-serialized wire-frame slab coalescer for multi-subscriber `tail_loop` fanout
//! (`DESIGN-aterm-fabric.md` §13, `Astream.Broker.TlaFanoutSlabCoalescer`).
//!
//! Eliminates the 64-subscriber lock-contention & re-serialization cliff on `Mutex<BrokerLog>`:
//! - When `append_batch` commits `[slab_base, slab_head)`, it publishes ONE immutable byte slab
//!   containing the pre-framed wire bytes and offset directory.
//! - Parked `tail_loop` subscribers whose cursor falls in `[slab_base, slab_head)` copy directly
//!   from the shared slab without re-locking `BrokerLog` or re-encoding `BrokerRecord` frames.
//! - Proves `slab_cursor <= slab_head` and `coalesced_wakes <= parked_subscribers`.

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
#[path = "fanout_slab_coalescer_island.rs"]
mod fanout_slab_coalescer_island;
#[cfg(clean_islands)]
pub use fanout_slab_coalescer_island::{slab_cursor_clamp, slab_wakes_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn slab_cursor_clamp(cursor: u64, slab_head: u64) -> u64 {
    if cursor < slab_head {
        cursor
    } else {
        slab_head
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn slab_wakes_clamp(wakes: u64, parked: u64) -> u64 {
    if wakes < parked {
        wakes
    } else {
        parked
    }
}

contract_fn! {
    /// Verified check that a subscriber cursor has unread records below `slab_head`
    /// (`cursor < slab_head`), linked via `clean-kernel-defeq` to
    /// `slab_cursor_behind_head_isl`.
    #[must_use]
    pub const fn slab_cursor_behind_head(cursor: u64, slab_head: u64) -> bool
    clauses [ensures result == (cursor < slab_head)]
    {
        cursor < slab_head
    }
}

/// Metadata for a single pre-framed record slice inside a [`CoalescedFanoutSlab`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlabRecordSlice {
    /// Log offset of this record.
    pub offset: u64,
    /// Subject string for filter matching without touching `BrokerLog`.
    pub subject: String,
    /// Inclusive byte start inside `wire_bytes`.
    pub byte_start: usize,
    /// Exclusive byte end inside `wire_bytes`.
    pub byte_end: usize,
}

/// Immutable pre-serialized wire batch published once per `append_batch` commit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoalescedFanoutSlab {
    slab_base: u64,
    slab_head: u64,
    entries: Vec<SlabRecordSlice>,
    wire_bytes: Vec<u8>,
}

impl CoalescedFanoutSlab {
    /// Assemble a coalesced slab starting at `slab_base` from `(subject, pre_framed_bytes)` pairs.
    #[must_use]
    pub fn from_framed_batch(slab_base: u64, records: &[(&str, &[u8])]) -> Self {
        let mut entries = Vec::new();
        let mut wire_bytes = Vec::new();
        let mut cur_off = slab_base;
        let mut rest = records;
        while let &[(subj, framed), ref tail @ ..] = rest {
            let start = wire_bytes.len();
            wire_bytes.extend_from_slice(framed);
            let end = wire_bytes.len();
            entries.push(SlabRecordSlice {
                offset: cur_off,
                subject: {
                    let mut s = String::new();
                    s.push_str(subj);
                    s
                },
                byte_start: start,
                byte_end: end,
            });
            cur_off = cur_off.saturating_add(1);
            rest = tail;
        }
        Self {
            slab_base,
            slab_head: cur_off,
            entries,
            wire_bytes,
        }
    }

    /// Inclusive start offset covered by this slab.
    #[must_use]
    pub const fn slab_base(&self) -> u64 {
        self.slab_base
    }

    /// Exclusive end offset covered by this slab.
    #[must_use]
    pub const fn slab_head(&self) -> u64 {
        self.slab_head
    }

    /// Drain matching pre-serialized wire bytes for a subscriber at `cursor` (`>= slab_base`)
    /// matching `subject_prefix`, returning `(advanced_cursor, concatenated_wire_bytes)`.
    #[must_use]
    pub fn drain_from(&self, cursor: u64, subject_prefix: &str) -> Option<(u64, Vec<u8>)> {
        if cursor < self.slab_base || !slab_cursor_behind_head(cursor, self.slab_head) {
            return None;
        }
        let mut out = Vec::new();
        let mut rest = self.entries.as_slice();
        while let [ent, tail @ ..] = rest {
            if ent.offset >= cursor && ent.subject.starts_with(subject_prefix) {
                if let Some(chunk) = self.wire_bytes.get(ent.byte_start..ent.byte_end) {
                    out.extend_from_slice(chunk);
                }
            }
            rest = tail;
        }
        let next_cur = slab_cursor_clamp(self.slab_head, self.slab_head);
        Some((next_cur, out))
    }
}

/// Accounting state tracking slab-served subscriber cursors and coalesced wakeups.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FanoutSlabTracker {
    slab_cursor: u64,
    slab_head: u64,
    coalesced_wakes: u64,
    parked_subscribers: u64,
}

impl FanoutSlabTracker {
    #[must_use]
    pub const fn new(parked_subscribers: u64) -> Self {
        Self {
            slab_cursor: 0,
            slab_head: 0,
            coalesced_wakes: 0,
            parked_subscribers,
        }
    }

    #[must_use]
    pub const fn slab_cursor(&self) -> u64 {
        self.slab_cursor
    }

    #[must_use]
    pub const fn slab_head(&self) -> u64 {
        self.slab_head
    }

    #[must_use]
    pub const fn coalesced_wakes(&self) -> u64 {
        self.coalesced_wakes
    }

    /// Record publication of a new batch slab up to `new_head`, waking `raw_matching_wakes`
    /// out of `parked_subscribers`.
    pub fn record_publish(
        &mut self,
        new_head: u64,
        advanced_cursor: u64,
        raw_matching_wakes: u64,
        parked_subscribers: u64,
    ) {
        if new_head > self.slab_head {
            self.slab_head = new_head;
        }
        self.slab_cursor = slab_cursor_clamp(advanced_cursor, self.slab_head);
        self.parked_subscribers = parked_subscribers;
        self.coalesced_wakes = slab_wakes_clamp(raw_matching_wakes, parked_subscribers);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serves_matching_wire_frames_without_reencoding_and_bounds_wake_counts() {
        let slab = CoalescedFanoutSlab::from_framed_batch(
            100,
            &[
                ("in/s1/mail", b"\x01frame100"),
                ("telemetry/cpu", b"\x02frame101"),
                ("in/s1/task", b"\x03frame102"),
            ],
        );
        assert_eq!((slab.slab_base(), slab.slab_head()), (100, 103));
        assert_eq!(slab.drain_from(99, "in/s1/"), None);
        assert_eq!(slab.drain_from(103, "in/s1/"), None);

        let (next_cur, bytes) = slab.drain_from(100, "in/s1/").expect("slab hit");
        assert_eq!(next_cur, 103);
        assert_eq!(bytes, b"\x01frame100\x03frame102");

        let mut tr = FanoutSlabTracker::new(64);
        tr.record_publish(103, next_cur, 99, 64);
        assert_eq!(tr.slab_cursor(), 103);
        assert_eq!(tr.coalesced_wakes(), 64);
    }
}
