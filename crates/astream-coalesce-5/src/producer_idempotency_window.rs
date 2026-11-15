// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! KIP-98 5-Batch Sliding Idempotent Kafka Producer Sequence Window.
//!
//! Kafka v2 idempotent producers (`enable.idempotence=true`, `max.in.flight.requests.per.connection <= 5`)
//! pipeline up to 5 concurrent `RecordBatch` requests per `(producer_id, topic, partition)`.
//! Maintaining only the single latest sequence falsely rejects pipelined retry of batch `N-2`
//! with `DUPLICATE_SEQUENCE` vs `OUT_OF_ORDER_SEQUENCE_NUMBER`. This module tracks the exact
//! KIP-98 5-entry ring of `(base_sequence, last_sequence, assigned_base_offset)` spans and
//! monotone `producer_epoch` fencing with zero heap allocation and zero closures.
//!
//! Backed by Clean TLA+ Island `Astream.Kafka.TlaIdempotentProducerWindow`
//! (`producer_idempotency_window_island.rs`), proving `windowEntries <= maxWindowCap` and
//! `prevEpoch <= producerEpoch`.

#[cfg(clean_islands)]
#[path = "producer_idempotency_window_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{kip98_epoch_advance, kip98_window_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn kip98_window_clamp(entries: u64, max_cap: u64) -> u64 {
    if entries < max_cap {
        entries
    } else {
        max_cap
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn kip98_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// Kernel-certified check that `req_epoch` is stale relative to `cur_epoch` (`PRODUCER_FENCED`).
    #[must_use]
    #[inline]
    pub const fn kip98_epoch_is_fenced(req_epoch: u64, cur_epoch: u64) -> bool
    clauses [ensures result == (req_epoch < cur_epoch)]
    {
        req_epoch < cur_epoch
    }
}

/// KIP-98 specification window size (`5` recent committed batches per producer-partition).
pub const KIP98_MAX_WINDOW_BATCHES: usize = 5;

/// Kafka error code `45`: `OUT_OF_ORDER_SEQUENCE_NUMBER`.
pub const KAFKA_ERR_OUT_OF_ORDER_SEQ: i16 = 45;

/// Kafka error code `59` / `90`: `PRODUCER_FENCED`.
pub const KAFKA_ERR_PRODUCER_FENCED: i16 = 90;

/// Committed batch span retained in the 5-slot ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CommittedBatchSpan {
    pub base_seq: i32,
    pub last_seq: i32,
    pub base_offset: i64,
}

impl CommittedBatchSpan {
    const EMPTY: Self = Self {
        base_seq: 0,
        last_seq: 0,
        base_offset: 0,
    };
}

/// Admission decision for an incoming idempotent `Produce` batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdempotentBatchVerdict {
    /// Fresh contiguous batch accepted and recorded at `assigned_base_offset`.
    AcceptedNew { assigned_base_offset: i64 },
    /// Exact retry of one of the last 5 committed batches -> return original `base_offset`!
    DuplicateBatch { original_base_offset: i64 },
    /// Rejected: `req_epoch < producer_epoch` (`PRODUCER_FENCED`).
    ProducerFenced { current_epoch: u16 },
    /// Rejected: non-contiguous sequence gap or partial overlap (`OUT_OF_ORDER_SEQUENCE_NUMBER`).
    OutOfOrderSequence { expected_base_seq: i32 },
}

/// Zero-allocation KIP-98 5-batch producer sequence tracker certified by `TlaIdempotentProducerWindow`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdempotentProducerWindow {
    initialized: bool,
    prev_epoch: u64,
    producer_epoch: u64,
    window_entries: u64,
    ring_head: usize,
    span0: CommittedBatchSpan,
    span1: CommittedBatchSpan,
    span2: CommittedBatchSpan,
    span3: CommittedBatchSpan,
    span4: CommittedBatchSpan,
}

impl Default for IdempotentProducerWindow {
    fn default() -> Self {
        Self::new()
    }
}

impl IdempotentProducerWindow {
    #[inline]
    pub const fn new() -> Self {
        Self {
            initialized: false,
            prev_epoch: 0,
            producer_epoch: 0,
            window_entries: 0,
            ring_head: 0,
            span0: CommittedBatchSpan::EMPTY,
            span1: CommittedBatchSpan::EMPTY,
            span2: CommittedBatchSpan::EMPTY,
            span3: CommittedBatchSpan::EMPTY,
            span4: CommittedBatchSpan::EMPTY,
        }
    }

    #[inline]
    pub const fn window_entries(&self) -> u64 {
        self.window_entries
    }

    #[inline]
    pub const fn prev_epoch(&self) -> u16 {
        self.prev_epoch as u16
    }

    #[inline]
    pub const fn producer_epoch(&self) -> u16 {
        self.producer_epoch as u16
    }

    #[inline]
    const fn span_at(&self, idx: usize) -> CommittedBatchSpan {
        match idx {
            0 => self.span0,
            1 => self.span1,
            2 => self.span2,
            3 => self.span3,
            _ => self.span4,
        }
    }

    #[inline]
    fn set_span(&mut self, idx: usize, span: CommittedBatchSpan) {
        match idx {
            0 => self.span0 = span,
            1 => self.span1 = span,
            2 => self.span2 = span,
            3 => self.span3 = span,
            _ => self.span4 = span,
        }
    }

    #[inline]
    const fn normalized_head(&self) -> usize {
        if self.ring_head < KIP98_MAX_WINDOW_BATCHES {
            self.ring_head
        } else {
            0
        }
    }

    /// Expected `base_seq` for the next fresh batch in the current epoch (`i32` wrapping at `i32::MAX -> 0`).
    #[inline]
    pub const fn expected_next_seq(&self) -> i32 {
        if self.window_entries == 0 {
            0
        } else {
            let head = self.normalized_head();
            let newest_idx = if head == 0 {
                KIP98_MAX_WINDOW_BATCHES - 1
            } else {
                head - 1
            };
            let last = self.span_at(newest_idx).last_seq;
            if last == i32::MAX {
                0
            } else {
                last.saturating_add(1)
            }
        }
    }

    /// Validates `(req_epoch, base_seq, record_count)` and records `next_log_offset` on accept.
    pub fn check_and_commit(
        &mut self,
        req_epoch: u16,
        base_seq: i32,
        record_count: u32,
        next_log_offset: i64,
    ) -> IdempotentBatchVerdict {
        if record_count == 0 || base_seq < 0 {
            return IdempotentBatchVerdict::OutOfOrderSequence {
                expected_base_seq: self.expected_next_seq(),
            };
        }
        let req_ep_u64 = req_epoch as u64;

        if self.initialized {
            if kip98_epoch_is_fenced(req_ep_u64, self.producer_epoch) {
                return IdempotentBatchVerdict::ProducerFenced {
                    current_epoch: self.producer_epoch as u16,
                };
            }
            if req_ep_u64 > self.producer_epoch {
                // Epoch bump resets sequence expectation to `0` per KIP-98!
                if base_seq != 0 {
                    return IdempotentBatchVerdict::OutOfOrderSequence {
                        expected_base_seq: 0,
                    };
                }
                let next_ep = kip98_epoch_advance(self.producer_epoch, req_ep_u64);
                self.prev_epoch = self.producer_epoch;
                self.producer_epoch = next_ep;
                self.window_entries = 0;
                self.ring_head = 0;
            }
        } else {
            self.initialized = true;
            self.prev_epoch = 0;
            self.producer_epoch = req_ep_u64;
        }

        let delta = record_count.saturating_sub(1) as i64;
        let last_seq = ((base_seq as i64).saturating_add(delta) & 0x7FFF_FFFF) as i32;

        // 1. Check 5-slot deduplication ring for an exact `(base_seq, last_seq)` retry!
        let head = self.normalized_head();
        let count = if (self.window_entries as usize) < KIP98_MAX_WINDOW_BATCHES {
            self.window_entries as usize
        } else {
            KIP98_MAX_WINDOW_BATCHES
        };
        let mut checked = 0usize;
        let mut slot = if head == 0 {
            KIP98_MAX_WINDOW_BATCHES - 1
        } else {
            head.saturating_sub(1)
        };
        while checked < count {
            let span = self.span_at(slot);
            if span.base_seq == base_seq && span.last_seq == last_seq {
                return IdempotentBatchVerdict::DuplicateBatch {
                    original_base_offset: span.base_offset,
                };
            }
            slot = if slot == 0 {
                KIP98_MAX_WINDOW_BATCHES - 1
            } else {
                slot.saturating_sub(1)
            };
            checked = checked.saturating_add(1);
        }

        // 2. Fresh batch: if initialized fresh with empty window, accept initial `base_seq == 0`
        //    (or first seen seq on broker restart); once `window_entries > 0`, require strict contiguity.
        if self.window_entries > 0 {
            let expected = self.expected_next_seq();
            if base_seq != expected {
                return IdempotentBatchVerdict::OutOfOrderSequence {
                    expected_base_seq: expected,
                };
            }
        }

        self.set_span(
            head,
            CommittedBatchSpan {
                base_seq,
                last_seq,
                base_offset: next_log_offset,
            },
        );
        let next_head = head.saturating_add(1);
        self.ring_head = if next_head >= KIP98_MAX_WINDOW_BATCHES {
            0
        } else {
            next_head
        };
        let raw_entries = self.window_entries.saturating_add(1);
        self.window_entries = kip98_window_clamp(raw_entries, KIP98_MAX_WINDOW_BATCHES as u64);

        IdempotentBatchVerdict::AcceptedNew {
            assigned_base_offset: next_log_offset,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_across_five_pipelined_batches_fences_stale_epoch_and_bumps_cleanly() {
        let mut win = IdempotentProducerWindow::new();

        // Commit 5 pipelined batches of 10 records each (seqs 0..9, 10..19, ..., 40..49).
        for b in 0..5i32 {
            assert_eq!(
                win.check_and_commit(1, b * 10, 10, (b * 100) as i64),
                IdempotentBatchVerdict::AcceptedNew {
                    assigned_base_offset: (b * 100) as i64
                }
            );
        }
        assert_eq!(win.window_entries(), 5);

        // Retrying batch #0 (`0..9`) while batches 1..4 already committed STILL deduplicates!
        assert_eq!(
            win.check_and_commit(1, 0, 10, 999),
            IdempotentBatchVerdict::DuplicateBatch {
                original_base_offset: 0
            }
        );

        // Gap batch (`base_seq = 60` instead of `50`) -> OutOfOrderSequence!
        assert_eq!(
            win.check_and_commit(1, 60, 5, 500),
            IdempotentBatchVerdict::OutOfOrderSequence {
                expected_base_seq: 50
            }
        );

        // Stale epoch 0 -> ProducerFenced!
        assert_eq!(
            win.check_and_commit(0, 50, 5, 500),
            IdempotentBatchVerdict::ProducerFenced { current_epoch: 1 }
        );

        // Epoch bump to 2 resets expected sequence to 0!
        assert_eq!(
            win.check_and_commit(2, 0, 4, 500),
            IdempotentBatchVerdict::AcceptedNew {
                assigned_base_offset: 500
            }
        );
        assert_eq!(win.window_entries(), 1);
    }
}
