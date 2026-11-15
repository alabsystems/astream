// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sealed-stream partial-record cut poisoning & whole-record short-write accounting
//! (`docs/AUDIT-2026-09.md` line 41; `Astream.Aead.TlaSealedSendCutPoisonGuard`).
//!
//! Enforces the two AEAD stream-integrity invariants from the September 2026 audit:
//! 1. If one or more complete AEAD frames were already flushed to the underlying socket
//!    before an I/O interruption at a frame boundary (`written_in_frame == 0`), `write`
//!    MUST report the short plaintext byte count (`ShortWholeRecordFlush`) so a caller retry
//!    never re-seals already-transmitted plaintext as fresh valid records!
//! 2. If a transport error cuts a sealed record mid-frame (`0 < written_in_frame < frame_wire_len`),
//!    the send side is irreversibly poisoned (`ErrCutMidRecordPoisoned`), refusing all subsequent
//!    writes so ciphertext fragments can never splice across retries.

#[cfg(clean_islands)]
#[path = "sealed_send_cut_poison_guard_island.rs"]
mod sealed_send_cut_poison_guard_island;
#[cfg(clean_islands)]
pub use sealed_send_cut_poison_guard_island::{
    sealed_frame_offset_clamp_b139, sealed_sent_frame_advance_b139,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the committed outbound AEAD frame sequence number.
#[must_use]
pub const fn sealed_sent_frame_advance_b139(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp the byte offset within the in-flight AEAD wire frame to `frame_wire_len`.
#[must_use]
pub const fn sealed_frame_offset_clamp_b139(written_in_frame: u64, frame_wire_len: u64) -> u64 {
    if written_in_frame < frame_wire_len {
        written_in_frame
    } else {
        frame_wire_len
    }
}

contract_fn! {
    /// True iff `already_poisoned` or a transport write stalled strictly mid-frame
    /// (`0 < written_in_frame < frame_wire_len`).
    #[must_use]
    pub const fn sealed_partial_write_poisons_b139(
        already_poisoned: bool,
        written_in_frame: u64,
        frame_wire_len: u64,
    ) -> bool
    clauses [ensures result == (already_poisoned || (written_in_frame > 0 && written_in_frame < frame_wire_len))]
    {
        already_poisoned || (written_in_frame > 0 && written_in_frame < frame_wire_len)
    }
}

/// Outcome of an outbound `SealedStream::write` batch across one or more AEAD records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SealedWriteOutcome {
    /// All requested records flushed cleanly (`flushed_plaintext_bytes`).
    FlushedAll {
        flushed_plaintext_bytes: u64,
        next_send_seq: u64,
    },
    /// At least one whole record flushed before an error at a clean record boundary:
    /// return `Ok(flushed_plaintext_bytes)` so caller advances instead of re-sending!
    ShortWholeRecordFlush {
        flushed_plaintext_bytes: u64,
        next_send_seq: u64,
    },
    /// Error before a single byte of any frame left the process: caller may retry cleanly.
    ErrBeforeAnyByte,
    /// Error mid-frame (or after an earlier mid-frame cut): send half irreversibly poisoned!
    ErrCutMidRecordPoisoned,
}

/// Send-side cut-poisoning state machine for `SealedStream`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SealedSendCutGuard {
    send_seq: u64,
    send_poisoned: bool,
}

impl SealedSendCutGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            send_seq: 0,
            send_poisoned: false,
        }
    }

    #[must_use]
    pub const fn send_seq(&self) -> u64 {
        self.send_seq
    }

    #[must_use]
    pub const fn is_poisoned(&self) -> bool {
        self.send_poisoned
    }

    /// Reconcile a write attempt where `whole_frames_flushed` records (`flushed_plaintext_bytes`)
    /// completed before the current frame (`frame_wire_len`) wrote `raw_written_in_frame` bytes.
    pub fn finish_write_attempt(
        &mut self,
        whole_frames_flushed: u64,
        flushed_plaintext_bytes: u64,
        raw_written_in_frame: u64,
        frame_wire_len: u64,
        io_failed_on_current_frame: bool,
    ) -> SealedWriteOutcome {
        let written_in_frame = sealed_frame_offset_clamp_b139(raw_written_in_frame, frame_wire_len);
        if self.send_poisoned {
            return SealedWriteOutcome::ErrCutMidRecordPoisoned;
        }
        let target_seq = self.send_seq.saturating_add(whole_frames_flushed);
        self.send_seq = sealed_sent_frame_advance_b139(self.send_seq, target_seq);

        if !io_failed_on_current_frame && written_in_frame == frame_wire_len {
            return SealedWriteOutcome::FlushedAll {
                flushed_plaintext_bytes,
                next_send_seq: self.send_seq,
            };
        }

        if sealed_partial_write_poisons_b139(self.send_poisoned, written_in_frame, frame_wire_len) {
            self.send_poisoned = true;
            return SealedWriteOutcome::ErrCutMidRecordPoisoned;
        }

        if whole_frames_flushed > 0 {
            SealedWriteOutcome::ShortWholeRecordFlush {
                flushed_plaintext_bytes,
                next_send_seq: self.send_seq,
            }
        } else {
            SealedWriteOutcome::ErrBeforeAnyByte
        }
    }
}

impl Default for SealedSendCutGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whole_record_short_write_reports_ok_bytes_and_mid_frame_cut_poisons() {
        let mut g = SealedSendCutGuard::new();
        // Error before any byte is retryable without poisoning:
        assert_eq!(
            g.finish_write_attempt(0, 0, 0, 1044, true),
            SealedWriteOutcome::ErrBeforeAnyByte
        );
        assert!(!g.is_poisoned());

        // Error after 2 whole frames at a clean frame boundary (`written_in_frame == 0`)
        // MUST report `ShortWholeRecordFlush` so caller does not duplicate those 2 records!
        assert_eq!(
            g.finish_write_attempt(2, 2048, 0, 1044, true),
            SealedWriteOutcome::ShortWholeRecordFlush {
                flushed_plaintext_bytes: 2048,
                next_send_seq: 2,
            }
        );
        assert!(!g.is_poisoned());

        // Mid-frame cut (`512` of `1044` wire bytes) poisons the send stream permanently:
        assert_eq!(
            g.finish_write_attempt(0, 0, 512, 1044, true),
            SealedWriteOutcome::ErrCutMidRecordPoisoned
        );
        assert!(g.is_poisoned());
        assert_eq!(
            g.finish_write_attempt(1, 1024, 1044, 1044, false),
            SealedWriteOutcome::ErrCutMidRecordPoisoned
        );
    }
}
