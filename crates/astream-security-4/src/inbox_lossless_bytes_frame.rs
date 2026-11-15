// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Lossless binary `inbox get --bytes` & `deliver` length-framed cursor
//! (`docs/DESIGN-aterm-fabric.md` §9.1, §11.2 register 21, §13 line 3826, §15 line 4047;
//! `Astream.Broker.TlaInboxLosslessBytesFrame`).
//!
//! Eliminates UTF-8 `String` lossiness and line-truncation on binary fabric bodies (`len=<n>\n<raw>`):
//! - Caps inline binary `post` / `deliver` payloads at `MAX_INBOX_BINARY_BYTES` (`256 KiB`, §13),
//!   steering larger blobs to offset/path references rather than truncating silently,
//! - Tracks byte-exact chunked transfer `[delivered_bytes <= declared_len]` with monotonic offset
//!   watermarks and terminal digest verification before committing the inbox row.

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
#[path = "inbox_lossless_bytes_frame_island.rs"]
mod inbox_lossless_bytes_frame_island;
#[cfg(clean_islands)]
pub use inbox_lossless_bytes_frame_island::{
    inbox_bytes_delivered_clamp_b127, inbox_bytes_offset_advance_b127,
};

#[cfg(not(clean_islands))]
/// Clamp delivered binary payload bytes to `declared_len`.
#[must_use]
pub const fn inbox_bytes_delivered_clamp_b127(cand_delivered: u64, declared_len: u64) -> u64 {
    if cand_delivered < declared_len {
        cand_delivered
    } else {
        declared_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the committed binary `inbox` record offset.
#[must_use]
pub const fn inbox_bytes_offset_advance_b127(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

contract_fn! {
    /// True iff `declared_len <= max_binary_bytes` (`256 KiB` inline fabric ceiling).
    #[must_use]
    pub const fn inbox_bytes_len_within_cap_b127(declared_len: u64, max_binary_bytes: u64) -> bool
    clauses [ensures result == (declared_len <= max_binary_bytes)]
    {
        declared_len <= max_binary_bytes
    }
}

pub const MAX_INBOX_BINARY_BYTES: u64 = 256 * 1024;

/// Progress/verdict for lossless `deliver` / `inbox get --bytes` framing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InboxBytesFrameVerdict {
    Begun {
        record_offset: u64,
        declared_len: u64,
    },
    ChunkAccepted {
        delivered_bytes: u64,
        declared_len: u64,
    },
    CompletedLossless {
        record_offset: u64,
        declared_len: u64,
    },
    RefusedExceedsInlineCeiling {
        declared_len: u64,
        max_binary_bytes: u64,
    },
    RefusedDigestMismatch {
        expected_fnv64: u64,
        observed_fnv64: u64,
    },
    RefusedOutOfOrderOffset {
        record_offset: u64,
        committed_offset: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct InFlightBinaryRow {
    record_offset: u64,
    declared_len: u64,
    delivered_bytes: u64,
    expected_fnv64: u64,
}

/// Lossless binary `deliver` / `inbox get --bytes` frame state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InboxLosslessBytesFramer {
    max_binary_bytes: u64,
    committed_offset: u64,
    in_flight: Option<InFlightBinaryRow>,
}

impl InboxLosslessBytesFramer {
    #[must_use]
    pub const fn new(max_binary_bytes: u64) -> Self {
        Self {
            max_binary_bytes,
            committed_offset: 0,
            in_flight: None,
        }
    }

    #[must_use]
    pub const fn committed_offset(&self) -> u64 {
        self.committed_offset
    }

    /// Begin framing a `len=<declared_len>\n` binary inbox body at 1-based `record_offset`.
    pub fn begin_frame(
        &mut self,
        record_offset: u64,
        declared_len: u64,
        expected_fnv64: u64,
    ) -> InboxBytesFrameVerdict {
        if record_offset == 0 || record_offset <= self.committed_offset {
            return InboxBytesFrameVerdict::RefusedOutOfOrderOffset {
                record_offset,
                committed_offset: self.committed_offset,
            };
        }
        if !inbox_bytes_len_within_cap_b127(declared_len, self.max_binary_bytes) {
            return InboxBytesFrameVerdict::RefusedExceedsInlineCeiling {
                declared_len,
                max_binary_bytes: self.max_binary_bytes,
            };
        }
        self.in_flight = Some(InFlightBinaryRow {
            record_offset,
            declared_len,
            delivered_bytes: 0,
            expected_fnv64,
        });
        InboxBytesFrameVerdict::Begun {
            record_offset,
            declared_len,
        }
    }

    /// Append `chunk_len` raw bytes without UTF-8 conversion or pct-decode loss.
    #[allow(clippy::question_mark)]
    pub fn push_raw_chunk(&mut self, chunk_len: u64) -> Option<InboxBytesFrameVerdict> {
        let Some(row) = self.in_flight.as_mut() else {
            return None;
        };
        let cand = row.delivered_bytes.saturating_add(chunk_len);
        row.delivered_bytes = inbox_bytes_delivered_clamp_b127(cand, row.declared_len);
        Some(InboxBytesFrameVerdict::ChunkAccepted {
            delivered_bytes: row.delivered_bytes,
            declared_len: row.declared_len,
        })
    }

    /// Seal and verify the completed binary body against `observed_fnv64`.
    #[allow(clippy::question_mark)]
    pub fn finish_frame(&mut self, observed_fnv64: u64) -> Option<InboxBytesFrameVerdict> {
        let Some(row) = self.in_flight else {
            return None;
        };
        if row.delivered_bytes < row.declared_len {
            return Some(InboxBytesFrameVerdict::ChunkAccepted {
                delivered_bytes: row.delivered_bytes,
                declared_len: row.declared_len,
            });
        }
        self.in_flight = None;
        if observed_fnv64 != row.expected_fnv64 {
            return Some(InboxBytesFrameVerdict::RefusedDigestMismatch {
                expected_fnv64: row.expected_fnv64,
                observed_fnv64,
            });
        }
        self.committed_offset =
            inbox_bytes_offset_advance_b127(self.committed_offset, row.record_offset);
        Some(InboxBytesFrameVerdict::CompletedLossless {
            record_offset: self.committed_offset,
            declared_len: row.declared_len,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_exact_binary_length_without_truncation_and_refuses_oversized_or_corrupt_bodies() {
        let mut framer = InboxLosslessBytesFramer::new(MAX_INBOX_BINARY_BYTES);

        // Over 256 KiB inline ceiling is refused cleanly (never silently truncated!).
        assert_eq!(
            framer.begin_frame(5, MAX_INBOX_BINARY_BYTES + 1, 0x11),
            InboxBytesFrameVerdict::RefusedExceedsInlineCeiling {
                declared_len: MAX_INBOX_BINARY_BYTES + 1,
                max_binary_bytes: MAX_INBOX_BINARY_BYTES,
            }
        );

        assert_eq!(
            framer.begin_frame(5, 4_096, 0xCAFE_BABE),
            InboxBytesFrameVerdict::Begun {
                record_offset: 5,
                declared_len: 4_096,
            }
        );
        assert_eq!(
            framer.push_raw_chunk(2_000),
            Some(InboxBytesFrameVerdict::ChunkAccepted {
                delivered_bytes: 2_000,
                declared_len: 4_096,
            })
        );
        assert_eq!(
            framer.push_raw_chunk(2_096),
            Some(InboxBytesFrameVerdict::ChunkAccepted {
                delivered_bytes: 4_096,
                declared_len: 4_096,
            })
        );
        assert_eq!(
            framer.finish_frame(0xCAFE_BABE),
            Some(InboxBytesFrameVerdict::CompletedLossless {
                record_offset: 5,
                declared_len: 4_096,
            })
        );
        assert_eq!(framer.committed_offset(), 5);
    }
}
