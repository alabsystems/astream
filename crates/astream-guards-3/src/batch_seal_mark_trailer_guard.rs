// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! BREC v2 `0xB4` (`CONTINUES`), `0xB5` (`SEAL`), and `0xB6` (`bt_ms`) trailer grammar &
//! `RECORD_MARGIN = 56` guard (`evidence/manifest.toml` `broker.batch-seals`;
//! `Astream.Broker.TlaBatchSealMarkTrailerGuard`).
//!
//! Enforces the exact BREC v2 post-body trailer grammar:
//! - Empty trailer -> legacy unmarked record,
//! - `0xB4` (`1` byte) -> batch continues (optionally followed by `0xB6` + `8`-byte `bt_ms`),
//! - `0xB5` + `u32 LE` (`5` bytes, `1 <= count <= seq + 1`) -> batch seal naming
//!   `[seq + 1 - count ..= seq]` (optionally followed by `0xB6` + `8`-byte `bt_ms`),
//! - Optional `0xB6` + `u64 LE` (`9` bytes) alone or after `0xB4`/`0xB5`,
//! - Any trailing garbage byte, double seal, `count == 0`, or `count > seq + 1` is refused!

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
#[path = "batch_seal_mark_trailer_guard_island.rs"]
mod batch_seal_mark_trailer_guard_island;
#[cfg(clean_islands)]
pub use batch_seal_mark_trailer_guard_island::{
    sealed_batch_end_advance_b150, trailer_margin_clamp_b150,
};

/// Batch CONTINUES trailer tag (`0xB4`).
pub const TAG_BATCH_CONTINUES: u8 = 0xB4;
/// Batch SEAL trailer tag (`0xB5`, followed by `u32 LE` count).
pub const TAG_BATCH_SEAL: u8 = 0xB5;
/// Broker monotone timestamp trailer tag (`0xB6`, followed by `u64 LE` `bt_ms`).
pub const TAG_BROKER_TIME: u8 = 0xB6;
/// Reserved record header + trailer + AEAD margin (`56` bytes).
pub const BREC_RECORD_MARGIN: u64 = 56;

#[cfg(not(clean_islands))]
/// Clamp trailer byte length to `BREC_RECORD_MARGIN`.
#[must_use]
pub const fn trailer_margin_clamp_b150(cand_len: u64, margin_cap: u64) -> u64 {
    if cand_len < margin_cap {
        cand_len
    } else {
        margin_cap
    }
}

#[cfg(not(clean_islands))]
/// Advance highest verified batch-sealed end sequence monotonically.
#[must_use]
pub const fn sealed_batch_end_advance_b150(cur_sealed_end: u64, cand_end: u64) -> u64 {
    if cur_sealed_end < cand_end {
        cand_end
    } else {
        cur_sealed_end
    }
}

contract_fn! {
    /// True iff `batch_count >= 1` and `batch_count <= seq_plus_one`.
    #[must_use]
    pub const fn batch_seal_count_valid_b150(batch_count: u64, seq_plus_one: u64) -> bool
    clauses [ensures result == (batch_count >= 1 && batch_count <= seq_plus_one)]
    {
        batch_count >= 1 && batch_count <= seq_plus_one
    }
}

/// Parsed BREC v2 trailer outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchTrailerDecision {
    LegacyUnmarked {
        bt_ms: Option<u64>,
    },
    BatchContinues {
        bt_ms: Option<u64>,
    },
    BatchSealed {
        batch_start_seq: u64,
        batch_end_seq: u64,
        bt_ms: Option<u64>,
    },
    RefusedMalformedTrailer,
}

/// Stateful BREC v2 batch-mark & `bt=` parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BatchSealTrailerGuard {
    highest_sealed_end: u64,
}

impl BatchSealTrailerGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            highest_sealed_end: 0,
        }
    }

    fn parse_optional_bt(rem: &[u8]) -> Result<Option<u64>, ()> {
        if rem.is_empty() {
            return Ok(None);
        }
        let &[TAG_BROKER_TIME, b0, b1, b2, b3, b4, b5, b6, b7] = rem else {
            return Err(());
        };
        Ok(Some(u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7])))
    }

    /// Parse the exact post-field trailer bytes of record `seq`.
    pub fn parse_record_trailer(&mut self, seq: u64, trailer: &[u8]) -> BatchTrailerDecision {
        let clamped_len = trailer_margin_clamp_b150(trailer.len() as u64, BREC_RECORD_MARGIN);
        if clamped_len != trailer.len() as u64 {
            return BatchTrailerDecision::RefusedMalformedTrailer;
        }
        let Some((&tag, after_tag)) = trailer.split_first() else {
            return BatchTrailerDecision::LegacyUnmarked { bt_ms: None };
        };
        if tag == TAG_BROKER_TIME {
            match Self::parse_optional_bt(trailer) {
                Ok(bt_ms) => BatchTrailerDecision::LegacyUnmarked { bt_ms },
                Err(()) => BatchTrailerDecision::RefusedMalformedTrailer,
            }
        } else if tag == TAG_BATCH_CONTINUES {
            match Self::parse_optional_bt(after_tag) {
                Ok(bt_ms) => BatchTrailerDecision::BatchContinues { bt_ms },
                Err(()) => BatchTrailerDecision::RefusedMalformedTrailer,
            }
        } else if tag == TAG_BATCH_SEAL {
            let &[c0, c1, c2, c3, ref rest @ ..] = after_tag else {
                return BatchTrailerDecision::RefusedMalformedTrailer;
            };
            let count = u32::from_le_bytes([c0, c1, c2, c3]) as u64;
            let seq_plus_one = seq.saturating_add(1);
            if !batch_seal_count_valid_b150(count, seq_plus_one) {
                return BatchTrailerDecision::RefusedMalformedTrailer;
            }
            let Ok(bt_ms) = Self::parse_optional_bt(rest) else {
                return BatchTrailerDecision::RefusedMalformedTrailer;
            };
            self.highest_sealed_end =
                sealed_batch_end_advance_b150(self.highest_sealed_end, seq_plus_one);
            BatchTrailerDecision::BatchSealed {
                batch_start_seq: seq_plus_one.saturating_sub(count),
                batch_end_seq: seq,
                bt_ms,
            }
        } else {
            BatchTrailerDecision::RefusedMalformedTrailer
        }
    }
}

impl Default for BatchSealTrailerGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_seal_and_bt_trailers_and_rejects_zero_count_or_double_seals() {
        let mut g = BatchSealTrailerGuard::new();
        assert_eq!(
            g.parse_record_trailer(0, &[TAG_BATCH_CONTINUES]),
            BatchTrailerDecision::BatchContinues { bt_ms: None }
        );
        // Valid 2-record batch seal at seq=1 with 0xB6 bt_ms=1700:
        let mut tr = Vec::new();
        tr.push(TAG_BATCH_SEAL);
        tr.extend_from_slice(&2u32.to_le_bytes());
        tr.push(TAG_BROKER_TIME);
        tr.extend_from_slice(&1700u64.to_le_bytes());
        assert_eq!(
            g.parse_record_trailer(1, &tr),
            BatchTrailerDecision::BatchSealed {
                batch_start_seq: 0,
                batch_end_seq: 1,
                bt_ms: Some(1700),
            }
        );
        // Zero-count seal or double-continues `[0xB4, 0xB4]` is refused!
        let mut zero_seal = vec![TAG_BATCH_SEAL];
        zero_seal.extend_from_slice(&0u32.to_le_bytes());
        assert_eq!(
            g.parse_record_trailer(1, &zero_seal),
            BatchTrailerDecision::RefusedMalformedTrailer
        );
        assert_eq!(
            g.parse_record_trailer(1, &[TAG_BATCH_CONTINUES, TAG_BATCH_CONTINUES]),
            BatchTrailerDecision::RefusedMalformedTrailer
        );
    }
}
