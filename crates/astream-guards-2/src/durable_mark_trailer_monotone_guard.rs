// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Additive `Response::Mark.durable` trailer decoder & notifier-paging monotone guard
//! (`evidence/manifest.toml` `broker.durable-mark`;
//! `Astream.Pump.TlaDurableMarkTrailerMonotoneGuard`).
//!
//! Enforces the `Response::Mark` durable-head trailer contract (`aterm`'s notifier paging signal):
//! - `0` trailer bytes after `resume` -> `LegacyNoDurableTrailer` (`durable = None`),
//! - `1..=7` trailer bytes after `resume` -> `RefusedTruncatedDurableTrailer` (malformed frame!),
//! - `>= 8` trailer bytes after `resume` -> `Some(durable_head)` (bytes past `8`, such as
//!   `oldest`, are skipped cleanly for forward compatibility),
//! - `seen_durable` advances monotonically (`seen_durable <= head`), and a runtime latch from
//!   `Ordered -> Strict` keeps emitting durable marks for the rest of the broker's open!

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
#[path = "durable_mark_trailer_monotone_guard_island.rs"]
mod durable_mark_trailer_monotone_guard_island;
#[cfg(clean_islands)]
pub use durable_mark_trailer_monotone_guard_island::{
    durable_clamp_to_head_b147, seen_durable_advance_b147,
};

/// Exact byte width of the `Mark.durable` `u64` LE trailer.
pub const DURABLE_TRAILER_BYTES: u64 = 8;

#[cfg(not(clean_islands))]
/// Clamp reported `durable` head so it never exceeds `mark_head`.
#[must_use]
pub const fn durable_clamp_to_head_b147(cand_durable: u64, mark_head: u64) -> u64 {
    if cand_durable < mark_head {
        cand_durable
    } else {
        mark_head
    }
}

#[cfg(not(clean_islands))]
/// Advance `seen_durable` monotonically across `Mark` frames.
#[must_use]
pub const fn seen_durable_advance_b147(cur_seen: u64, cand_durable: u64) -> u64 {
    if cur_seen < cand_durable {
        cand_durable
    } else {
        cur_seen
    }
}

contract_fn! {
    /// True iff `trailer_len` is either `0` (older broker) or `>= 8` (whole durable trailer).
    #[must_use]
    pub const fn durable_trailer_len_well_formed_b147(trailer_len: u64) -> bool
    clauses [ensures result == (trailer_len == 0 || trailer_len >= 8)]
    {
        trailer_len == 0 || trailer_len >= 8
    }
}

/// Outcome of inspecting a `Mark` frame's additive trailer after `resume`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DurableMarkDecision {
    LegacyNoDurableTrailer {
        seen_durable: Option<u64>,
    },
    UpdatedDurableWatermark {
        seen_durable: u64,
        newly_covered_records: bool,
    },
    RefusedTruncatedDurableTrailer {
        trailer_len: u64,
    },
}

/// Tracks `seen_durable` and whether the broker started `Ordered` (so a latch to `Strict`
/// keeps emitting durable marks for the remainder of the open).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DurableMarkTracker {
    seen_durable: Option<u64>,
    emits_durable_marks: bool,
}

impl DurableMarkTracker {
    #[must_use]
    pub const fn new(opened_as_ordered: bool) -> Self {
        Self {
            seen_durable: None,
            emits_durable_marks: opened_as_ordered,
        }
    }

    /// Runtime barrier-refusal latch (`Ordered -> Strict`) preserves `emits_durable_marks`!
    pub fn on_runtime_latch_to_strict(&mut self) {
        // Intentionally preserves `self.emits_durable_marks`: once opened `Ordered`,
        // tails attached during that open continue receiving durable marks!
    }

    #[must_use]
    pub const fn emits_durable_marks(&self) -> bool {
        self.emits_durable_marks
    }

    #[must_use]
    pub const fn seen_durable(&self) -> Option<u64> {
        self.seen_durable
    }

    /// Validate trailer length and update `seen_durable` monotonically.
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn observe_mark_trailer(
        &mut self,
        mark_head: u64,
        trailer_bytes: &[u8],
    ) -> DurableMarkDecision {
        let len = trailer_bytes.len() as u64;
        if !durable_trailer_len_well_formed_b147(len) {
            return DurableMarkDecision::RefusedTruncatedDurableTrailer { trailer_len: len };
        }
        let &[b0, b1, b2, b3, b4, b5, b6, b7, ..] = trailer_bytes else {
            return DurableMarkDecision::LegacyNoDurableTrailer {
                seen_durable: self.seen_durable,
            };
        };
        let raw_durable = u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7]);
        let bounded = durable_clamp_to_head_b147(raw_durable, mark_head);
        let prev = match self.seen_durable {
            Some(v) => v,
            None => 0,
        };
        let next = seen_durable_advance_b147(prev, bounded);
        let newly_covered = match self.seen_durable {
            None => next > 0,
            Some(old) => next > old,
        };
        self.seen_durable = Some(next);
        DurableMarkDecision::UpdatedDurableWatermark {
            seen_durable: next,
            newly_covered_records: newly_covered,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_1_to_7_byte_truncated_trailer_skips_extra_bytes_and_survives_strict_latch() {
        let mut t = DurableMarkTracker::new(true);
        for short_len in 1usize..=7 {
            let buf = [0u8; 7];
            assert_eq!(
                t.observe_mark_trailer(10, &buf[..short_len]),
                DurableMarkDecision::RefusedTruncatedDurableTrailer {
                    trailer_len: short_len as u64,
                }
            );
        }
        // Empty trailer -> legacy None:
        assert_eq!(
            t.observe_mark_trailer(10, &[]),
            DurableMarkDecision::LegacyNoDurableTrailer { seen_durable: None }
        );
        // 16-byte trailer (8-byte durable=6 + 8-byte oldest=0) parses durable=6 and skips extra bytes!
        let mut tr = [0u8; 16];
        tr[..8].copy_from_slice(&6u64.to_le_bytes());
        assert_eq!(
            t.observe_mark_trailer(10, &tr),
            DurableMarkDecision::UpdatedDurableWatermark {
                seen_durable: 6,
                newly_covered_records: true,
            }
        );
        t.on_runtime_latch_to_strict();
        assert!(t.emits_durable_marks());
    }
}
