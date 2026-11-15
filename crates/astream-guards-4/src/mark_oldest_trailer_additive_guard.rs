// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Additive `Response::Mark` `(durable, oldest)` dual-trailer decoder & `seen_oldest` guard
//! (`evidence/manifest.toml` `broker.retention-rules` & `broker.durable-mark`;
//! `Astream.Wire.TlaMarkOldestTrailerAdditiveGuard`).
//!
//! Enforces the exact additive byte-width law for `Response::Mark` trailers after `resume`:
//! - `0` bytes -> `durable = None, oldest = None` (pre-durable broker),
//! - `8` bytes -> `durable = Some(d), oldest = None` (pre-oldest broker),
//! - `>= 16` bytes -> `durable = Some(d), oldest = Some(o)` (bytes past `16` skipped cleanly),
//! - `1..=7` or `9..=15` bytes -> `RefusedTruncatedMarkTrailer` (never silently dropped!),
//! - `seen_oldest` advances monotonically and never exceeds `mark_head`.
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "mark_oldest_trailer_additive_guard_island.rs"]
mod mark_oldest_trailer_additive_guard_island;
#[cfg(clean_islands)]
pub use mark_oldest_trailer_additive_guard_island::{
    mark_oldest_clamp_b151, seen_oldest_advance_b151,
};

#[cfg(not(clean_islands))]
/// Clamp reported `oldest` trailer to `mark_head`.
#[must_use]
pub const fn mark_oldest_clamp_b151(cand_oldest: u64, mark_head: u64) -> u64 {
    if cand_oldest < mark_head {
        cand_oldest
    } else {
        mark_head
    }
}

#[cfg(not(clean_islands))]
/// Advance `seen_oldest` monotonically across `Mark` frames.
#[must_use]
pub const fn seen_oldest_advance_b151(cur_oldest: u64, cand_oldest: u64) -> u64 {
    if cur_oldest < cand_oldest {
        cand_oldest
    } else {
        cur_oldest
    }
}

contract_fn! {
    /// True iff `trailer_len` is `0`, `8`, or `>= 16` (no partial 8-byte `u64` trailer).
    #[must_use]
    pub const fn mark_dual_trailer_len_valid_b151(trailer_len: u64) -> bool
    clauses [ensures result == (trailer_len == 0 || trailer_len == 8 || trailer_len >= 16)]
    {
        trailer_len == 0 || trailer_len == 8 || trailer_len >= 16
    }
}

/// Decoded `(durable, oldest)` outcome for a `Response::Mark` trailer.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MarkDualTrailerDecision {
    ParsedMarkTrailers {
        durable: Option<u64>,
        oldest: Option<u64>,
        seen_oldest: Option<u64>,
    },
    RefusedTruncatedMarkTrailer {
        trailer_len: u64,
    },
}

/// Client-side `seen_oldest` monotone tracker for `Response::Mark`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MarkOldestTrailerTracker {
    has_seen_oldest: bool,
    seen_oldest: u64,
}

impl MarkOldestTrailerTracker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            has_seen_oldest: false,
            seen_oldest: 0,
        }
    }

    #[must_use]
    pub const fn seen_oldest(&self) -> Option<u64> {
        if self.has_seen_oldest {
            Some(self.seen_oldest)
        } else {
            None
        }
    }

    /// Decode `trailer` bytes following `Mark.resume` against `mark_head`.
    pub fn decode_trailers(&mut self, mark_head: u64, trailer: &[u8]) -> MarkDualTrailerDecision {
        let len = trailer.len() as u64;
        if !mark_dual_trailer_len_valid_b151(len) {
            return MarkDualTrailerDecision::RefusedTruncatedMarkTrailer { trailer_len: len };
        }
        let &[d0, d1, d2, d3, d4, d5, d6, d7, ref after_durable @ ..] = trailer else {
            return MarkDualTrailerDecision::ParsedMarkTrailers {
                durable: None,
                oldest: None,
                seen_oldest: self.seen_oldest(),
            };
        };
        let dur = mark_oldest_clamp_b151(
            u64::from_le_bytes([d0, d1, d2, d3, d4, d5, d6, d7]),
            mark_head,
        );
        let &[o0, o1, o2, o3, o4, o5, o6, o7, ..] = after_durable else {
            return MarkDualTrailerDecision::ParsedMarkTrailers {
                durable: Some(dur),
                oldest: None,
                seen_oldest: self.seen_oldest(),
            };
        };
        let old = mark_oldest_clamp_b151(
            u64::from_le_bytes([o0, o1, o2, o3, o4, o5, o6, o7]),
            mark_head,
        );
        self.has_seen_oldest = true;
        self.seen_oldest = seen_oldest_advance_b151(self.seen_oldest, old);
        MarkDualTrailerDecision::ParsedMarkTrailers {
            durable: Some(dur),
            oldest: Some(old),
            seen_oldest: Some(self.seen_oldest),
        }
    }
}

impl Default for MarkOldestTrailerTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_0_8_and_16_plus_byte_trailers_and_rejects_9_to_15_byte_cuts() {
        let mut t = MarkOldestTrailerTracker::new();
        assert_eq!(
            t.decode_trailers(20, &[0u8; 12]),
            MarkDualTrailerDecision::RefusedTruncatedMarkTrailer { trailer_len: 12 }
        );
        assert_eq!(
            t.decode_trailers(20, &8u64.to_le_bytes()),
            MarkDualTrailerDecision::ParsedMarkTrailers {
                durable: Some(8),
                oldest: None,
                seen_oldest: None,
            }
        );
        let mut both = [0u8; 20];
        both[..8].copy_from_slice(&15u64.to_le_bytes());
        both[8..16].copy_from_slice(&5u64.to_le_bytes());
        assert_eq!(
            t.decode_trailers(20, &both),
            MarkDualTrailerDecision::ParsedMarkTrailers {
                durable: Some(15),
                oldest: Some(5),
                seen_oldest: Some(5),
            }
        );
    }
}
