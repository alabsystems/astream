// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Additive `Response::Mark` trailer codec (`next`, `head`, `resume`, optional `durable` &
//! `oldest` 8-byte LE trailers) (`Astream.Wire.TlaMarkDurableTrailer`, Island #293).
//!
//! Written to `astream-wire`'s strict `0 mandated, 0 runtime_checked` bar:
//! - Uses slice pattern matching (`[b0, b1, ..., b7, rest @ ..]`) exclusively — zero panicking
//!   indexing terminators, zero closures, zero arithmetic overflow assertions.
//! - Rejects 1..=7-byte truncated `durable` or `oldest` trailers fail-closed (`MarkDecodeError`)
//!   while skipping unknown additive bytes beyond `oldest` for forward wire compatibility.

#[cfg(clean_islands)]
#[path = "mark_durable_trailer_island.rs"]
mod mark_durable_trailer_island;
#[cfg(clean_islands)]
pub use mark_durable_trailer_island::{mark_durable_clamp, mark_oldest_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn mark_durable_clamp(durable: u64, head: u64) -> u64 {
    if durable < head {
        durable
    } else {
        head
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn mark_oldest_clamp(oldest: u64, head: u64) -> u64 {
    if oldest < head {
        oldest
    } else {
        head
    }
}

contract_fn! {
    /// Verified check whether `durable_head` covers a delivered record at `offset`
    /// (`offset < durable_head`), linked via `clean-kernel-defeq` to
    /// `mark_durable_covers_offset_isl`.
    #[must_use]
    pub const fn mark_durable_covers_offset(offset: u64, durable_head: u64) -> bool
    clauses [ensures result == (offset < durable_head)]
    {
        offset < durable_head
    }
}

/// Decoded additive `Mark` payload (`24`, `32`, or `>= 40` bytes).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct DecodedMarkFrame {
    pub next: u64,
    pub head: u64,
    pub resume: u64,
    pub durable: Option<u64>,
    pub oldest: Option<u64>,
}

/// Wire error returned when decoding a `Mark` body.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MarkDecodeError {
    /// Core 24-byte `(next, head, resume)` header is truncated.
    ShortBaseHeader,
    /// Optional 8-byte `durable` trailer was cut 1..=7 bytes short.
    TruncatedDurableTrailer,
    /// Optional 8-byte `oldest` trailer was cut 1..=7 bytes short.
    TruncatedOldestTrailer,
}

const fn read_u64_le_split(bytes: &[u8]) -> Option<(u64, &[u8])> {
    match bytes {
        [b0, b1, b2, b3, b4, b5, b6, b7, rest @ ..] => {
            let val = u64::from_le_bytes([*b0, *b1, *b2, *b3, *b4, *b5, *b6, *b7]);
            Some((val, rest))
        }
        _ => None,
    }
}

impl DecodedMarkFrame {
    /// Construct a normalized `Mark` frame with `durable` and `oldest` clamped to `<= head`.
    #[must_use]
    pub const fn normalized(
        next: u64,
        head: u64,
        resume: u64,
        durable: Option<u64>,
        oldest: Option<u64>,
    ) -> Self {
        let dur = match durable {
            Some(d) => Some(mark_durable_clamp(d, head)),
            None => None,
        };
        let old = match oldest {
            Some(o) => Some(mark_oldest_clamp(o, head)),
            None => None,
        };
        Self {
            next,
            head,
            resume,
            durable: dur,
            oldest: old,
        }
    }

    /// Encode this `Mark` into a fixed 40-byte stack buffer, returning `(bytes, active_len)` where
    /// `active_len` is `24` (base), `32` (`+ durable`), or `40` (`+ durable + oldest`).
    #[must_use]
    pub const fn encode_fixed(&self) -> ([u8; 40], usize) {
        let [n0, n1, n2, n3, n4, n5, n6, n7] = self.next.to_le_bytes();
        let [h0, h1, h2, h3, h4, h5, h6, h7] = self.head.to_le_bytes();
        let [r0, r1, r2, r3, r4, r5, r6, r7] = self.resume.to_le_bytes();
        let (dur_val, old_val, len) = match (self.durable, self.oldest) {
            (None, None) => (0u64, 0u64, 24usize),
            (Some(d), None) => (mark_durable_clamp(d, self.head), 0u64, 32usize),
            (Some(d), Some(o)) => (
                mark_durable_clamp(d, self.head),
                mark_oldest_clamp(o, self.head),
                40usize,
            ),
            (None, Some(o)) => (0u64, mark_oldest_clamp(o, self.head), 40usize),
        };
        let [d0, d1, d2, d3, d4, d5, d6, d7] = dur_val.to_le_bytes();
        let [o0, o1, o2, o3, o4, o5, o6, o7] = old_val.to_le_bytes();
        (
            [
                n0, n1, n2, n3, n4, n5, n6, n7, h0, h1, h2, h3, h4, h5, h6, h7, r0, r1, r2, r3, r4,
                r5, r6, r7, d0, d1, d2, d3, d4, d5, d6, d7, o0, o1, o2, o3, o4, o5, o6, o7,
            ],
            len,
        )
    }

    /// Decode an additive `Mark` body, rejecting 1..=7-byte cut trailers and ignoring unknown
    /// future trailers past byte 40.
    pub const fn decode(body: &[u8]) -> Result<Self, MarkDecodeError> {
        let Some((next, r1)) = read_u64_le_split(body) else {
            return Err(MarkDecodeError::ShortBaseHeader);
        };
        let Some((head, r2)) = read_u64_le_split(r1) else {
            return Err(MarkDecodeError::ShortBaseHeader);
        };
        let Some((resume, r3)) = read_u64_le_split(r2) else {
            return Err(MarkDecodeError::ShortBaseHeader);
        };
        if r3.is_empty() {
            return Ok(Self {
                next,
                head,
                resume,
                durable: None,
                oldest: None,
            });
        }
        let Some((raw_durable, r4)) = read_u64_le_split(r3) else {
            return Err(MarkDecodeError::TruncatedDurableTrailer);
        };
        let durable = Some(mark_durable_clamp(raw_durable, head));
        if r4.is_empty() {
            return Ok(Self {
                next,
                head,
                resume,
                durable,
                oldest: None,
            });
        }
        let Some((raw_oldest, _future_trailers)) = read_u64_le_split(r4) else {
            return Err(MarkDecodeError::TruncatedOldestTrailer);
        };
        let oldest = Some(mark_oldest_clamp(raw_oldest, head));
        Ok(Self {
            next,
            head,
            resume,
            durable,
            oldest,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn additive_trailers_roundtrip_and_reject_short_cuts() {
        let m = DecodedMarkFrame::normalized(10, 25, 10, Some(20), Some(5));
        let (raw, len) = m.encode_fixed();
        assert_eq!(len, 40);
        let mut buf = raw[..len].to_vec();
        assert_eq!(DecodedMarkFrame::decode(&buf), Ok(m));

        // Legacy 24-byte reader view and legacy 24-byte frame:
        assert_eq!(
            DecodedMarkFrame::decode(&buf[..24]),
            Ok(DecodedMarkFrame {
                next: 10,
                head: 25,
                resume: 10,
                durable: None,
                oldest: None,
            })
        );

        // 1..=7-byte cuts in durable or oldest fail closed:
        for cut in 25..32 {
            assert_eq!(
                DecodedMarkFrame::decode(&buf[..cut]),
                Err(MarkDecodeError::TruncatedDurableTrailer)
            );
        }
        for cut in 33..40 {
            assert_eq!(
                DecodedMarkFrame::decode(&buf[..cut]),
                Err(MarkDecodeError::TruncatedOldestTrailer)
            );
        }

        // Future additive trailer bytes past 40 are skipped cleanly:
        buf.extend_from_slice(&[0xAA, 0xBB, 0xCC]);
        assert_eq!(DecodedMarkFrame::decode(&buf), Ok(m));
    }
}
