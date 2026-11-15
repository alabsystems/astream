// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack canonical unsigned LEB128/varint codec (`Astream.Wire.TlaFrameVarintCanonicalGate`).
//!
//! Prevents transcript/digest malleability from overlong LEB128 encodings
//! (e.g. `0x80 0x00` for `0` or `10`-byte encodings with high bits >= `0x02`):
//! guarantees a 1:1 bijection between `u64` values and valid wire byte sequences
//! with **zero heap allocations**.

#![allow(clippy::assign_op_pattern)]

#[cfg(clean_islands)]
#[path = "frame_varint_canonical_gate_island.rs"]
mod frame_varint_canonical_gate_island;
#[cfg(clean_islands)]
pub use frame_varint_canonical_gate_island::{varint_bytes_clamp, varint_decoded_advance};

/// Maximum bytes in a canonical `u64` LEB128 varint (`ceil(64 / 7) = 10`).
pub const MAX_U64_VARINT_BYTES: usize = 10;

#[cfg(not(clean_islands))]
/// Monotonically advance count of canonically decoded `u64` varints.
#[must_use]
pub const fn varint_decoded_advance(cur_decoded: u64, cand_decoded: u64) -> u64 {
    if cur_decoded < cand_decoded {
        cand_decoded
    } else {
        cur_decoded
    }
}

#[cfg(not(clean_islands))]
/// Clamp consumed varint byte length to `max_varint_bytes`.
#[must_use]
pub const fn varint_bytes_clamp(cand_bytes: u64, max_varint_bytes: u64) -> u64 {
    if cand_bytes < max_varint_bytes {
        cand_bytes
    } else {
        max_varint_bytes
    }
}

contract_fn! {
    /// True iff `actual_bytes` equals `min_canonical_bytes` (no trailing zero-7bit groups).
    #[must_use]
    pub const fn varint_len_canonical(actual_bytes: u64, min_canonical_bytes: u64) -> bool
    clauses [ensures result == (actual_bytes == min_canonical_bytes)]
    {
        actual_bytes == min_canonical_bytes
    }
}

/// Refusal reasons when decoding a canonical `u64` LEB128 varint.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CanonicalVarintError {
    Truncated,
    Overflow64Bit,
    NonCanonicalOverlong {
        actual_bytes: usize,
        canonical_bytes: usize,
    },
}

/// Exact canonical byte length (`1..=10`) required to encode `value` in unsigned LEB128.
#[must_use]
pub const fn canonical_u64_varint_len(mut value: u64) -> usize {
    let mut len = 1usize;
    while value >= 0x80 {
        value = value >> 7;
        len = len.saturating_add(1);
    }
    len
}

/// Encode `value` into a fixed `[u8; 10]` stack buffer, returning `(buf, canonical_len)`.
#[must_use]
pub fn encode_canonical_u64(mut value: u64) -> ([u8; MAX_U64_VARINT_BYTES], usize) {
    let mut buf = [0u8; MAX_U64_VARINT_BYTES];
    let mut idx = 0usize;
    while value >= 0x80 {
        if let Some(slot) = buf.get_mut(idx) {
            *slot = ((value as u8) & 0x7f) | 0x80;
        }
        value = value >> 7;
        idx = idx.saturating_add(1);
    }
    if let Some(slot) = buf.get_mut(idx) {
        *slot = value as u8;
    }
    (buf, idx.saturating_add(1))
}

/// Pure stack canonical varint decoder gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FrameVarintCanonicalGate {
    decoded_count: u64,
    last_bytes: u64,
}

impl Default for FrameVarintCanonicalGate {
    fn default() -> Self {
        Self::new()
    }
}

impl FrameVarintCanonicalGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            decoded_count: 0,
            last_bytes: 0,
        }
    }

    #[must_use]
    pub const fn decoded_count(&self) -> u64 {
        self.decoded_count
    }

    #[must_use]
    pub const fn last_bytes(&self) -> u64 {
        self.last_bytes
    }

    /// Decode `(value, consumed_bytes)` from `src`, rejecting truncated, overflowing, or overlong inputs.
    pub fn decode_u64(&mut self, src: &[u8]) -> Result<(u64, usize), CanonicalVarintError> {
        let mut acc = 0u64;
        let mut shift = 0u32;
        let mut consumed = 0usize;
        let mut rest = src;

        while let &[b, ref tail @ ..] = rest {
            consumed = consumed.saturating_add(1);
            if consumed > MAX_U64_VARINT_BYTES {
                return Err(CanonicalVarintError::Overflow64Bit);
            }
            if consumed == MAX_U64_VARINT_BYTES && b > 0x01 {
                return Err(CanonicalVarintError::Overflow64Bit);
            }
            if shift > 63 {
                return Err(CanonicalVarintError::Overflow64Bit);
            }
            let low = (b & 0x7f) as u64;
            acc = acc | (low << (shift & 63));
            if (b & 0x80) == 0 {
                let min_len = canonical_u64_varint_len(acc);
                if !varint_len_canonical(consumed as u64, min_len as u64) {
                    return Err(CanonicalVarintError::NonCanonicalOverlong {
                        actual_bytes: consumed,
                        canonical_bytes: min_len,
                    });
                }
                self.last_bytes = varint_bytes_clamp(consumed as u64, MAX_U64_VARINT_BYTES as u64);
                let cand = self.decoded_count.saturating_add(1);
                self.decoded_count = varint_decoded_advance(self.decoded_count, cand);
                return Ok((acc, consumed));
            }
            shift = shift.saturating_add(7);
            rest = tail;
        }
        Err(CanonicalVarintError::Truncated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_canonical_boundaries_and_rejects_overlong_and_overflow() {
        let mut gate = FrameVarintCanonicalGate::new();
        for &v in &[0u64, 1, 127, 128, 16_383, 16_384, u32::MAX as u64, u64::MAX] {
            let (buf, len) = encode_canonical_u64(v);
            assert_eq!(gate.decode_u64(&buf[..len]), Ok((v, len)));
        }
        // Overlong encoding of 0 as [0x80, 0x00] MUST fail!
        assert_eq!(
            gate.decode_u64(&[0x80, 0x00]),
            Err(CanonicalVarintError::NonCanonicalOverlong {
                actual_bytes: 2,
                canonical_bytes: 1,
            })
        );
        // 10th byte = 0x02 overflows u64::MAX!
        assert_eq!(
            gate.decode_u64(&[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02]),
            Err(CanonicalVarintError::Overflow64Bit)
        );
    }
}
