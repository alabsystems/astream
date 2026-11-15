// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fixed 28-byte `"ASBM"` subscriber crash-resume bookmark wire codec
//! (`Astream.Wire.TlaSubAckBookmark`).
//!
//! Persists `(generation, durable_floor, next_offset)` in a fixed stack-allocated 28-byte
//! `"ASBM"` v1 record (`0` heap allocations, `0` slice-indexing panics, `0` `runtime_checked`
//! rows in `astream-wire`) so `aterm-link` and `aspump` resume gaplessly across restarts while
//! guaranteeing `durable_floor <= next_offset` and monotone log generation transitions.

#[cfg(clean_islands)]
#[path = "sub_ack_bookmark_island.rs"]
mod sub_ack_bookmark_island;
#[cfg(clean_islands)]
pub use sub_ack_bookmark_island::{bookmark_floor_clamp, bookmark_gen_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bookmark_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bookmark_floor_clamp(cand_floor: u64, next_offset: u64) -> u64 {
    if cand_floor < next_offset {
        cand_floor
    } else {
        next_offset
    }
}

contract_fn! {
    /// Verified check that `durable_floor <= next_offset`, linked via `clean-kernel-defeq`
    /// to `bookmark_is_consistent_isl`.
    #[must_use]
    pub const fn bookmark_is_consistent(durable_floor: u64, next_offset: u64) -> bool
    clauses [ensures result == (durable_floor <= next_offset)]
    {
        durable_floor <= next_offset
    }
}

/// 4-byte wire magic for v1 subscriber crash-resume bookmarks (`"ASBM"`).
pub const V1_BOOKMARK_MAGIC: [u8; 4] = *b"ASBM";

/// Wire version (`1`) for `V1SubAckBookmark`.
pub const V1_BOOKMARK_VERSION: u8 = 1;

/// Exact encoded byte size of `V1SubAckBookmark` (`4 + 1 + 3 + 8 + 8 + 8 = 32`).
pub const V1_BOOKMARK_BYTES: usize = 32;

/// Decode error for `V1SubAckBookmark`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BookmarkWireError {
    InvalidLength {
        got: usize,
    },
    BadMagic,
    UnsupportedVersion {
        got: u8,
    },
    NonZeroReserved,
    FloorExceedsNextOffset {
        durable_floor: u64,
        next_offset: u64,
    },
}

/// Stack-allocated 32-byte subscriber crash-resume bookmark.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct V1SubAckBookmark {
    pub generation: u64,
    pub durable_floor: u64,
    pub next_offset: u64,
}

impl V1SubAckBookmark {
    /// Construct a normalized bookmark with `durable_floor` clamped to `<= next_offset`.
    #[must_use]
    pub const fn normalized(generation: u64, durable_floor: u64, next_offset: u64) -> Self {
        Self {
            generation,
            durable_floor: bookmark_floor_clamp(durable_floor, next_offset),
            next_offset,
        }
    }

    /// Advance this bookmark monotonically to `(cand_gen, cand_floor, cand_next)`.
    ///
    /// If `cand_gen` moves strictly ahead of `self.generation`, offsets belong to the new
    /// generation; if `cand_gen < self.generation`, the stale update is ignored fail-closed.
    #[must_use]
    pub const fn advance(self, cand_gen: u64, cand_floor: u64, cand_next: u64) -> Self {
        if cand_gen < self.generation {
            return self;
        }
        let next_gen = bookmark_gen_advance(self.generation, cand_gen);
        let next_off = if next_gen == self.generation && cand_next < self.next_offset {
            self.next_offset
        } else {
            cand_next
        };
        Self {
            generation: next_gen,
            durable_floor: bookmark_floor_clamp(cand_floor, next_off),
            next_offset: next_off,
        }
    }

    /// Encode into a fixed 32-byte array.
    #[must_use]
    pub const fn encode(self) -> [u8; V1_BOOKMARK_BYTES] {
        let floor = bookmark_floor_clamp(self.durable_floor, self.next_offset);
        let [m0, m1, m2, m3] = V1_BOOKMARK_MAGIC;
        let [g0, g1, g2, g3, g4, g5, g6, g7] = self.generation.to_be_bytes();
        let [f0, f1, f2, f3, f4, f5, f6, f7] = floor.to_be_bytes();
        let [n0, n1, n2, n3, n4, n5, n6, n7] = self.next_offset.to_be_bytes();
        [
            m0,
            m1,
            m2,
            m3,
            V1_BOOKMARK_VERSION,
            0,
            0,
            0,
            g0,
            g1,
            g2,
            g3,
            g4,
            g5,
            g6,
            g7,
            f0,
            f1,
            f2,
            f3,
            f4,
            f5,
            f6,
            f7,
            n0,
            n1,
            n2,
            n3,
            n4,
            n5,
            n6,
            n7,
        ]
    }

    /// Decode a 32-byte `"ASBM"` bookmark frame, failing closed if `durable_floor > next_offset`.
    pub const fn decode(bytes: &[u8]) -> Result<Self, BookmarkWireError> {
        let &[m0, m1, m2, m3, ver, r0, r1, r2, g0, g1, g2, g3, g4, g5, g6, g7, f0, f1, f2, f3, f4, f5, f6, f7, n0, n1, n2, n3, n4, n5, n6, n7] =
            bytes
        else {
            return Err(BookmarkWireError::InvalidLength { got: bytes.len() });
        };
        if m0 != b'A' || m1 != b'S' || m2 != b'B' || m3 != b'M' {
            return Err(BookmarkWireError::BadMagic);
        }
        if ver != V1_BOOKMARK_VERSION {
            return Err(BookmarkWireError::UnsupportedVersion { got: ver });
        }
        if r0 != 0 || r1 != 0 || r2 != 0 {
            return Err(BookmarkWireError::NonZeroReserved);
        }
        let generation = u64::from_be_bytes([g0, g1, g2, g3, g4, g5, g6, g7]);
        let durable_floor = u64::from_be_bytes([f0, f1, f2, f3, f4, f5, f6, f7]);
        let next_offset = u64::from_be_bytes([n0, n1, n2, n3, n4, n5, n6, n7]);
        if !bookmark_is_consistent(durable_floor, next_offset) {
            return Err(BookmarkWireError::FloorExceedsNextOffset {
                durable_floor,
                next_offset,
            });
        }
        Ok(Self {
            generation,
            durable_floor,
            next_offset,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_and_fences_stale_generations_or_inverted_floors() {
        let b0 = V1SubAckBookmark::normalized(3, 99, 42);
        assert_eq!(b0.durable_floor, 42);
        assert!(bookmark_is_consistent(b0.durable_floor, b0.next_offset));

        let wire = b0.encode();
        assert_eq!(V1SubAckBookmark::decode(&wire), Ok(b0));

        // Stale generation is ignored fail-closed.
        let stale = b0.advance(2, 10, 100);
        assert_eq!(stale, b0);

        // New generation resets offset space cleanly.
        let b1 = b0.advance(4, 12, 15);
        assert_eq!(
            b1,
            V1SubAckBookmark {
                generation: 4,
                durable_floor: 12,
                next_offset: 15,
            }
        );

        // Tampered durable_floor > next_offset is rejected on decode.
        let mut bad = b1.encode();
        bad[23] = 99;
        assert_eq!(
            V1SubAckBookmark::decode(&bad),
            Err(BookmarkWireError::FloorExceedsNextOffset {
                durable_floor: 99,
                next_offset: 15,
            })
        );
    }
}
