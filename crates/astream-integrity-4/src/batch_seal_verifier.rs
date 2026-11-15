// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `"ASB1"` 20-byte atomic group-commit batch seal codec & torn-batch verifier.
//!
//! Group-committed log segments (`aterm-restore` snapshots and `astream-broker` batches)
//! seal an atomic batch of `record_count` contiguous records starting at `first_offset`
//! together with a rolling 32-bit FNV-1a checksum accumulator (`checksum32`). A power loss
//! that writes fewer than `record_count` records leaves an incomplete seal that readers
//! reject cleanly back to `first_offset` without linking broker internals.
//!
//! Encodes and decodes via total slice-pattern destructuring (`0` `runtime_checked` indexing
//! obligations in `astream-wire`).
//!
//! Clean specification: `batch_seal_verifier_island.rs` (`Astream.Wire.TlaBatchSealVerifier`).

#[cfg(clean_islands)]
#[path = "batch_seal_verifier_island.rs"]
mod batch_seal_verifier_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn batch_seal_seen_clamp(cand_seen: u64, expected_count: u64) -> u64 {
    if cand_seen < expected_count {
        cand_seen
    } else {
        expected_count
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn batch_seal_offset_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}
#[cfg(clean_islands)]
pub use batch_seal_verifier_island::{batch_seal_offset_advance, batch_seal_seen_clamp};

/// 4-byte wire magic for v1 atomic batch seals (`"ASB1"`).
pub const V1_BATCH_SEAL_MAGIC: [u8; 4] = *b"ASB1";
/// Exact encoded byte size of `V1BatchSeal` (`4 + 8 + 4 + 4 = 20`).
pub const V1_BATCH_SEAL_BYTES: usize = 20;

const FNV32_OFFSET: u32 = 0x811c_9dc5;
const FNV32_PRIME: u32 = 0x0100_0193;

contract_fn! {
    /// Kernel-certified check that `seen <= expected`, linked via
    /// `clean-kernel-defeq` to `batch_seal_seen_within_expected_isl`.
    #[must_use]
    pub const fn batch_seal_seen_within_expected(seen: u64, expected: u64) -> bool
    clauses [ensures result == (seen <= expected)]
    {
        seen <= expected
    }
}

/// Deterministic 32-bit FNV-1a step over `bytes` starting from `seed` (zero indexing panics).
#[must_use]
pub fn fnv1a32_update(mut hash: u32, mut bytes: &[u8]) -> u32 {
    while let &[b, ref rest @ ..] = bytes {
        hash = (hash ^ (b as u32)).wrapping_mul(FNV32_PRIME);
        bytes = rest;
    }
    hash
}

/// Decode or verification error for `V1BatchSeal`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BatchSealError {
    InvalidLength { got: usize },
    BadMagic,
    EmptyBatch,
    OffsetDiscontinuity { expected: u64, got: u64 },
    TornBatch { seen: u32, expected: u32 },
    OverfullBatch { expected: u32 },
    ChecksumMismatch { expected: u32, got: u32 },
}

/// Fixed 20-byte `"ASB1"` atomic batch seal descriptor.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct V1BatchSeal {
    pub first_offset: u64,
    pub record_count: u32,
    pub checksum32: u32,
}

impl V1BatchSeal {
    #[must_use]
    pub const fn encode(self) -> [u8; V1_BATCH_SEAL_BYTES] {
        let [m0, m1, m2, m3] = V1_BATCH_SEAL_MAGIC;
        let [o0, o1, o2, o3, o4, o5, o6, o7] = self.first_offset.to_be_bytes();
        let [c0, c1, c2, c3] = self.record_count.to_be_bytes();
        let [h0, h1, h2, h3] = self.checksum32.to_be_bytes();
        [
            m0, m1, m2, m3, o0, o1, o2, o3, o4, o5, o6, o7, c0, c1, c2, c3, h0, h1, h2, h3,
        ]
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, BatchSealError> {
        let &[m0, m1, m2, m3, o0, o1, o2, o3, o4, o5, o6, o7, c0, c1, c2, c3, h0, h1, h2, h3] =
            bytes
        else {
            return Err(BatchSealError::InvalidLength { got: bytes.len() });
        };
        if [m0, m1, m2, m3] != V1_BATCH_SEAL_MAGIC {
            return Err(BatchSealError::BadMagic);
        }
        let record_count = u32::from_be_bytes([c0, c1, c2, c3]);
        if record_count == 0 {
            return Err(BatchSealError::EmptyBatch);
        }
        Ok(Self {
            first_offset: u64::from_be_bytes([o0, o1, o2, o3, o4, o5, o6, o7]),
            record_count,
            checksum32: u32::from_be_bytes([h0, h1, h2, h3]),
        })
    }
}

/// Incremental verifier for an `"ASB1"` atomic batch of records.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BatchSealVerifier {
    seal: V1BatchSeal,
    seen_records: u64,
    next_expected_offset: u64,
    running_hash: u32,
}

impl BatchSealVerifier {
    #[must_use]
    pub const fn begin(seal: V1BatchSeal) -> Self {
        Self {
            seal,
            seen_records: 0,
            next_expected_offset: seal.first_offset,
            running_hash: FNV32_OFFSET,
        }
    }

    #[must_use]
    pub const fn seen_records(&self) -> u64 {
        self.seen_records
    }

    /// Observe one record at `offset` with `payload` inside the batch.
    pub fn observe_record(&mut self, offset: u64, payload: &[u8]) -> Result<(), BatchSealError> {
        let expected_u64 = self.seal.record_count as u64;
        if self.seen_records >= expected_u64 {
            return Err(BatchSealError::OverfullBatch {
                expected: self.seal.record_count,
            });
        }
        if offset != self.next_expected_offset {
            return Err(BatchSealError::OffsetDiscontinuity {
                expected: self.next_expected_offset,
                got: offset,
            });
        }
        self.running_hash = fnv1a32_update(self.running_hash, &offset.to_be_bytes());
        self.running_hash = fnv1a32_update(self.running_hash, payload);

        let next_seen = batch_seal_seen_clamp(self.seen_records.saturating_add(1), expected_u64);
        let _ = batch_seal_seen_within_expected(next_seen, expected_u64);
        self.seen_records = next_seen;
        self.next_expected_offset = batch_seal_offset_advance(
            self.next_expected_offset,
            self.next_expected_offset.saturating_add(1),
        );
        Ok(())
    }

    /// Verify that all `record_count` records arrived intact and matched `checksum32`,
    /// returning the exclusive end offset (`first_offset + record_count`).
    pub fn finish(self) -> Result<u64, BatchSealError> {
        if self.seen_records < self.seal.record_count as u64 {
            return Err(BatchSealError::TornBatch {
                seen: self.seen_records as u32,
                expected: self.seal.record_count,
            });
        }
        if self.running_hash != self.seal.checksum32 {
            return Err(BatchSealError::ChecksumMismatch {
                expected: self.seal.checksum32,
                got: self.running_hash,
            });
        }
        Ok(self.next_expected_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn batch_seal_roundtrip_and_torn_tail_detection() {
        let mut h = FNV32_OFFSET;
        h = fnv1a32_update(h, &10u64.to_be_bytes());
        h = fnv1a32_update(h, b"rec-a");
        h = fnv1a32_update(h, &11u64.to_be_bytes());
        h = fnv1a32_update(h, b"rec-b");

        let seal = V1BatchSeal {
            first_offset: 10,
            record_count: 2,
            checksum32: h,
        };
        let decoded = V1BatchSeal::decode(&seal.encode()).expect("valid seal");
        assert_eq!(decoded, seal);

        // Intact 2-record batch succeeds and returns exclusive end offset 12.
        let mut v_ok = BatchSealVerifier::begin(decoded);
        v_ok.observe_record(10, b"rec-a").expect("r0");
        v_ok.observe_record(11, b"rec-b").expect("r1");
        assert_eq!(v_ok.finish(), Ok(12));

        // Torn 1-of-2 batch fails closed with TornBatch.
        let mut v_torn = BatchSealVerifier::begin(decoded);
        v_torn.observe_record(10, b"rec-a").expect("r0");
        assert_eq!(
            v_torn.finish(),
            Err(BatchSealError::TornBatch {
                seen: 1,
                expected: 2,
            })
        );
    }
}
