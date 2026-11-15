// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Canonical Multi-Shard Causal Vector Clock (`"ASC1"`, `Astream.Broker.TlaCausalVectorClock`).
//!
//! When `aterm` worker sessions coordinate across a `ShardedBroker` or federated multi-log
//! topology, causal dependencies span multiple independent `(shard_id, log_offset)` timelines.
//! [`V1ShardClock`] carries a canonical, strictly sorted, duplicate-free vector of up to
//! [`MAX_SHARD_CLOCK_ENTRIES`] `(shard_id: u32, witnessed_offset: u64)` coordinates:
//! - Componentwise lattice join ([`V1ShardClock::merge`]) advances each shard's offset via
//!   Clean-origin [`vclock_offset_advance`] while bounding total entries via Clean-origin
//!   [`vclock_entries_clamp`].
//! - [`V1ShardClock::dominates`] decides whether local shard progress satisfies every causal
//!   precondition in an incoming message's vector clock.
//! - Written strictly with slice-pattern destructuring (`while let &[first, ref rest @ ..]`) and
//!   constant-capacity `Vec` constructors so `astream-wire` preserves `0` new `runtime_checked`
//!   and `0 mandated` obligations.

#[cfg(clean_islands)]
#[path = "causal_barrier_island.rs"]
mod causal_barrier_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn vclock_entries_clamp(cand_entries: u64, max_entries: u64) -> u64 {
    if cand_entries < max_entries {
        cand_entries
    } else {
        max_entries
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn vclock_offset_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}
#[cfg(clean_islands)]
pub use causal_barrier_island::{vclock_entries_clamp, vclock_offset_advance};

/// 4-byte wire magic (`"ASC1"`) for [`V1ShardClock`].
pub const SHARD_CLOCK_MAGIC: [u8; 4] = *b"ASC1";

/// Maximum `(shard_id, offset)` pairs carried in one [`V1ShardClock`] envelope.
pub const MAX_SHARD_CLOCK_ENTRIES: usize = 64;

contract_fn! {
    /// Kernel-certified check that `count <= max_entries`, linked via `clean-kernel-defeq`
    /// to `vclock_entries_within_cap_isl`.
    #[must_use]
    pub const fn vclock_entries_within_cap(count: u64, max_entries: u64) -> bool
    clauses [ensures result == (count <= max_entries)]
    {
        count <= max_entries
    }
}

/// Single `(shard_id, offset)` coordinate inside a [`V1ShardClock`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardClockEntry {
    pub shard_id: u32,
    pub offset: u64,
}

/// Wire/validation errors for [`V1ShardClock`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShardClockError {
    /// Frame ended before header or declared entries finished, or trailing bytes remained.
    TruncatedOrTrailing,
    /// Leading 4 bytes did not match [`SHARD_CLOCK_MAGIC`].
    BadMagic,
    /// Reserved header byte was non-zero.
    NonZeroReserved,
    /// Entry count exceeded [`MAX_SHARD_CLOCK_ENTRIES`].
    TooManyEntries,
    /// Decoded `(shard_id, offset)` entries were unsorted or contained duplicate `shard_id`s.
    NotStrictlySorted,
}

/// Canonical strictly-sorted vector clock over up to [`MAX_SHARD_CLOCK_ENTRIES`] broker shards.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct V1ShardClock {
    entries: Vec<ShardClockEntry>,
}

impl V1ShardClock {
    /// Empty causal vector clock (`0` shards witnessed).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Borrow the strictly sorted `(shard_id, offset)` slice.
    #[must_use]
    pub fn entries(&self) -> &[ShardClockEntry] {
        &self.entries
    }

    /// Lookup witnessed offset for `shard_id`, if present.
    #[must_use]
    pub fn offset_for(&self, shard_id: u32) -> Option<u64> {
        let mut cur = self.entries.as_slice();
        while let &[head, ref rest @ ..] = cur {
            if head.shard_id == shard_id {
                return Some(head.offset);
            }
            if head.shard_id > shard_id {
                return None;
            }
            cur = rest;
        }
        None
    }

    /// Witness `(shard_id, cand_offset)`, advancing monotonically via [`vclock_offset_advance`]
    /// if `shard_id` is already present, or inserting in sorted order up to
    /// [`MAX_SHARD_CLOCK_ENTRIES`].
    pub fn witness(&mut self, shard_id: u32, cand_offset: u64) -> Result<u64, ShardClockError> {
        let mut out = Vec::new();
        let mut inserted = false;
        let mut resulting_offset = cand_offset;
        let mut cur = self.entries.as_slice();

        while let &[head, ref rest @ ..] = cur {
            if !inserted && shard_id == head.shard_id {
                let merged = vclock_offset_advance(head.offset, cand_offset);
                resulting_offset = merged;
                out.push(ShardClockEntry {
                    shard_id,
                    offset: merged,
                });
                inserted = true;
            } else if !inserted && shard_id < head.shard_id {
                if !vclock_entries_within_cap(
                    (self.entries.len() as u64).saturating_add(1),
                    MAX_SHARD_CLOCK_ENTRIES as u64,
                ) {
                    return Err(ShardClockError::TooManyEntries);
                }
                out.push(ShardClockEntry {
                    shard_id,
                    offset: cand_offset,
                });
                out.push(head);
                inserted = true;
            } else {
                out.push(head);
            }
            cur = rest;
        }

        if !inserted {
            if !vclock_entries_within_cap(
                (self.entries.len() as u64).saturating_add(1),
                MAX_SHARD_CLOCK_ENTRIES as u64,
            ) {
                return Err(ShardClockError::TooManyEntries);
            }
            out.push(ShardClockEntry {
                shard_id,
                offset: cand_offset,
            });
        }

        self.entries = out;
        Ok(resulting_offset)
    }

    /// Componentwise lattice join (`self := max(self, other)`), failing closed if the union
    /// exceeds [`MAX_SHARD_CLOCK_ENTRIES`].
    pub fn merge(&self, other: &Self) -> Result<Self, ShardClockError> {
        let mut out = Vec::new();
        let mut a = self.entries.as_slice();
        let mut b = other.entries.as_slice();

        loop {
            match (a.split_first(), b.split_first()) {
                (Some((&ha, ra)), Some((&hb, rb))) => {
                    if ha.shard_id == hb.shard_id {
                        out.push(ShardClockEntry {
                            shard_id: ha.shard_id,
                            offset: vclock_offset_advance(ha.offset, hb.offset),
                        });
                        a = ra;
                        b = rb;
                    } else if ha.shard_id < hb.shard_id {
                        out.push(ha);
                        a = ra;
                    } else {
                        out.push(hb);
                        b = rb;
                    }
                }
                (Some((&ha, ra)), None) => {
                    out.push(ha);
                    a = ra;
                }
                (None, Some((&hb, rb))) => {
                    out.push(hb);
                    b = rb;
                }
                (None, None) => break,
            }
            if !vclock_entries_within_cap(out.len() as u64, MAX_SHARD_CLOCK_ENTRIES as u64) {
                return Err(ShardClockError::TooManyEntries);
            }
        }

        Ok(Self { entries: out })
    }

    /// Returns `true` iff for every `(shard_id, req_offset)` in `required`, `self` has witnessed
    /// `shard_id` at an offset `>= req_offset`.
    #[must_use]
    pub fn dominates(&self, required: &Self) -> bool {
        let mut a = self.entries.as_slice();
        let mut b = required.entries.as_slice();

        while let &[req, ref rb @ ..] = b {
            let mut matched = false;
            while let &[loc, ref ra @ ..] = a {
                if loc.shard_id < req.shard_id {
                    a = ra;
                    continue;
                }
                if loc.shard_id == req.shard_id {
                    if loc.offset < req.offset {
                        return false;
                    }
                    a = ra;
                    matched = true;
                }
                break;
            }
            if !matched {
                return false;
            }
            b = rb;
        }
        true
    }

    /// Encode into canonical `"ASC1"` bytes:
    /// `magic[4] || count_u16_le[2] || reserved_zero[2] || count * (shard_u32_le[4] || offset_u64_le[8])`.
    pub fn encode(&self) -> Result<Vec<u8>, ShardClockError> {
        let clamped =
            vclock_entries_clamp(self.entries.len() as u64, MAX_SHARD_CLOCK_ENTRIES as u64);
        if (self.entries.len() as u64) != clamped {
            return Err(ShardClockError::TooManyEntries);
        }

        let mut out = Vec::new();
        out.extend_from_slice(&SHARD_CLOCK_MAGIC);
        out.extend_from_slice(&(self.entries.len() as u16).to_le_bytes());
        out.extend_from_slice(&[0u8, 0u8]);

        let mut prev_shard: Option<u32> = None;
        let mut cur = self.entries.as_slice();
        while let &[entry, ref rest @ ..] = cur {
            if let Some(prev) = prev_shard {
                if entry.shard_id <= prev {
                    return Err(ShardClockError::NotStrictlySorted);
                }
            }
            prev_shard = Some(entry.shard_id);
            out.extend_from_slice(&entry.shard_id.to_le_bytes());
            out.extend_from_slice(&entry.offset.to_le_bytes());
            cur = rest;
        }
        Ok(out)
    }

    /// Decode a canonical `"ASC1"` frame, failing closed on unsorted shards, non-zero reserved
    /// bytes, oversize counts, or trailing garbage.
    pub fn decode(buf: &[u8]) -> Result<Self, ShardClockError> {
        let &[m0, m1, m2, m3, c0, c1, r0, r1, ref tail_init @ ..] = buf else {
            return Err(ShardClockError::TruncatedOrTrailing);
        };
        let mut cur = tail_init;
        if [m0, m1, m2, m3] != SHARD_CLOCK_MAGIC {
            return Err(ShardClockError::BadMagic);
        }
        if r0 != 0 || r1 != 0 {
            return Err(ShardClockError::NonZeroReserved);
        }
        let declared = u16::from_le_bytes([c0, c1]) as u64;
        if !vclock_entries_within_cap(declared, MAX_SHARD_CLOCK_ENTRIES as u64) {
            return Err(ShardClockError::TooManyEntries);
        }

        let mut entries = Vec::new();
        let mut prev_shard: Option<u32> = None;
        let mut read_count = 0u64;
        while read_count < declared {
            let &[s0, s1, s2, s3, o0, o1, o2, o3, o4, o5, o6, o7, ref rest @ ..] = cur else {
                return Err(ShardClockError::TruncatedOrTrailing);
            };
            let shard_id = u32::from_le_bytes([s0, s1, s2, s3]);
            let offset = u64::from_le_bytes([o0, o1, o2, o3, o4, o5, o6, o7]);
            if let Some(prev) = prev_shard {
                if shard_id <= prev {
                    return Err(ShardClockError::NotStrictlySorted);
                }
            }
            prev_shard = Some(shard_id);
            entries.push(ShardClockEntry { shard_id, offset });
            cur = rest;
            read_count = read_count.saturating_add(1);
        }
        if !cur.is_empty() {
            return Err(ShardClockError::TruncatedOrTrailing);
        }
        Ok(Self { entries })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sorted_witness_merge_dominates_and_wire_roundtrip() {
        let mut c1 = V1ShardClock::new();
        assert_eq!(c1.witness(4, 100), Ok(100));
        assert_eq!(c1.witness(1, 50), Ok(50));
        // Stale witness on shard 4 stays at 100.
        assert_eq!(c1.witness(4, 80), Ok(100));

        let mut c2 = V1ShardClock::new();
        assert_eq!(c2.witness(1, 75), Ok(75));
        assert_eq!(c2.witness(2, 10), Ok(10));

        assert!(!c1.dominates(&c2));
        let joined = c1.merge(&c2).expect("merge within 64 shards");
        assert!(joined.dominates(&c1));
        assert!(joined.dominates(&c2));
        assert_eq!(joined.offset_for(1), Some(75));
        assert_eq!(joined.offset_for(2), Some(10));
        assert_eq!(joined.offset_for(4), Some(100));

        let bytes = joined.encode().expect("encode");
        let decoded = V1ShardClock::decode(&bytes).expect("decode");
        assert_eq!(decoded, joined);
    }

    #[test]
    fn decode_rejects_unsorted_duplicate_or_trailing_bytes() {
        let mut raw = Vec::new();
        raw.extend_from_slice(&SHARD_CLOCK_MAGIC);
        raw.extend_from_slice(&2u16.to_le_bytes());
        raw.extend_from_slice(&[0u8, 0u8]);
        raw.extend_from_slice(&5u32.to_le_bytes());
        raw.extend_from_slice(&10u64.to_le_bytes());
        raw.extend_from_slice(&5u32.to_le_bytes());
        raw.extend_from_slice(&20u64.to_le_bytes());
        assert_eq!(
            V1ShardClock::decode(&raw),
            Err(ShardClockError::NotStrictlySorted)
        );
    }
}
