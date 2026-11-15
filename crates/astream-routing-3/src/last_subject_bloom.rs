// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack 256-bit subject-prefix Bloom filter for O(1) negative `Last` lookups
//! (`Astream.Broker.TlaLastSubjectBloom`).
//!
//! Avoids acquiring/holding `BTreeMap<String, Offset>` scans on misses for
//! structured fabric subjects (`/a/presence/<sid>`, `/a/inbox/<sid>`): indexes
//! the 2-segment subject root (`/seg1/seg2`) into 4 x `u64` words using double
//! FNV-1a hashing (`k = 3`), with zero false negatives and bounded saturation.

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
#[path = "last_subject_bloom_island.rs"]
mod last_subject_bloom_island;
#[cfg(clean_islands)]
pub use last_subject_bloom_island::{bloom_bits_clamp, bloom_gen_advance};

/// Total bits in the stack Bloom filter (`4 * 64 = 256`).
pub const BLOOM_TOTAL_BITS: u64 = 256;

/// Saturation threshold (`192 / 256 = 75%`) recommending rebuild on next compaction.
pub const DEFAULT_SATURATION_BITS: u64 = 192;

const FNV_BASIS_A: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_BASIS_B: u64 = 0x8422_2325_cbf2_9ce4;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[cfg(not(clean_islands))]
/// Monotonically advance the Bloom filter compaction/rebuild generation.
#[must_use]
pub const fn bloom_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Clamp tracked set-bit count to `max_bits`.
#[must_use]
pub const fn bloom_bits_clamp(cand_bits: u64, max_bits: u64) -> u64 {
    if cand_bits < max_bits {
        cand_bits
    } else {
        max_bits
    }
}

contract_fn! {
    /// True iff `set_bits` has reached or exceeded `sat_threshold`.
    #[must_use]
    pub const fn bloom_saturated(sat_threshold: u64, set_bits: u64) -> bool
    clauses [ensures result == (sat_threshold <= set_bits)]
    {
        sat_threshold <= set_bits
    }
}

/// Extract the canonical 2-segment root prefix (e.g. `"/a/inbox/s1"` -> `"/a/inbox"`).
#[must_use]
#[allow(clippy::manual_unwrap_or)]
pub fn canonical_subject_root(subject: &[u8]) -> &[u8] {
    let mut slashes = 0usize;
    let mut idx = 0usize;
    let mut rest = subject;
    while let &[b, ref tail @ ..] = rest {
        if b == b'/' {
            slashes = slashes.saturating_add(1);
            if slashes == 3 {
                return match subject.get(..idx) {
                    Some(s) => s,
                    None => subject,
                };
            }
        }
        idx = idx.saturating_add(1);
        rest = tail;
    }
    subject
}

fn hash_pair(bytes: &[u8]) -> (u64, u64) {
    let mut ha = FNV_BASIS_A;
    let mut hb = FNV_BASIS_B;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        ha = (ha ^ (b as u64)).wrapping_mul(FNV_PRIME);
        hb = (hb ^ ((b ^ 0x5c) as u64)).wrapping_mul(FNV_PRIME);
        rest = tail;
    }
    (ha, hb | 1)
}

const fn bit_indices(ha: u64, hb: u64) -> [usize; 3] {
    [
        (ha & 0xff) as usize,
        (ha.wrapping_add(hb) & 0xff) as usize,
        (ha.wrapping_add(hb.wrapping_mul(2)) & 0xff) as usize,
    ]
}

/// Pure stack 256-bit subject-root Bloom filter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LastSubjectBloom {
    words: [u64; 4],
    set_bits: u64,
    rebuild_gen: u64,
}

impl Default for LastSubjectBloom {
    fn default() -> Self {
        Self::new()
    }
}

impl LastSubjectBloom {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            words: [0; 4],
            set_bits: 0,
            rebuild_gen: 0,
        }
    }

    #[must_use]
    pub const fn set_bits(&self) -> u64 {
        self.set_bits
    }

    #[must_use]
    pub const fn rebuild_gen(&self) -> u64 {
        self.rebuild_gen
    }

    #[must_use]
    pub const fn needs_compaction_rebuild(&self) -> bool {
        bloom_saturated(DEFAULT_SATURATION_BITS, self.set_bits)
    }

    /// Record a published subject's canonical 2-segment root in the filter.
    pub fn insert_subject(&mut self, subject: &[u8]) {
        let root = canonical_subject_root(subject);
        let (ha, hb) = hash_pair(root);
        let probes = bit_indices(ha, hb);
        let mut rest = probes.as_slice();
        while let &[bit, ref tail @ ..] = rest {
            let word_idx = (bit >> 6) & 3;
            let mask = 1u64 << (bit & 63);
            if let Some(w) = self.words.get_mut(word_idx) {
                let prev = *w;
                let next = prev | mask;
                if prev != next {
                    *w = next;
                    let cand = self.set_bits.saturating_add(1);
                    self.set_bits = bloom_bits_clamp(cand, BLOOM_TOTAL_BITS);
                }
            }
            rest = tail;
        }
    }

    /// Returns `false` if NO subject under `query_prefix`'s canonical root exists (zero false negatives).
    #[must_use]
    pub fn may_contain_prefix(&self, query_prefix: &[u8]) -> bool {
        let slashes_in_query = {
            let mut c = 0usize;
            let mut r = query_prefix;
            while let &[b, ref t @ ..] = r {
                if b == b'/' {
                    c = c.saturating_add(1);
                }
                r = t;
            }
            c
        };
        // Short broad queries like "/" or "/a/" could span multiple 2-segment roots -> conservatively true.
        if slashes_in_query < 2 || (slashes_in_query == 2 && matches!(query_prefix, [.., b'/'])) {
            return true;
        }
        let root = canonical_subject_root(query_prefix);
        let (ha, hb) = hash_pair(root);
        let probes = bit_indices(ha, hb);
        let mut rest = probes.as_slice();
        while let &[bit, ref tail @ ..] = rest {
            let word_idx = (bit >> 6) & 3;
            let mask = 1u64 << (bit & 63);
            match self.words.get(word_idx) {
                Some(&w) if (w & mask) != 0 => {}
                _ => return false,
            }
            rest = tail;
        }
        true
    }

    /// Clear and advance `rebuild_gen` during `retain_before` compaction.
    pub fn reset_for_compaction(&mut self) -> u64 {
        self.words = [0; 4];
        self.set_bits = 0;
        let cand = self.rebuild_gen.saturating_add(1);
        self.rebuild_gen = bloom_gen_advance(self.rebuild_gen, cand);
        self.rebuild_gen
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn filters_absent_subject_roots_with_zero_false_negatives() {
        let mut bf = LastSubjectBloom::new();
        bf.insert_subject(b"/a/presence/s-alpha");
        bf.insert_subject(b"/a/will/s-alpha");

        assert!(bf.may_contain_prefix(b"/a/presence/s-alpha"));
        assert!(bf.may_contain_prefix(b"/a/presence/s-other"));
        assert!(bf.may_contain_prefix(b"/a/"));
        assert!(!bf.may_contain_prefix(b"/a/inbox/s-alpha"));

        assert_eq!(bf.reset_for_compaction(), 1);
        assert_eq!(bf.set_bits(), 0);
        assert!(!bf.may_contain_prefix(b"/a/presence/s-alpha"));
    }
}
