// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A set of entries under one 2,048-byte hash that follows what changed.
//!
//! The lattice set hash of Bellare and Micciancio in the LtHash16-1024 parameters: 1,024
//! lanes of 16 bits. An entry's digest is expanded to 2,048 bytes, sixty-four hashes of
//! `"astream/sync/sethash/1" ‖ digest ‖ block`, and added to the lanes, or subtracted from
//! them, lane by lane modulo 2^16. So one entry is added or removed with the same work at
//! any set size, the hash of a set is the same in whatever order it was built, and the hash
//! of two disjoint sets is the lane-wise sum of theirs ([`SetHash::plus_set`]), which lets a
//! fold be split by key across threads.
//!
//! It hashes a set, never a multiset: an entry added 65,536 times sums to zero in every
//! lane. The caller holds its entries in a map with unique keys, adds an entry only when it
//! enters that map and removes it only when it leaves, and carries the entry count beside the
//! hash wherever the hash is signed.
//!
//! A commitment, not authority: equal hashes say two sets of entries are the same, and
//! nothing about who may write them. The caller supplies the hash (this crate has none),
//! which is SHA-256 wherever a hash leaves the machine. Nothing here counts entries, reads a
//! clock or does I/O.

use super::Digest;

/// The hash that expands an entry and names a state: SHA-256 wherever a hash leaves the
/// machine. The integrating application supplies it, as it computes every [`Digest`] this
/// crate holds.
pub type Hasher = fn(&[u8]) -> Digest;

/// Lanes of 16 bits in a set hash.
pub const LANES: usize = 1024;

/// A set hash's bytes: each lane little-endian, in lane order.
pub const BYTES: usize = 2 * LANES;

/// Leads every expansion block. With a digest and a block number it is 55 bytes, one
/// SHA-256 block with its padding.
const EXPAND: &[u8; 22] = b"astream/sync/sethash/1";

/// Leads the bytes [`SetHash::digest`] hashes.
const STATE: &[u8; 28] = b"astream/sync/sethash/state/1";

const BLOCKS: usize = BYTES / size_of::<Digest>();
const BLOCK_LANES: usize = size_of::<Digest>() / 2;

/// The hash of a set of entry digests. [`SetHash::EMPTY`] is the empty set's.
#[derive(Clone, PartialEq, Eq)]
pub struct SetHash {
    lanes: [u16; LANES],
}

impl std::fmt::Debug for SetHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let live = self.lanes.iter().filter(|lane| **lane != 0).count();
        write!(f, "SetHash({live} of {LANES} lanes set)")
    }
}

impl Default for SetHash {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl SetHash {
    /// The hash of the set with no entries: every lane zero.
    pub const EMPTY: Self = Self { lanes: [0; LANES] };

    /// Add `entry`, which the set does not hold.
    pub fn plus(&mut self, hash: Hasher, entry: &Digest) {
        expand(
            hash,
            entry,
            |lane, word| *lane = lane.wrapping_add(word),
            &mut self.lanes,
        );
    }

    /// Remove `entry`, which the set holds.
    pub fn minus(&mut self, hash: Hasher, entry: &Digest) {
        expand(
            hash,
            entry,
            |lane, word| *lane = lane.wrapping_sub(word),
            &mut self.lanes,
        );
    }

    /// Add every entry of `other`, a set that shares none with this one.
    pub fn plus_set(&mut self, other: &Self) {
        for (lane, word) in self.lanes.iter_mut().zip(&other.lanes) {
            *lane = lane.wrapping_add(*word);
        }
    }

    /// Remove every entry of `other`, a set this one contains.
    pub fn minus_set(&mut self, other: &Self) {
        for (lane, word) in self.lanes.iter_mut().zip(&other.lanes) {
            *lane = lane.wrapping_sub(*word);
        }
    }

    /// The 2,048 bytes: what a floor file stores and two machines compare.
    #[must_use]
    pub fn to_bytes(&self) -> [u8; BYTES] {
        let mut bytes = [0; BYTES];
        for (pair, lane) in bytes.as_chunks_mut::<2>().0.iter_mut().zip(&self.lanes) {
            *pair = lane.to_le_bytes();
        }
        bytes
    }

    /// The hash those bytes are. Every 2,048 bytes are some lanes, so this refuses nothing:
    /// whether they are the hash of the set the caller holds is the caller's comparison.
    #[must_use]
    pub fn from_bytes(bytes: &[u8; BYTES]) -> Self {
        let mut lanes = [0; LANES];
        for (lane, pair) in lanes.iter_mut().zip(bytes.as_chunks::<2>().0) {
            *lane = u16::from_le_bytes(*pair);
        }
        Self { lanes }
    }

    /// A 32-byte name of the hash, for a signed body that has no room for 2,048 bytes.
    #[must_use]
    pub fn digest(&self, hash: Hasher) -> Digest {
        let mut bytes = Vec::with_capacity(STATE.len() + BYTES);
        bytes.extend_from_slice(STATE);
        bytes.extend_from_slice(&self.to_bytes());
        hash(&bytes)
    }
}

/// Apply `step` to each lane with the word of `entry`'s expansion that falls on it.
fn expand(hash: Hasher, entry: &Digest, step: fn(&mut u16, u16), lanes: &mut [u16; LANES]) {
    let mut input = [0u8; EXPAND.len() + size_of::<Digest>() + 1];
    let (domain, rest) = input.split_at_mut(EXPAND.len());
    domain.copy_from_slice(EXPAND);
    // `rest` is the digest's 32 bytes and the block byte: the entry fills the first 32.
    for (slot, byte) in rest.iter_mut().zip(entry) {
        *slot = *byte;
    }
    // Sixty-four blocks of sixteen lanes, so the block number is one byte.
    for (block, lanes) in (0u8..).zip(lanes.as_chunks_mut::<BLOCK_LANES>().0) {
        if let Some(last) = input.last_mut() {
            *last = block;
        }
        let words = hash(&input);
        for (lane, pair) in lanes.iter_mut().zip(words.as_chunks::<2>().0) {
            step(lane, u16::from_le_bytes(*pair));
        }
    }
}

const _: () = assert!(BLOCKS == 64 && BLOCKS * BLOCK_LANES == LANES);

#[cfg(test)]
#[path = "sethash_tests.rs"]
mod tests;
