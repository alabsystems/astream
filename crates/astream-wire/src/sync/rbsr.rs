// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Range reconciliation works on immutable inventory facts, never authority.
//! Fingerprints summarize content identities supplied by the caller; they do not
//! authenticate records, classify historical sources or replace current permission
//! checks. Unknown metadata may remain in the physical inventory without gaining
//! authority from reconciliation.

use super::{Actor, Digest, Index};
use std::collections::{BTreeMap, BTreeSet};
use std::mem::size_of;
use std::ops::Bound;
use std::sync::{Arc, OnceLock};

/// Bounded, canonical reconciliation messages, independent of transport framing.
pub mod codec;
/// Stateful, transport-independent exchange over immutable inventory snapshots.
pub mod exchange;

/// A malformed range, inconsistent prefix, or impossible fingerprint arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A digest prefix contains bits outside its declared range.
    Range,
    /// A prefix anchor is absent, forked, or differs from the retained dense chain.
    Prefix,
    /// A count overflowed or a subtraction removed more records than were held.
    Count,
    /// A message is malformed, noncanonical, truncated, or exceeds a frame bound.
    Wire,
    /// A message does not match the exchange phase or outstanding request.
    Phase,
    /// The integrating application's explicit work or remote-record budget ran out.
    Budget,
    /// Claimed differences do not conserve the full root count and digest sum.
    Conservation,
}

/// Commutative range summary: digest sum modulo 2^256 and record count.
/// As with any fingerprint, equal summaries are not authority or a proof that
/// arbitrary caller-supplied sets are equal. In particular, short probes must be
/// followed by conservation of the full summary before accepting reconciliation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Fingerprint {
    /// Number of distinct retained identities.
    pub count: u64,
    /// Big-endian sum of identities, with overflow discarded.
    pub sum: Digest,
}

impl Fingerprint {
    /// Combine disjoint inventory summaries.
    /// # Errors
    /// [`Error::Count`] on count overflow.
    pub fn plus(self, other: Self) -> Result<Self, Error> {
        let count = self.count.checked_add(other.count).ok_or(Error::Count)?;
        let mut sum = self.sum;
        let mut carry = 0u16;
        for (slot, byte) in sum.iter_mut().zip(other.sum).rev() {
            let next = u16::from(*slot) + u16::from(byte) + carry;
            *slot = next as u8;
            carry = next >> 8;
        }
        Ok(Self { count, sum })
    }

    /// Remove a known subset's contribution, retaining the full 256-bit sum.
    /// # Errors
    /// [`Error::Count`] if the subset count exceeds the original count.
    pub fn minus(self, subset: Self) -> Result<Self, Error> {
        let count = self.count.checked_sub(subset.count).ok_or(Error::Count)?;
        let mut sum = self.sum;
        let mut borrow = 0u16;
        for (slot, byte) in sum.iter_mut().zip(subset.sum).rev() {
            let left = u16::from(*slot);
            let right = u16::from(byte) + borrow;
            *slot = left.wrapping_sub(right) as u8;
            borrow = u16::from(left < right);
        }
        Ok(Self { count, sum })
    }

    /// Count and low 32 bits for a compact range probe. This alone never closes
    /// reconciliation: full-summary conservation detects omitted differences.
    #[must_use]
    pub fn probe(self) -> (u64, [u8; 4]) {
        (
            self.count,
            [self.sum[28], self.sum[29], self.sum[30], self.sum[31]],
        )
    }
}

/// A canonical hexadecimal digest prefix, from the whole space to one identity.
/// Each nonterminal range splits into sixteen disjoint children.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Range {
    prefix: Digest,
    nibbles: u8,
}

impl Range {
    /// The entire digest space.
    pub const ROOT: Self = Self {
        prefix: [0; 32],
        nibbles: 0,
    };

    /// Construct a range with zero bits beyond its declared prefix.
    /// # Errors
    /// [`Error::Range`] on a depth over 64 or noncanonical trailing bits.
    pub fn new(prefix: Digest, nibbles: u8) -> Result<Self, Error> {
        if nibbles > 64 {
            return Err(Error::Range);
        }
        let bytes = usize::from(nibbles / 2);
        let tail = if nibbles % 2 == 1 {
            if prefix[bytes] & 15 != 0 {
                return Err(Error::Range);
            }
            bytes + 1
        } else {
            bytes
        };
        if prefix[tail..].iter().any(|byte| *byte != 0) {
            return Err(Error::Range);
        }
        Ok(Self { prefix, nibbles })
    }

    /// Canonical lower inclusive endpoint and hexadecimal depth.
    #[must_use]
    pub const fn prefix(self) -> (Digest, u8) {
        (self.prefix, self.nibbles)
    }

    /// Exclusive upper endpoint; `None` is the end of the digest space.
    #[must_use]
    pub fn upper(self) -> Option<Digest> {
        if self.nibbles == 0 {
            return None;
        }
        let mut upper = self.prefix;
        let mut nibble = usize::from(self.nibbles);
        while nibble > 0 {
            nibble -= 1;
            let shift = if nibble % 2 == 0 { 4 } else { 0 };
            let byte = &mut upper[nibble / 2];
            if (*byte >> shift) & 15 != 15 {
                *byte += 1 << shift;
                return Some(upper);
            }
            *byte &= !(15 << shift);
        }
        None
    }

    /// Sixteen disjoint children in digest order, or `None` at one identity.
    #[must_use]
    pub fn children(self) -> Option<[Self; 16]> {
        if self.nibbles == 64 {
            return None;
        }
        Some(std::array::from_fn(|child| {
            let mut prefix = self.prefix;
            let byte = usize::from(self.nibbles / 2);
            let shift = if self.nibbles % 2 == 0 { 4 } else { 0 };
            prefix[byte] |= (child as u8) << shift;
            Self {
                prefix,
                nibbles: self.nibbles + 1,
            }
        }))
    }

    /// Whether the identity belongs to this range.
    #[must_use]
    pub fn contains(self, id: &Digest) -> bool {
        *id >= self.prefix && self.upper().is_none_or(|upper| *id < upper)
    }
}

/// A dense, unforked actor-prefix anchor. A sequence watermark without its exact
/// content identity cannot distinguish signed forks or prove a shared prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Frontier {
    /// Writer identity and installation incarnation.
    pub actor: Actor,
    /// Last sequence in the dense prefix.
    pub sequence: u64,
    /// Content identity of that sequence, committing its previous-link chain.
    pub id: Digest,
}

/// An immutable inventory and the dense, unforked actor prefixes it proves.
/// Applications can reuse these physical facts while revalidating permission
/// separately at every access boundary.
#[derive(Clone, Debug)]
pub struct Snapshot {
    ids: Arc<[Digest]>,
    fingerprint: OnceLock<Fingerprint>,
    prefixes: Vec<(Actor, Vec<(u64, Digest)>)>,
    // Only identities outside the dense chains. Retaining this partition once
    // lets a round build the remaining suffixes without cloning a shared prefix.
    unprefixed: Vec<Digest>,
}

impl Snapshot {
    /// Generic content inventory, without any actor-prefix optimization.
    #[must_use]
    pub fn new(ids: BTreeSet<Digest>) -> Self {
        Self {
            ids: ids.into_iter().collect(),
            fingerprint: OnceLock::new(),
            prefixes: Vec::new(),
            unprefixed: Vec::new(),
        }
    }

    /// Retain every index identity, including forks and pending records. Only a
    /// dense previous-link chain from sequence one of an unforked actor may be
    /// used by the frontier pre-exchange; later records after a gap remain ranges.
    #[must_use]
    pub fn from_index(index: &Index) -> Self {
        Self::from_inventory(index.inventory().copied().collect(), index)
    }

    /// Reconcile exactly `ids`, using the index only for available header facts.
    /// An application index may omit records awaiting membership and include
    /// restrictive certificate-source headers whose payloads are not held.
    /// Unknown metadata leaves an identity in range reconciliation; additional
    /// index headers never create payload inventory. Their fork evidence still
    /// disables the affected actor's prefix optimization.
    #[must_use]
    pub fn from_inventory(ids: BTreeSet<Digest>, index: &Index) -> Self {
        let forks = index.forks();
        let mut actors = BTreeMap::<Actor, BTreeMap<u64, &super::Header>>::new();
        let mut unprefixed = BTreeSet::new();
        let mut known = index.records.values().peekable();
        for id in &ids {
            while known.peek().is_some_and(|header| header.id < *id) {
                known.next();
            }
            if let Some(header) = known
                .peek()
                .copied()
                .filter(|header| header.id == *id && !forks.contains_key(&header.actor))
            {
                actors
                    .entry(header.actor)
                    .or_default()
                    .insert(header.sequence, header);
            } else {
                unprefixed.insert(*id);
            }
        }
        let mut prefixes = Vec::new();
        for (actor, records) in actors {
            let mut held = Vec::new();
            let mut next = Some((1, None));
            for (sequence, header) in records {
                if next.is_some_and(|(expected, previous)| {
                    sequence == expected && header.previous == previous
                }) {
                    held.push((sequence, header.id));
                    next = sequence
                        .checked_add(1)
                        .map(|sequence| (sequence, Some(header.id)));
                } else {
                    unprefixed.insert(header.id);
                    next = None;
                }
            }
            if !held.is_empty() {
                prefixes.push((actor, held));
            }
        }
        if prefixes.is_empty() {
            return Self::new(ids);
        }
        Self {
            ids: ids.into_iter().collect(),
            fingerprint: OnceLock::new(),
            prefixes,
            unprefixed: unprefixed.into_iter().collect(),
        }
    }

    /// Every retained identity in sorted order.
    pub fn ids(&self) -> impl Iterator<Item = &Digest> {
        self.ids.iter()
    }

    /// Storage retained by the snapshot value, its shared identity slice and its
    /// vector capacities, saturating on overflow. Shared identity storage is
    /// charged in full. Allocator bookkeeping and sharing headers are excluded;
    /// a cache must include those in its fixed per-entry overhead.
    #[must_use]
    pub fn retained_bytes(&self) -> usize {
        let mut bytes = size_of::<Self>()
            .saturating_add(self.ids.len().saturating_mul(size_of::<Digest>()))
            .saturating_add(
                self.prefixes
                    .capacity()
                    .saturating_mul(size_of::<(Actor, Vec<(u64, Digest)>)>()),
            )
            .saturating_add(
                self.unprefixed
                    .capacity()
                    .saturating_mul(size_of::<Digest>()),
            );
        for (_, prefix) in &self.prefixes {
            bytes =
                bytes.saturating_add(prefix.capacity().saturating_mul(size_of::<(u64, Digest)>()));
        }
        bytes
    }

    fn contains(&self, id: &Digest) -> bool {
        self.ids.binary_search(id).is_ok()
    }

    fn range_ids(&self, lo: Bound<Digest>, hi: Bound<Digest>) -> &[Digest] {
        let start = match lo {
            Bound::Unbounded => 0,
            Bound::Included(lo) => self.ids.partition_point(|id| *id < lo),
            Bound::Excluded(lo) => self.ids.partition_point(|id| *id <= lo),
        };
        let end = match hi {
            Bound::Unbounded => self.ids.len(),
            Bound::Included(hi) => self.ids.partition_point(|id| *id <= hi),
            Bound::Excluded(hi) => self.ids.partition_point(|id| *id < hi),
        };
        &self.ids[start..end]
    }

    fn prefix_id(&self, actor: &Actor, sequence: u64) -> Option<&Digest> {
        let actor = self
            .prefixes
            .binary_search_by(|(candidate, _)| candidate.cmp(actor))
            .ok()?;
        let prefix = &self.prefixes[actor].1;
        let position = prefix
            .binary_search_by_key(&sequence, |(sequence, _)| *sequence)
            .ok()?;
        Some(&prefix[position].1)
    }

    /// Full immutable inventory summary, reused across rounds without rescanning
    /// unchanged history. This is a physical fact, never a permission verdict.
    /// # Errors
    /// [`Error::Count`] if the inventory count overflows.
    pub fn fingerprint(&self) -> Result<Fingerprint, Error> {
        if let Some(fingerprint) = self.fingerprint.get() {
            return Ok(*fingerprint);
        }
        let fingerprint = self.range_fingerprint(None, None)?;
        // Concurrent readers compute the same immutable summary; either can install it.
        let _ = self.fingerprint.set(fingerprint);
        Ok(fingerprint)
    }

    /// Sum and count in `[lo, hi)`, with `None` for an unbounded endpoint.
    /// # Errors
    /// [`Error::Range`] for reversed endpoints; [`Error::Count`] on overflow.
    pub fn range_fingerprint(
        &self,
        lo: Option<Digest>,
        hi: Option<Digest>,
    ) -> Result<Fingerprint, Error> {
        if lo.zip(hi).is_some_and(|(lo, hi)| lo > hi) {
            return Err(Error::Range);
        }
        let bounds = (
            lo.map_or(Bound::Unbounded, Bound::Included),
            hi.map_or(Bound::Unbounded, Bound::Excluded),
        );
        self.range_ids(bounds.0, bounds.1)
            .iter()
            .try_fold(Fingerprint::default(), |sum, id| {
                sum.plus(Fingerprint { count: 1, sum: *id })
            })
    }

    /// One anchor per actor with a provable dense, unforked prefix.
    pub fn frontiers(&self) -> impl Iterator<Item = Frontier> + '_ {
        self.prefixes.iter().filter_map(|(actor, prefix)| {
            prefix.last().map(|(sequence, id)| Frontier {
                actor: *actor,
                sequence: *sequence,
                id: *id,
            })
        })
    }

    /// Peer anchors this snapshot can independently prove. Exchange the union of
    /// both peers' proposals before excluding any prefix; a peer with a shorter
    /// chain cannot itself prove the other peer's higher anchor.
    /// # Errors
    /// [`Error::Prefix`] if peer anchors are repeated or not sorted by actor.
    pub fn shared_prefixes(&self, peer: &[Frontier]) -> Result<Vec<Frontier>, Error> {
        if peer.windows(2).any(|pair| pair[0].actor >= pair[1].actor) {
            return Err(Error::Prefix);
        }
        Ok(peer
            .iter()
            .filter(|anchor| self.prefix_id(&anchor.actor, anchor.sequence) == Some(&anchor.id))
            .copied()
            .collect())
    }

    /// Exclude independently checked shared prefixes from range reconciliation.
    /// Every other identity, including gapped and forked history, remains.
    /// # Errors
    /// [`Error::Prefix`] for unordered, repeated, absent or inconsistent anchors.
    pub fn without_prefixes(&self, shared: &[Frontier]) -> Result<Self, Error> {
        if shared.windows(2).any(|pair| pair[0].actor >= pair[1].actor) {
            return Err(Error::Prefix);
        }
        for anchor in shared {
            if self.prefix_id(&anchor.actor, anchor.sequence) != Some(&anchor.id) {
                return Err(Error::Prefix);
            }
        }
        if shared.is_empty() {
            return Ok(Self {
                ids: Arc::clone(&self.ids),
                fingerprint: self.fingerprint.clone(),
                prefixes: Vec::new(),
                unprefixed: Vec::new(),
            });
        }
        let cuts: BTreeMap<_, _> = shared
            .iter()
            .map(|anchor| (anchor.actor, anchor.sequence))
            .collect();
        let mut ids: BTreeSet<_> = self.unprefixed.iter().copied().collect();
        for (actor, prefix) in &self.prefixes {
            let after = cuts.get(actor).copied().unwrap_or(0);
            let start = prefix.partition_point(|(sequence, _)| *sequence <= after);
            ids.extend(prefix[start..].iter().map(|(_, id)| *id));
        }
        Ok(Self::new(ids))
    }
}

#[cfg(test)]
#[path = "rbsr_tests.rs"]
mod tests;
