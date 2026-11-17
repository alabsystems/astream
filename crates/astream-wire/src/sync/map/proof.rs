// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A proof says one row lies under one root. It is evidence about a root the reader
//! already trusts, never a reason to trust a root: the reader compares the root the
//! proof folds to with the one it holds.

use super::page::{self, Entry};
use super::{nibble, Digest, Error, Hasher, LEAF_ROWS, LEVELS, VALUE_BYTES};

const MAGIC: [u8; 5] = *b"ATPF1";
/// Magic, level count, leaf row count, the row's place, key and value length.
const HEADER: usize = 5 + 3 + 32 + 2;
/// Fifteen siblings of a hash and a row count each.
const LEVEL: usize = 15 * 40;

/// One row, the hashes of the other rows of its leaf, and the fifteen siblings of each
/// interior page above it: the row itself and 600 bytes a level, whatever the other rows hold.
///
/// Format `ATPF1`, every number big-endian: `"ATPF1"`, `u8` interior levels, `u8` rows in
/// the leaf, `u8` place of the row among them, key 32, `u16` length, value, each other
/// row's hash in key order, then for each level from the root down the fifteen other
/// children in nibble order as (hash 32, row count `u64`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub(super) key: Digest,
    pub(super) value: Vec<u8>,
    /// The row's place among its leaf's rows; at most `others.len()`.
    pub(super) at: usize,
    pub(super) others: Vec<Digest>,
    /// Root first.
    pub(super) levels: Vec<[Entry; 15]>,
}

impl Proof {
    /// The key of the row proved.
    #[must_use]
    pub const fn key(&self) -> &Digest {
        &self.key
    }

    /// The value of the row proved.
    #[must_use]
    pub fn value(&self) -> &[u8] {
        &self.value
    }

    /// The root this row lies under and the rows under that root: compare both with a
    /// root held from elsewhere. Under a root computed from a [`super::Map`], or from
    /// pages one admitted, a key has one row. The proof alone does not show that: the
    /// leaf's other rows travel as hashes, so nothing here reads their keys or order.
    /// # Errors
    /// [`Error::Count`] if the row counts overflow; [`Error::Proof`] for a proof built
    /// outside [`Proof::decode`] and [`super::Map::prove`] that breaks their bounds.
    pub fn root(&self, hasher: Hasher) -> Result<(Digest, u64), Error> {
        if self.levels.len() > LEVELS || self.others.len() >= LEAF_ROWS {
            return Err(Error::Proof);
        }
        let row = hasher(&page::row(&self.key, &self.value));
        let (before, after) = self.others.split_at_checked(self.at).ok_or(Error::Proof)?;
        let hashes = before.iter().chain(std::iter::once(&row)).chain(after);
        let mut rows = (self.others.len() as u64).saturating_add(1);
        let mut hash = hasher(&page::leaf_hashed(
            self.others.len().saturating_add(1),
            hashes,
        ));
        for (depth, level) in self.levels.iter().enumerate().rev() {
            let at = nibble(&self.key, depth);
            let mut siblings = level.iter();
            let mut children = [([0; 32], 0); 16];
            for (index, child) in children.iter_mut().enumerate() {
                *child = if index == at {
                    (hash, rows)
                } else {
                    siblings.next().copied().ok_or(Error::Proof)?
                };
            }
            rows = children
                .iter()
                .try_fold(0u64, |sum, (_, count)| sum.checked_add(*count))
                .ok_or(Error::Count)?;
            hash = hasher(&page::interior(&children));
        }
        Ok((hash, rows))
    }

    /// The proof's one encoding.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&MAGIC);
        out.push(u8::try_from(self.levels.len()).unwrap_or(u8::MAX));
        out.push(u8::try_from(self.others.len().saturating_add(1)).unwrap_or(u8::MAX));
        out.push(u8::try_from(self.at).unwrap_or(u8::MAX));
        out.extend_from_slice(&page::row(&self.key, &self.value));
        for hash in &self.others {
            out.extend_from_slice(hash);
        }
        for (hash, rows) in self.levels.iter().flatten() {
            out.extend_from_slice(hash);
            out.extend_from_slice(&rows.to_be_bytes());
        }
        out
    }

    /// Read a proof of at most `limit` bytes. Its length, its level count against
    /// [`LEVELS`] and its leaf against [`LEAF_ROWS`] are checked before anything is
    /// allocated or hashed.
    /// # Errors
    /// [`Error::Budget`] past `limit`; [`Error::Proof`] for bytes that are not one
    /// canonical proof.
    pub fn decode(bytes: &[u8], limit: usize) -> Result<Self, Error> {
        if bytes.len() > limit {
            return Err(Error::Budget);
        }
        let (header, body) = bytes.split_at_checked(HEADER).ok_or(Error::Proof)?;
        let (magic, header) = header.split_at_checked(5).ok_or(Error::Proof)?;
        let (&[levels, rows, at], header) = header.split_first_chunk().ok_or(Error::Proof)?;
        let (key, length) = header.split_first_chunk::<32>().ok_or(Error::Proof)?;
        let length = usize::from(u16::from_be_bytes(
            length.try_into().map_err(|_| Error::Proof)?,
        ));
        let (levels, rows, at) = (usize::from(levels), usize::from(rows), usize::from(at));
        if magic != MAGIC || levels > LEVELS || rows == 0 || rows > LEAF_ROWS || at >= rows {
            return Err(Error::Proof);
        }
        let others = rows.saturating_sub(1);
        if length > VALUE_BYTES
            || body.len()
                != length
                    .saturating_add(others.saturating_mul(32))
                    .saturating_add(levels.saturating_mul(LEVEL))
        {
            return Err(Error::Proof);
        }
        let (value, body) = body.split_at_checked(length).ok_or(Error::Proof)?;
        let (hashes, body) = body
            .split_at_checked(others.saturating_mul(32))
            .ok_or(Error::Proof)?;
        let entries: Vec<Entry> = body
            .as_chunks::<40>()
            .0
            .iter()
            .filter_map(|entry| {
                let (hash, rows) = entry.split_first_chunk::<32>()?;
                Some((*hash, u64::from_be_bytes(rows.try_into().ok()?)))
            })
            .collect();
        Ok(Self {
            key: *key,
            value: value.to_vec(),
            at,
            others: hashes.as_chunks().0.to_vec(),
            levels: entries.as_chunks().0.to_vec(),
        })
    }
}
