// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `ATPG1` page bytes. One page has one encoding: a reader refuses a page that is
//! truncated, trailed, unordered or over a leaf's row count before it holds a row.

use super::{Digest, Error, Row, LEAF_ROWS};
use std::sync::Arc;

const MAGIC: [u8; 5] = *b"ATPG1";
const INTERIOR: u8 = 1;
const LEAF: u8 = 2;

/// A child's hash and row count, as an interior page and a proof carry them.
pub(super) type Entry = (Digest, u64);

/// A decoded page, its rows not yet hashed.
pub(super) enum Page {
    Interior(Box<[Entry; 16]>),
    Leaf(Vec<Row>),
}

fn length(bytes: usize) -> [u8; 2] {
    u16::try_from(bytes).unwrap_or(u16::MAX).to_be_bytes()
}

/// What a row's hash is over: key, `u16` length, value.
pub(super) fn row(key: &Digest, value: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(key);
    out.extend_from_slice(&length(value.len()));
    out.extend_from_slice(value);
    out
}

/// An interior page, which is also what its hash is over.
pub(super) fn interior(children: &[Entry; 16]) -> Vec<u8> {
    let mut out = Vec::with_capacity(646);
    out.extend_from_slice(&MAGIC);
    out.push(INTERIOR);
    for (hash, rows) in children {
        out.extend_from_slice(hash);
        out.extend_from_slice(&rows.to_be_bytes());
    }
    out
}

/// A leaf page: its rows whole, in key order.
pub(super) fn leaf(rows: &[Row]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC);
    out.push(LEAF);
    out.extend_from_slice(&length(rows.len()));
    for held in rows {
        out.extend_from_slice(&row(&held.key, &held.value));
    }
    out
}

/// What a leaf's hash is over: its header and each row's hash in key order, never the rows.
pub(super) fn leaf_hashed<'a>(count: usize, hashes: impl Iterator<Item = &'a Digest>) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC);
    out.push(LEAF);
    out.extend_from_slice(&length(count));
    for hash in hashes {
        out.extend_from_slice(hash);
    }
    out
}

/// Read one canonical page.
/// # Errors
/// [`Error::Page`] for anything else.
pub(super) fn decode(bytes: &[u8]) -> Result<Page, Error> {
    let mut input = Reader { bytes, at: 0 };
    if input.take::<5>()? != MAGIC {
        return Err(Error::Page);
    }
    let page = match input.take::<1>()? {
        [INTERIOR] => {
            let mut children = Box::new([([0; 32], 0); 16]);
            for child in children.iter_mut() {
                *child = (input.take()?, u64::from_be_bytes(input.take()?));
            }
            Page::Interior(children)
        }
        [LEAF] => {
            let count = usize::from(u16::from_be_bytes(input.take()?));
            if count > LEAF_ROWS {
                return Err(Error::Page);
            }
            let mut rows = Vec::<Row>::with_capacity(count);
            for _ in 0..count {
                let key = input.take()?;
                let length = usize::from(u16::from_be_bytes(input.take()?));
                let value = input.slice(length)?;
                if rows.last().is_some_and(|last| last.key >= key) {
                    return Err(Error::Page);
                }
                rows.push(Row::new(key, Arc::from(value)));
            }
            Page::Leaf(rows)
        }
        _ => return Err(Error::Page),
    };
    if input.at != bytes.len() {
        return Err(Error::Page);
    }
    Ok(page)
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn slice(&mut self, count: usize) -> Result<&'a [u8], Error> {
        let end = self.at.checked_add(count).ok_or(Error::Page)?;
        let bytes = self.bytes.get(self.at..end).ok_or(Error::Page)?;
        self.at = end;
        Ok(bytes)
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        self.slice(N)?.try_into().map_err(|_| Error::Page)
    }
}
