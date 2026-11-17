// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A paged Merkle map whose shape is a pure function of its rows.
//!
//! A sixteen-way radix map keyed by a 32-byte digest. A node holds its rows directly
//! while it has at most [`LEAF_ROWS`]; past that it holds sixteen children by the next
//! key nibble. Two maps with the same rows therefore have the same pages and the same
//! root, whatever order the rows arrived in, and a node is addressed by the [`Range`]
//! of the keys under it, so a map and a reconciliation walk share one addressing.
//!
//! Pages, format `ATPG1`, every number big-endian:
//!
//! * interior: `"ATPG1"`, `0x01`, then sixteen × (child hash 32, child row count `u64`).
//!   Its hash is the hash of those bytes.
//! * leaf: `"ATPG1"`, `0x02`, `u16` row count, then each row in key order: key 32, `u16`
//!   length, value. Its hash is the hash of `"ATPG1" ‖ 0x02 ‖ u16 count ‖` each row's
//!   `hash(key ‖ u16 length ‖ value)`: over the rows' hashes, not the page's bytes, so a
//!   [`Proof`] of one row carries the other rows' hashes and never the rows.
//!
//! A child with no rows is the empty leaf, and the empty map's root is its hash.
//!
//! States are persistent: a clone shares every page, and a change rewrites one leaf and
//! its ancestors. A map is a cache of pages and never authority: one opened from a root
//! holds no page until the caller admits it, each page is checked against the hash that
//! names it, and a root is only as good as where the caller got it. The caller supplies
//! the hash (this crate has none), states the bytes a map may retain, and fetches and
//! stores pages; nothing here counts rows against a fixed number, reads a clock or does I/O.

use super::rbsr::Range;
use super::Digest;
use std::mem::size_of;
use std::sync::{Arc, OnceLock};

mod page;
mod proof;

pub use proof::Proof;

/// The hash that names rows and pages: SHA-256 wherever a root leaves the machine. The
/// integrating application supplies it, as it computes every [`Digest`] this crate holds.
pub type Hasher = fn(&[u8]) -> Digest;

/// Rows a node holds directly; with one more it holds sixteen children. A shape, not a bound.
pub const LEAF_ROWS: usize = 32;
/// The longest value a row's `u16` length states.
pub const VALUE_BYTES: usize = 65_535;
/// Interior levels above any row: at most one for each nibble of its key.
pub const LEVELS: usize = 64;

const NODE: usize = size_of::<Node>();
const ROW: usize = size_of::<Row>();

/// A refusal; none changes the map.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A value longer than [`VALUE_BYTES`].
    Value,
    /// The page at this range, named by this hash, is not held: fetch it by its hash,
    /// [`Map::admit`] it there and ask again.
    Missing(Range, Digest),
    /// The range names no page that can be admitted or released: it lies inside a leaf,
    /// or its page is already held.
    Range,
    /// Bytes that are not one canonical page, or not the page the map names at that range.
    Page,
    /// Bytes that are not one canonical proof, or a proof deeper than [`LEVELS`].
    Proof,
    /// The map would retain more bytes than its caller stated, or the input is longer
    /// than the caller's limit.
    Budget,
    /// A row count overflowed.
    Count,
}

#[derive(Clone, Debug)]
struct Row {
    key: Digest,
    value: Arc<[u8]>,
    hash: OnceLock<Digest>,
}

impl Row {
    fn new(key: Digest, value: Arc<[u8]>) -> Self {
        Self {
            key,
            value,
            hash: OnceLock::new(),
        }
    }

    fn hash(&self, hasher: Hasher) -> Digest {
        *self
            .hash
            .get_or_init(|| hasher(&page::row(&self.key, &self.value)))
    }
}

#[derive(Clone, Debug)]
enum Body {
    /// Named by its parent's page, or by the caller for a root, and not held.
    Absent(Digest),
    /// At most [`LEAF_ROWS`] rows in key order.
    Leaf(Vec<Row>),
    /// More than [`LEAF_ROWS`] rows, by the key nibble at this depth.
    Interior([Arc<Node>; 16]),
}

#[derive(Clone, Debug)]
struct Node {
    /// Rows under this node.
    rows: u64,
    /// Bytes this node and every held page under it retain.
    held: usize,
    /// The page's hash once computed. A change clears it along one path.
    hash: OnceLock<Digest>,
    /// Whether these are the bytes a store gave ([`Map::admit`]), unchanged since.
    stored: bool,
    body: Body,
}

impl Node {
    fn of(body: Body) -> Self {
        let mut node = Self {
            rows: 0,
            held: NODE,
            hash: OnceLock::new(),
            stored: false,
            body,
        };
        node.tally();
        node
    }

    /// A page known by its hash and row count, and not held.
    fn absent(hash: Digest, rows: u64) -> Self {
        Self {
            rows,
            held: NODE,
            hash: OnceLock::new(),
            stored: false,
            body: Body::Absent(hash),
        }
    }

    fn leaf(rows: Vec<Row>) -> Self {
        Self::of(Body::Leaf(rows))
    }

    /// A node known by its name alone. One with no rows is the empty leaf, which is
    /// held, and no other page has the empty leaf's hash.
    fn named(hash: Digest, rows: u64, empty: &Digest) -> Result<Self, Error> {
        if (rows == 0) != (hash == *empty) {
            return Err(Error::Page);
        }
        Ok(if rows == 0 {
            Self::leaf(Vec::new())
        } else {
            Self::absent(hash, rows)
        })
    }

    /// Recount the rows and bytes of a held page from its own rows or children.
    fn tally(&mut self) {
        match &self.body {
            Body::Absent(_) => {}
            Body::Leaf(rows) => {
                self.rows = rows.len() as u64;
                self.held = rows.iter().fold(NODE, |held, row| {
                    held.saturating_add(ROW).saturating_add(row.value.len())
                });
            }
            Body::Interior(children) => {
                self.rows = children
                    .iter()
                    .fold(0, |rows: u64, child| rows.saturating_add(child.rows));
                self.held = children
                    .iter()
                    .fold(NODE, |held, child| held.saturating_add(child.held));
            }
        }
    }

    /// A changed page: its hash is no longer known, and no store has it.
    fn settle(&mut self) {
        self.hash = OnceLock::new();
        self.stored = false;
        self.tally();
    }

    fn hash(&self, hasher: Hasher) -> Digest {
        match &self.body {
            Body::Absent(hash) => *hash,
            Body::Leaf(rows) => *self.hash.get_or_init(|| leaf_hash(rows, hasher)),
            Body::Interior(children) => *self
                .hash
                .get_or_init(|| hasher(&page::interior(&entries(children, hasher)))),
        }
    }
}

fn entries(children: &[Arc<Node>; 16], hasher: Hasher) -> [page::Entry; 16] {
    children
        .each_ref()
        .map(|child| (child.hash(hasher), child.rows))
}

fn leaf_hash(rows: &[Row], hasher: Hasher) -> Digest {
    let hashes: Vec<Digest> = rows.iter().map(|row| row.hash(hasher)).collect();
    hasher(&page::leaf_hashed(hashes.len(), hashes.iter()))
}

/// The key's nibble at `depth`, high nibble of each byte first as [`Range`] orders them.
fn nibble(key: &Digest, depth: usize) -> usize {
    let byte = key.get(depth / 2).copied().unwrap_or(0);
    usize::from(if depth % 2 == 0 { byte >> 4 } else { byte & 15 })
}

/// The range of the keys that share `key`'s first `depth` nibbles.
fn prefix(key: &Digest, depth: usize) -> Range {
    let mut prefix = [0; 32];
    for (index, (slot, byte)) in prefix.iter_mut().zip(key).enumerate() {
        if index < depth / 2 {
            *slot = *byte;
        } else if index == depth / 2 && depth % 2 == 1 {
            *slot = *byte & 0xF0;
        }
    }
    Range::new(prefix, u8::try_from(depth).unwrap_or(u8::MAX)).unwrap_or(Range::ROOT)
}

/// Keys a range `nibbles` deep can hold, where a `u64` can say so.
fn room(nibbles: u8) -> u64 {
    64u32
        .checked_sub(u32::from(nibbles))
        .and_then(|free| 1u64.checked_shl(free.saturating_mul(4)))
        .unwrap_or(u64::MAX)
}

fn search(rows: &[Row], key: &Digest) -> Result<usize, usize> {
    rows.binary_search_by(|row| row.key.cmp(key))
}

/// Sixteen children of more than [`LEAF_ROWS`] rows that share their first `depth` nibbles.
fn split(rows: Vec<Row>, depth: usize) -> Body {
    let mut parts: [Vec<Row>; 16] = Default::default();
    for row in rows {
        if let Some(part) = parts.get_mut(nibble(&row.key, depth)) {
            part.push(row);
        }
    }
    let empty = Arc::new(Node::leaf(Vec::new()));
    Body::Interior(parts.map(|part| {
        if part.is_empty() {
            Arc::clone(&empty)
        } else if part.len() > LEAF_ROWS && depth < LEVELS - 1 {
            Arc::new(Node::of(split(part, depth.saturating_add(1))))
        } else {
            Arc::new(Node::leaf(part))
        }
    }))
}

/// Interior pages a leaf of `rows` becomes when `key` joins it: one, and one more for
/// each further nibble all of them share.
fn split_levels(rows: &[Row], key: &Digest, depth: usize) -> usize {
    (depth..LEVELS - 1)
        .take_while(|depth| {
            rows.iter()
                .all(|row| nibble(&row.key, *depth) == nibble(key, *depth))
        })
        .count()
        .saturating_add(1)
}

fn insert(node: &mut Arc<Node>, key: Digest, value: Arc<[u8]>, depth: usize) {
    let node = Arc::make_mut(node);
    let full = match &mut node.body {
        Body::Absent(_) => None,
        Body::Interior(children) => {
            if let Some(child) = children.get_mut(nibble(&key, depth)) {
                insert(child, key, value, depth.saturating_add(1));
            }
            None
        }
        Body::Leaf(rows) => {
            if let Some(row) = search(rows, &key).ok().and_then(|at| rows.get_mut(at)) {
                *row = Row::new(key, value);
            } else {
                // The new row goes last and steps down past each larger key: no index to be wrong.
                rows.push(Row::new(key, value));
                let mut larger = rows.iter_mut().rev();
                if let Some(mut new) = larger.next() {
                    for row in larger.take_while(|row| row.key > key) {
                        std::mem::swap(row, new);
                        new = row;
                    }
                }
            }
            (rows.len() > LEAF_ROWS).then(|| std::mem::take(rows))
        }
    };
    if let Some(rows) = full {
        node.body = split(rows, depth);
    }
    node.settle();
}

fn delete(node: &mut Arc<Node>, key: &Digest, depth: usize) {
    let node = Arc::make_mut(node);
    match &mut node.body {
        Body::Absent(_) => {}
        Body::Interior(children) => {
            if let Some(child) = children.get_mut(nibble(key, depth)) {
                delete(child, key, depth.saturating_add(1));
            }
        }
        Body::Leaf(rows) => {
            rows.retain(|row| row.key != *key);
        }
    }
    node.settle();
    if node.rows <= LEAF_ROWS as u64 && matches!(node.body, Body::Interior(_)) {
        let mut rows = Vec::new();
        gather(node, &mut rows);
        *node = Node::leaf(rows);
    }
}

fn gather(node: &Node, out: &mut Vec<Row>) {
    match &node.body {
        Body::Absent(_) => {}
        Body::Leaf(rows) => out.extend(rows.iter().cloned()),
        Body::Interior(children) => children.iter().for_each(|child| gather(child, out)),
    }
}

/// The first page under `node` that is not held.
fn held(node: &Node, range: Range) -> Result<(), Error> {
    match &node.body {
        Body::Absent(hash) => Err(Error::Missing(range, *hash)),
        Body::Leaf(_) => Ok(()),
        Body::Interior(children) => {
            let ranges = range.children().ok_or(Error::Range)?;
            children
                .iter()
                .zip(ranges)
                .try_for_each(|(child, range)| held(child, range))
        }
    }
}

/// Put `new` where the node `nibbles` deep on `key`'s path is, below held interior pages
/// whose own bytes do not change.
fn replace(node: &mut Arc<Node>, key: &Digest, nibbles: usize, depth: usize, new: Node) {
    if depth >= nibbles {
        *node = Arc::new(new);
        return;
    }
    let node = Arc::make_mut(node);
    if let Body::Interior(children) = &mut node.body {
        if let Some(child) = children.get_mut(nibble(key, depth)) {
            replace(child, key, nibbles, depth.saturating_add(1), new);
        }
    }
    node.tally();
}

/// A page [`Map::written`] has yet to judge, or has judged changed and lists once the
/// pages under it are listed.
enum Step<'a> {
    Judge(&'a Arc<Node>, Option<&'a Arc<Node>>, Range),
    Visit(Range, Digest),
}

/// What a range names: a page, or some of one leaf's rows.
enum Found<'a> {
    Node(&'a Node),
    Rows(&'a [Row]),
}

/// One state of a Merkle map: rows by key, in pages named by their hashes, within a
/// byte budget its caller states. `clone` is a second state that shares every page.
#[derive(Clone, Debug)]
pub struct Map {
    root: Arc<Node>,
    hasher: Hasher,
    budget: usize,
}

impl Map {
    /// The empty map, which refuses to retain more than `budget` bytes.
    #[must_use]
    pub fn new(hasher: Hasher, budget: usize) -> Self {
        Self {
            root: Arc::new(Node::leaf(Vec::new())),
            hasher,
            budget,
        }
    }

    /// The map of `rows` rows under `root`, holding none of its pages yet. Whether that
    /// root is the right one is the caller's to know; every page admitted is checked
    /// against it.
    /// # Errors
    /// [`Error::Page`] for no rows under a root that is not the empty map's, or rows
    /// under the empty map's root.
    pub fn from_root(
        hasher: Hasher,
        budget: usize,
        root: Digest,
        rows: u64,
    ) -> Result<Self, Error> {
        Ok(Self {
            root: Arc::new(Node::named(root, rows, &leaf_hash(&[], hasher))?),
            hasher,
            budget,
        })
    }

    /// The map under `root`, read from its root page alone: for a root kept without its
    /// row count, which the page states. The page is held; the pages under it are not.
    /// # Errors
    /// [`Error::Page`] for bytes that are not the page `root` names;
    /// [`Error::Budget`] when holding it would pass the budget.
    pub fn open(hasher: Hasher, budget: usize, root: Digest, page: &[u8]) -> Result<Self, Error> {
        let rows = match page::decode(page)? {
            page::Page::Leaf(rows) => rows.len() as u64,
            page::Page::Interior(children) => children
                .iter()
                .try_fold(0u64, |sum, (_, rows)| sum.checked_add(*rows))
                .filter(|rows| *rows > LEAF_ROWS as u64)
                .ok_or(Error::Page)?,
        };
        let mut map = Self::from_root(hasher, budget, root, rows)?;
        if !map.is_empty() {
            map.admit(Range::ROOT, page)?;
        }
        Ok(map)
    }

    /// The root: the hash of the root page. Only pages changed since it was last read
    /// are hashed, and a row's own hash only once.
    #[must_use]
    pub fn root(&self) -> Digest {
        self.root.hash(self.hasher)
    }

    /// Rows in the map, held or not.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.root.rows
    }

    /// Whether the map has no rows.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.root.rows == 0
    }

    /// The bytes this map may retain.
    #[must_use]
    pub const fn budget(&self) -> usize {
        self.budget
    }

    /// Bytes this state retains: every held page and row by its length, saturating on
    /// overflow, with pages shared with another state charged in full. Allocator
    /// bookkeeping, sharing headers and spare capacity are excluded.
    #[must_use]
    pub fn retained_bytes(&self) -> usize {
        self.root.held
    }

    /// The leaf rows on `key`'s path and their depth.
    fn leaf(&self, key: &Digest) -> Result<(&[Row], usize), Error> {
        let mut node = &*self.root;
        for depth in 0..=LEVELS {
            match &node.body {
                Body::Absent(hash) => return Err(Error::Missing(prefix(key, depth), *hash)),
                Body::Leaf(rows) => return Ok((rows, depth)),
                Body::Interior(children) => {
                    node = children.get(nibble(key, depth)).ok_or(Error::Range)?;
                }
            }
        }
        Err(Error::Range)
    }

    fn find(&self, range: Range) -> Result<Found<'_>, Error> {
        let (key, nibbles) = range.prefix();
        let mut node = &*self.root;
        for depth in 0..usize::from(nibbles) {
            match &node.body {
                Body::Absent(hash) => return Err(Error::Missing(prefix(&key, depth), *hash)),
                Body::Leaf(rows) => {
                    let from = rows.partition_point(|row| row.key < key);
                    let to = range.upper().map_or(rows.len(), |upper| {
                        rows.partition_point(|row| row.key < upper)
                    });
                    return Ok(Found::Rows(rows.get(from..to).unwrap_or(&[])));
                }
                Body::Interior(children) => {
                    node = children.get(nibble(&key, depth)).ok_or(Error::Range)?;
                }
            }
        }
        Ok(Found::Node(node))
    }

    /// The value at `key`, if the map has that row.
    /// # Errors
    /// [`Error::Missing`] names the page on the key's path that is not held.
    pub fn get(&self, key: &Digest) -> Result<Option<&[u8]>, Error> {
        let (rows, _) = self.leaf(key)?;
        Ok(search(rows, key)
            .ok()
            .and_then(|at| rows.get(at))
            .map(|row| &*row.value))
    }

    /// Put `value` at `key`. Nothing is hashed until a root or a proof is read.
    /// # Errors
    /// [`Error::Value`] past [`VALUE_BYTES`]; [`Error::Missing`] for a page on the key's
    /// path; [`Error::Budget`] when the map would grow past its budget;
    /// [`Error::Count`] at `u64::MAX` rows.
    pub fn set(&mut self, key: Digest, value: &[u8]) -> Result<(), Error> {
        if value.len() > VALUE_BYTES {
            return Err(Error::Value);
        }
        let (rows, depth) = self.leaf(&key)?;
        let (freed, grown) = match search(rows, &key).ok().and_then(|at| rows.get(at)) {
            Some(row) if *row.value == *value => return Ok(()),
            Some(row) => (row.value.len(), value.len()),
            None if self.root.rows == u64::MAX => return Err(Error::Count),
            None if rows.len() < LEAF_ROWS => (0, ROW.saturating_add(value.len())),
            None => (
                0,
                split_levels(rows, &key, depth)
                    .saturating_mul(16)
                    .saturating_mul(NODE)
                    .saturating_add(ROW)
                    .saturating_add(value.len()),
            ),
        };
        self.grow(freed, grown)?;
        insert(&mut self.root, key, Arc::from(value), 0);
        Ok(())
    }

    /// A change that frees `freed` bytes and adds `grown`: refused only when it grows the
    /// map past its budget.
    fn grow(&self, freed: usize, grown: usize) -> Result<(), Error> {
        let after = self.root.held.saturating_sub(freed).saturating_add(grown);
        if after > self.budget && after > self.root.held {
            return Err(Error::Budget);
        }
        Ok(())
    }

    /// Take the row at `key` out; `false` if the map has no such row. A node left with
    /// [`LEAF_ROWS`] rows or fewer becomes one leaf again.
    /// # Errors
    /// [`Error::Missing`] for a page on the key's path, or for one whose rows the leaf
    /// that replaces sixteen children must hold.
    pub fn remove(&mut self, key: &Digest) -> Result<bool, Error> {
        let mut node = &*self.root;
        let mut folds = None;
        for depth in 0..=LEVELS {
            match &node.body {
                Body::Absent(hash) => return Err(Error::Missing(prefix(key, depth), *hash)),
                Body::Leaf(rows) => {
                    if search(rows, key).is_err() {
                        return Ok(false);
                    }
                    break;
                }
                Body::Interior(children) => {
                    if folds.is_none() && node.rows == LEAF_ROWS as u64 + 1 {
                        folds = Some((node, depth));
                    }
                    node = children.get(nibble(key, depth)).ok_or(Error::Range)?;
                }
            }
        }
        if let Some((node, depth)) = folds {
            held(node, prefix(key, depth))?;
        }
        delete(&mut self.root, key, 0);
        Ok(true)
    }

    /// The hash and row count of the page that holds exactly this map's rows in `range`.
    /// For a range inside a leaf that is the leaf those rows alone would make, so two
    /// maps answer alike wherever their rows in the range are alike, whatever else they hold.
    /// # Errors
    /// [`Error::Missing`] for a page above the range.
    pub fn node(&self, range: Range) -> Result<(Digest, u64), Error> {
        Ok(match self.find(range)? {
            Found::Node(node) => (node.hash(self.hasher), node.rows),
            Found::Rows(rows) => (leaf_hash(rows, self.hasher), rows.len() as u64),
        })
    }

    /// The `ATPG1` bytes of the page [`Map::node`] names at `range`: what a store keeps
    /// under that hash.
    /// # Errors
    /// [`Error::Missing`] for that page or one above it.
    pub fn page(&self, range: Range) -> Result<Vec<u8>, Error> {
        match self.find(range)? {
            Found::Rows(rows) => Ok(page::leaf(rows)),
            Found::Node(node) => match &node.body {
                Body::Absent(hash) => Err(Error::Missing(range, *hash)),
                Body::Leaf(rows) => Ok(page::leaf(rows)),
                Body::Interior(children) => Ok(page::interior(&entries(children, self.hasher))),
            },
        }
    }

    /// The rows in `range` in key order, those after the key `after` only: a listing
    /// that continues where its last page ended. The first page that is not held ends it
    /// with [`Error::Missing`].
    #[must_use]
    pub fn rows(&self, range: Range, after: Option<Digest>) -> Rows<'_> {
        Rows {
            stack: vec![(&self.root, Range::ROOT)],
            leaf: [].iter(),
            range,
            after,
        }
    }

    /// Hold the page at `range`, which the map names and does not hold. The bytes must
    /// be that page: its hash, its row count, its place and its shape are checked first.
    /// # Errors
    /// [`Error::Missing`] for a page above it; [`Error::Range`] when the range names a
    /// held page or none; [`Error::Page`] for any other bytes; [`Error::Budget`] when
    /// holding it would pass the budget.
    pub fn admit(&mut self, range: Range, bytes: &[u8]) -> Result<(), Error> {
        let Found::Node(node) = self.find(range)? else {
            return Err(Error::Range);
        };
        let Body::Absent(named) = node.body else {
            return Err(Error::Range);
        };
        let mut held = match page::decode(bytes)? {
            page::Page::Leaf(rows) => {
                if rows.len() as u64 != node.rows
                    || rows.iter().any(|row| !range.contains(&row.key))
                    || leaf_hash(&rows, self.hasher) != named
                {
                    return Err(Error::Page);
                }
                Node::leaf(rows)
            }
            page::Page::Interior(children) => {
                let rows = children
                    .iter()
                    .try_fold(0u64, |sum, (_, rows)| sum.checked_add(*rows));
                let room = room(range.prefix().1.saturating_add(1));
                if rows != Some(node.rows)
                    || node.rows <= LEAF_ROWS as u64
                    || children.iter().any(|(_, rows)| *rows > room)
                    || (self.hasher)(bytes) != named
                {
                    return Err(Error::Page);
                }
                let empty = leaf_hash(&[], self.hasher);
                let mut nodes = Vec::with_capacity(16);
                for (hash, rows) in children.iter() {
                    nodes.push(Arc::new(Node::named(*hash, *rows, &empty)?));
                }
                Node::of(Body::Interior(nodes.try_into().map_err(|_| Error::Page)?))
            }
        };
        held.hash = OnceLock::from(named);
        held.stored = true;
        self.grow(NODE, held.held)?;
        let (key, nibbles) = range.prefix();
        replace(&mut self.root, &key, usize::from(nibbles), 0, held);
        Ok(())
    }

    /// Stop holding the page at `range` and every page under it, keeping its hash and
    /// row count. Store its pages first ([`Map::written`], [`Map::page`]): a page
    /// released and stored nowhere is lost.
    /// # Errors
    /// [`Error::Missing`] for a page above it; [`Error::Range`] inside a leaf.
    pub fn release(&mut self, range: Range) -> Result<(), Error> {
        let Found::Node(node) = self.find(range)? else {
            return Err(Error::Range);
        };
        if node.rows == 0 || matches!(node.body, Body::Absent(_)) {
            return Ok(());
        }
        let absent = Node::absent(node.hash(self.hasher), node.rows);
        let (key, nibbles) = range.prefix();
        replace(&mut self.root, &key, usize::from(nibbles), 0, absent);
        Ok(())
    }

    /// Every page this state holds that a store lacks, as its range and hash, children
    /// before the page that names them: what a store must write for this state, in an
    /// order that never leaves a written page naming an unwritten one. A store has the
    /// pages `base` has at the same range and the pages it gave ([`Map::admit`]) that
    /// have not changed since. The empty leaf is never listed; any reader makes it.
    /// Each state's pages are hashed with its own hasher. The walk keeps its own stack,
    /// and the list holds only changed pages: a leaf and its ancestors for one row.
    #[must_use]
    pub fn written(&self, base: &Self) -> Vec<(Range, Digest)> {
        let mut pages = Vec::new();
        let mut steps = vec![Step::Judge(&self.root, Some(&base.root), Range::ROOT)];
        while let Some(step) = steps.pop() {
            let (node, theirs, range) = match step {
                Step::Visit(range, hash) => {
                    pages.push((range, hash));
                    continue;
                }
                Step::Judge(node, theirs, range) => (node, theirs, range),
            };
            // Under a page a store gave, every page is one it gave, or absent, or empty.
            if node.rows == 0 || node.stored || matches!(node.body, Body::Absent(_)) {
                continue;
            }
            let hash = node.hash(self.hasher);
            if let Some(theirs) = theirs {
                if Arc::ptr_eq(node, theirs) || theirs.hash(base.hasher) == hash {
                    continue;
                }
            }
            steps.push(Step::Visit(range, hash));
            if let (Body::Interior(children), Some(ranges)) = (&node.body, range.children()) {
                // Pushed last to first, so the first child's pages are listed first.
                for (index, (child, range)) in children.iter().zip(ranges).enumerate().rev() {
                    let theirs = theirs.and_then(|theirs| match &theirs.body {
                        Body::Interior(children) => children.get(index),
                        Body::Absent(_) | Body::Leaf(_) => None,
                    });
                    steps.push(Step::Judge(child, theirs, range));
                }
            }
        }
        pages
    }

    /// The proof that the row at `key` lies under [`Map::root`]; `None` if the map has
    /// no such row. Hashes already computed are reused.
    /// # Errors
    /// [`Error::Missing`] for a page on the key's path.
    pub fn prove(&self, key: &Digest) -> Result<Option<Proof>, Error> {
        let mut node = &*self.root;
        let mut levels = Vec::new();
        for depth in 0..=LEVELS {
            match &node.body {
                Body::Absent(hash) => return Err(Error::Missing(prefix(key, depth), *hash)),
                Body::Leaf(rows) => {
                    let Ok(at) = search(rows, key) else {
                        return Ok(None);
                    };
                    let Some(row) = rows.get(at) else {
                        return Ok(None);
                    };
                    return Ok(Some(Proof {
                        key: *key,
                        value: row.value.to_vec(),
                        at,
                        others: rows
                            .iter()
                            .filter(|other| other.key != *key)
                            .map(|other| other.hash(self.hasher))
                            .collect(),
                        levels,
                    }));
                }
                Body::Interior(children) => {
                    let at = nibble(key, depth);
                    let mut siblings = children
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| *index != at)
                        .map(|(_, child)| (child.hash(self.hasher), child.rows));
                    levels.push(std::array::from_fn(|_| {
                        siblings.next().unwrap_or(([0; 32], 0))
                    }));
                    node = children.get(at).ok_or(Error::Range)?;
                }
            }
        }
        Err(Error::Range)
    }
}

/// Rows of a [`Map`] in key order ([`Map::rows`]).
#[derive(Clone, Debug)]
pub struct Rows<'a> {
    /// Pages still to read, the next one last.
    stack: Vec<(&'a Arc<Node>, Range)>,
    leaf: std::slice::Iter<'a, Row>,
    range: Range,
    after: Option<Digest>,
}

impl<'a> Iterator for Rows<'a> {
    type Item = Result<(&'a Digest, &'a [u8]), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            for row in self.leaf.by_ref() {
                if self.range.contains(&row.key) && self.after.is_none_or(|after| row.key > after) {
                    return Some(Ok((&row.key, &row.value)));
                }
            }
            let (node, range) = self.stack.pop()?;
            match &node.body {
                Body::Absent(hash) => {
                    self.stack.clear();
                    return Some(Err(Error::Missing(range, *hash)));
                }
                Body::Leaf(rows) => self.leaf = rows.iter(),
                Body::Interior(children) => {
                    let ranges = range.children()?;
                    for (child, range) in children.iter().zip(ranges).rev() {
                        let (low, _) = range.prefix();
                        let wanted =
                            self.range.contains(&low) || range.contains(&self.range.prefix().0);
                        let passed = self
                            .after
                            .zip(range.upper())
                            .is_some_and(|(after, upper)| upper <= after);
                        if child.rows > 0 && wanted && !passed {
                            self.stack.push((child, range));
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "map_tests.rs"]
mod tests;
