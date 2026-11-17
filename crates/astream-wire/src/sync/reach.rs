// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ancestry among any number of actors: every record's causal past as one shared map.
//!
//! A record's past is a version vector: for each actor, the highest sequence among the
//! record and its ancestors. [`Reach`] holds each vector as a persistent 16-way map from
//! actor ordinal to sequence. A node is found by its hash and held once, so two records
//! that reach the same sub-vector share it however each came by it: a record's map
//! shares every unchanged node with its parents' maps, and a record that joins many
//! heads adds nodes, and does work, only on the paths of the entries in which those
//! heads differ. "Is this record in the past of that one" is one read down one path, one
//! node per hexadecimal digit of the largest actor ordinal the later record holds, and
//! no vector is cut at an entry count: the one bound is the bytes the caller states.
//!
//! A hash finds a node and the node's content names it: two nodes are one only when
//! every word of them is equal, so no collision changes an answer. This crate has no
//! cryptographic hash, and a short name taken for identity would let two different
//! pasts read as one. A collision costs a longer search, so the hash takes a key
//! ([`Reach::keyed`]): a writer who cannot guess it cannot aim nodes at one another.
//!
//! Nothing here authenticates or orders. The caller gives each record after its parents.
//! The actor is a key that names ONE chain: a sequence is one record only there. A
//! caller that withdraws a forked actor, as [`super::Projection`] does, gives none of its
//! records; one that must judge both branches of a fork gives each branch a key of its
//! own, continued along the branch, and asks by that key. A record with no past here
//! (never given, or refused) gives none to any record that names it: such a record is
//! not given either, and never with [`Past::EMPTY`] in that parent's place.
//!
//! Entries are the caller's. An index with a floor gives the records above it, each
//! parent at or below the floor as [`Past::EMPTY`] and no other parent so, and answers a
//! question at or below the floor from the floor itself. A store is a cache of what its
//! records state: rebuild it from them on restart and whenever the floor moves, and drop
//! every [`Past`] the old store made. No clocks, network, retention or I/O.

use super::Actor;
use std::collections::BTreeMap;
use std::mem::size_of;

/// Places in one node: one hexadecimal digit of an actor ordinal.
const FAN: usize = 16;

/// Slots zeroed at one step while a slot table is filled.
const FILL: usize = 1 << 16;

/// A reach refusal; none changes a past, a name, an ordinal or an answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A zero sequence, or a sequence the record's own parents already reach.
    Shape,
    /// The store would hold more bytes than its caller stated; or the allocator refused a
    /// node's room, or names ran out (past four thousand million nodes of one kind). The
    /// record has no past here, and nor has any record that names it: answer questions
    /// about them some other way, or rebuild under a larger budget.
    Budget,
}

/// One causal past in the [`Reach`] that made it: eight bytes a caller keeps beside its
/// record. Two pasts of one store are equal exactly when they hold the same sequence
/// for every actor. A past means nothing to any other store, a rebuilt one and a clone
/// that has since recorded included: there it reads as whatever that store holds under
/// the same name, and no check can tell. Keep each with its store.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Past {
    /// The name of the top node; zero for a past that holds nothing.
    root: u32,
    /// Levels under the root, a leaf counted: the digits of the largest ordinal held.
    height: u8,
}

impl Past {
    /// The past of a record with no parents, before the record itself: no actor, no sequence.
    pub const EMPTY: Self = Self { root: 0, height: 0 };

    /// Whether this past holds no record.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.root == 0
    }
}

/// What one question found, and what it read to find it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Seen {
    /// The highest sequence of the actor in the past; zero when the past holds none.
    pub sequence: u64,
    /// Nodes read: at most one per hexadecimal digit of the store's actor count.
    pub nodes: u32,
}

#[cfg(test)]
thread_local! {
    /// Nodes offered for a name, and slots written, on this thread: the work a test bounds.
    static WORK: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

#[cfg(test)]
fn work(named: usize, placed: usize) {
    WORK.with(|work| work.set((work.get().0 + named, work.get().1 + placed)));
}

/// One SipHash round.
const fn sip_round([mut a, mut b, mut c, mut d]: [u64; 4]) -> [u64; 4] {
    a = a.wrapping_add(b);
    b = b.rotate_left(13) ^ a;
    a = a.rotate_left(32);
    c = c.wrapping_add(d);
    d = d.rotate_left(16) ^ c;
    a = a.wrapping_add(d);
    d = d.rotate_left(21) ^ a;
    c = c.wrapping_add(b);
    b = b.rotate_left(17) ^ c;
    c = c.rotate_left(32);
    [a, b, c, d]
}

/// SipHash under `key` of `words` as little-endian bytes, `rounds` rounds a word and
/// `last` to finish: a keyed function of every bit of every word.
fn sip_hash(key: [u64; 2], words: impl Iterator<Item = u64>, rounds: u8, last: u8) -> u64 {
    let [k0, k1] = key;
    let mut state = [
        k0 ^ 0x736f_6d65_7073_6575,
        k1 ^ 0x646f_7261_6e64_6f6d,
        k0 ^ 0x6c79_6765_6e65_7261,
        k1 ^ 0x7465_6462_7974_6573,
    ];
    let mut press = |word: u64| {
        let [a, b, c, d] = state;
        state = [a, b, c, d ^ word];
        for _ in 0..rounds {
            state = sip_round(state);
        }
        let [a, b, c, d] = state;
        state = [a ^ word, b, c, d];
    };
    let mut bytes = 0_u64;
    for word in words {
        bytes = bytes.wrapping_add(8);
        press(word);
    }
    // The closing word: no bytes left over, and the byte count in its top byte.
    press(bytes << 56);
    let [a, b, c, d] = state;
    state = [a, b, c ^ 0xff, d];
    for _ in 0..last {
        state = sip_round(state);
    }
    let [a, b, c, d] = state;
    a ^ b ^ c ^ d
}

/// One word of a node: a leaf's sequence or a branch's child name.
trait Word: Copy + Default + PartialEq {
    fn bits(self) -> u64;
}

impl Word for u64 {
    fn bits(self) -> u64 {
        self
    }
}

impl Word for u32 {
    fn bits(self) -> u64 {
        u64::from(self)
    }
}

/// Nodes of one kind, each distinct content held once. A node's name is its position
/// plus one; zero names the node of all zeros, which is never held.
#[derive(Clone)]
struct Nodes<W> {
    held: Vec<[W; FAN]>,
    /// Nodes `held` has been given room for. Room is taken a quarter more at a time,
    /// counted when taken and never given back.
    reserved: usize,
    /// Open-addressed names by content hash: zero is free, and at most half are taken.
    /// The slots only grow.
    slots: Vec<u32>,
    key: [u64; 2],
}

impl<W: Word> Nodes<W> {
    fn keyed(key: [u64; 2]) -> Self {
        Self {
            held: Vec::new(),
            reserved: 0,
            slots: Vec::new(),
            key,
        }
    }

    fn get(&self, name: u32) -> Option<&[W; FAN]> {
        let at = usize::try_from(name).ok()?.checked_sub(1)?;
        self.held.get(at)
    }

    /// Slots for `nodes` nodes: a power of two at least twice their number.
    fn room(nodes: usize) -> usize {
        if nodes == 0 {
            return 0;
        }
        nodes
            .saturating_mul(2)
            .checked_next_power_of_two()
            .unwrap_or(usize::MAX)
            .max(FAN)
    }

    /// The slot that names `node`, or the free slot it would take, and the name there.
    fn seek(&self, node: &[W; FAN]) -> Option<(usize, u32)> {
        let slots = self.slots.len();
        // SipHash-1-3, the keyed hash a hash table is given against chosen keys.
        let hash = sip_hash(self.key, node.iter().map(|word| word.bits()), 1, 3);
        let start = (hash as usize).checked_rem(slots)?;
        (0..slots).find_map(|step| {
            let at = start.wrapping_add(step).checked_rem(slots)?;
            let name = *self.slots.get(at)?;
            (name == 0 || self.get(name) == Some(node)).then_some((at, name))
        })
    }

    /// Write the held node `name` into the free slot its content hashes to.
    fn place(&mut self, name: u32) {
        #[cfg(test)]
        work(0, 1);
        let free = self.get(name).and_then(|node| self.seek(node));
        if let Some(slot) = free.and_then(|(at, _)| self.slots.get_mut(at)) {
            *slot = name;
        }
    }

    /// Take `room` slots and name every held node in them, oldest first. `None`, with
    /// nothing changed, when the allocator refuses.
    fn grow(&mut self, room: usize) -> Option<()> {
        let mut slots = Vec::new();
        slots.try_reserve_exact(room).ok()?;
        while slots.len() < room {
            let more = room.saturating_sub(slots.len()).min(FILL);
            slots.extend(std::iter::repeat_n(0_u32, more));
        }
        self.slots = slots;
        for name in (1..=self.held.len()).filter_map(|name| u32::try_from(name).ok()) {
            self.place(name);
        }
        Some(())
    }

    /// The name of `node`, held from now on. A node not yet held takes room only within
    /// `spare` bytes, charged before it is taken: `None` when the room does not fit, the
    /// allocator refuses it or names have run out, and then no node was added.
    fn name(&mut self, node: [W; FAN], spare: usize) -> Option<u32> {
        if node == [W::default(); FAN] {
            return Some(0);
        }
        #[cfg(test)]
        work(1, 0);
        if let Some((_, name @ 1..)) = self.seek(&node) {
            return Some(name);
        }
        let nodes = self.held.len().checked_add(1)?;
        let name = u32::try_from(nodes).ok()?;
        let room = Self::room(nodes).max(self.slots.len());
        let slots = room
            .saturating_sub(self.slots.len())
            .saturating_mul(size_of::<u32>());
        // Room for a quarter more nodes, or for as many as the spare bytes still pay for.
        let afford = spare
            .checked_sub(slots)?
            .checked_div(size_of::<[W; FAN]>())?;
        let step = if nodes > self.reserved {
            (self.reserved / 4).max(1).min(afford)
        } else {
            0
        };
        let reserved = self.reserved.checked_add(step)?;
        if reserved < nodes {
            return None;
        }
        self.held
            .try_reserve_exact(reserved.saturating_sub(self.held.len()))
            .ok()?;
        self.reserved = reserved;
        if room > self.slots.len() {
            self.grow(room)?;
        }
        self.held.push(node);
        self.place(name);
        Some(name)
    }

    /// Forget every node named after the first `nodes`, newest first.
    fn truncate(&mut self, nodes: usize) {
        // The newest node took a slot that was free when every older one was placed, so
        // freeing it leaves each older node where its own search still finds it.
        while self.held.len() > nodes {
            let taken = self.held.last().and_then(|node| self.seek(node));
            if let Some(slot) = taken.and_then(|(at, _)| self.slots.get_mut(at)) {
                *slot = 0;
            }
            self.held.pop();
        }
    }

    fn bytes(&self) -> usize {
        (self.reserved.saturating_mul(size_of::<[W; FAN]>()))
            .saturating_add(self.slots.len().saturating_mul(size_of::<u32>()))
    }
}

/// Hexadecimal digits `ordinal` needs: the height of the shortest past that can hold it.
fn span(ordinal: u32) -> u8 {
    let bits = u32::BITS - ordinal.leading_zeros();
    u8::try_from(bits.div_ceil(4).max(1)).unwrap_or(u8::MAX)
}

/// The place of `ordinal` in a node `level` levels above the leaves.
fn digit(ordinal: u32, level: u8) -> usize {
    ordinal
        .checked_shr(u32::from(level).saturating_mul(4))
        .map_or(0, |rest| (rest & 15) as usize)
}

/// Rebuildable store of causal pasts for ONE dataset/audience generation, bounded by the
/// bytes its caller states. A clone is a whole copy, node for node.
#[derive(Clone)]
pub struct Reach {
    /// Each actor's ordinal: its place in the order this store first saw the actors.
    actors: BTreeMap<Actor, u32>,
    /// Sixteen sequences, for the actors whose ordinals differ in the last digit alone.
    leaves: Nodes<u64>,
    /// Sixteen names of the nodes one level down, leaves under the lowest branches.
    branches: Nodes<u32>,
    budget: usize,
}

impl std::fmt::Debug for Reach {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Reach")
            .field("actors", &self.actors.len())
            .field("nodes", &self.nodes())
            .field("bytes", &self.bytes())
            .field("budget", &self.budget)
            .finish()
    }
}

impl Reach {
    /// An empty store that never holds more than `bytes` ([`Reach::bytes`]), for records
    /// whose writers do not choose them against it: it finds its nodes under a key
    /// anyone knows.
    #[must_use]
    pub fn with_budget(bytes: usize) -> Self {
        Self::keyed(bytes, [0; 2])
    }

    /// An empty store that never holds more than `bytes`, finding its nodes under `key`.
    /// The key changes no past, no answer and no byte count, only where a node sits among
    /// the slots that find it. State one a writer cannot guess, fresh for each store,
    /// wherever a writer may be hostile: against a known key a writer can choose records
    /// whose nodes all search one run of slots, and every search through that run pays.
    #[must_use]
    pub fn keyed(bytes: usize, key: [u64; 2]) -> Self {
        Self {
            actors: BTreeMap::new(),
            leaves: Nodes::keyed(key),
            branches: Nodes::keyed(key),
            budget: bytes,
        }
    }

    /// The bytes the caller stated.
    #[must_use]
    pub fn budget(&self) -> usize {
        self.budget
    }

    /// Bytes one actor is counted at: its key and its ordinal.
    const ACTOR: usize = size_of::<Actor>() + size_of::<u32>();

    /// Bytes held, never more than the budget: the room taken for nodes (up to a quarter
    /// more than the nodes held, and kept when a record is refused), the slots that find
    /// them, and each actor with its ordinal. Not counted: what the allocator and the
    /// actor map keep around those.
    #[must_use]
    pub fn bytes(&self) -> usize {
        self.leaves
            .bytes()
            .saturating_add(self.branches.bytes())
            .saturating_add(self.actors.len().saturating_mul(Self::ACTOR))
    }

    /// Distinct nodes held, over every past this store made.
    #[must_use]
    pub fn nodes(&self) -> usize {
        self.leaves
            .held
            .len()
            .saturating_add(self.branches.held.len())
    }

    /// Actors with an ordinal.
    #[must_use]
    pub fn actors(&self) -> usize {
        self.actors.len()
    }

    /// The past of the record of `actor` at `sequence` whose parents' pasts are `parents`:
    /// their entrywise maximum, with `sequence` at `actor`. It adds a node, and does work,
    /// only where the parents differ among themselves and down the path of `actor`.
    ///
    /// # Errors
    /// [`Refusal::Shape`] for a zero sequence or one a parent already reaches, which no
    /// record that comes after its parents on one chain can have; [`Refusal::Budget`] when
    /// the store would pass its budget.
    pub fn record(
        &mut self,
        actor: &Actor,
        sequence: u64,
        parents: &[Past],
    ) -> Result<Past, Refusal> {
        let known = self.actors.get(actor).copied();
        let reached = known.is_some_and(|ordinal| {
            parents
                .iter()
                .any(|parent| self.read(*parent, ordinal).sequence >= sequence)
        });
        if sequence == 0 || reached {
            return Err(Refusal::Shape);
        }
        let ordinal = match known {
            Some(ordinal) => ordinal,
            None if Self::ACTOR > self.spare() => return Err(Refusal::Budget),
            None => u32::try_from(self.actors.len()).map_err(|_| Refusal::Budget)?,
        };
        self.actors.insert(*actor, ordinal);
        let made = self.settle(parents, Some((ordinal, sequence)));
        if made.is_err() && known.is_none() {
            self.actors.remove(actor);
        }
        made
    }

    /// The entrywise maximum of `pasts`: what a record naming each of them as a parent has
    /// in its past before the record itself. It adds a node only where they differ, and
    /// the store holds what it adds for good, within its budget: this is for a past the
    /// caller keeps, such as the frontier of its heads. A question asked once of several
    /// pasts is the highest [`Reach::seen`] among them, which adds nothing.
    ///
    /// # Errors
    /// [`Refusal::Budget`] when the store would pass its budget.
    pub fn join(&mut self, pasts: &[Past]) -> Result<Past, Refusal> {
        self.settle(pasts, None)
    }

    /// The highest sequence of `actor` in `later`, and the nodes read to find it: one per
    /// level of `later`, fewer where it holds nothing on the way.
    #[must_use]
    pub fn seen(&self, later: Past, actor: &Actor) -> Seen {
        self.actors
            .get(actor)
            .map_or(Seen::default(), |ordinal| self.read(later, *ordinal))
    }

    /// Whether `later` reaches `sequence` of `actor`: for a record of `actor` at `sequence`
    /// on its one chain, whether that record is `later`'s own or in its causal past.
    /// Sequence zero names no record.
    #[must_use]
    pub fn reaches(&self, later: Past, actor: &Actor, sequence: u64) -> bool {
        sequence > 0 && self.seen(later, actor).sequence >= sequence
    }

    fn read(&self, later: Past, ordinal: u32) -> Seen {
        let mut seen = Seen::default();
        if later.height < span(ordinal) {
            return seen;
        }
        let mut name = later.root;
        for level in (1..later.height).rev() {
            let Some(branch) = self.branches.get(name) else {
                return seen;
            };
            seen.nodes = seen.nodes.saturating_add(1);
            name = branch.get(digit(ordinal, level)).copied().unwrap_or(0);
        }
        if let Some(leaf) = self.leaves.get(name) {
            seen.nodes = seen.nodes.saturating_add(1);
            seen.sequence = leaf.get(digit(ordinal, 0)).copied().unwrap_or(0);
        }
        seen
    }

    /// Merge and keep the result, or put back every node the merge added.
    /// Bytes the budget still allows.
    fn spare(&self) -> usize {
        self.budget.saturating_sub(self.bytes())
    }

    fn settle(&mut self, pasts: &[Past], own: Option<(u32, u64)>) -> Result<Past, Refusal> {
        let held = (self.leaves.held.len(), self.branches.held.len());
        let height = pasts
            .iter()
            .filter(|past| !past.is_empty())
            .map(|past| past.height)
            .chain(own.map(|(ordinal, _)| span(ordinal)))
            .max()
            .unwrap_or(0);
        match self.merge(height, pasts, own) {
            Some(0) => Ok(Past::EMPTY),
            Some(root) => Ok(Past { root, height }),
            None => {
                self.leaves.truncate(held.0);
                self.branches.truncate(held.1);
                Err(Refusal::Budget)
            }
        }
    }

    /// The name of the node `height` levels tall that holds the entrywise maximum of
    /// `subs`, with `own`'s sequence at its ordinal. `None` when a node's room is refused.
    fn merge(&mut self, height: u8, subs: &[Past], own: Option<(u32, u64)>) -> Option<u32> {
        let mut subs: Vec<Past> = subs.iter().copied().filter(|sub| sub.root != 0).collect();
        subs.sort_unstable();
        subs.dedup();
        // Where every past agrees there is nothing to build: the one node stands.
        match (subs.as_slice(), own) {
            ([], None) => return Some(0),
            ([one], None) => return self.lift(*one, height),
            _ => {}
        }
        if height <= 1 {
            let mut leaf = [0_u64; FAN];
            for sub in subs.iter().filter(|sub| sub.height == 1) {
                if let Some(held) = self.leaves.get(sub.root) {
                    for (slot, seen) in leaf.iter_mut().zip(held) {
                        *slot = (*slot).max(*seen);
                    }
                }
            }
            if let Some((ordinal, sequence)) = own {
                if let Some(slot) = leaf.get_mut(digit(ordinal, 0)) {
                    *slot = (*slot).max(sequence);
                }
            }
            let spare = self.spare();
            return self.leaves.name(leaf, spare);
        }
        let below = height - 1;
        let kids: Vec<[Past; FAN]> = subs.iter().map(|sub| self.kids(*sub, height)).collect();
        let mut branch = [0_u32; FAN];
        for (at, slot) in branch.iter_mut().enumerate() {
            let under: Vec<Past> = kids.iter().filter_map(|kid| kid.get(at).copied()).collect();
            let own = own.filter(|(ordinal, _)| digit(*ordinal, below) == at);
            *slot = self.merge(below, &under, own)?;
        }
        let spare = self.spare();
        self.branches.name(branch, spare)
    }

    /// The sixteen subtrees of `sub` read as a node `height` levels tall: its children, or,
    /// for a shorter subtree, itself in the first place, where every ordinal it holds lies.
    fn kids(&self, sub: Past, height: u8) -> [Past; FAN] {
        let mut kids = [Past::EMPTY; FAN];
        if sub.height < height {
            if let Some(first) = kids.first_mut() {
                *first = sub;
            }
        } else if let Some(branch) = self.branches.get(sub.root).filter(|_| sub.height == height) {
            for (kid, name) in kids.iter_mut().zip(branch) {
                *kid = Past {
                    root: *name,
                    height: height.saturating_sub(1),
                };
            }
        }
        kids
    }

    /// The name of `sub` as a node `height` levels tall: its own, or that of the branches
    /// that hold it in their first place. `None` when a node's room is refused.
    fn lift(&mut self, mut sub: Past, height: u8) -> Option<u32> {
        while sub.root != 0 && sub.height < height {
            let mut branch = [0_u32; FAN];
            if let Some(first) = branch.first_mut() {
                *first = sub.root;
            }
            let spare = self.spare();
            sub = Past {
                root: self.branches.name(branch, spare)?,
                height: sub.height.checked_add(1)?,
            };
        }
        Some(if sub.height == height { sub.root } else { 0 })
    }
}

#[cfg(test)]
#[path = "reach_tests.rs"]
mod tests;
