// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Causal application synchronization above astream's local durable log.
//!
//! Local broker offsets cannot name multi-writer history. This index uses immutable
//! record digests and actor-incarnation sequences instead. It never authenticates
//! bytes: the caller verifies signatures, authorization and the digest BEFORE insert,
//! and durably stores the full record BEFORE acknowledging it. Rebuild on restart.
//! Inventory is a set of digests, including forks: a sequence watermark alone hides
//! two signed records at the same sequence. No clocks, network, retention or I/O.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

/// Range fingerprints and actor prefixes for immutable inventory reconciliation.
pub mod rbsr;

/// SHA-256 content identity, computed and verified by the integrating application.
pub type Digest = [u8; 32];
/// Application-defined public actor key plus fresh installation incarnation.
pub type Actor = [u8; 48];
/// Bound on references carried by one record.
pub const MAX_PARENTS: usize = 64;

/// An authenticated record's replication header; payload semantics live above this index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    /// Content digest of the complete authenticated record.
    pub id: Digest,
    /// Writer and installation incarnation, scoped by the enclosing index.
    pub actor: Actor,
    /// Dense actor sequence, starting at one.
    pub sequence: u64,
    /// Previous record of this actor; also a member of `parents`.
    pub previous: Option<Digest>,
    /// Sorted, unique exact dependencies. References never imply another audience's data.
    pub parents: Vec<Digest>,
}

/// An index refusal; none changes the index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// Zero sequence, impossible previous link, unordered/duplicate parents, or self-reference.
    Shape,
    /// A previously supplied digest names a different header.
    DigestCollision,
    /// The configured retained-record bound is full. Do not acknowledge this record.
    Capacity,
}

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "sync_island.rs"]
mod sync_island;
#[cfg(not(clean_islands))]
pub use crate::twins::sync_clamp_parent_count;
#[cfg(clean_islands)]
pub use sync_island::sync_clamp_parent_count;

contract_fn! {
    /// Kernel-certified check that `retained` sits strictly below `capacity`
    /// (`retained < capacity`), backed by `sync_within_capacity_isl` (`clean-kernel-defeq`)
    /// and the Clean-origin [`sync_clamp_parent_count`] (`min(len, cap)`).
    #[must_use]
    pub const fn sync_within_capacity(retained: u64, capacity: u64) -> bool
    clauses [ensures result == (retained < capacity)]
    {
        retained < capacity
    }
}

/// Whether `next` densely follows `previous`, without wrapping at `u64::MAX`.
///
/// Level-0 overflow safety (`previous + 1`) is kernel-certified from `previous < u64::MAX`,
/// and the full functional specification is recorded in `sync_island.rs`
/// (`sync_sequence_follows_isl`).
#[must_use]
pub const fn sequence_follows(previous: u64, next: u64) -> bool {
    previous < u64::MAX && next == previous + 1
}

const fn raw_discharge(unfulfilled: u64) -> u64 {
    if unfulfilled == 0 {
        0
    } else {
        unfulfilled - 1
    }
}

contract_fn! {
    const fn clamp_le_unfulfilled(v: u64, hi: u64) -> u64
    clauses [ensures result <= hi]
    {
        if v > hi { hi } else { v }
    }
}

contract_fn! {
    /// Discharge one previously unfulfilled edge; saturates only for an empty set.
    #[must_use]
    pub const fn discharge(unfulfilled: u64) -> u64
    clauses [ensures result <= unfulfilled]
    {
        clamp_le_unfulfilled(raw_discharge(unfulfilled), unfulfilled)
    }
}

impl Header {
    /// Parent count clamped to [`MAX_PARENTS`] via Clean-origin [`sync_clamp_parent_count`].
    #[must_use]
    pub fn clamped_parent_count(&self) -> usize {
        sync_clamp_parent_count(self.parents.len() as u64, MAX_PARENTS as u64) as usize
    }

    /// Whether [`Index::insert`] admits this header's shape: a header it refuses as
    /// [`Refusal::Shape`] is not shaped.
    #[must_use]
    pub fn is_shaped(&self) -> bool {
        self.sequence > 0
            && (self.sequence == 1) == self.previous.is_none()
            && self.parents.len() <= MAX_PARENTS
            && self.clamped_parent_count() == self.parents.len()
            && !self.parents.contains(&self.id)
            && self.parents.windows(2).all(|p| p[0] < p[1])
            && self
                .previous
                .is_none_or(|p| self.parents.binary_search(&p).is_ok())
    }

    // Only shaped headers reach this helper: a predecessor then has sequence >= 2.
    fn claims(&self) -> impl Iterator<Item = (u64, Digest)> + '_ {
        std::iter::once((self.sequence, self.id)).chain(
            self.previous
                .zip(self.sequence.checked_sub(1))
                .map(|(id, seq)| (seq, id)),
        )
    }
}

/// Two retained source headers whose dense-chain claims contradict one another.
/// These are references, not an authentication certificate: the application
/// must verify the exact headers and their signatures in the enclosing scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fork {
    pub actor: Actor,
    /// Lexicographically smaller source record ID.
    pub first: Digest,
    /// Lexicographically larger source record ID; not a missing predecessor ID.
    pub second: Digest,
}
impl Fork {
    /// Recognize contradictory claims in two distinct, well-shaped headers of
    /// one actor. This performs no signature, payload or authorization check.
    pub fn between(a: &Header, b: &Header) -> Option<Self> {
        if a.actor != b.actor || a.id == b.id || !a.is_shaped() || !b.is_shaped() {
            return None;
        }
        a.claims()
            .any(|(seq, id)| {
                b.claims()
                    .any(|(other_seq, other_id)| seq == other_seq && id != other_id)
            })
            .then_some(Self::sources(a.actor, a.id, b.id))
    }

    fn sources(actor: Actor, a: Digest, b: Digest) -> Self {
        Self {
            actor,
            first: a.min(b),
            second: a.max(b),
        }
    }
}

/// Rebuildable, bounded causal index for ONE dataset/audience generation.
#[derive(Clone, Debug)]
pub struct Index {
    records: BTreeMap<Digest, Header>,
    /// Each retained actor's highest retained sequence, kept at insert ([`Index::frontier`]).
    frontier: BTreeMap<Actor, u64>,
    capacity: usize,
    /// Records a checkpoint stands for ([`Index::insert_floor`]), apart from `records`.
    floor: BTreeMap<Digest, FloorRecord>,
}

/// A record at the boundary of a checkpoint's cut, admitted on the checkpoint's word rather than
/// its own: its header and its causal past as a version vector (for each actor, the highest
/// sequence in the record's past, its own included). The records below it are absent.
///
/// A floor record is never in [`Index::inventory`], never a fork witness and never ordered by a
/// projection: the checkpoint's state already holds its effects. It is present for readiness (a
/// record naming it as a parent or predecessor is ready without the floor record's own past) and
/// as a discharged root, so a question about a record above it reads the given vector below it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FloorRecord {
    /// The record's header.
    pub header: Header,
    /// For each actor, the highest sequence in the record's causal past, the record included.
    pub past: BTreeMap<Actor, u64>,
}

/// Incremental admission against an immutable index and earlier accepted proposals.
/// Rejected headers leave the proposal unchanged, so callers can preserve per-record
/// refusals while collecting one accepted batch. Only distinct new headers occupy
/// borrowed scratch space; retained history is neither cloned nor modified.
/// Authentication and application policy remain the caller's obligations.
pub struct Proposal<'index, 'headers> {
    index: &'index Index,
    proposed: BTreeMap<Digest, &'headers Header>,
}

impl<'headers> Proposal<'_, 'headers> {
    /// Check one verified header, retaining its metadata hint on a new admission.
    /// `false` is an identical duplicate. A refusal reserves no room and leaves
    /// earlier accepted proposals intact. This never reserves capacity in the
    /// underlying index; actual insertion checks its then-current state again.
    /// # Errors
    /// [`Refusal`] names malformed headers, digest collisions and exhausted capacity.
    pub fn check_insert(&mut self, header: &'headers Header) -> Result<bool, Refusal> {
        if !header.is_shaped() {
            return Err(Refusal::Shape);
        }
        let old = self
            .proposed
            .get(&header.id)
            .copied()
            .or_else(|| self.index.records.get(&header.id));
        let accepted = Index::admit_shaped(
            header,
            old,
            self.index.records.len().saturating_add(self.proposed.len()),
            self.index.capacity,
        )?;
        if accepted {
            self.proposed.insert(header.id, header);
        }
        Ok(accepted)
    }

    /// Number of distinct new headers accepted by this proposal.
    #[must_use]
    pub fn new_records(&self) -> usize {
        self.proposed.len()
    }
}

/// A borrowed dense-sequence claim within one actor.
#[derive(Clone, Copy)]
struct DotClaim<'a> {
    sequence: u64,
    source: &'a Digest,
    id: &'a Digest,
}

/// The least source of one dot and the least source claiming a different identity.
/// Claims may arrive in any order within a sequence bucket, and one may arrive twice.
/// A header claims a dot at most once (its own claim and its predecessor claim sit at
/// two sequences), so distinct headers give a dot claims of distinct sources. Then
/// `first` is the least-source claim inserted and `different` the least-source claim
/// whose id is not `first`'s, whatever the order of insertion. A repeated header
/// repeats a claim, source and id alike, and `insert` ignores it: equal to `first`,
/// its source is not below `first`'s and its id is `first`'s; equal to another claim
/// already inserted, its source is above `first`'s and either its id is `first`'s or
/// its source is not below `different`'s.
struct DotGroup<'a> {
    first: DotClaim<'a>,
    different: Option<DotClaim<'a>>,
}

impl<'a> DotGroup<'a> {
    fn new(first: DotClaim<'a>) -> Self {
        Self {
            first,
            different: None,
        }
    }

    fn insert(&mut self, claim: DotClaim<'a>) {
        if claim.source < self.first.source {
            if claim.id != self.first.id {
                self.different = Some(self.first);
            }
            self.first = claim;
        } else if claim.id != self.first.id
            && self
                .different
                .is_none_or(|other| claim.source < other.source)
        {
            self.different = Some(claim);
        }
    }

    fn witness(self, actor: Actor) -> Option<Fork> {
        self.different
            .map(|other| Fork::sources(actor, *self.first.source, *other.source))
    }
}

/// Deterministic projection of the whole known authenticated history.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Projection {
    /// Causal order; simultaneous ready records are ordered by digest.
    pub ordered: Vec<Digest>,
    /// Maximal visible records; include these in a new operation's dependencies.
    pub heads: BTreeSet<Digest>,
    /// Every actor whose authenticated headers claim distinct digests at one
    /// dense sequence, including claims made by predecessor links.
    pub quarantined: BTreeSet<Actor>,
    /// Records missing prerequisites, with impossible links, or depending on quarantine.
    pub pending: BTreeSet<Digest>,
    /// The causal past of each record of `ordered`, as a version vector computed once in
    /// causal order; [`Projection::observes`] reads it. A projection built elsewhere may
    /// leave it empty, and then every question walks the index.
    pub vectors: VersionVectors,
}

/// Entries a projection's version vectors may hold per retained record, [`MAX_PARENTS`]:
/// as many as one header may name parents, so the vectors never outgrow what the
/// headers themselves may hold, however many actors write.
pub const VECTOR_ENTRIES_PER_RECORD: usize = MAX_PARENTS;

/// Each discharged record's causal past as a version vector: for every actor in it, the
/// highest sequence among the record and its ancestors.
///
/// A discharged record's ancestors are all discharged: each of its parents was, and
/// each of its actor's records below it is retained in one dense previous-linked chain
/// of an actor no fork quarantines. So one discharged record observes another exactly
/// when the first's vector reaches the second's sequence at the second's actor: the
/// ancestor that sets that entry reaches, down its own chain, the one retained record
/// of that actor at that sequence, and a second record there would be a fork.
///
/// A row is sparse, one entry per actor in the record's past, and all rows together hold
/// at most [`VECTOR_ENTRIES_PER_RECORD`] entries per retained record. A record whose row
/// would pass that bound gets none, and nor does any record after it that names a
/// record with none: questions about those walk, so the answer never changes, only its
/// cost.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct VersionVectors {
    /// Actor ordinals: every actor the projected index retained, sorted.
    actors: Vec<Actor>,
    /// Each discharged record's row.
    rows: BTreeMap<Digest, usize>,
    /// Each row's own dot and where its entries sit.
    dots: Vec<Dot>,
    /// Every row's entries, each row's sorted by actor ordinal: the ordinal...
    ordinals: Vec<u32>,
    /// ... and the highest sequence of that actor in the row's past.
    sequences: Vec<u64>,
    /// Entries the rows may hold in all.
    budget: usize,
}

/// A row's own actor ordinal and sequence, and the span of its entries.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Dot {
    actor: u32,
    sequence: u64,
    start: usize,
    end: usize,
}

impl std::fmt::Debug for VersionVectors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VersionVectors")
            .field("records", &self.dots.len())
            .field("actors", &self.actors.len())
            .field("entries", &self.ordinals.len())
            .finish()
    }
}

impl VersionVectors {
    fn new(actors: Vec<Actor>, retained: usize) -> Self {
        Self {
            actors,
            budget: retained.saturating_mul(VECTOR_ENTRIES_PER_RECORD),
            ..Self::default()
        }
    }

    /// Discharge `header` after each of its parents: its vector is their entrywise
    /// maximum with its own sequence at its own actor. A header whose actor has no
    /// ordinal, whose parent has no row, or whose row would pass the budget gets no row.
    fn discharge(&mut self, header: &Header) {
        let Some(own) = self
            .actors
            .binary_search(&header.actor)
            .ok()
            .and_then(|own| u32::try_from(own).ok())
        else {
            return;
        };
        let mut merged = vec![(own, header.sequence)];
        for parent in &header.parents {
            let Some(dot) = self.rows.get(parent).and_then(|row| self.dots.get(*row)) else {
                return;
            };
            let (Some(ordinals), Some(sequences)) = (
                self.ordinals.get(dot.start..dot.end),
                self.sequences.get(dot.start..dot.end),
            ) else {
                return;
            };
            merged.extend(ordinals.iter().copied().zip(sequences.iter().copied()));
        }
        // Each actor's highest sequence first, then one entry per actor.
        merged.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)));
        merged.dedup_by_key(|entry| entry.0);
        if merged.len() > self.budget.saturating_sub(self.ordinals.len()) {
            return;
        }
        let start = self.ordinals.len();
        for (ordinal, sequence) in merged {
            self.ordinals.push(ordinal);
            self.sequences.push(sequence);
        }
        self.rows.insert(header.id, self.dots.len());
        self.dots.push(Dot {
            actor: own,
            sequence: header.sequence,
            start,
            end: self.ordinals.len(),
        });
    }

    /// Give the floor record `header` the row `past`, with an allowance of its own beyond the
    /// budget: a floor record has no retained past to walk instead.
    fn seed(&mut self, header: &Header, past: &BTreeMap<Actor, u64>) {
        let Some(own) = self
            .actors
            .binary_search(&header.actor)
            .ok()
            .and_then(|own| u32::try_from(own).ok())
        else {
            return;
        };
        let start = self.ordinals.len();
        for (actor, sequence) in past {
            let Some(ordinal) = self
                .actors
                .binary_search(actor)
                .ok()
                .and_then(|at| u32::try_from(at).ok())
            else {
                continue;
            };
            self.ordinals.push(ordinal);
            self.sequences.push(*sequence);
        }
        self.budget = self.budget.saturating_add(self.ordinals.len() - start);
        self.rows.insert(header.id, self.dots.len());
        self.dots.push(Dot {
            actor: own,
            sequence: header.sequence,
            start,
            end: self.ordinals.len(),
        });
    }

    /// Whether the row `row`'s past reaches `sequence` of `actor`.
    fn reaches(&self, row: usize, actor: &Actor, sequence: u64) -> bool {
        let (Some(dot), Ok(ordinal)) = (self.dots.get(row), self.actors.binary_search(actor))
        else {
            return false;
        };
        let (Some(ordinals), Some(sequences), Ok(ordinal)) = (
            self.ordinals.get(dot.start..dot.end),
            self.sequences.get(dot.start..dot.end),
            u32::try_from(ordinal),
        ) else {
            return false;
        };
        ordinals
            .binary_search(&ordinal)
            .ok()
            .and_then(|at| sequences.get(at))
            .is_some_and(|seen| *seen >= sequence)
    }

    /// Whether the discharged record at `row` observes the discharged `earlier`.
    fn covers(&self, row: usize, earlier: &Digest) -> bool {
        let (Some(dot), Some(earlier)) = (
            self.dots.get(row),
            self.rows.get(earlier).and_then(|at| self.dots.get(*at)),
        ) else {
            return false;
        };
        let (Some(ordinals), Some(sequences)) = (
            self.ordinals.get(dot.start..dot.end),
            self.sequences.get(dot.start..dot.end),
        ) else {
            return false;
        };
        ordinals
            .binary_search(&earlier.actor)
            .ok()
            .and_then(|at| sequences.get(at))
            .is_some_and(|seen| *seen >= earlier.sequence)
    }
}

impl Projection {
    /// Whether `later`'s causal past reaches `sequence` of `actor`: what [`Projection::observes`]
    /// answers for a record that is not in the index, such as a candidate of a checkpoint's state
    /// whose record lies below the floor. Answered from the version vectors where `later` has a
    /// row, else by walking `later`'s retained parents to the records with a row.
    #[must_use]
    pub fn reaches(&self, index: &Index, later: &Digest, actor: &Actor, sequence: u64) -> bool {
        let vectors = &self.vectors;
        let mut todo = vec![*later];
        let mut visited = BTreeSet::new();
        while let Some(id) = todo.pop() {
            if !visited.insert(id) {
                continue;
            }
            if let Some(row) = vectors.rows.get(&id) {
                if vectors.reaches(*row, actor, sequence) {
                    return true;
                }
                continue;
            }
            match index.records.get(&id) {
                Some(header) if header.actor == *actor && header.sequence >= sequence => {
                    return true;
                }
                Some(header) => todo.extend(&header.parents),
                None => {}
            }
        }
        false
    }

    /// [`Index::observes`] of the projected `index`, answered from the version vectors
    /// where `later` has a row: then `later` observes exactly the records with a row its
    /// vector reaches, and nothing else (every ancestor of a record with a row has one).
    /// Any other `later` (pending, excluded, quarantined, or past the vectors' budget)
    /// walks its retained parents as [`Index::observes`] does, and stops at each record
    /// with a row, whose vector answers for everything below it. `index` must be the
    /// index this projection came from, or one that retains more.
    #[must_use]
    pub fn observes(&self, index: &Index, later: &Digest, earlier: &Digest) -> bool {
        let vectors = &self.vectors;
        if let Some(row) = vectors.rows.get(later) {
            return vectors.covers(*row, earlier);
        }
        if !index.records.contains_key(later) {
            return false;
        }
        let earlier_discharged = vectors.rows.contains_key(earlier);
        let mut todo = vec![*later];
        let mut visited = BTreeSet::new();
        while let Some(id) = todo.pop() {
            if !visited.insert(id) {
                continue;
            }
            if &id == earlier {
                return index.records.contains_key(earlier) || index.floor.contains_key(earlier);
            }
            if let Some(row) = vectors.rows.get(&id) {
                if earlier_discharged && vectors.covers(*row, earlier) {
                    return true;
                }
                continue;
            }
            if let Some(header) = index.records.get(&id) {
                todo.extend(&header.parents);
            }
        }
        false
    }
}

impl Index {
    /// Empty index with an explicit capacity. The integrator also bounds payload bytes.
    pub fn new(capacity: usize) -> Self {
        Self {
            records: BTreeMap::new(),
            frontier: BTreeMap::new(),
            capacity,
            floor: BTreeMap::new(),
        }
    }

    /// Admit `record` as a floor record ([`FloorRecord`]). `false` when the index already holds
    /// that record, retained or as a floor record with the same past. A floor record takes no
    /// capacity: it stands for history the index does not hold.
    ///
    /// # Errors
    /// [`Refusal::Shape`] for a malformed header or a past that does not include the record's own
    /// sequence at its actor; [`Refusal::DigestCollision`] for a different header or past under
    /// an id already held.
    pub fn insert_floor(&mut self, record: FloorRecord) -> Result<bool, Refusal> {
        if !record.header.is_shaped()
            || record.past.get(&record.header.actor) != Some(&record.header.sequence)
        {
            return Err(Refusal::Shape);
        }
        if let Some(held) = self.records.get(&record.header.id) {
            return if *held == record.header {
                Ok(false)
            } else {
                Err(Refusal::DigestCollision)
            };
        }
        match self.floor.entry(record.header.id) {
            Entry::Occupied(old) if *old.get() == record => Ok(false),
            Entry::Occupied(_) => Err(Refusal::DigestCollision),
            Entry::Vacant(slot) => {
                slot.insert(record);
                Ok(true)
            }
        }
    }

    /// The floor records, by id.
    #[must_use]
    pub fn floor(&self) -> &BTreeMap<Digest, FloorRecord> {
        &self.floor
    }

    /// Check admission of a verified header without changing this index.
    ///
    /// `false` is an identical duplicate. This reserves no capacity: a later insertion
    /// checks the then-current state again.
    ///
    /// # Errors
    /// [`Refusal`] names malformed headers, digest collisions and exhausted capacity.
    pub fn check_insert(&self, header: &Header) -> Result<bool, Refusal> {
        if !header.is_shaped() {
            return Err(Refusal::Shape);
        }
        Self::admit_shaped(
            header,
            self.records.get(&header.id),
            self.records.len(),
            self.capacity,
        )
    }

    /// Start a borrowed admission proposal without reserving or cloning history.
    /// Its headers must remain available while the proposal is used.
    #[must_use]
    pub fn proposal<'headers>(&self) -> Proposal<'_, 'headers> {
        Proposal {
            index: self,
            proposed: BTreeMap::new(),
        }
    }

    /// Check a sequence of verified headers against this index and earlier headers
    /// in the sequence, without cloning retained history or reserving capacity.
    /// Returns the number of distinct new headers. Duplicate identities are compared
    /// with both retained and proposed headers, and consume no additional capacity.
    /// Scratch space is proportional to distinct new headers, bounded by capacity.
    /// Authentication and application policy remain the caller's obligations.
    ///
    /// # Errors
    /// The first [`Refusal`] sequential insertion would produce; the index is unchanged
    /// even when an earlier header would have been admitted. Actual insertion must
    /// still check the then-current state.
    pub fn check_insert_many<'h>(
        &self,
        headers: impl IntoIterator<Item = &'h Header>,
    ) -> Result<usize, Refusal> {
        let mut proposal = self.proposal();
        for header in headers {
            proposal.check_insert(header)?;
        }
        Ok(proposal.new_records())
    }

    fn admit_shaped(
        header: &Header,
        old: Option<&Header>,
        retained: usize,
        capacity: usize,
    ) -> Result<bool, Refusal> {
        if let Some(old) = old {
            return if old == header {
                Ok(false)
            } else {
                Err(Refusal::DigestCollision)
            };
        }
        if !sync_within_capacity(retained as u64, capacity as u64) {
            return Err(Refusal::Capacity);
        }
        Ok(true)
    }

    /// Insert a verified header. `false` is an identical duplicate.
    ///
    /// # Errors
    /// [`Refusal`] names malformed headers, digest collisions and exhausted capacity.
    pub fn insert(&mut self, header: Header) -> Result<bool, Refusal> {
        if !header.is_shaped() {
            return Err(Refusal::Shape);
        }
        // One search of `records`. The entry holds the map, so the retained count is read
        // first; a vacant entry left unfilled changes nothing.
        let retained = self.records.len();
        let capacity = self.capacity;
        match self.records.entry(header.id) {
            Entry::Occupied(old) => {
                Self::admit_shaped(&header, Some(old.get()), retained, capacity)
            }
            Entry::Vacant(slot) => {
                let accepted = Self::admit_shaped(&header, None, retained, capacity)?;
                if accepted {
                    let highest = self.frontier.entry(header.actor).or_insert(0);
                    *highest = (*highest).max(header.sequence);
                    slot.insert(header);
                }
                Ok(accepted)
            }
        }
    }

    /// Every retained digest, including pending records and fork evidence.
    pub fn inventory(&self) -> impl Iterator<Item = &Digest> {
        self.records.keys()
    }

    /// Header by exact content identity.
    pub fn get(&self, id: &Digest) -> Option<&Header> {
        self.records.get(id)
    }

    /// Each retained actor's highest retained sequence, kept at insert, so a peer's
    /// summary costs one entry per actor and no scan. A summary, never evidence: it
    /// says nothing of a gap or a fork below it, which [`Index::forks`] and the
    /// projection judge, and it never stands for the inventory it summarizes.
    #[must_use]
    pub fn frontier(&self) -> &BTreeMap<Actor, u64> {
        &self.frontier
    }

    /// One deterministic witness per conflicting actor. Each pair references
    /// retained records, even when a contradictory predecessor is missing.
    /// The lexicographically least pair is independent of arrival order.
    /// Applications can transfer authenticated source records as restrictive
    /// evidence without treating their payloads as authorized operations.
    /// [`forks_of`] answers the same over borrowed headers, with no index built.
    pub fn forks(&self) -> BTreeMap<Actor, Fork> {
        let mut retained = self.records.values();
        let (Some(first), Some(second)) = (retained.next(), retained.next()) else {
            return BTreeMap::new();
        };
        // `records` iterates in id order, so these are the globally least retained
        // sources. If they contradict and all sources have this actor, no other pair can
        // improve the witness. This shortcut reads that order, which `forks_of`'s input
        // does not have; the scan below reads no order.
        if let Some(fork) = Fork::between(first, second)
            .filter(|_| retained.all(|header| header.actor == first.actor))
        {
            return BTreeMap::from([(first.actor, fork)]);
        }
        forks_by_actor(&mut self.records.values().collect::<Vec<_>>())
    }

    /// Whether `later` transitively names `earlier` as a dependency. Equality is
    /// reflexive only for a retained record. Missing history never proves observation.
    pub fn observes(&self, later: &Digest, earlier: &Digest) -> bool {
        if !self.records.contains_key(later) {
            return false;
        }
        let mut todo = vec![*later];
        let mut visited = BTreeSet::new();
        while let Some(id) = todo.pop() {
            if !visited.insert(id) {
                continue;
            }
            if &id == earlier {
                return self.records.contains_key(earlier);
            }
            if let Some(header) = self.records.get(&id) {
                todo.extend(&header.parents);
            }
        }
        false
    }

    /// Every retained record `id` transitively names through retained records: exactly
    /// the `earlier` other than `id` for which [`Index::observes`]`(id, earlier)` holds,
    /// found in one walk, so a caller asking that of many records walks once. Empty for
    /// a record not retained.
    #[must_use]
    pub fn ancestors(&self, id: &Digest) -> BTreeSet<Digest> {
        let mut found = BTreeSet::new();
        let Some(header) = self.records.get(id) else {
            return found;
        };
        let mut todo = header.parents.clone();
        while let Some(parent) = todo.pop() {
            if parent == *id {
                continue;
            }
            let Some(header) = self.records.get(&parent) else {
                continue;
            };
            if found.insert(parent) {
                todo.extend(&header.parents);
            }
        }
        found
    }

    /// Recompute from the set, withdrawing an equivocating actor AND all its dependents.
    /// Never incrementally accept a winner based on which branch arrived first.
    pub fn project(&self) -> Projection {
        self.project_excluding(&BTreeSet::new())
    }

    /// Derive a projection under deterministic application policy exclusions.
    /// Excluded records remain in inventory and fork detection; every dependent
    /// is withheld by the same exact-parent closure as missing or forked history.
    /// The policy must derive from authenticated retained facts, not arrival time.
    pub fn project_excluding(&self, excluded: &BTreeSet<Digest>) -> Projection {
        let mut actors: BTreeSet<Actor> = self.frontier.keys().copied().collect();
        for record in self.floor.values() {
            actors.extend(record.past.keys().copied());
        }
        let mut out = Projection {
            quarantined: self.forks().into_keys().collect(),
            vectors: VersionVectors::new(actors.into_iter().collect(), self.records.len()),
            ..Projection::default()
        };
        // Floor records first, each with the vector it was given and an allowance of its own,
        // so a wide past is never refused a row: a question crossing the floor has nothing
        // below it to walk.
        for record in self.floor.values() {
            out.vectors.seed(&record.header, &record.past);
            // A floor record is a head unless another one's past reaches it: every maximal
            // record of the cut is a floor record, so one that is not maximal is reached.
            let header = &record.header;
            let reached = self.floor.values().any(|other| {
                other.header.id != header.id
                    && other
                        .past
                        .get(&header.actor)
                        .is_some_and(|seen| *seen >= header.sequence)
            });
            if !reached {
                out.heads.insert(header.id);
            }
        }
        let mut waiting = BTreeMap::<Digest, u64>::new();
        let mut children = BTreeMap::<Digest, Vec<Digest>>::new();
        let mut ready = BTreeSet::new();
        for header in self.records.values() {
            out.pending.insert(header.id);
            if out.quarantined.contains(&header.actor) || excluded.contains(&header.id) {
                continue;
            }
            if let Some(previous) = header.previous {
                let Some(parent) = self
                    .records
                    .get(&previous)
                    .or_else(|| self.floor.get(&previous).map(|record| &record.header))
                else {
                    continue;
                };
                if parent.actor != header.actor
                    || !sequence_follows(parent.sequence, header.sequence)
                {
                    continue;
                }
            }
            let below: Vec<&Digest> = header
                .parents
                .iter()
                .filter(|parent| !self.floor.contains_key(*parent))
                .collect();
            waiting.insert(header.id, below.len() as u64);
            if below.is_empty() {
                ready.insert(header.id);
            }
            for parent in below {
                children.entry(*parent).or_default().push(header.id);
            }
        }
        while let Some(id) = ready.pop_first() {
            out.pending.remove(&id);
            out.ordered.push(id);
            out.heads.insert(id);
            if let Some(header) = self.records.get(&id) {
                for parent in &header.parents {
                    out.heads.remove(parent);
                }
                out.vectors.discharge(header);
            }
            for child in children.get(&id).into_iter().flatten() {
                if let Some(count) = waiting.get_mut(child) {
                    *count = discharge(*count);
                    if *count == 0 {
                        ready.insert(*child);
                    }
                }
            }
        }
        out
    }
}

/// [`Index::forks`] of an index holding exactly the set of `headers`, read from the
/// borrowed headers with no index built.
///
/// The headers may come in any order, and one may come more than once: it is still the
/// one header an index would hold once. Each must be shaped ([`Header::is_shaped`]),
/// and two headers sharing an id must be equal, which is what [`Index::insert`]
/// admits; any other input gets an unspecified answer, never a panic.
pub fn forks_of<'h>(headers: impl IntoIterator<Item = &'h Header>) -> BTreeMap<Actor, Fork> {
    forks_by_actor(&mut headers.into_iter().collect::<Vec<_>>())
}

/// One canonical witness per actor whose `headers` contradict, the one fork scan
/// [`Index::forks`] and [`forks_of`] share. It reads no order of `headers` (it sorts
/// them by actor, then each actor's by sequence, and finds the least two source IDs by
/// a scan), and a header given twice cannot change its answer (below).
fn forks_by_actor(headers: &mut [&Header]) -> BTreeMap<Actor, Fork> {
    let mut out = BTreeMap::new();
    // Partition once by actor so dense-sequence sorting never compares actor bytes.
    // Each actor's witness is independent of every other actor's claims.
    headers.sort_unstable_by_key(|header| &header.actor);
    for group in headers.chunk_by_mut(|a, b| a.actor == b.actor) {
        let mut sources = group.iter().copied();
        let (Some(mut least), Some(mut second)) = (sources.next(), sources.next()) else {
            continue;
        };
        let actor = least.actor;
        if second.id < least.id {
            std::mem::swap(&mut least, &mut second);
        }
        for header in sources {
            if header.id < least.id {
                second = least;
                least = header;
            } else if header.id < second.id {
                second = header;
            }
        }
        // The two least source IDs bound every possible pair for this actor.
        // Their contradiction settles even a large, heavily forked history.
        // In any order, `least` ends with the least ID and `second` with the least
        // ID of the rest once one copy of `least` is set aside. A repeat of the least
        // header therefore leaves `second` the same header as `least`, and
        // `Fork::between` answers `None` for one header twice (`a.id == b.id`): that
        // falls through to the claim scan, which finds the witness without this
        // shortcut. A repeat of any other header leaves `second` the true second-least.
        if let Some(fork) = Fork::between(least, second) {
            out.insert(actor, fork);
            continue;
        }
        // Equal sequences need no source-ID sort: DotGroup finds the canonical pair
        // in any tie order, keeping low-dot-density histories inexpensive. After this
        // sort both claim streams below run in sequence order whatever the input's
        // order (a predecessor claim sits one below its source's own sequence), and a
        // repeated header only repeats claims, which DotGroup ignores.
        group.sort_unstable_by_key(|header| header.sequence);
        let mut own = group
            .iter()
            .map(|header| DotClaim {
                sequence: header.sequence,
                source: &header.id,
                id: &header.id,
            })
            .peekable();
        let mut previous = group
            .iter()
            .filter_map(|header| {
                header
                    .previous
                    .as_ref()
                    .zip(header.sequence.checked_sub(1))
                    .map(|(id, sequence)| DotClaim {
                        sequence,
                        source: &header.id,
                        id,
                    })
            })
            .peekable();
        let mut dot: Option<DotGroup<'_>> = None;
        let mut best: Option<Fork> = None;
        loop {
            let next = match (own.peek(), previous.peek()) {
                (Some(a), Some(b)) if a.sequence <= b.sequence => own.next(),
                (_, Some(_)) => previous.next(),
                (Some(_), None) => own.next(),
                (None, None) => None,
            };
            let Some(claim) = next else { break };
            match dot.as_mut() {
                Some(held) if held.first.sequence == claim.sequence => held.insert(claim),
                _ => {
                    if let Some(fork) = dot.take().and_then(|group| group.witness(actor)) {
                        best = Some(best.map_or(fork, |old| old.min(fork)));
                    }
                    dot = Some(DotGroup::new(claim));
                }
            }
        }
        if let Some(fork) = dot.and_then(|group| group.witness(actor)) {
            best = Some(best.map_or(fork, |old| old.min(fork)));
        }
        if let Some(fork) = best {
            out.insert(actor, fork);
        }
    }
    out
}

#[cfg(test)]
#[path = "sync_batch_tests.rs"]
mod batch_tests;

#[cfg(test)]
#[path = "sync_vector_tests.rs"]
mod vector_tests;

#[cfg(test)]
#[path = "sync_floor_tests.rs"]
mod floor_tests;

#[cfg(test)]
mod tests {
    use super::*;
    fn header(id: u8, actor: u8, sequence: u64, previous: Option<u8>, parents: &[u8]) -> Header {
        Header {
            id: [id; 32],
            actor: [actor; 48],
            sequence,
            previous: previous.map(|p| [p; 32]),
            parents: parents.iter().map(|p| [*p; 32]).collect(),
        }
    }
    fn permutations(items: &[Header], visit: &mut impl FnMut(&[Header])) {
        fn walk(prefix: &mut Vec<Header>, rest: Vec<Header>, visit: &mut impl FnMut(&[Header])) {
            if rest.is_empty() {
                visit(prefix);
                return;
            }
            for i in 0..rest.len() {
                let mut next = rest.clone();
                prefix.push(next.remove(i));
                walk(prefix, next, visit);
                prefix.pop();
            }
        }
        walk(&mut Vec::new(), items.to_vec(), visit);
    }
    /// The quadratic oracle, written apart from the scan: for each actor, the least
    /// [`Fork::between`] answer over every ordered pair of `headers`.
    fn pairwise<'h>(
        headers: impl IntoIterator<Item = &'h Header> + Clone,
    ) -> BTreeMap<Actor, Fork> {
        let mut least = BTreeMap::<Actor, Fork>::new();
        for a in headers.clone() {
            for b in headers.clone() {
                if let Some(fork) = Fork::between(a, b) {
                    least
                        .entry(fork.actor)
                        .and_modify(|old| *old = (*old).min(fork))
                        .or_insert(fork);
                }
            }
        }
        least
    }
    #[test]
    fn offline_islands_converge_after_every_delivery_order_and_duplicate() {
        let records = [
            header(1, 1, 1, None, &[]),
            header(2, 2, 1, None, &[]),
            header(3, 1, 2, Some(1), &[1, 2]),
            header(4, 2, 2, Some(2), &[2]),
        ];
        let mut reference = Index::new(8);
        for h in &records {
            reference.insert(h.clone()).unwrap();
        }
        let expected = reference.project();
        permutations(&records, &mut |order| {
            let mut index = Index::new(8);
            for h in order {
                assert!(index.insert(h.clone()).unwrap());
                assert!(!index.insert(h.clone()).unwrap());
                let p = index.project();
                let mut seen = BTreeSet::new();
                for id in p.ordered {
                    assert!(index
                        .get(&id)
                        .unwrap()
                        .parents
                        .iter()
                        .all(|parent| seen.contains(parent)));
                    seen.insert(id);
                }
            }
            assert_eq!(index.project(), expected);
        });
        assert_eq!(expected.heads, BTreeSet::from([[3; 32], [4; 32]]));
        assert!(reference.observes(&[3; 32], &[1; 32]));
        assert!(!reference.observes(&[4; 32], &[1; 32]));
    }
    #[test]
    fn forks_withdraw_past_effects_and_dependents_even_when_watermarks_match() {
        let a = header(1, 1, 1, None, &[]);
        let b = header(2, 1, 1, None, &[]);
        let child = header(3, 2, 1, None, &[1]);
        permutations(&[a, b, child], &mut |order| {
            let mut index = Index::new(8);
            for h in order {
                index.insert(h.clone()).unwrap();
            }
            let p = index.project();
            assert!(p.ordered.is_empty());
            assert_eq!(p.quarantined, BTreeSet::from([[1; 48]]));
            assert_eq!(p.pending.len(), 3);
            assert_eq!(
                index.inventory().count(),
                3,
                "fork evidence stays in repair inventory"
            );
        });
    }
    #[test]
    fn gaps_cycles_bad_predecessors_and_caps_cannot_become_visible() {
        let mut index = Index::new(3);
        index.insert(header(2, 1, 2, Some(1), &[1])).unwrap();
        assert!(index.project().ordered.is_empty());
        index.insert(header(1, 2, 1, None, &[])).unwrap();
        assert_eq!(index.project().ordered, [[1; 32]]);
        assert_eq!(
            index.insert(header(5, 3, 1, None, &[5])),
            Err(Refusal::Shape)
        );
        index.insert(header(3, 3, 1, None, &[4])).unwrap();
        assert_eq!(
            index.insert(header(4, 4, 1, None, &[3])),
            Err(Refusal::Capacity)
        );
        assert_eq!(index.inventory().count(), 3);
        assert!(!sequence_follows(u64::MAX, 0));
        assert!(!sequence_follows(0, 0));
        assert!(sequence_follows(0, 1));
    }

    #[test]
    fn policy_exclusions_withhold_dependents_without_losing_evidence() {
        let mut index = Index::new(8);
        for h in [
            header(1, 1, 1, None, &[]),
            header(2, 2, 1, None, &[1]),
            header(3, 3, 1, None, &[]),
        ] {
            index.insert(h).unwrap();
        }
        let view = index.project_excluding(&BTreeSet::from([[1; 32]]));
        assert_eq!(view.ordered, [[3; 32]]);
        assert_eq!(view.pending, BTreeSet::from([[1; 32], [2; 32]]));
        assert_eq!(index.inventory().count(), 3);
        assert_eq!(
            index.project().ordered.len(),
            3,
            "the evidence set is unchanged"
        );
    }

    #[test]
    fn predecessor_claims_expose_forks_before_the_missing_branch_arrives() {
        let records = [
            header(1, 1, 1, None, &[]),
            header(3, 1, 2, Some(2), &[2]),
            header(4, 2, 1, None, &[1]),
            header(5, 3, 1, None, &[]),
        ];
        permutations(&records, &mut |order| {
            let mut index = Index::new(8);
            for h in order {
                index.insert(h.clone()).unwrap();
            }
            for excluded in [BTreeSet::new(), BTreeSet::from([[3; 32]])] {
                let view = index.project_excluding(&excluded);
                assert_eq!(view.quarantined, BTreeSet::from([[1; 48]]));
                assert_eq!(view.ordered, [[5; 32]]);
                assert_eq!(view.pending, BTreeSet::from([[1; 32], [3; 32], [4; 32]]));
                assert_eq!(index.inventory().count(), 4);
            }
            // Arrival of the committed predecessor adds evidence; it cannot
            // repair the already inconsistent dot or revive its dependents.
            index.insert(header(2, 1, 1, None, &[])).unwrap();
            assert_eq!(index.project().ordered, [[5; 32]]);
            assert_eq!(index.project().quarantined, BTreeSet::from([[1; 48]]));
        });
    }

    #[test]
    fn matching_predecessor_claims_and_sequence_boundaries_are_not_forks() {
        let mut index = Index::new(8);
        index.insert(header(1, 1, 1, None, &[])).unwrap();
        index.insert(header(2, 1, 2, Some(1), &[1])).unwrap();
        index.insert(header(3, 2, u64::MAX, Some(4), &[4])).unwrap();
        assert!(index.project().quarantined.is_empty());
        assert_eq!(index.project().ordered, [[1; 32], [2; 32]]);
        index
            .insert(header(5, 2, u64::MAX - 1, Some(6), &[6]))
            .unwrap();
        assert_eq!(index.project().quarantined, BTreeSet::from([[2; 48]]));
    }

    #[test]
    fn fork_witnesses_name_retained_sources_and_are_canonical_in_every_order() {
        // A predecessor's source can sort before the matching own claim; a later dot can
        // also supply the lexicographically least witness of the whole actor.
        for (records, second) in [
            (
                vec![
                    header(1, 1, 2, Some(2), &[2]),
                    header(2, 1, 1, None, &[]),
                    header(3, 1, 1, None, &[]),
                    header(7, 2, 1, None, &[]),
                    header(9, 2, 1, None, &[]),
                ],
                3,
            ),
            (
                vec![
                    header(1, 1, 4, Some(8), &[8]),
                    header(2, 1, 1, None, &[]),
                    header(3, 1, 2, Some(4), &[4]),
                    header(5, 1, 3, Some(6), &[6]),
                    header(7, 2, 1, None, &[]),
                    header(9, 2, 1, None, &[]),
                ],
                5,
            ),
        ] {
            permutations(&records, &mut |order| {
                let mut index = Index::new(8);
                for h in order {
                    index.insert(h.clone()).unwrap();
                }
                let expected = pairwise(&records);
                let forks = index.forks();
                assert_eq!(forks, expected);
                assert_eq!(forks[&[1; 48]].first, [1; 32]);
                assert_eq!(forks[&[1; 48]].second, [second; 32]);
                assert_eq!(forks[&[2; 48]], Fork::sources([2; 48], [7; 32], [9; 32]));
                for fork in forks.values() {
                    assert_eq!(
                        Fork::between(
                            index.get(&fork.first).unwrap(),
                            index.get(&fork.second).unwrap()
                        ),
                        Some(*fork)
                    );
                }
                assert_eq!(index.project().quarantined, forks.into_keys().collect());
            });
        }
    }

    proptest::proptest! {
        #[test]
        fn fork_scan_matches_all_retained_pairs(
            rows in proptest::collection::vec(
                (0u8..4, 1u64..9, proptest::prop_oneof![0u8..40, 128u8..255]),
                0..40,
            ),
            homogeneous in proptest::bool::ANY,
            chained in proptest::bool::ANY,
            mutation_after in proptest::option::of(2u64..7),
            order in proptest::strategy::Strategy::prop_shuffle(
                proptest::strategy::Just((0..40).collect::<Vec<usize>>()),
            ),
            repeats in proptest::collection::vec((0usize..40, 0usize..80), 0..6),
        ) {
            let mut index = Index::new(rows.len());
            let mut tips = [None::<(u8, u64)>; 4];
            for (row, (actor, sequence, predecessor)) in rows.into_iter().enumerate() {
                let id = row as u8;
                let actor = if homogeneous { 0 } else { actor };
                let tip = &mut tips[usize::from(actor)];
                let sequence = if chained {
                    tip.map_or(1, |(_, sequence)| sequence.saturating_add(1))
                } else if homogeneous {
                    2
                } else {
                    sequence
                };
                let mut previous = (sequence > 1).then_some(predecessor);
                if chained {
                    previous = tip.map(|(id, _)| id);
                    // Healthy chains and their two least sources agree. A later
                    // mutated link exercises the scan beyond that compatible prefix.
                    if mutation_after.is_some_and(|after| sequence == after.saturating_add(1)) {
                        previous = Some(predecessor);
                        if previous == tip.map(|(id, _)| id) {
                            previous = Some(255);
                        }
                    }
                }
                // Arbitrary claims may name retained IDs, but never themselves.
                if previous == Some(id) {
                    previous = Some(255);
                }
                let mut h = header(id, 0, sequence, previous, &[]);
                // Shared prefixes must not merge distinct actor incarnations.
                h.actor[47] = actor;
                h.parents.extend(h.previous);
                index.insert(h).unwrap();
                *tip = Some((id, sequence));
            }
            let expected = pairwise(index.records.values());
            proptest::prop_assert_eq!(&index.forks(), &expected);
            // The same set as `forks_of` reads it: in an order the proptest chose (a
            // shuffle of 0..40 read for the retained rows alone is a uniform order of
            // them), with some headers given again at chosen places.
            let retained: Vec<&Header> = index.records.values().collect();
            let mut read: Vec<&Header> =
                order.iter().filter_map(|row| retained.get(*row).copied()).collect();
            for (row, at) in repeats {
                if let Some(twice) = retained.get(row) {
                    read.insert(at % (read.len() + 1), twice);
                }
            }
            proptest::prop_assert_eq!(forks_of(read), expected);
        }
    }

    /// Ten shaped headers of two actors, in id order, which is not their sequence order.
    /// Actor 1: a linked chain 5 <- 3 <- 7 (sequences 1, 2, 3); 6, a second header at
    /// sequence 2; 2, at sequence 3, linked to that forked branch; 4, at sequence 4, whose
    /// predecessor 30 is never retained; and 1, at sequence 9, past a gap. Actor 2: 8 and
    /// 9 at `u64::MAX`, 8 linked to 10 at `u64::MAX - 1` and 9 naming another predecessor
    /// there.
    fn fork_pool() -> [Header; 10] {
        [
            header(1, 1, 9, Some(31), &[31]),
            header(2, 1, 3, Some(6), &[6]),
            header(3, 1, 2, Some(5), &[5]),
            header(4, 1, 4, Some(30), &[30]),
            header(5, 1, 1, None, &[]),
            header(6, 1, 2, Some(5), &[5]),
            header(7, 1, 3, Some(3), &[3]),
            header(8, 2, u64::MAX, Some(10), &[10]),
            header(9, 2, u64::MAX, Some(32), &[32]),
            header(10, 2, u64::MAX - 1, Some(33), &[33]),
        ]
    }

    #[test]
    fn forks_of_reads_any_order_and_any_repeat_as_forks_of_the_set() {
        let pool = fork_pool();
        assert_eq!(
            pairwise(&pool),
            BTreeMap::from([
                ([1; 48], Fork::sources([1; 48], [2; 32], [3; 32])),
                ([2; 48], Fork::sources([2; 48], [8; 32], [9; 32])),
            ]),
            "the pool forks both actors, and actor 1's least pair is not its two least IDs"
        );
        for mask in 0..1u32 << pool.len() {
            let set: Vec<&Header> = pool
                .iter()
                .enumerate()
                .filter(|(bit, _)| mask >> bit & 1 == 1)
                .map(|(_, h)| h)
                .collect();
            let mut index = Index::new(pool.len());
            for h in &set {
                assert_eq!(index.insert((*h).clone()), Ok(true));
            }
            let expected = pairwise(set.iter().copied());
            assert_eq!(
                index.forks(),
                expected,
                "Index::forks of subset {mask:#012b}"
            );
            let descending: Vec<&Header> = set.iter().rev().copied().collect();
            let mut rotated = set.clone();
            rotated.rotate_left(set.len() / 2);
            for (name, order) in [
                ("ascending", set.clone()),
                ("descending", descending),
                ("rotated", rotated),
            ] {
                assert_eq!(
                    forks_of(order.iter().copied()),
                    expected,
                    "forks_of, {name} subset {mask:#012b}"
                );
                for twice in &order {
                    assert_eq!(
                        forks_of(order.iter().copied().chain([*twice])),
                        expected,
                        "forks_of, {name} subset {mask:#012b} with {} again last",
                        twice.id[0]
                    );
                }
            }
        }
    }

    /// Component wall-time measurement; no latency threshold is a correctness assertion.
    #[test]
    #[ignore = "isolated optimized fork-scan measurement"]
    fn fork_scan_measurement() {
        fn digest(row: usize, compatible_prefix: bool) -> Digest {
            let mut id = [0; 32];
            let mixed = if compatible_prefix {
                row as u64 + 1
            } else {
                (row as u64 + 1)
                    .wrapping_mul(0x9e3779b97f4a7c15)
                    .rotate_left(17)
            };
            id[..8].copy_from_slice(&mixed.to_be_bytes());
            id
        }
        for records in [128usize, 3_000, 8_192] {
            for (actors, forked, compatible_prefix) in [
                (1usize, false, false),
                (64, false, false),
                (1, true, false),
                (2, true, false),
                (64, true, false),
                (1, true, true),
                (2, true, true),
                (64, true, true),
            ] {
                let mut index = Index::new(records);
                for row in 0..records {
                    let sequence = if compatible_prefix {
                        if row < actors {
                            1
                        } else {
                            2
                        }
                    } else if forked {
                        1
                    } else {
                        row / actors + 1
                    };
                    let previous = (sequence > 1).then(|| {
                        digest(
                            if compatible_prefix {
                                row % actors
                            } else {
                                row - actors
                            },
                            compatible_prefix,
                        )
                    });
                    index
                        .insert(Header {
                            id: digest(row, compatible_prefix),
                            actor: [(row % actors) as u8; 48],
                            sequence: sequence as u64,
                            previous,
                            parents: previous.into_iter().collect(),
                        })
                        .unwrap();
                }
                let expected = if compatible_prefix {
                    records.saturating_sub(2 * actors).min(actors)
                } else if forked {
                    actors
                } else {
                    0
                };
                assert_eq!(index.forks().len(), expected);
                let iterations = 1_000_000 / records;
                let started = std::time::Instant::now();
                for _ in 0..iterations {
                    std::hint::black_box(std::hint::black_box(&index).forks());
                }
                eprintln!(
                    "FORK-SCAN records={records} actors={actors} forked={forked} compatible_prefix={compatible_prefix} iterations={iterations} wall_ns_per_scan={}",
                    started.elapsed().as_nanos() / iterations as u128,
                );
            }
        }
    }

    #[test]
    fn a_fork_pair_requires_distinct_shaped_headers_of_the_same_actor() {
        let a = header(1, 1, 1, None, &[]);
        let b = header(3, 1, 2, Some(2), &[2]);
        assert_eq!(
            Fork::between(&a, &b),
            Some(Fork::sources([1; 48], [1; 32], [3; 32]))
        );
        assert_eq!(Fork::between(&b, &a), Fork::between(&a, &b));
        assert_eq!(Fork::between(&a, &a), None);
        assert_eq!(Fork::between(&a, &header(2, 2, 1, None, &[])), None);
        assert_eq!(Fork::between(&a, &header(2, 1, 2, Some(1), &[1])), None);
        assert_eq!(Fork::between(&a, &header(2, 1, 0, Some(1), &[1])), None);
        assert_eq!(Fork::between(&a, &header(2, 1, 2, Some(1), &[])), None);
    }

    /// What `observes` answers to, written apart from it: `later` reaches `earlier` along the
    /// parents of retained records, and both ends are retained.
    fn reaches_through_retained(index: &Index, later: &Digest, earlier: &Digest) -> bool {
        fn walk(index: &Index, at: &Digest, earlier: &Digest, seen: &mut BTreeSet<Digest>) -> bool {
            let Some(header) = index.get(at) else {
                return false;
            };
            at == earlier
                || (seen.insert(*at)
                    && header
                        .parents
                        .iter()
                        .any(|parent| walk(index, parent, earlier, seen)))
        }
        walk(index, later, earlier, &mut BTreeSet::new())
    }

    /// The first pair of `ids` on which `answer` and the law above disagree.
    fn observation_breach(
        index: &Index,
        ids: &[u8],
        answer: impl Fn(&Digest, &Digest) -> bool,
    ) -> Option<(u8, u8)> {
        ids.iter()
            .flat_map(|later| ids.iter().map(move |earlier| (*later, *earlier)))
            .find(|(later, earlier)| {
                let (later, earlier) = ([*later; 32], [*earlier; 32]);
                answer(&later, &earlier) != reaches_through_retained(index, &later, &earlier)
            })
    }

    /// The first record `view` gets wrong, written apart from the projection: it admits a record
    /// of a quarantined actor, an excluded record, or one with a parent it has not admitted first
    /// (so anything depending on any of those), or it lets a retained record be both admitted and
    /// pending, or neither.
    fn projection_breach(
        index: &Index,
        excluded: &BTreeSet<Digest>,
        view: &Projection,
    ) -> Option<Digest> {
        let quarantined: BTreeSet<Actor> = index.forks().into_keys().collect();
        let mut admitted = BTreeSet::new();
        for id in &view.ordered {
            let Some(header) = index.get(id) else {
                return Some(*id);
            };
            if quarantined.contains(&header.actor)
                || excluded.contains(id)
                || !header
                    .parents
                    .iter()
                    .all(|parent| admitted.contains(parent))
            {
                return Some(*id);
            }
            admitted.insert(*id);
        }
        index
            .inventory()
            .find(|id| admitted.contains(*id) == view.pending.contains(*id))
            .copied()
    }

    /// A forked actor's two records (1 and 2), a dependent of them (3), a record with a gap below
    /// it (4), a record the tests exclude (5) and its dependent (6), and one record nothing
    /// withholds (7).
    fn withheld_history() -> Vec<Header> {
        vec![
            header(1, 1, 1, None, &[]),
            header(2, 1, 1, None, &[]),
            header(3, 2, 1, None, &[1]),
            header(4, 3, 2, Some(9), &[9]),
            header(5, 4, 1, None, &[]),
            header(6, 5, 1, None, &[5]),
            header(7, 6, 1, None, &[]),
        ]
    }

    #[test]
    fn observes_is_false_across_a_missing_intermediate() {
        let mut index = Index::new(8);
        index.insert(header(1, 1, 1, None, &[])).unwrap();
        index.insert(header(3, 1, 3, Some(2), &[2])).unwrap();
        assert!(
            !index.observes(&[3; 32], &[1; 32]),
            "both ends are retained and the link between them is not"
        );
        assert!(index.observes(&[3; 32], &[3; 32]));
        // The missing record proves the link once it is here, in the direction the link runs.
        index.insert(header(2, 1, 2, Some(1), &[1])).unwrap();
        assert!(index.observes(&[3; 32], &[1; 32]));
        assert!(!index.observes(&[1; 32], &[3; 32]));
    }

    #[test]
    fn observes_is_false_for_a_record_not_retained() {
        let mut index = Index::new(8);
        index.insert(header(1, 1, 1, None, &[])).unwrap();
        index.insert(header(3, 2, 1, None, &[1, 2])).unwrap();
        assert!(index.observes(&[3; 32], &[1; 32]));
        assert!(
            !index.observes(&[3; 32], &[2; 32]),
            "an `earlier` a retained record names as its parent and nothing retains"
        );
        assert!(
            !index.observes(&[2; 32], &[1; 32]),
            "a `later` not retained"
        );
        assert!(
            !index.observes(&[2; 32], &[2; 32]),
            "equality is reflexive only for a retained record"
        );
    }

    #[test]
    fn admission_queries_leave_room_unreserved_and_recheck_changed_state() {
        let mut index = Index::new(1);
        let first = header(1, 1, 1, None, &[]);
        let other = header(2, 2, 1, None, &[]);
        for _ in 0..2 {
            assert_eq!(index.check_insert(&first), Ok(true));
            assert_eq!(index.inventory().count(), 0);
        }
        assert_eq!(index.insert(other.clone()), Ok(true));
        assert_eq!(index.check_insert(&first), Err(Refusal::Capacity));
        assert_eq!(index.insert(first), Err(Refusal::Capacity));
        assert_eq!(index.check_insert(&other), Ok(false));
        assert_eq!(index.inventory().count(), 1);
        assert_eq!(index.get(&other.id), Some(&other));
    }

    #[test]
    fn a_refusal_leaves_the_whole_index_unchanged() {
        let mut index = Index::new(3);
        for h in [
            header(1, 1, 1, None, &[]),
            header(2, 1, 1, None, &[]),
            header(3, 2, 2, Some(4), &[4]),
        ] {
            index.insert(h).unwrap();
        }
        let state = |index: &Index| {
            let records: Vec<Header> = index
                .inventory()
                .map(|id| index.get(id).unwrap().clone())
                .collect();
            let excluding = index.project_excluding(&BTreeSet::from([[2; 32]]));
            (records, index.forks(), index.project(), excluding)
        };
        let before = state(&index);
        assert!(!before.1.is_empty() && !before.2.pending.is_empty());
        for (refused, why) in refused_headers() {
            assert_eq!(index.check_insert(&refused), Err(why));
            assert_eq!(state(&index), before, "{why:?} changed the queried index");
            assert_eq!(index.insert(refused), Err(why));
            assert_eq!(state(&index), before, "{why:?} changed the index");
        }
        assert_eq!(
            index.insert(header(1, 1, 1, None, &[])),
            Ok(false),
            "an identical duplicate is no refusal, at capacity too"
        );
        assert_eq!(state(&index), before);
    }

    /// What `a_refusal_leaves_the_whole_index_unchanged` offers an index that holds 1, 2
    /// and 3 at its capacity of 3, each with the refusal it must answer: nine shapes, the
    /// last under 1's id (the shape is judged before the id is looked up, so it is no
    /// collision), a collision with 1, and a shaped new header with no room.
    fn refused_headers() -> [(Header, Refusal); 11] {
        let too_many: Vec<u8> = (0..=MAX_PARENTS as u8).collect();
        [
            (header(9, 1, 0, None, &[]), Refusal::Shape),
            (header(9, 1, 1, Some(1), &[1]), Refusal::Shape),
            (header(9, 1, 2, None, &[]), Refusal::Shape),
            (header(9, 1, 2, Some(1), &[]), Refusal::Shape),
            (header(9, 1, 1, None, &[2, 1]), Refusal::Shape),
            (header(9, 1, 1, None, &[1, 1]), Refusal::Shape),
            (header(9, 1, 1, None, &[9]), Refusal::Shape),
            (header(200, 1, 1, None, &too_many), Refusal::Shape),
            (header(1, 1, 0, None, &[]), Refusal::Shape),
            (header(1, 7, 1, None, &[]), Refusal::DigestCollision),
            (header(9, 7, 1, None, &[]), Refusal::Capacity),
        ]
    }

    #[test]
    fn exactly_max_parents_is_shaped() {
        let most: Vec<u8> = (0..MAX_PARENTS as u8).collect();
        let mut index = Index::new(1);
        assert_eq!(index.insert(header(200, 1, 1, None, &most)), Ok(true));
    }

    #[test]
    fn is_shaped_is_false_exactly_where_insert_refuses_the_shape() {
        let most: Vec<u8> = (0..MAX_PARENTS as u8).collect();
        let headers: Vec<Header> = refused_headers()
            .map(|(h, _)| h)
            .into_iter()
            .chain([header(200, 1, 1, None, &most)])
            .collect();
        // Written apart from the code: the nine shape refusals, the collision and the
        // capacity refusal (both shaped), then exactly MAX_PARENTS parents.
        let shaped = [
            false, false, false, false, false, false, false, false, false, true, true, true,
        ];
        assert_eq!(headers.len(), shaped.len());
        for (row, (h, shaped)) in headers.into_iter().zip(shaped).enumerate() {
            assert_eq!(h.is_shaped(), shaped, "row {row}: is_shaped");
            assert_eq!(
                Index::new(1).insert(h) == Err(Refusal::Shape),
                !shaped,
                "row {row}: insert"
            );
        }
    }

    #[test]
    fn every_order_and_duplicate_converges_on_what_it_withholds() {
        let records = withheld_history();
        let excluded = BTreeSet::from([[5; 32]]);
        let mut reference = Index::new(16);
        for h in &records {
            reference.insert(h.clone()).unwrap();
        }
        let whole = reference.project();
        let view = reference.project_excluding(&excluded);
        assert_eq!(whole.quarantined, BTreeSet::from([[1; 48]]));
        assert_eq!(whole.ordered, [[5; 32], [6; 32], [7; 32]]);
        assert_eq!(view.ordered, [[7; 32]]);
        assert_eq!(
            view.pending,
            [1, 2, 3, 4, 5, 6].map(|id| [id; 32]).into_iter().collect()
        );
        assert_eq!(reference.inventory().count(), records.len());
        assert_eq!(
            projection_breach(&reference, &BTreeSet::new(), &whole),
            None
        );
        assert_eq!(projection_breach(&reference, &excluded, &view), None);
        permutations(&records, &mut |order| {
            let mut index = Index::new(16);
            for h in order {
                assert_eq!(index.insert(h.clone()), Ok(true));
                assert_eq!(index.insert(h.clone()), Ok(false));
            }
            assert_eq!(index.project(), whole);
            assert_eq!(index.project_excluding(&excluded), view);
            assert_eq!(index.forks(), reference.forks());
        });
    }

    #[test]
    fn the_observation_law_catches_a_walk_that_crosses_a_missing_parent() {
        let mut index = Index::new(8);
        index.insert(header(1, 1, 1, None, &[])).unwrap();
        index.insert(header(3, 1, 3, Some(2), &[2])).unwrap();
        index.insert(header(4, 2, 1, None, &[3])).unwrap();
        index.insert(header(5, 3, 1, None, &[1, 6])).unwrap();
        index.insert(header(6, 4, 1, None, &[5])).unwrap();
        let ids = [1, 2, 3, 4, 5, 6];
        assert_eq!(
            observation_breach(&index, &ids, |later, earlier| index
                .observes(later, earlier)),
            None
        );
        // Planted: an actor's dense chain read as if no link of it could be missing, the
        // watermark reasoning this index exists to refuse.
        let watermark = |later: &Digest, earlier: &Digest| {
            index.observes(later, earlier)
                || matches!(
                    (index.get(later), index.get(earlier)),
                    (Some(l), Some(e)) if l.actor == e.actor && l.sequence >= e.sequence
                )
        };
        assert_eq!(
            observation_breach(&index, &ids, watermark),
            Some((3, 1)),
            "NEGATIVE CONTROL: the law misses an `observes` that crosses a missing parent"
        );
    }

    #[test]
    fn the_projection_law_catches_a_dependent_of_a_quarantined_actor() {
        let mut index = Index::new(16);
        for h in withheld_history() {
            index.insert(h).unwrap();
        }
        let none = BTreeSet::new();
        let excluded = BTreeSet::from([[5; 32]]);
        // Planted, one by one: the projection admits what it must withhold, the dependent of a
        // quarantined actor and of an excluded record among them.
        for (policy, id) in [(&none, 1), (&none, 3), (&excluded, 5), (&excluded, 6)] {
            let mut planted = index.project_excluding(policy);
            assert!(planted.pending.remove(&[id; 32]));
            planted.ordered.push([id; 32]);
            assert_eq!(
                projection_breach(&index, policy, &planted),
                Some([id; 32]),
                "NEGATIVE CONTROL: the law misses record {id} admitted"
            );
        }
        // Planted: a withheld record dropped from the view, as if it had left the inventory.
        let mut planted = index.project();
        assert!(planted.pending.remove(&[1; 32]));
        assert_eq!(
            projection_breach(&index, &none, &planted),
            Some([1; 32]),
            "NEGATIVE CONTROL: the law misses evidence dropped from the view"
        );
    }
}
