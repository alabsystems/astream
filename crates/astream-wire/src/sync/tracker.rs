// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! What a projection answers about heads, pending records, quarantined actors and each actor's
//! tip, kept as each header arrives.
//!
//! [`super::Index`] feeds its [`Tracker`] every header it newly retains and every floor record it
//! newly admits, and nothing else: a duplicate or a refusal changes nothing. After each feed the
//! tracker equals [`super::Index::project`] on those fields, without reading the whole set.
//!
//! The rule it keeps is the projection's. Let R be the retained records, F the floor records, Q
//! the actors whose retained records contradict ([`super::Index::forks`]) and D the discharged
//! records. D is the least set with: `r ∈ D` exactly when r's actor is not in Q, r's predecessor
//! link is absent or names a held record of r's actor one sequence below, and every parent of r
//! is in F or in D. Then the pending set is `R \ D`, and the heads are the records of D and the
//! floor records no other floor record's past reaches, less every parent a record of D names.
//!
//! An insert reads the inserted header, its parents, its dots and its children, and the
//! records whose state it changes. A fork withdraws its actor's discharged records and every
//! discharged record above them, once: a record of a quarantined actor never discharges again,
//! so neither does anything above it. A withdrawal reads each withdrawn record, its parents and
//! its children; a parent is a head again when its count of discharged records naming it
//! falls to zero. Nothing here scans the retained set or the pending set.

use super::{discharge, sequence_follows, Actor, Digest, FloorRecord, Header, Headers};
use std::borrow::Cow;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

/// An index's floor records, by id.
type Floor = BTreeMap<Digest, FloorRecord>;

/// How a pending record's predecessor link stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Link {
    /// The record has no predecessor: it is its actor's first.
    None,
    /// The predecessor is neither retained nor a floor record.
    Unknown,
    /// The predecessor is held, of the record's actor, one sequence below it.
    Good,
    /// The predecessor is held and is of another actor or not one sequence below. Headers are
    /// immutable by id, so this never changes.
    Bad,
}

/// What a pending record waits on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Wait {
    /// Its parents that are neither floor records nor discharged.
    pub unmet: u64,
    /// Its predecessor link.
    pub link: Link,
}

/// An actor's highest record among the discharged and floor records, by sequence, then id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tip {
    /// The record's sequence.
    pub sequence: u64,
    /// The record's id.
    pub id: Digest,
}

/// The fields of a projection an index keeps as each header arrives
/// ([`super::Index::tracker`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tracker {
    /// Every retained record not discharged, with what it waits on.
    pending: BTreeMap<Digest, Wait>,
    /// Discharged and unreached floor records that no discharged record names.
    heads: BTreeSet<Digest>,
    /// Actors whose retained records contradict.
    quarantined: BTreeSet<Actor>,
    /// Each actor's discharged sequences, as disjoint inclusive intervals keyed by their start.
    runs: BTreeMap<Actor, BTreeMap<u64, u64>>,
    /// The floor records no other floor record's past reaches, by actor, as (sequence, id).
    floor_max: BTreeMap<Actor, BTreeSet<(u64, Digest)>>,
    /// For each actor, the highest sequence any floor record's past holds.
    floor_top: BTreeMap<Actor, u64>,
    /// Each actor's highest floor record.
    floor_tip: BTreeMap<Actor, Tip>,
    /// Each actor's highest discharged or floor record.
    tips: BTreeMap<Actor, Tip>,
    /// For each record a discharged record names, how many discharged records name it.
    named: BTreeMap<Digest, u64>,
}

/// Discharged records returned to pending, worked out against a tracker without changing it:
/// a fork applies one ([`Tracker::apply`]) and [`Tracked`] reads one beside the tracker.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Withdrawal {
    /// Each withdrawn record, with what it then waits on.
    withdrawn: BTreeMap<Digest, Wait>,
    /// Each pending record outside `withdrawn` that names a withdrawn record, with its count of
    /// unmet parents raised by those.
    raised: BTreeMap<Digest, Wait>,
    /// For each parent of a withdrawn record, how many withdrawn records name it.
    unnamed: BTreeMap<Digest, u64>,
    /// Records outside `withdrawn` that only withdrawn records named, and that are heads after.
    heads: BTreeSet<Digest>,
    /// Each actor with a withdrawn record: its withdrawn sequences and its tip after.
    actors: BTreeMap<Actor, (BTreeSet<u64>, Option<Tip>)>,
}

/// The tracked fields under exclusions ([`super::Index::tracked_excluding`]): what
/// [`super::Index::project_excluding`] answers for them, read from the tracker and the
/// withdrawal the exclusions make, which is all this holds of its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tracked<'a> {
    tracker: &'a Tracker,
    withdrawal: Withdrawal,
}

/// The items of `a` and `b`, each ascending by `key` and with no key in both, ascending.
fn merged<T, K: Ord>(
    a: impl Iterator<Item = T>,
    b: impl Iterator<Item = T>,
    key: impl Fn(&T) -> K,
) -> impl Iterator<Item = T> {
    let mut a = a.peekable();
    let mut b = b.peekable();
    std::iter::from_fn(move || match (a.peek(), b.peek()) {
        (Some(x), Some(y)) if key(x) > key(y) => b.next(),
        (Some(_), _) => a.next(),
        (None, _) => b.next(),
    })
}

impl Tracked<'_> {
    /// Whether `id` is a head: discharged or an unreached floor record, named by no discharged
    /// record.
    #[must_use]
    pub fn is_head(&self, id: &Digest) -> bool {
        self.withdrawal.heads.contains(id)
            || (self.tracker.heads.contains(id) && !self.withdrawal.withdrawn.contains_key(id))
    }

    /// The heads, ascending: what [`super::Projection::heads`] holds.
    pub fn heads(&self) -> impl Iterator<Item = Digest> + '_ {
        let kept = self
            .tracker
            .heads
            .iter()
            .filter(|id| !self.withdrawal.withdrawn.contains_key(*id))
            .copied();
        merged(kept, self.withdrawal.heads.iter().copied(), |id| *id)
    }

    /// What the pending record `id` waits on; `None` for a record not pending.
    #[must_use]
    pub fn wait(&self, id: &Digest) -> Option<Wait> {
        self.withdrawal
            .withdrawn
            .get(id)
            .or_else(|| self.withdrawal.raised.get(id))
            .or_else(|| self.tracker.pending.get(id))
            .copied()
    }

    /// Every retained record not discharged, with what it waits on, ascending by id: the ids are
    /// what [`super::Projection::pending`] holds.
    pub fn pending(&self) -> impl Iterator<Item = (Digest, Wait)> + '_ {
        let kept = self.tracker.pending.iter().map(|(id, wait)| {
            (
                *id,
                self.withdrawal.raised.get(id).copied().unwrap_or(*wait),
            )
        });
        let withdrawn = self
            .withdrawal
            .withdrawn
            .iter()
            .map(|(id, wait)| (*id, *wait));
        merged(kept, withdrawn, |(id, _)| *id)
    }

    /// How many records are pending.
    #[must_use]
    pub fn pending_len(&self) -> usize {
        self.tracker
            .pending
            .len()
            .saturating_add(self.withdrawal.withdrawn.len())
    }

    /// Actors whose retained records contradict: what [`super::Projection::quarantined`] holds.
    #[must_use]
    pub const fn quarantined(&self) -> &BTreeSet<Actor> {
        &self.tracker.quarantined
    }

    /// `actor`'s highest discharged or floor record.
    #[must_use]
    pub fn tip(&self, actor: &Actor) -> Option<Tip> {
        match self.withdrawal.actors.get(actor) {
            Some((_, tip)) => *tip,
            None => self.tracker.tips.get(actor).copied(),
        }
    }

    /// Each actor's highest discharged or floor record, ascending by actor.
    pub fn tips(&self) -> impl Iterator<Item = (Actor, Tip)> + '_ {
        self.tracker.tips.iter().filter_map(|(actor, tip)| {
            match self.withdrawal.actors.get(actor) {
                Some((_, after)) => after.map(|after| (*actor, after)),
                None => Some((*actor, *tip)),
            }
        })
    }
}

/// The header held under `id`, retained or as a floor record.
fn held<'a, S: Headers>(store: &'a S, floor: &'a Floor, id: &Digest) -> Option<Cow<'a, Header>> {
    store
        .header(id)
        .or_else(|| floor.get(id).map(|record| Cow::Borrowed(&record.header)))
}

/// `header`'s link given its predecessor `previous`.
fn link_to(header: &Header, previous: &Header) -> Link {
    if previous.actor == header.actor && sequence_follows(previous.sequence, header.sequence) {
        Link::Good
    } else {
        Link::Bad
    }
}

/// `header`'s link as the store and the floor hold its predecessor.
fn judge<S: Headers>(store: &S, floor: &Floor, header: &Header) -> Link {
    let Some(previous) = header.previous else {
        return Link::None;
    };
    held(store, floor, &previous).map_or(Link::Unknown, |previous| link_to(header, &previous))
}

/// Whether the retained `header` contradicts a record at its own dot or the record at the dot
/// below it: another record where [`Headers::at`] names `header`'s dot, or a record below it other
/// than its predecessor.
///
/// Over every header of a store, the actors with a header it answers `true` for are exactly the
/// forked actors, whichever record [`Headers::at`] names at a dot holding several. A contradicting
/// pair either shares a dot, and the one `at` does not name answers `true`; or one's predecessor
/// claim names a dot the other holds with another id, and then the other answers `true` where
/// `at` does not name it there, and the claimant answers `true` where it does.
pub(super) fn forks_below<S: Headers>(store: &S, header: &Header) -> bool {
    if store.at(&header.actor, header.sequence) != Some(header.id) {
        return true;
    }
    header
        .sequence
        .checked_sub(1)
        .filter(|below| *below > 0)
        .and_then(|below| store.at(&header.actor, below))
        .is_some_and(|id| Some(id) != header.previous)
}

/// The actors of `store` whose records contradict, reading each header once and keeping none:
/// the actors with a header [`forks_below`] answers `true` for.
pub(super) fn forked_actors<S: Headers>(store: &S) -> BTreeSet<Actor> {
    let mut forked = BTreeSet::new();
    for header in store.headers() {
        if !forked.contains(&header.actor) && forks_below(store, &header) {
            forked.insert(header.actor);
        }
    }
    forked
}

/// Whether the retained `header`, just retained and its actor unforked until now, contradicts
/// another retained record. Every contradicting pair names one of three dots: a second record at
/// `header`'s own dot, a record below it other than its predecessor ([`forks_below`]), or a
/// record above it, retained earlier, naming another predecessor. Each dot holds at most one
/// record of an unforked actor, so it answers exactly.
fn forks_with<S: Headers>(store: &S, header: &Header) -> bool {
    forks_below(store, header)
        || header
            .sequence
            .checked_add(1)
            .and_then(|above| store.at(&header.actor, above))
            .and_then(|above| store.header(&above))
            .is_some_and(|above| above.previous != Some(header.id))
}

impl Tracker {
    /// A tracker of an empty index.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pending: BTreeMap::new(),
            heads: BTreeSet::new(),
            quarantined: BTreeSet::new(),
            runs: BTreeMap::new(),
            floor_max: BTreeMap::new(),
            floor_top: BTreeMap::new(),
            floor_tip: BTreeMap::new(),
            tips: BTreeMap::new(),
            named: BTreeMap::new(),
        }
    }

    /// Discharged and unreached floor records that no discharged record names: what
    /// [`super::Projection::heads`] holds.
    #[must_use]
    pub const fn heads(&self) -> &BTreeSet<Digest> {
        &self.heads
    }

    /// Every retained record not discharged, with what it waits on: the keys are what
    /// [`super::Projection::pending`] holds.
    #[must_use]
    pub const fn pending(&self) -> &BTreeMap<Digest, Wait> {
        &self.pending
    }

    /// Actors whose retained records contradict: what [`super::Projection::quarantined`] holds.
    #[must_use]
    pub const fn quarantined(&self) -> &BTreeSet<Actor> {
        &self.quarantined
    }

    /// Each actor's highest discharged or floor record.
    #[must_use]
    pub const fn tips(&self) -> &BTreeMap<Actor, Tip> {
        &self.tips
    }

    /// How many of `actor`'s retained records are discharged.
    #[must_use]
    pub fn discharged_by(&self, actor: &Actor) -> u64 {
        self.runs.get(actor).map_or(0, |runs| {
            runs.iter().fold(0_u64, |sum, (start, end)| {
                sum.saturating_add(end.saturating_sub(*start).saturating_add(1))
            })
        })
    }

    /// A tracker of `store` and `floor` as they stand. One pass reads each header in turn and
    /// keeps none: it quarantines the actor of each header [`forks_below`] answers `true` for and
    /// enters the header as pending; then the discharge runs from those that wait on nothing,
    /// reading each again.
    pub(super) fn rebuild<S: Headers>(store: &S, floor: &Floor) -> Self {
        let mut tracker = Self::new();
        for id in floor.keys() {
            tracker.floor_inserted(store, floor, id);
        }
        let mut ready = Vec::new();
        for header in store.headers() {
            if !tracker.quarantined.contains(&header.actor) && forks_below(store, &header) {
                tracker.quarantined.insert(header.actor);
            }
            let unmet = header
                .parents
                .iter()
                .filter(|parent| !floor.contains_key(*parent))
                .count() as u64;
            let link = judge(store, floor, &header);
            tracker.pending.insert(header.id, Wait { unmet, link });
            if unmet == 0 {
                ready.push(header.id);
            }
        }
        tracker.release(store, ready);
        tracker
    }

    /// Whether `id`, as a parent, waits on nothing: a floor record or a discharged record.
    fn satisfied<S: Headers>(&self, store: &S, floor: &Floor, id: &Digest) -> bool {
        floor.contains_key(id) || (!self.pending.contains_key(id) && store.contains(id))
    }

    /// Whether `wait` lets a record of `actor` discharge.
    fn eligible(&self, actor: &Actor, wait: &Wait) -> bool {
        wait.unmet == 0
            && matches!(wait.link, Link::None | Link::Good)
            && !self.quarantined.contains(actor)
    }

    /// Feed the retained record `id`, which the store has just retained.
    pub(super) fn inserted<S: Headers>(&mut self, store: &S, floor: &Floor, id: &Digest) {
        let Some(header) = store.header(id) else {
            return;
        };
        // Pending from the start, so a withdrawal below never reads it as discharged.
        self.pending.insert(
            header.id,
            Wait {
                unmet: 0,
                link: Link::Unknown,
            },
        );
        if !self.quarantined.contains(&header.actor) && forks_with(store, &header) {
            self.quarantine(store, floor, header.actor);
        }
        let unmet = header
            .parents
            .iter()
            .filter(|parent| !self.satisfied(store, floor, parent))
            .count() as u64;
        let link = judge(store, floor, &header);
        self.pending.insert(header.id, Wait { unmet, link });
        // A child that came first and names this record as its predecessor learns its link.
        for child in store.children(id) {
            self.judge_child(store, &child, &header);
        }
        self.release(store, Vec::from([header.id]));
    }

    /// Judge the pending `child`'s link if `previous` is the predecessor it was waiting for.
    fn judge_child<S: Headers>(&mut self, store: &S, child: &Digest, previous: &Header) {
        let Some(wait) = self.pending.get_mut(child) else {
            return;
        };
        if wait.link != Link::Unknown {
            return;
        }
        if let Some(header) = store.header(child) {
            if header.previous == Some(previous.id) {
                wait.link = link_to(&header, previous);
            }
        }
    }

    /// Feed the floor record `id`, which the index has just admitted.
    pub(super) fn floor_inserted<S: Headers>(&mut self, store: &S, floor: &Floor, id: &Digest) {
        let Some(record) = floor.get(id) else {
            return;
        };
        let header = &record.header;
        // Reached by a floor record already admitted, whose past holds this one's dot.
        let reached = self
            .floor_top
            .get(&header.actor)
            .is_some_and(|top| *top >= header.sequence);
        for (actor, sequence) in &record.past {
            let top = self.floor_top.entry(*actor).or_insert(0);
            *top = (*top).max(*sequence);
            if let Some(unreached) = self.floor_max.get_mut(actor) {
                let now_reached: Vec<(u64, Digest)> = unreached
                    .range(..=(*sequence, [u8::MAX; 32]))
                    .copied()
                    .collect();
                for entry in now_reached {
                    unreached.remove(&entry);
                    self.heads.remove(&entry.1);
                }
                if unreached.is_empty() {
                    self.floor_max.remove(actor);
                }
            }
        }
        if !reached {
            self.floor_max
                .entry(header.actor)
                .or_default()
                .insert((header.sequence, header.id));
            // No discharged record names it yet: until now it was unsatisfied.
            self.heads.insert(header.id);
        }
        let tip = Tip {
            sequence: header.sequence,
            id: header.id,
        };
        let floor_tip = self.floor_tip.entry(header.actor).or_insert(tip);
        *floor_tip = (*floor_tip).max(tip);
        let best = self.tips.entry(header.actor).or_insert(tip);
        *best = (*best).max(tip);
        // Every child was pending, counting this record as unmet.
        let mut ready = Vec::new();
        for child in store.children(id) {
            self.judge_child(store, &child, header);
            if let Some(wait) = self.pending.get_mut(&child) {
                wait.unmet = discharge(wait.unmet);
                if wait.unmet == 0 {
                    ready.push(child);
                }
            }
        }
        self.release(store, ready);
    }

    /// Discharge each of `ready` that may discharge, and each record that then may.
    fn release<S: Headers>(&mut self, store: &S, mut ready: Vec<Digest>) {
        while let Some(id) = ready.pop() {
            let Some(wait) = self.pending.get(&id) else {
                continue;
            };
            let Some(header) = store.header(&id) else {
                continue;
            };
            if !self.eligible(&header.actor, wait) {
                continue;
            }
            self.pending.remove(&id);
            self.heads.insert(id);
            for parent in &header.parents {
                self.heads.remove(parent);
                let count = self.named.entry(*parent).or_insert(0);
                *count = count.saturating_add(1);
            }
            self.run_add(header.actor, header.sequence);
            let tip = Tip {
                sequence: header.sequence,
                id,
            };
            let best = self.tips.entry(header.actor).or_insert(tip);
            *best = (*best).max(tip);
            for child in store.children(&id) {
                if let Some(wait) = self.pending.get_mut(&child) {
                    wait.unmet = discharge(wait.unmet);
                    if wait.unmet == 0 {
                        ready.push(child);
                    }
                }
            }
        }
    }

    /// Quarantine `actor`, withdrawing its discharged records and every discharged record
    /// above them.
    fn quarantine<S: Headers>(&mut self, store: &S, floor: &Floor, actor: Actor) {
        self.quarantined.insert(actor);
        // The actor was unforked, so each discharged dot holds exactly the record discharged,
        // and `at` named it when its fork check read that dot.
        let own: Vec<Digest> = self
            .runs
            .get(&actor)
            .into_iter()
            .flatten()
            .flat_map(|(start, end)| *start..=*end)
            .filter_map(|sequence| store.at(&actor, sequence))
            .collect();
        let withdrawal = self.withdrawal(store, floor, own);
        self.apply(withdrawal);
    }

    /// `start`'s discharged records and every discharged record that names one of them,
    /// transitively.
    fn above<S: Headers>(&self, store: &S, start: Vec<Digest>) -> BTreeSet<Digest> {
        let mut found = BTreeSet::new();
        let mut todo = start;
        while let Some(id) = todo.pop() {
            if self.pending.contains_key(&id) || !found.insert(id) {
                continue;
            }
            todo.extend(store.children(&id));
        }
        found
    }

    /// The withdrawal of `start`'s discharged records and every discharged record above them,
    /// worked out without changing the tracker. It reads each withdrawn record, its parents and
    /// its children, and each affected actor's runs down past its withdrawn sequences.
    fn withdrawal<S: Headers>(&self, store: &S, floor: &Floor, start: Vec<Digest>) -> Withdrawal {
        let ids = self.above(store, start);
        let mut out = Withdrawal::default();
        let mut sequences = BTreeMap::<Actor, BTreeSet<u64>>::new();
        for id in &ids {
            let Some(header) = store.header(id) else {
                continue;
            };
            // A parent waits on nothing when it is a floor record, or discharged and staying so.
            let unmet = header
                .parents
                .iter()
                .filter(|parent| {
                    !floor.contains_key(*parent)
                        && (ids.contains(*parent) || !self.satisfied(store, floor, parent))
                })
                .count() as u64;
            // It was discharged, so its link is absent or good.
            let link = if header.previous.is_some() {
                Link::Good
            } else {
                Link::None
            };
            out.withdrawn.insert(*id, Wait { unmet, link });
            // Every child outside the withdrawal is pending: a discharged one would be above.
            for child in store.children(id) {
                if ids.contains(&child) {
                    continue;
                }
                let Some(wait) = out
                    .raised
                    .get(&child)
                    .or_else(|| self.pending.get(&child))
                    .copied()
                else {
                    continue;
                };
                out.raised.insert(
                    child,
                    Wait {
                        unmet: wait.unmet.saturating_add(1),
                        link: wait.link,
                    },
                );
            }
            for parent in &header.parents {
                let count = out.unnamed.entry(*parent).or_insert(0);
                *count = count.saturating_add(1);
            }
            sequences
                .entry(header.actor)
                .or_default()
                .insert(header.sequence);
        }
        // A parent every discharged record naming which is withdrawn is a head, if it can be one.
        for (parent, count) in &out.unnamed {
            if !ids.contains(parent)
                && self.named.get(parent) == Some(count)
                && self.may_head(store, floor, parent)
            {
                out.heads.insert(*parent);
            }
        }
        for (actor, gone) in sequences {
            let tip = self.tip_without(store, &actor, &gone);
            out.actors.insert(actor, (gone, tip));
        }
        out
    }

    /// Make `withdrawal`, worked out against this tracker as it stands.
    fn apply(&mut self, withdrawal: Withdrawal) {
        for (id, wait) in withdrawal.withdrawn {
            self.heads.remove(&id);
            self.pending.insert(id, wait);
        }
        self.pending.extend(withdrawal.raised);
        for (parent, count) in withdrawal.unnamed {
            if let Entry::Occupied(mut named) = self.named.entry(parent) {
                let left = named.get().saturating_sub(count);
                if left == 0 {
                    named.remove();
                } else {
                    *named.get_mut() = left;
                }
            }
        }
        self.heads.extend(withdrawal.heads);
        for (actor, (gone, tip)) in withdrawal.actors {
            for sequence in gone {
                self.run_remove(&actor, sequence);
            }
            match tip {
                Some(tip) => {
                    self.tips.insert(actor, tip);
                }
                None => {
                    self.tips.remove(&actor);
                }
            }
        }
    }

    /// Whether `id` is discharged or an unreached floor record.
    fn may_head<S: Headers>(&self, store: &S, floor: &Floor, id: &Digest) -> bool {
        match floor.get(id) {
            Some(record) => self
                .floor_max
                .get(&record.header.actor)
                .is_some_and(|unreached| unreached.contains(&(record.header.sequence, *id))),
            None => !self.pending.contains_key(id) && store.contains(id),
        }
    }

    /// `actor`'s tip once its discharged sequences in `gone` are withdrawn: its highest other
    /// discharged sequence, found walking down from its highest past those in `gone`, or its
    /// floor tip, whichever is higher.
    fn tip_without<S: Headers>(
        &self,
        store: &S,
        actor: &Actor,
        gone: &BTreeSet<u64>,
    ) -> Option<Tip> {
        let discharged = self
            .runs
            .get(actor)
            .and_then(|runs| {
                runs.iter()
                    .rev()
                    .flat_map(|(start, end)| (*start..=*end).rev())
                    .find(|sequence| !gone.contains(sequence))
            })
            .and_then(|sequence| store.at(actor, sequence).map(|id| Tip { sequence, id }));
        discharged.max(self.floor_tip.get(actor).copied())
    }

    /// Add `sequence` to `actor`'s discharged runs.
    fn run_add(&mut self, actor: Actor, sequence: u64) {
        let runs = self.runs.entry(actor).or_default();
        let below = runs
            .range(..=sequence)
            .next_back()
            .map(|(start, end)| (*start, *end));
        if below.is_some_and(|(_, end)| end >= sequence) {
            return;
        }
        let above = sequence
            .checked_add(1)
            .and_then(|next| runs.get(&next).map(|end| (next, *end)));
        let start = match below {
            Some((start, end)) if end.checked_add(1) == Some(sequence) => start,
            _ => sequence,
        };
        let end = match above {
            Some((next, end)) => {
                runs.remove(&next);
                end
            }
            None => sequence,
        };
        runs.insert(start, end);
    }

    /// Remove `sequence` from `actor`'s discharged runs.
    fn run_remove(&mut self, actor: &Actor, sequence: u64) {
        let Some(runs) = self.runs.get_mut(actor) else {
            return;
        };
        let Some((start, end)) = runs
            .range(..=sequence)
            .next_back()
            .map(|(start, end)| (*start, *end))
            .filter(|(_, end)| *end >= sequence)
        else {
            return;
        };
        runs.remove(&start);
        if let Some(left) = sequence.checked_sub(1).filter(|left| *left >= start) {
            runs.insert(start, left);
        }
        if let Some(right) = sequence.checked_add(1).filter(|right| *right <= end) {
            runs.insert(right, end);
        }
        if runs.is_empty() {
            self.runs.remove(actor);
        }
    }

    /// The tracked fields with `excluded` withheld, and every record above an excluded one: the
    /// withdrawal a fork makes, worked out beside this tracker. A floor record, a pending record
    /// or an id not retained in `excluded` changes nothing.
    pub(super) fn excluding<S: Headers>(
        &self,
        store: &S,
        floor: &Floor,
        excluded: &BTreeSet<Digest>,
    ) -> Tracked<'_> {
        let start: Vec<Digest> = excluded
            .iter()
            .filter(|id| !self.pending.contains_key(*id) && store.contains(id))
            .copied()
            .collect();
        Tracked {
            tracker: self,
            withdrawal: self.withdrawal(store, floor, start),
        }
    }
}

#[cfg(test)]
#[path = "tracker_tests.rs"]
mod tests;
