// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A read-only, keyed view of a tape's reply doors.
//!
//! [`ReplaySeam`](crate::ReplaySeam) answers in order and consumes as it goes:
//! the right shape for re-running the recorded program, the wrong one for
//! asking a recorded question out of order. A second reader — a candidate
//! decision function re-deciding a recorded point, a "why did it do that"
//! report — needs "what had the door `probe.git_view` answered to THIS request
//! once the program had read N records?" without disturbing the replay that
//! drives the program, and without depending on the order in which it asks. [`KeyedView`] is that
//! reader: it makes every [`Exchange`](crate::EffectRecord::Exchange) available by
//! (door, request), and each [`lookup`](KeyedView::lookup) is a pure
//! function of the tape and its arguments.
//!
//! [`KeyedIndex`] is the same index over records it HOLDS — a `Vec`, a `Box`
//! or an `Arc` of them — for a reader that asks from many places and cannot
//! keep a borrow of the tape alive across them: every look of every decision
//! re-decided on one tape, each made through its own `'static` handle, asks one
//! index built once (behind an `Arc`), where a [`KeyedView`] would have to be
//! built again from the whole tape for each look. Both answer through the one
//! search below, so they cannot disagree.

use crate::replay::ReplayDivergence;
use crate::seam::EffectRecord;
use std::collections::BTreeMap;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "keyed_island.rs"]
mod keyed_island;
#[cfg(not(clean_islands))]
pub use crate::twins::keyed_clamp_cutoff;
#[cfg(clean_islands)]
pub use keyed_island::keyed_clamp_cutoff;

contract_fn! {
    /// Verified check that an indexed exchange at `pos` is among the first `seen`
    /// records (`pos < seen`), linked via `clean-kernel-defeq` to
    /// `keyed_hit_within_cutoff_isl`.
    #[must_use]
    pub const fn keyed_hit_within_cutoff(pos: usize, seen: usize) -> bool
    clauses [ensures result == (pos < seen)]
    {
        pos < seen
    }
}

/// The answer a [`KeyedView`] found: the reply and where on the tape it sits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyedReply<'a> {
    /// The index of the `Exchange` record in the slice the view was built from.
    pub position: usize,
    /// The recorded reply.
    pub reply: &'a [u8],
}

/// The (door, request) an `Exchange` record answers, or `None` for any other
/// record: a clock or a file read is not a question with a reusable answer.
fn exchange_key(record: &EffectRecord) -> Option<(&str, &[u8])> {
    match record {
        EffectRecord::Exchange { door, request, .. } => Some((door.as_str(), request.as_slice())),
        _ => None,
    }
}

fn key_at<'r>(
    positions: &[usize],
    records: &'r [EffectRecord],
    index: usize,
) -> Option<(&'r str, &'r [u8])> {
    positions
        .get(index)
        .and_then(|&p| records.get(p))
        .and_then(exchange_key)
}

fn partition_key_lt(
    positions: &[usize],
    records: &[EffectRecord],
    asked: Option<(&str, &[u8])>,
) -> usize {
    let mut low = 0usize;
    let mut high = positions.len();
    while low < high {
        let mid = low.saturating_add(high.saturating_sub(low) / 2);
        if key_at(positions, records, mid) < asked {
            low = mid.saturating_add(1);
        } else {
            high = mid;
        }
    }
    low
}

fn partition_key_le(
    positions: &[usize],
    records: &[EffectRecord],
    asked: Option<(&str, &[u8])>,
) -> usize {
    let mut low = 0usize;
    let mut high = positions.len();
    while low < high {
        let mid = low.saturating_add(high.saturating_sub(low) / 2);
        if key_at(positions, records, mid) <= asked {
            low = mid.saturating_add(1);
        } else {
            high = mid;
        }
    }
    low
}

fn partition_within_cutoff(run: &[usize], seen: usize) -> usize {
    let mut low = 0usize;
    let mut high = run.len();
    while low < high {
        let mid = low.saturating_add(high.saturating_sub(low) / 2);
        if run
            .get(mid)
            .is_some_and(|&p| keyed_hit_within_cutoff(p, seen))
        {
            low = mid.saturating_add(1);
        } else {
            high = mid;
        }
    }
    low
}

/// Every [`Exchange`](crate::EffectRecord::Exchange) of a record slice as
/// positions into it, ordered by (door, request) and, within one (door,
/// request), by ascending position: the index a [`KeyedView`] and a
/// [`KeyedIndex`] both answer from. It holds no record, so an indexed tape
/// costs one word per exchange whatever the requests and replies weigh.
/// Longer tapes use a backwards scan instead of allocating an unbounded index.
///
/// It is built through a `BTreeMap` rather than a hash map so the crate stays
/// free of randomness anywhere a replay can reach: no answer depends on the
/// map's order, but a reviewer should not have to check that.
#[derive(Clone)]
enum Order {
    Indexed(Vec<usize>),
    Scanned(usize),
}

// Bound all eager index construction, including its temporary BTreeMap. This
// is an optimization budget, never a limit on which tape records can answer.
const MAX_INDEX_RECORDS: usize = 1 << 20;

impl Default for Order {
    fn default() -> Self {
        Self::Indexed(Vec::new())
    }
}

impl Order {
    /// Index `records`.
    fn of(records: &[EffectRecord]) -> Order {
        if records.len() > MAX_INDEX_RECORDS {
            return Order::Scanned(records.iter().filter(|r| exchange_key(r).is_some()).count());
        }
        let mut runs: BTreeMap<(&str, &[u8]), Vec<usize>> = BTreeMap::new();
        let mut total = 0usize;
        let mut position = 0usize;
        let mut rest = records;
        while let [record, tail @ ..] = rest {
            if let Some(key) = exchange_key(record) {
                // The slice is walked front to back, so each run is pushed in
                // ascending position.
                runs.entry(key).or_default().push(position);
                total = total.saturating_add(1);
            }
            position = position.saturating_add(1);
            rest = tail;
        }
        // The input bound above also bounds every run and their combined
        // length. Keep the allocation's bound explicit for the verifier.
        let mut positions = Vec::with_capacity(total.min(MAX_INDEX_RECORDS));
        for run in runs.into_values() {
            positions.extend(run);
        }
        Order::Indexed(positions)
    }

    /// The LATEST exchange through `door` with exactly `request` among the
    /// first `seen` of `records` — the slice this order was built from. A
    /// record at an indexed position that is no longer that exchange (a slice
    /// other than the one indexed) is never answered from: every hit is
    /// checked to be the exchange asked for.
    fn find<'r>(
        &self,
        records: &'r [EffectRecord],
        door: &str,
        request: &[u8],
        seen: usize,
    ) -> Option<KeyedReply<'r>> {
        let asked = Some((door, request));
        let positions = match self {
            Self::Indexed(positions) => positions.as_slice(),
            Self::Scanned(_) => {
                let mut end = seen.min(records.len());
                while let Some(position) = end.checked_sub(1) {
                    if let Some(EffectRecord::Exchange {
                        door: d,
                        request: r,
                        reply,
                    }) = records.get(position)
                    {
                        if d == door && r.as_slice() == request {
                            return Some(KeyedReply {
                                position,
                                reply: reply.as_slice(),
                            });
                        }
                    }
                    end = position;
                }
                return None;
            }
        };
        // The run of (door, request): its keys are neither below nor above
        // the one asked.
        let start = partition_key_lt(positions, records, asked);
        let end = partition_key_le(positions, records, asked);
        let run = positions.get(start..end)?;
        // The run is sorted by tape position: the hits within the cutoff are
        // a prefix of it, and the answer is its last.
        let admitted = partition_within_cutoff(run, seen);
        let position = *run.get(admitted.checked_sub(1)?)?;
        match records.get(position)? {
            EffectRecord::Exchange {
                door: d,
                request: r,
                reply,
            } if d == door && r.as_slice() == request => Some(KeyedReply {
                position,
                reply: reply.as_slice(),
            }),
            _ => None,
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Indexed(positions) => positions.len(),
            Self::Scanned(exchanges) => *exchanges,
        }
    }
}

/// The refusal a lookup that found nothing returns.
fn unrecorded(door: &str, request: &[u8]) -> ReplayDivergence {
    ReplayDivergence::Unrecorded {
        door: door.to_string(),
        request: request.to_vec(),
    }
}

/// Every [`Exchange`](crate::EffectRecord::Exchange) of a tape, indexed by
/// (door, request). Built once from a slice of records; never consumes, never
/// mutates, never asks the live world. Other record kinds are ignored: a clock
/// or a file read is not a question with a reusable answer.
///
/// The view BORROWS the records; [`KeyedIndex`] is the same index over
/// records it holds.
#[derive(Clone, Default)]
pub struct KeyedView<'a> {
    records: &'a [EffectRecord],
    order: Order,
}

impl std::fmt::Debug for KeyedView<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KeyedView")
            .field("records", &self.records.len())
            .field("exchanges", &self.order.len())
            .finish()
    }
}

impl<'a> KeyedView<'a> {
    /// Index `records` — typically the whole tape, decoded once.
    ///
    /// Up to 1,048,576 records are indexed eagerly. Longer tapes retain every
    /// answer and use an allocation-free backwards scan for each lookup.
    pub fn new(records: &'a [EffectRecord]) -> KeyedView<'a> {
        KeyedView {
            records,
            order: Order::of(records),
        }
    }

    /// The LATEST exchange through `door` with exactly `request` among the
    /// first `seen` records of the slice the view was built from: its position
    /// is strictly less than `seen`. `0` admits nothing, and the slice's length
    /// (or anything past it, `usize::MAX` included) admits the whole tape.
    ///
    /// The prefix is the whole point: a reader standing where the recorded
    /// program stood may use what it had learned by then, never what it learned
    /// later — an answer from the future would let a re-decision see a world
    /// the recorded one had not reached. A miss is
    /// [`ReplayDivergence::Unrecorded`], never a reason to ask the live world.
    ///
    /// The bound is a COUNT of records read, not the index of a record, because
    /// that is what a reader holds: [`ReplaySeam::position`](crate::ReplaySeam::position)
    /// is how many records a replay over the same slice has consumed, so
    /// `lookup(door, request, replay.position())` answers from exactly what that
    /// replay has read and never from the record it is about to read. An
    /// inclusive index could not say "nothing read yet" at all — the
    /// `position() - 1` it would need underflows at the start of the tape, and
    /// a wrapped `usize::MAX` reads as "anywhere". A reader at a mark that
    /// stands at record N, and has seen it, passes `N + 1`.
    pub fn lookup(
        &self,
        door: &str,
        request: &[u8],
        seen: usize,
    ) -> Result<KeyedReply<'a>, ReplayDivergence> {
        self.order
            .find(self.records, door, request, seen)
            .ok_or_else(|| unrecorded(door, request))
    }

    /// How many exchanges the view indexed.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Whether the tape held no exchange at all.
    pub fn is_empty(&self) -> bool {
        self.order.len() == 0
    }
}

/// A [`KeyedView`] over records it HOLDS: `R` is a `Vec<EffectRecord>`, a
/// `Box<[EffectRecord]>`, an `Arc<[EffectRecord]>` — anything that lends the
/// slice. Built once, it answers [`lookup`](Self::lookup) exactly as a view
/// built over the same records does, for as long as anything holds it, with
/// no borrow of the tape to keep alive: the shape for a reader whose looks
/// are made through handles that must own what they read (a policy's probe
/// object, one per decision re-decided, all sharing one index behind an
/// `Arc`), which with a [`KeyedView`] would rebuild the index from the whole
/// tape at every look.
///
/// `R` must lend the same slice every time it is asked (every `Vec`, `Box`
/// and `Arc` does); a lookup over a slice other than the one indexed answers
/// only a hit that is still the exchange asked for, never another record.
#[derive(Clone)]
pub struct KeyedIndex<R> {
    records: R,
    order: Order,
}

impl<R: AsRef<[EffectRecord]>> std::fmt::Debug for KeyedIndex<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KeyedIndex")
            .field("records", &self.records.as_ref().len())
            .field("exchanges", &self.order.len())
            .finish()
    }
}

impl<R: AsRef<[EffectRecord]>> KeyedIndex<R> {
    /// Index `records`, and keep them. As with [`KeyedView::new`], tapes longer
    /// than 1,048,576 records use a backwards scan instead of an eager index.
    pub fn new(records: R) -> KeyedIndex<R> {
        let order = Order::of(records.as_ref());
        KeyedIndex { records, order }
    }

    /// The records the index holds.
    pub fn records(&self) -> &[EffectRecord] {
        self.records.as_ref()
    }

    /// [`KeyedView::lookup`] over the records the index holds: the LATEST
    /// exchange through `door` with exactly `request` among the first `seen`
    /// of them, or [`ReplayDivergence::Unrecorded`].
    pub fn lookup(
        &self,
        door: &str,
        request: &[u8],
        seen: usize,
    ) -> Result<KeyedReply<'_>, ReplayDivergence> {
        self.order
            .find(self.records.as_ref(), door, request, seen)
            .ok_or_else(|| unrecorded(door, request))
    }

    /// How many exchanges the index holds.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Whether the records held no exchange at all.
    pub fn is_empty(&self) -> bool {
        self.order.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn exchange(reply: &[u8]) -> EffectRecord {
        EffectRecord::Exchange {
            door: "probe".into(),
            request: b"request".to_vec(),
            reply: reply.to_vec(),
        }
    }

    #[test]
    fn eager_index_budget_preserves_every_lookup() {
        let mut records = vec![EffectRecord::Mono(0); MAX_INDEX_RECORDS];
        let middle = MAX_INDEX_RECORDS / 2;
        records[0] = exchange(b"first");
        records[middle] = exchange(b"middle");
        records[MAX_INDEX_RECORDS - 1] = exchange(b"last indexed");
        {
            let view = KeyedView::new(&records);
            assert!(matches!(&view.order, Order::Indexed(positions) if positions.len() == 3));
            assert_eq!(
                view.lookup("probe", b"request", usize::MAX),
                Ok(KeyedReply {
                    position: MAX_INDEX_RECORDS - 1,
                    reply: b"last indexed",
                })
            );
        }
        records.push(exchange(b"beyond the index budget"));
        records.push(EffectRecord::Emit {
            door: "probe".into(),
            bytes: b"request".to_vec(),
        });
        let records: Arc<[EffectRecord]> = records.into();
        let view = KeyedView::new(&records);
        let index = KeyedIndex::new(Arc::clone(&records));
        assert!(matches!(view.order, Order::Scanned(4)));
        assert!(matches!(index.order, Order::Scanned(4)));
        assert_eq!(view.len(), 4);
        assert_eq!(index.len(), 4);
        assert!(!view.is_empty());
        assert!(!index.is_empty());
        type LookupCase = (usize, Option<(usize, &'static [u8])>);
        let cases: &[LookupCase] = &[
            (0, None),
            (1, Some((0, b"first"))),
            (middle, Some((0, b"first"))),
            (middle + 1, Some((middle, b"middle"))),
            (MAX_INDEX_RECORDS - 1, Some((middle, b"middle"))),
            (
                MAX_INDEX_RECORDS,
                Some((MAX_INDEX_RECORDS - 1, b"last indexed")),
            ),
            (
                MAX_INDEX_RECORDS + 1,
                Some((MAX_INDEX_RECORDS, b"beyond the index budget")),
            ),
            (
                usize::MAX,
                Some((MAX_INDEX_RECORDS, b"beyond the index budget")),
            ),
        ];
        for &(seen, expected) in cases.iter().rev().chain(cases) {
            let wanted = expected.map(|(position, reply)| KeyedReply { position, reply });
            assert_eq!(view.lookup("probe", b"request", seen).ok(), wanted);
            assert_eq!(index.lookup("probe", b"request", seen).ok(), wanted);
        }
        assert!(matches!(
            view.lookup("another door", b"request", usize::MAX),
            Err(ReplayDivergence::Unrecorded { .. })
        ));
        assert!(matches!(
            index.lookup("probe", b"another request", usize::MAX),
            Err(ReplayDivergence::Unrecorded { .. })
        ));
        assert!(Arc::ptr_eq(&records, &index.records));
    }
}
