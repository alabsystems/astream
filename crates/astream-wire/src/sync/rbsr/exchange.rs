// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Both endpoints retain immutable snapshots through the exchange. The result
//! names records to transfer; it neither acknowledges their storage nor grants
//! access to their payloads. Integrators revalidate those decisions separately.

use super::codec::{Message, Probe, PAGE};
use super::{Actor, Digest, Error, Fingerprint, Frontier, Range, Snapshot};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound;
use std::sync::Arc;

/// Explicit application budgets, independent of protocol page size. There is no
/// fixed total inventory-list cap: callers choose their admitted remote size.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Maximum remote inventory count admitted for this exchange.
    pub remote_records: u64,
    /// Maximum requests, including setup, pages and any full-width refinement.
    pub messages: u64,
}

/// A complete difference from this endpoint's perspective, sorted by digest.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Difference {
    /// Held here and absent at the peer.
    pub send: Vec<Digest>,
    /// Held at the peer and absent here.
    pub want: Vec<Digest>,
}

/// Keep transport failures distinct from protocol refusals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExchangeError<E> {
    /// Malformed, inconsistent or over-budget peer behavior.
    Protocol(Error),
    /// The integrating transport's original error.
    Transport(E),
}

impl<E> From<Error> for ExchangeError<E> {
    fn from(error: Error) -> Self {
        Self::Protocol(error)
    }
}

struct Budget {
    used: u64,
    limit: u64,
}

impl Budget {
    fn charge(&mut self) -> Result<(), Error> {
        self.used = self.used.checked_add(1).ok_or(Error::Budget)?;
        if self.used > self.limit {
            return Err(Error::Budget);
        }
        Ok(())
    }
}

fn call<E>(
    exchange: &mut impl FnMut(Message) -> Result<Message, E>,
    budget: &mut Budget,
    message: Message,
) -> Result<Message, ExchangeError<E>> {
    budget.charge()?;
    exchange(message).map_err(ExchangeError::Transport)
}

fn root(snapshot: &Snapshot) -> Result<Fingerprint, Error> {
    snapshot.fingerprint()
}

fn contribution(mut ids: impl Iterator<Item = Digest>) -> Result<Fingerprint, Error> {
    ids.try_fold(Fingerprint::default(), |sum, id| {
        sum.plus(Fingerprint { count: 1, sum: id })
    })
}

fn validate_root(value: Fingerprint, limit: u64) -> Result<(), Error> {
    if value.count > limit {
        return Err(Error::Budget);
    }
    if value.count == 0 && value.sum != [0; 32] {
        return Err(Error::Wire);
    }
    Ok(())
}

fn append_anchors(
    out: &mut Vec<Frontier>,
    items: Vec<Frontier>,
    done: bool,
    finished: &mut bool,
    limit: u64,
) -> Result<(), Error> {
    if *finished {
        return if items.is_empty() && done {
            Ok(())
        } else {
            Err(Error::Phase)
        };
    }
    if items.len() > PAGE || (!done && items.is_empty()) {
        return Err(Error::Wire);
    }
    if out.len().saturating_add(items.len()) as u64 > limit {
        return Err(Error::Budget);
    }
    for item in items {
        if item.sequence == 0 || out.last().is_some_and(|last| last.actor >= item.actor) {
            return Err(Error::Prefix);
        }
        out.push(item);
    }
    *finished = done;
    Ok(())
}

fn union_prefixes(ours: &[Frontier], theirs: &[Frontier]) -> Result<Vec<Frontier>, Error> {
    let mut shared = BTreeMap::<Actor, Frontier>::new();
    for anchor in ours.iter().chain(theirs) {
        if shared.get(&anchor.actor).is_some_and(|old| old != anchor) {
            return Err(Error::Prefix);
        }
        shared.insert(anchor.actor, *anchor);
    }
    Ok(shared.into_values().collect())
}

fn reduced(
    original: &Arc<Snapshot>,
    ours: Fingerprint,
    theirs: Fingerprint,
    shared: &[Frontier],
) -> Result<(Arc<Snapshot>, Fingerprint, Fingerprint), Error> {
    let view = if shared.is_empty() {
        Arc::clone(original)
    } else {
        Arc::new(original.without_prefixes(shared)?)
    };
    let ours_reduced = root(&view)?;
    let shared_contribution = ours.minus(ours_reduced)?;
    let theirs_reduced = theirs.minus(shared_contribution)?;
    Ok((view, ours_reduced, theirs_reduced))
}

fn anchor_exchange<E>(
    ours: &[Frontier],
    prefixes: bool,
    peer_limit: u64,
    exchange: &mut impl FnMut(Message) -> Result<Message, E>,
    budget: &mut Budget,
) -> Result<Vec<Frontier>, ExchangeError<E>> {
    let mut at = 0usize;
    let mut peer = Vec::new();
    let mut peer_done = false;
    loop {
        let end = at.saturating_add(PAGE).min(ours.len());
        let done = end == ours.len();
        let items = ours[at..end].to_vec();
        let request = if prefixes {
            Message::Prefixes { items, done }
        } else {
            Message::Frontiers { items, done }
        };
        let answer = call(exchange, budget, request)?;
        let (items, finished) = match (prefixes, answer) {
            (false, Message::Frontiers { items, done })
            | (true, Message::Prefixes { items, done }) => (items, done),
            _ => return Err(Error::Phase.into()),
        };
        append_anchors(&mut peer, items, finished, &mut peer_done, peer_limit)?;
        if done && peer_done {
            return Ok(peer);
        }
        at = end;
    }
}

fn in_range(
    snapshot: &Snapshot,
    range: Range,
    after: Option<Digest>,
) -> impl Iterator<Item = &Digest> {
    let lower = after.map_or(Bound::Included(range.prefix().0), Bound::Excluded);
    let upper = range.upper().map_or(Bound::Unbounded, Bound::Excluded);
    snapshot.range_ids(lower, upper).iter()
}

fn list<E>(
    range: Range,
    expected: u64,
    exchange: &mut impl FnMut(Message) -> Result<Message, E>,
    budget: &mut Budget,
) -> Result<BTreeSet<Digest>, ExchangeError<E>> {
    let mut ids = BTreeSet::new();
    let mut after = None;
    loop {
        let answer = call(exchange, budget, Message::ListRequest { range, after })?;
        let Message::List {
            range: answered,
            ids: page,
            done,
        } = answer
        else {
            return Err(Error::Phase.into());
        };
        if answered != range || page.len() > PAGE || (!done && page.is_empty()) {
            return Err(Error::Wire.into());
        }
        for id in page {
            if !range.contains(&id) || after.is_some_and(|previous| previous >= id) {
                return Err(Error::Wire.into());
            }
            after = Some(id);
            ids.insert(id);
            if ids.len() as u64 > expected {
                return Err(Error::Count.into());
            }
        }
        if done {
            return if ids.len() as u64 == expected {
                Ok(ids)
            } else {
                Err(Error::Count.into())
            };
        }
    }
}

fn find<E>(
    view: &Snapshot,
    ours: Fingerprint,
    theirs: Fingerprint,
    full: bool,
    exchange: &mut impl FnMut(Message) -> Result<Message, E>,
    budget: &mut Budget,
) -> Result<(BTreeSet<Digest>, BTreeSet<Digest>), ExchangeError<E>> {
    let mut send = BTreeSet::new();
    let mut want = BTreeSet::new();
    let mut pending = Vec::new();
    if ours != theirs {
        pending.push((Range::ROOT, ours, theirs.count));
    }
    while let Some((range, local, peer_count)) = pending.pop() {
        if peer_count == 0 {
            send.extend(in_range(view, range, None).copied());
        } else if local.count == 0 || local.count.max(peer_count) <= 3 || range.children().is_none()
        {
            let peer = list(range, peer_count, exchange, budget)?;
            send.extend(
                in_range(view, range, None)
                    .filter(|id| !peer.contains(*id))
                    .copied(),
            );
            want.extend(peer.into_iter().filter(|id| !view.contains(id)));
        } else {
            let children = range.children().ok_or(Error::Range)?;
            let mut summaries = [Fingerprint::default(); 16];
            let mut probes = Box::new([Probe::Compact(0, [0; 4]); 16]);
            for (position, child) in children.into_iter().enumerate() {
                summaries[position] =
                    view.range_fingerprint(Some(child.prefix().0), child.upper())?;
                probes[position] = Probe::new(summaries[position], full);
            }
            let answer = call(
                exchange,
                budget,
                Message::Split {
                    range,
                    children: probes,
                },
            )?;
            let Message::SplitReply {
                range: answered,
                different,
                counts,
            } = answer
            else {
                return Err(Error::Phase.into());
            };
            if answered != range {
                return Err(Error::Phase.into());
            }
            let mut total = 0u64;
            for (position, child) in children.into_iter().enumerate() {
                let unequal = different & (1 << position) != 0;
                let count = if unequal {
                    counts[position]
                } else {
                    summaries[position].count
                };
                if !unequal && counts[position] != 0 {
                    return Err(Error::Wire.into());
                }
                total = total.checked_add(count).ok_or(Error::Count)?;
                if unequal {
                    pending.push((child, summaries[position], count));
                }
            }
            if total != peer_count {
                return Err(Error::Count.into());
            }
        }
    }
    Ok((send, want))
}

fn conserved(
    ours: Fingerprint,
    theirs: Fingerprint,
    send: Fingerprint,
    want: Fingerprint,
) -> Result<bool, Error> {
    Ok(ours.minus(send)? == theirs.minus(want)?)
}

/// Reconcile through an integrating transport's request/reply closure. The peer
/// runs [`Responder::answer`]. Every received frame must first pass the codec.
/// Results are exposed only after both endpoints check full-root conservation.
/// # Errors
/// Preserves the transport error, or refuses malformed, out-of-phase, inconsistent
/// or over-budget behavior. A compact-probe mismatch refines once at full width;
/// a remaining conservation failure returns no tentative difference.
pub fn reconcile<E>(
    snapshot: Arc<Snapshot>,
    limits: Limits,
    mut exchange: impl FnMut(Message) -> Result<Message, E>,
) -> Result<Difference, ExchangeError<E>> {
    let ours = root(&snapshot)?;
    let mut budget = Budget {
        used: 0,
        limit: limits.messages,
    };
    let Message::Root(theirs) = call(&mut exchange, &mut budget, Message::Root(ours))? else {
        return Err(Error::Phase.into());
    };
    validate_root(theirs, limits.remote_records)?;
    let (view, ours, theirs) = if ours == theirs {
        (Arc::clone(&snapshot), ours, theirs)
    } else {
        let frontiers: Vec<_> = snapshot.frontiers().collect();
        let peer_frontiers =
            anchor_exchange(&frontiers, false, theirs.count, &mut exchange, &mut budget)?;
        let proposals = snapshot.shared_prefixes(&peer_frontiers)?;
        let peer_proposals = anchor_exchange(
            &proposals,
            true,
            peer_frontiers.len() as u64,
            &mut exchange,
            &mut budget,
        )?;
        let shared = union_prefixes(&proposals, &peer_proposals)?;
        reduced(&snapshot, ours, theirs, &shared)?
    };
    let (mut send, mut want) = find(&view, ours, theirs, false, &mut exchange, &mut budget)?;
    let mut sent = contribution(send.iter().copied())?;
    let mut wanted = contribution(want.iter().copied())?;
    if !conserved(ours, theirs, sent, wanted)? {
        if call(&mut exchange, &mut budget, Message::Refine)? != Message::Accepted {
            return Err(Error::Phase.into());
        }
        (send, want) = find(&view, ours, theirs, true, &mut exchange, &mut budget)?;
        sent = contribution(send.iter().copied())?;
        wanted = contribution(want.iter().copied())?;
        if !conserved(ours, theirs, sent, wanted)? {
            return Err(Error::Conservation.into());
        }
    }
    for (ids, local_only) in [(&send, true), (&want, false)] {
        let mut remaining = ids.iter().copied();
        loop {
            let page: Vec<_> = remaining.by_ref().take(PAGE).collect();
            let done = remaining.len() == 0;
            let answer = call(
                &mut exchange,
                &mut budget,
                Message::Difference {
                    ids: page,
                    done,
                    local_only,
                },
            )?;
            if answer != Message::Accepted {
                return Err(Error::Phase.into());
            }
            if done {
                break;
            }
        }
    }
    let finish = Message::Finish {
        local_only: sent,
        remote_only: wanted,
    };
    if call(&mut exchange, &mut budget, finish.clone())? != finish {
        return Err(Error::Conservation.into());
    }
    Ok(Difference {
        send: send.into_iter().collect(),
        want: want.into_iter().collect(),
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Root,
    Frontiers,
    Prefixes,
    Ranges,
    Send,
    Want,
    Finish,
    Done,
    Failed,
}

/// Pure responder state. Any error before completion fences the exchange. A
/// completed result remains available even if a later request is refused.
pub struct Responder {
    original: Arc<Snapshot>,
    working: Arc<Snapshot>,
    original_root: Fingerprint,
    peer_root: Fingerprint,
    own_view_root: Fingerprint,
    peer_view_root: Fingerprint,
    limits: Limits,
    budget: Budget,
    phase: Phase,
    frontiers: Vec<Frontier>,
    proposals: Vec<Frontier>,
    peer_items: Vec<Frontier>,
    peer_done: bool,
    at: usize,
    full: bool,
    send: BTreeSet<Digest>,
    want: BTreeSet<Digest>,
    difference: Option<Difference>,
}

impl Responder {
    /// Prepare one exchange over immutable physical inventory facts.
    /// # Errors
    /// [`Error::Count`] if a local fingerprint count overflows.
    pub fn new(snapshot: Arc<Snapshot>, limits: Limits) -> Result<Self, Error> {
        let original_root = root(&snapshot)?;
        Ok(Self {
            original: Arc::clone(&snapshot),
            working: snapshot,
            original_root,
            peer_root: Fingerprint::default(),
            own_view_root: Fingerprint::default(),
            peer_view_root: Fingerprint::default(),
            limits,
            budget: Budget {
                used: 0,
                limit: limits.messages,
            },
            phase: Phase::Root,
            frontiers: Vec::new(),
            proposals: Vec::new(),
            peer_items: Vec::new(),
            peer_done: false,
            at: 0,
            full: false,
            send: BTreeSet::new(),
            want: BTreeSet::new(),
            difference: None,
        })
    }

    /// A complete local send/want set, absent until full validation finishes.
    #[must_use]
    pub fn difference(&self) -> Option<&Difference> {
        self.difference.as_ref()
    }

    /// Handle the next decoded request, preserving no authority decision.
    /// # Errors
    /// Malformed, out-of-phase, over-budget or inconsistent input fences an
    /// unfinished exchange. No tentative difference becomes observable.
    pub fn answer(&mut self, message: Message) -> Result<Message, Error> {
        if matches!(self.phase, Phase::Done | Phase::Failed) {
            return Err(Error::Phase);
        }
        let answer = self.budget.charge().and_then(|()| self.inner(message));
        if answer.is_err() {
            self.phase = Phase::Failed;
        }
        answer
    }

    fn anchors(
        &mut self,
        items: Vec<Frontier>,
        done: bool,
        prefixes: bool,
    ) -> Result<Message, Error> {
        append_anchors(
            &mut self.peer_items,
            items,
            done,
            &mut self.peer_done,
            self.peer_root.count,
        )?;
        let ours = if prefixes {
            &self.proposals
        } else {
            &self.frontiers
        };
        let end = self.at.saturating_add(PAGE).min(ours.len());
        let items = ours[self.at..end].to_vec();
        let finished = end == ours.len();
        self.at = end;
        let reply = if prefixes {
            Message::Prefixes {
                items,
                done: finished,
            }
        } else {
            Message::Frontiers {
                items,
                done: finished,
            }
        };
        if finished && self.peer_done {
            if prefixes {
                let shared = union_prefixes(&self.proposals, &self.peer_items)?;
                (self.working, self.own_view_root, self.peer_view_root) =
                    reduced(&self.original, self.original_root, self.peer_root, &shared)?;
                self.phase = Phase::Ranges;
            } else {
                self.proposals = self.original.shared_prefixes(&self.peer_items)?;
                self.phase = Phase::Prefixes;
            }
            self.at = 0;
            self.peer_done = false;
            self.peer_items.clear();
        }
        Ok(reply)
    }

    fn inner(&mut self, message: Message) -> Result<Message, Error> {
        match (self.phase, message) {
            (Phase::Root, Message::Root(peer)) => {
                validate_root(peer, self.limits.remote_records)?;
                self.peer_root = peer;
                if peer == self.original_root {
                    self.own_view_root = self.original_root;
                    self.peer_view_root = peer;
                    self.phase = Phase::Ranges;
                } else {
                    self.frontiers = self.original.frontiers().collect();
                    self.phase = Phase::Frontiers;
                }
                Ok(Message::Root(self.original_root))
            }
            (Phase::Frontiers, Message::Frontiers { items, done }) => {
                self.anchors(items, done, false)
            }
            (Phase::Prefixes, Message::Prefixes { items, done }) => self.anchors(items, done, true),
            (Phase::Ranges, Message::Refine) if !self.full => {
                self.full = true;
                Ok(Message::Accepted)
            }
            (Phase::Ranges, Message::Split { range, children }) => {
                let ranges = range.children().ok_or(Error::Range)?;
                let mut different = 0;
                let mut counts = [0; 16];
                for (position, (range, probe)) in
                    ranges.into_iter().zip(children.iter()).enumerate()
                {
                    if self.full && !matches!(probe, Probe::Full(_)) {
                        return Err(Error::Phase);
                    }
                    let held = self
                        .working
                        .range_fingerprint(Some(range.prefix().0), range.upper())?;
                    if !probe.matches(held) {
                        different |= 1 << position;
                        counts[position] = held.count;
                    }
                }
                Ok(Message::SplitReply {
                    range,
                    different,
                    counts,
                })
            }
            (Phase::Ranges, Message::ListRequest { range, after }) => {
                if after.is_some_and(|id| !range.contains(&id)) {
                    return Err(Error::Range);
                }
                let mut remaining = in_range(&self.working, range, after);
                let ids = remaining.by_ref().take(PAGE).copied().collect();
                let done = remaining.next().is_none();
                Ok(Message::List { range, ids, done })
            }
            (
                Phase::Ranges | Phase::Send,
                Message::Difference {
                    ids,
                    done,
                    local_only: true,
                },
            ) => self.difference_page(ids, done, true),
            (
                Phase::Want,
                Message::Difference {
                    ids,
                    done,
                    local_only: false,
                },
            ) => self.difference_page(ids, done, false),
            (
                Phase::Finish,
                Message::Finish {
                    local_only,
                    remote_only,
                },
            ) => {
                let want = contribution(self.want.iter().copied())?;
                let send = contribution(self.send.iter().copied())?;
                if want != local_only
                    || send != remote_only
                    || !conserved(self.own_view_root, self.peer_view_root, send, want)?
                {
                    return Err(Error::Conservation);
                }
                self.difference = Some(Difference {
                    send: std::mem::take(&mut self.send).into_iter().collect(),
                    want: std::mem::take(&mut self.want).into_iter().collect(),
                });
                self.phase = Phase::Done;
                Ok(Message::Finish {
                    local_only,
                    remote_only,
                })
            }
            _ => Err(Error::Phase),
        }
    }

    fn difference_page(
        &mut self,
        ids: Vec<Digest>,
        done: bool,
        initiator_only: bool,
    ) -> Result<Message, Error> {
        if ids.len() > PAGE || (!done && ids.is_empty()) {
            return Err(Error::Wire);
        }
        let (target, bound) = if initiator_only {
            (&mut self.want, self.peer_view_root.count)
        } else {
            (&mut self.send, self.own_view_root.count)
        };
        if target.len().saturating_add(ids.len()) as u64 > bound {
            return Err(Error::Count);
        }
        for id in ids {
            let present = if initiator_only {
                self.original.contains(&id)
            } else {
                self.working.contains(&id)
            };
            if present == initiator_only || target.last().is_some_and(|last| *last >= id) {
                return Err(Error::Wire);
            }
            target.insert(id);
        }
        self.phase = if initiator_only {
            if done {
                Phase::Want
            } else {
                Phase::Send
            }
        } else if done {
            Phase::Finish
        } else {
            Phase::Want
        };
        Ok(Message::Accepted)
    }
}

#[cfg(test)]
#[path = "exchange_tests.rs"]
mod tests;
