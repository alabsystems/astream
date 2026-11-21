// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::super::floor_tests::{boundary, cut_of, id, Rng};
use super::super::{forks_of, Header, Headers, Index, Projection, Refusal, Retained, Unwritten};
use super::*;
use std::cell::Cell;
use std::collections::VecDeque;

/// A digest no generated record has: `kind` and `n` in a pattern `id` never makes.
fn absent(kind: u8, n: u64) -> Digest {
    let mut id = [0xEE; 32];
    id[1] = kind;
    id[2..10].copy_from_slice(&n.to_be_bytes());
    id
}

/// `header`'s link, written apart from the tracker: none without a predecessor, unknown when
/// the index holds no predecessor, good when the held predecessor is of its actor exactly one
/// sequence below.
fn link_of<S: Headers>(index: &Index<S>, header: &Header) -> Link {
    let Some(previous) = header.previous else {
        return Link::None;
    };
    let held = index
        .header(&previous)
        .map(Cow::into_owned)
        .or_else(|| index.floor().get(&previous).map(|r| r.header.clone()));
    match held {
        None => Link::Unknown,
        Some(p)
            if p.actor == header.actor && p.sequence.checked_add(1) == Some(header.sequence) =>
        {
            Link::Good
        }
        Some(_) => Link::Bad,
    }
}

/// Each actor's highest record among `p.ordered` and the floor, by sequence then id.
fn tips_of<S: Headers>(index: &Index<S>, p: &Projection) -> BTreeMap<Actor, Tip> {
    let mut tips = BTreeMap::<Actor, Tip>::new();
    let mut offer = |actor: Actor, sequence: u64, id: Digest| {
        let tip = Tip { sequence, id };
        let at = tips.entry(actor).or_insert(tip);
        *at = (*at).max(tip);
    };
    for id in &p.ordered {
        if let Some(h) = index.header(id) {
            offer(h.actor, h.sequence, h.id);
        }
    }
    for record in index.floor().values() {
        offer(
            record.header.actor,
            record.header.sequence,
            record.header.id,
        );
    }
    tips
}

/// The first field on which the tracked `heads`, `pending`, `quarantined` and `tips` disagree
/// with `p`, a projection of `index`: the heads, the pending set, each pending record's count
/// of parents neither floor nor ordered and its link, the quarantine and the tips.
fn disagreement<S: Headers>(
    index: &Index<S>,
    p: &Projection,
    heads: &BTreeSet<Digest>,
    pending: &BTreeMap<Digest, Wait>,
    quarantined: &BTreeSet<Actor>,
    tips: &BTreeMap<Actor, Tip>,
) -> Option<String> {
    if *heads != p.heads {
        let extra: Vec<_> = heads
            .difference(&p.heads)
            .map(|d| d[..4].to_vec())
            .collect();
        let missing: Vec<_> = p.heads.difference(heads).map(|d| d[..4].to_vec()).collect();
        return Some(format!("heads: extra {extra:?}, missing {missing:?}"));
    }
    if !pending.keys().eq(p.pending.iter()) {
        let tracked: BTreeSet<Digest> = pending.keys().copied().collect();
        let extra = tracked.difference(&p.pending).count();
        let missing = p.pending.difference(&tracked).count();
        return Some(format!("pending: {extra} extra, {missing} missing"));
    }
    for (id, wait) in pending {
        let Some(header) = index.header(id) else {
            return Some(format!("pending {:?} not retained", &id[..4]));
        };
        let unmet = header
            .parents
            .iter()
            .filter(|q| {
                !index.floor().contains_key(*q)
                    && (index.header(q).is_none() || p.pending.contains(*q))
            })
            .count() as u64;
        let link = link_of(index, &header);
        if *wait != (Wait { unmet, link }) {
            return Some(format!(
                "wait of {:?}: tracked {wait:?}, fresh {:?}",
                &id[..4],
                Wait { unmet, link }
            ));
        }
    }
    if *quarantined != p.quarantined {
        return Some(format!(
            "quarantined: tracked {}, fresh {}",
            quarantined.len(),
            p.quarantined.len()
        ));
    }
    let fresh = tips_of(index, p);
    if *tips != fresh {
        let differ = tips
            .iter()
            .find(|(a, t)| fresh.get(*a) != Some(t))
            .map(|(a, t)| (a[0], *t, fresh.get(a).copied()));
        return Some(format!("tips: first differing {differ:?}"));
    }
    None
}

/// [`disagreement`] of the index's own tracker with `p`.
fn tracker_disagreement<S: Headers>(index: &Index<S>, p: &Projection) -> Option<String> {
    let t = index.tracker();
    disagreement(index, p, t.heads(), t.pending(), t.quarantined(), t.tips())
}

/// The tracker's internal invariants beyond the projection's fields: the quarantine is
/// exactly the actors [`forks_of`] names over every retained header (the pairwise claim check,
/// apart from the dot check the tracker and `Index::forks` share), a tracker rebuilt from the
/// store and the floor equals it, and each actor's discharged runs hold exactly the sequences
/// of its ordered records.
fn internal_breach<S: Headers>(index: &Index<S>, p: &Projection) -> Option<String> {
    let t = index.tracker();
    let held: Vec<Cow<'_, Header>> = index.store().headers().collect();
    let forked: BTreeSet<Actor> = forks_of(held.iter().map(|h| &**h)).into_keys().collect();
    if t.quarantined != forked {
        return Some("quarantine is not forks_of".into());
    }
    if *t != Tracker::rebuild(index.store(), index.floor()) {
        return Some("a rebuilt tracker differs".into());
    }
    let mut ordered = BTreeMap::<Actor, BTreeSet<u64>>::new();
    for id in &p.ordered {
        if let Some(h) = index.header(id) {
            ordered.entry(h.actor).or_default().insert(h.sequence);
        }
    }
    let mut runs = BTreeMap::<Actor, BTreeSet<u64>>::new();
    for (actor, intervals) in &t.runs {
        let mut last = None;
        for (start, end) in intervals {
            if start > end || last.is_some_and(|l: u64| l.saturating_add(1) >= *start) {
                return Some(format!("runs of {:?} not disjoint and apart", actor[0]));
            }
            last = Some(*end);
            runs.entry(*actor).or_default().extend(*start..=*end);
        }
    }
    if runs != ordered {
        return Some("runs are not the ordered sequences".into());
    }
    for (actor, set) in &ordered {
        if t.discharged_by(actor) != set.len() as u64 {
            return Some("discharged_by is not the ordered count".into());
        }
    }
    None
}

/// The group an actor of the scale history writes in: 0 forkers, 1 their satellites, 2 the
/// fringe, 3 the mainstream.
fn group(actor: u64) -> u8 {
    match actor {
        0..10 => 0,
        10..30 => 1,
        30..100 => 2,
        _ => 3,
    }
}

/// A generated history and the order its records arrive in, repeats included.
struct Delivery {
    headers: Vec<Header>,
    order: Vec<usize>,
}

/// Records by `actors` actors in dense chains until `delivered` of them are delivered. Each names
/// its actor's previous record and up to three records heard in a stale window of the last 256.
/// The mainstream (actors 100 and up) names only the mainstream. The fringe (30 to 99) also names
/// the fringe; only it has never-delivered records (about 0.3% of all), bad links (about 0.2%:
/// a side record linked to another actor's record or across a skipped sequence, at a dot its
/// chain never reaches) and references to records generated later (about 0.5%). Forkers (0 to 9)
/// each fork once at a seeded point, half by a second record at their latest sequence and half
/// by a record naming a predecessor never written, between 50% and 95% of the run; only
/// satellites (10 to 29) name forkers, a forker's latest record in about one pick in 50, and
/// only satellites name satellites, a satellite's latest record in about one pick in four, so a
/// withdrawal stays within those 30 actors.
/// Delivery shuffles within 256 positions, delays about 1% by up to 10,000 more, and delivers
/// about 2% again.
fn scale_history(rng: &mut Rng, delivered: usize, actors: u64) -> Delivery {
    let fork_at: Vec<u64> = (0..10)
        .map(|_| delivered as u64 / 2 + rng.below(delivered as u64 * 9 / 20))
        .collect();
    let mut forked = [false; 10];
    let mut tips: BTreeMap<u64, (u64, Digest, Option<Digest>)> = BTreeMap::new();
    let mut window: VecDeque<(Digest, u8)> = VecDeque::new();
    let mut headers = Vec::new();
    let mut undelivered = BTreeSet::new();
    let mut n = 0;
    while headers.len() - undelivered.len() < delivered {
        let actor = rng.below(actors);
        let kind = group(actor);
        let me = {
            let mut a = [0; 48];
            a[..8].copy_from_slice(&actor.to_be_bytes());
            a
        };
        let tip = tips.get(&actor).copied();
        let mut parents = BTreeSet::new();
        for _ in 0..rng.below(4) {
            if kind == 1 && rng.below(50) == 0 {
                parents.extend(tips.get(&rng.below(10)).map(|tip| tip.1));
                continue;
            }
            if kind == 1 && rng.below(4) == 0 {
                parents.extend(tips.get(&(10 + rng.below(20))).map(|tip| tip.1));
                continue;
            }
            let Some(&(heard, from)) = window.get(rng.below(256) as usize) else {
                continue;
            };
            let allowed = matches!((kind, from), (_, 3) | (2, 2) | (1, 1));
            if allowed {
                parents.insert(heard);
            }
        }
        let (sequence, previous, chain) = if kind == 0
            && !forked[actor as usize % 10]
            && n >= fork_at[actor as usize % 10]
            && tip.is_some()
        {
            forked[actor as usize % 10] = true;
            let (sequence, _, below) = tip.unwrap_or_default();
            if actor % 2 == 0 {
                (sequence, below, false)
            } else {
                (sequence + 1, Some(absent(1, actor)), false)
            }
        } else if kind == 2 && rng.below(1000) < 29 {
            match tip {
                Some((sequence, tip, _)) if rng.below(2) == 0 => {
                    (sequence + 1_000_000, Some(tip), false)
                }
                _ => {
                    let other = window
                        .iter()
                        .rev()
                        .find(|(_, from)| *from == 3)
                        .map_or(absent(2, n), |(d, _)| *d);
                    (2_000_000 + n, Some(other), false)
                }
            }
        } else {
            match tip {
                Some((sequence, tip, _)) => (sequence + 1, Some(tip), true),
                None => (1, None, true),
            }
        };
        if kind == 2 && rng.below(1000) < 70 {
            parents.insert(id(n as usize + 1 + rng.below(200) as usize));
        }
        parents.extend(previous);
        let header = Header {
            id: id(n as usize),
            actor: me,
            sequence,
            previous,
            parents: parents.into_iter().collect(),
        };
        if chain {
            tips.insert(actor, (sequence, header.id, previous));
            window.push_back((header.id, kind));
            if window.len() > 256 {
                window.pop_front();
            }
        }
        if kind == 2 && rng.below(1000) < 43 {
            undelivered.insert(headers.len());
        }
        headers.push(header);
        n += 1;
    }
    let mut keyed = Vec::new();
    let mut position = 0_u64;
    for at in 0..headers.len() {
        if undelivered.contains(&at) {
            continue;
        }
        let mut key = position + rng.below(256);
        if rng.below(100) == 0 {
            key += rng.below(10_000);
        }
        keyed.push((key, rng.below(u64::MAX), at));
        if rng.below(50) == 0 {
            keyed.push((position + 1 + rng.below(10_000), rng.below(u64::MAX), at));
        }
        position += 1;
    }
    keyed.sort_unstable();
    Delivery {
        headers,
        order: keyed.into_iter().map(|(_, _, at)| at).collect(),
    }
}

/// 1,000 insert counts from 100 to `last`, log-spaced and strictly increasing, the last `last`.
fn samples(last: u64) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    for i in 0..1000 {
        let at = (100.0 * (last as f64 / 100.0).powf(f64::from(i) / 999.0)).round() as u64;
        let at = out.last().map_or(at, |prev| at.max(prev + 1));
        out.push(at);
    }
    out
}

/// What the scale run saw.
#[derive(Debug, Default)]
struct Seen {
    duplicates: u64,
    withdrawn: u64,
    late_releases: u64,
}

/// Feed `delivery` to `index`, checking the tracker against a fresh projection at each sampled
/// insert count, and count what the run saw.
fn feed_and_sample(index: &mut Index, delivery: &Delivery, at: &[u64]) -> Result<Seen, String> {
    let mut seen = Seen::default();
    let mut inserted = 0_u64;
    let mut next = at.iter().peekable();
    for &row in &delivery.order {
        let header = delivery.headers[row].clone();
        let t = index.tracker();
        let (quarantined, discharged) =
            (t.quarantined().len(), inserted - t.pending().len() as u64);
        match index.insert(header) {
            Ok(true) => inserted += 1,
            Ok(false) => {
                seen.duplicates += 1;
                continue;
            }
            Err(e) => return Err(format!("refused {e:?}")),
        }
        let t = index.tracker();
        let now = inserted - t.pending().len() as u64;
        if t.quarantined().len() > quarantined {
            seen.withdrawn += discharged.saturating_sub(now);
        } else if now > discharged + 1 {
            seen.late_releases += 1;
        }
        if next.peek() == Some(&&inserted) {
            next.next();
            if let Some(why) = tracker_disagreement(index, &index.project()) {
                return Err(format!("at insert {inserted}: {why}"));
            }
        }
    }
    if next.peek().is_some() {
        return Err(format!("only {inserted} inserts"));
    }
    Ok(seen)
}

/// Over 100,000 inserts by 1,000 actors (late and repeated deliveries, forward references,
/// records never delivered, bad links and ten forks) the tracker equals a fresh projection at
/// 1,000 log-spaced insert counts: heads, the pending set, each pending record's unmet count and
/// link, the quarantine and every actor's tip. The run saw at least five quarantines, 1,000
/// records withdrawn, releases of records that waited for a late parent, pending records with a
/// bad link, and duplicates.
/// NEGATIVE CONTROL: with a quarantine withdrawing only the forked actor's own records and not
/// the records above them (`above` not following children): `at insert 28409: heads: extra
/// [[26, 0, 0, 0], [38, 0, 0, 0], [56, 0, 0, 0]], missing [[52, 0, 0, 0], [153, 0, 0, 0], …]`.
#[test]
fn a_tracker_over_100000_inserts_by_1000_actors_equals_a_fresh_projection_at_each_of_1000_sampled_inserts(
) {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let delivery = scale_history(&mut rng, 100_000, 1000);
    let at = samples(100_000);
    assert_eq!((at.len(), at.last()), (1000, Some(&100_000)));
    let mut index = Index::with_budget(u64::MAX);
    let seen = feed_and_sample(&mut index, &delivery, &at).unwrap();
    let t = index.tracker();
    let bad = t.pending().values().filter(|w| w.link == Link::Bad).count();
    eprintln!(
        "quarantined {} pending {} heads {} bad {bad} {seen:?}",
        t.quarantined().len(),
        t.pending().len(),
        t.heads().len()
    );
    assert!(t.quarantined().len() >= 5, "{}", t.quarantined().len());
    assert!(seen.withdrawn >= 1000, "{seen:?}");
    assert!(seen.late_releases > 0, "{seen:?}");
    assert!(bad > 0);
    assert!(seen.duplicates > 0, "{seen:?}");
}

/// What one property run delivers: a retained record, a floor record, or either again.
#[derive(Clone, Copy, Debug)]
enum Event {
    Record(usize),
    Floor(usize),
    RecordAgain(usize),
    FloorAgain(usize),
    FloorAsRecord(usize),
}

/// Six actors' records, each naming its actor's previous record and up to two records heard in
/// the last 16: actors 4 and 5 sometimes fork (a second record at the latest sequence, or a
/// predecessor never written), about 3% name a record generated later (some of which name them
/// back: a cycle), about 3% are side records with a bad link (to another actor's record, which
/// may lie below the floor, or across a skipped sequence), and about 3% are never delivered.
fn small_history(rng: &mut Rng, records: usize) -> (Vec<Header>, BTreeSet<usize>) {
    let mut tips: BTreeMap<u8, (u64, Digest, Option<Digest>)> = BTreeMap::new();
    let mut window: VecDeque<Digest> = VecDeque::new();
    let mut out = Vec::new();
    let mut undelivered = BTreeSet::new();
    for n in 0..records {
        let actor = rng.below(6) as u8;
        let tip = tips.get(&actor).copied();
        let mut parents = BTreeSet::new();
        for _ in 0..rng.below(3) {
            if let Some(heard) = window.get(rng.below(16) as usize) {
                parents.insert(*heard);
            }
        }
        if rng.below(100) < 3 {
            parents.insert(id(n + 1 + rng.below(5) as usize));
        }
        let (sequence, previous, chain) = match tip {
            Some((sequence, _, below)) if actor >= 4 && rng.below(12) == 0 => {
                if rng.below(2) == 0 {
                    (sequence, below, false)
                } else {
                    (sequence + 1, Some(absent(3, n as u64)), false)
                }
            }
            Some((sequence, tip, _)) if rng.below(100) < 3 => {
                if rng.below(2) == 0 {
                    (sequence + 1000, Some(tip), false)
                } else {
                    let other = window.get(rng.below(16) as usize).copied().unwrap_or(tip);
                    (5000 + n as u64, Some(other), false)
                }
            }
            Some((sequence, tip, _)) => (sequence + 1, Some(tip), true),
            None => (1, None, true),
        };
        parents.extend(previous);
        let header = Header {
            id: id(n),
            actor: [actor; 48],
            sequence,
            previous,
            parents: parents.into_iter().collect(),
        };
        if chain {
            tips.insert(actor, (sequence, header.id, previous));
        }
        window.push_front(header.id);
        window.truncate(16);
        if rng.below(100) < 3 {
            undelivered.insert(n);
        }
        out.push(header);
    }
    (out, undelivered)
}

/// The events of one property run: the records above a cut drawn from the first 40%, the cut's
/// boundary as floor records, all in a random order (a floor record often after its children),
/// with some delivered again.
fn property_run(seed: u64, records: usize) -> (Vec<Header>, Vec<FloorRecord>, Vec<Event>) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let (headers, undelivered) = small_history(&mut rng, records);
    let mut full = Index::with_budget(u64::MAX);
    for header in &headers {
        full.insert(header.clone()).unwrap();
    }
    let roots: Vec<Digest> = (0..rng.below(3))
        .map(|_| headers[rng.below(records as u64 * 2 / 5) as usize].id)
        .collect();
    let mut cut = cut_of(&full, &roots);
    let mut floor = boundary(&full, &headers, &cut);
    // A cut whose past runs through a side record or a cycle can put a higher sequence of a
    // boundary record's own actor below it, which no floor record may state: take no cut then.
    if floor
        .iter()
        .any(|r| r.past.get(&r.header.actor) != Some(&r.header.sequence))
    {
        cut.clear();
        floor.clear();
    }
    let mut events: Vec<Event> = (0..headers.len())
        .filter(|n| !undelivered.contains(n) && !cut.contains(&headers[*n].id))
        .map(Event::Record)
        .chain((0..floor.len()).map(Event::Floor))
        .collect();
    for at in (1..events.len()).rev() {
        events.swap(at, rng.below(at as u64 + 1) as usize);
    }
    let base = events.len();
    for _ in 0..base / 10 {
        let at = rng.below(events.len() as u64 + 1) as usize;
        let again = match events.get(rng.below(base as u64) as usize) {
            Some(Event::Record(n)) => Event::RecordAgain(*n),
            Some(Event::Floor(k)) if rng.below(2) == 0 => Event::FloorAgain(*k),
            Some(Event::Floor(k)) => Event::FloorAsRecord(*k),
            _ => continue,
        };
        events.insert(at, again);
    }
    (headers, floor, events)
}

/// Apply `event` to `index`: whether the index admitted it (a repeat may come before the first,
/// and then it is the first). A floor header offered as a record before its floor record is
/// held is not offered: it would be retained, not a floor record.
fn apply(index: &mut Index, headers: &[Header], floor: &[FloorRecord], event: Event) -> bool {
    match event {
        Event::Record(n) | Event::RecordAgain(n) => index.insert(headers[n].clone()).is_ok(),
        Event::Floor(k) | Event::FloorAgain(k) => index.insert_floor(floor[k].clone()).is_ok(),
        Event::FloorAsRecord(k) => {
            !index.floor().contains_key(&floor[k].header.id)
                || index.insert(floor[k].header.clone()) == Ok(false)
        }
    }
}

/// About 5% of the retained ids, and now and then a floor id or an id nothing holds.
fn exclusions(rng: &mut Rng, index: &Index) -> BTreeSet<Digest> {
    let mut out: BTreeSet<Digest> = index
        .inventory()
        .filter(|_| rng.below(20) == 0)
        .copied()
        .collect();
    if rng.below(4) == 0 {
        out.extend(index.floor().keys().next().copied());
        out.insert(absent(9, rng.below(1000)));
    }
    out
}

/// Where `view`'s lookups disagree with its listings: `is_head` with `heads`, `wait` and
/// `pending_len` with `pending`, `tip` with `tips`, or a listing not strictly ascending.
fn view_breach(view: &Tracked<'_>) -> Option<String> {
    let heads: Vec<Digest> = view.heads().collect();
    let pending: Vec<(Digest, Wait)> = view.pending().collect();
    let tips: Vec<(Actor, Tip)> = view.tips().collect();
    if !heads.windows(2).all(|w| w[0] < w[1])
        || !pending.windows(2).all(|w| w[0].0 < w[1].0)
        || !tips.windows(2).all(|w| w[0].0 < w[1].0)
    {
        return Some("a view listing is not strictly ascending".into());
    }
    if heads.iter().any(|id| !view.is_head(id)) || pending.iter().any(|(id, _)| view.is_head(id)) {
        return Some("view is_head disagrees with heads".into());
    }
    if pending.len() != view.pending_len()
        || pending
            .iter()
            .any(|(id, wait)| view.wait(id) != Some(*wait))
        || heads.iter().any(|id| view.wait(id).is_some())
    {
        return Some("view wait disagrees with pending".into());
    }
    if tips
        .iter()
        .any(|(actor, tip)| view.tip(actor) != Some(*tip))
    {
        return Some("view tip disagrees with tips".into());
    }
    None
}

/// The first event of the run for `seed` after which the tracker breaks a law: a field the fresh
/// projection answers otherwise, the quarantine not being `forks()`, the runs not being the
/// ordered sequences, or `tracked_excluding` differing from `project_excluding` under a random
/// exclusion set.
fn property_breach(seed: u64, records: usize) -> Option<String> {
    let (headers, floor, events) = property_run(seed, records);
    let mut rng = Rng(seed ^ 0xA5A5_A5A5_A5A5_A5A5);
    let mut index = Index::with_budget(u64::MAX);
    // Read before the first event, so every event feeds it.
    let _ = index.tracker();
    for (step, event) in events.iter().enumerate() {
        if !apply(&mut index, &headers, &floor, *event) {
            return Some(format!(
                "seed {seed} step {step}: {event:?} answered wrongly"
            ));
        }
        let p = index.project();
        if let Some(why) = tracker_disagreement(&index, &p).or_else(|| internal_breach(&index, &p))
        {
            return Some(format!("seed {seed} step {step} {event:?}: {why}"));
        }
        let excluded = exclusions(&mut rng, &index);
        let view = index.tracked_excluding(&excluded);
        let fresh = index.project_excluding(&excluded);
        if let Some(why) = view_breach(&view).or_else(|| {
            disagreement(
                &index,
                &fresh,
                &view.heads().collect(),
                &view.pending().collect(),
                view.quarantined(),
                &view.tips().collect(),
            )
        }) {
            return Some(format!(
                "seed {seed} step {step} excluding {}: {why}",
                excluded.len()
            ));
        }
    }
    None
}

/// After every insert and every floor insert of 200 seeded runs (six actors, forks, cycles, bad
/// links into retained and floor records, never-delivered parents, floor records arriving after
/// their children, and repeats of each) the tracker equals the fresh projection on heads,
/// pending records with their counts and links, quarantine and tips; its quarantine is what
/// `forks_of` finds over every retained header; a tracker rebuilt from the store and the floor
/// equals it; its runs are the ordered sequences; and `tracked_excluding` equals
/// `project_excluding` under a random exclusion of about 5%, its lookups agreeing with its
/// ascending listings.
/// NEGATIVE CONTROLS, each applied, run (this test's first failure quoted), and restored:
/// - `release` not visiting a discharged record's children (no cascade): `seed 1 step 25
///   Record(2): heads: extra [[178, 0, 0, 0]], missing [[32, 0, 0, 0]]`.
/// - an arriving record not judging its waiting children's links: `seed 1 step 5 Record(40):
///   wait of [135, 0, 0, 0]: tracked Wait { unmet: 2, link: Unknown }, fresh Wait { unmet: 2,
///   link: Good }`.
/// - `link_to` not asking `sequence_follows`: `seed 2 step 72 Record(7): wait of
///   [137, 0, 0, 0]: tracked Wait { unmet: 1, link: Good }, fresh Wait { unmet: 1, link: Bad }`.
/// - a floor record's arrival not decrementing its children: `seed 1 step 67 Floor(1): heads:
///   extra [[16, 0, 0, 0], [48, 0, 0, 0], [194, 0, 0, 0]], missing [[153, 0, 0, 0], …]`.
/// - the fork check without the dot below (which `Index::forks` shares): `seed 2 step 14
///   Record(57): quarantined: tracked 1, fresh 0`; without the dot above: `seed 2 step 14
///   Record(57): quarantined: tracked 0, fresh 1`.
/// - a withdrawal without the records above (`above` not following children): `seed 1 step 33
///   excluding 2: heads: extra [[32, 0, 0, 0]], missing []`.
/// - a withdrawal not restoring parent heads: `seed 1 step 36 excluding 3: heads: extra [],
///   missing [[178, 0, 0, 0]]`.
/// - a floor record reached by a later floor record's past staying a head: `seed 3 step 64
///   Floor(0): heads: extra [[64, 0, 0, 0]], missing []`.
/// - `Index::insert` feeding the tracker a duplicate (`Ok(false)`): `seed 1 step 77
///   Record(16): heads: extra [[39, 0, 0, 0], [71, 0, 0, 0]], missing [[169, 0, 0, 0]]`.
/// - tips not moving on a withdrawal: `seed 1 step 29 excluding 3: tips: first differing
///   Some((4, Tip { sequence: 1, .. }, None))`.
/// - `excluding` withdrawing the excluded records without the records above them: `seed 1
///   step 33 excluding 2: heads: extra [[32, 0, 0, 0]], missing []`.
/// - `satisfied` not counting a floor parent as met: `seed 2 step 72 Record(7): wait of
///   [121, 0, 0, 0]: tracked Wait { unmet: 1, link: None }, fresh Wait { unmet: 0, link: None }`.
/// - a withdrawal making a parent a head while a discharged record still names it (the named
///   count compared with `>=`): `seed 1 step 76 excluding 6: heads: extra [[16, 0, 0, 0],
///   [153, 0, 0, 0]], missing []`.
/// - `rebuild` leaving the quarantine empty: `seed 2 step 14 Record(57): a rebuilt tracker
///   differs`.
#[test]
fn a_tracker_equals_the_projection_after_every_insert_under_random_orders_duplicates_forks_floors_late_parents_and_exclusions(
) {
    let mut kinds = [0_u64; 3];
    for seed in 1..=200 {
        if let Some(why) = property_breach(seed, 80) {
            panic!("{why}");
        }
        let (headers, floor, _) = property_run(seed, 80);
        kinds[0] += floor.len() as u64;
        kinds[1] += headers.len() as u64;
        kinds[2] += u64::from(!floor.is_empty());
    }
    assert!(kinds[2] > 100, "{kinds:?}: most runs have a floor");
}

/// A store that counts every read: a header or containment by id, a dot, and each child.
#[derive(Default)]
struct Counted {
    inner: Retained,
    reads: Cell<u64>,
}

impl Counted {
    fn read(&self) {
        self.reads.set(self.reads.get() + 1);
    }
}

impl Headers for Counted {
    fn header(&self, id: &Digest) -> Option<Cow<'_, Header>> {
        self.read();
        self.inner.header(id)
    }
    fn contains(&self, id: &Digest) -> bool {
        self.read();
        self.inner.contains(id)
    }
    fn at(&self, actor: &Actor, sequence: u64) -> Option<Digest> {
        self.read();
        self.inner.at(actor, sequence)
    }
    fn children(&self, id: &Digest) -> impl Iterator<Item = Digest> + '_ {
        self.inner.children(id).inspect(|_| self.read())
    }
    fn headers(&self) -> impl Iterator<Item = Cow<'_, Header>> + '_ {
        self.inner.headers().inspect(|_| self.read())
    }
    fn len(&self) -> usize {
        self.inner.len()
    }
    fn put(&mut self, header: Header) -> Result<(), Unwritten> {
        self.inner.put(header)
    }
}

/// A store that retains its first `room` headers and refuses every write after them.
struct Refusing {
    inner: Retained,
    room: usize,
}

impl Headers for Refusing {
    fn header(&self, id: &Digest) -> Option<Cow<'_, Header>> {
        self.inner.header(id)
    }
    fn at(&self, actor: &Actor, sequence: u64) -> Option<Digest> {
        self.inner.at(actor, sequence)
    }
    fn children(&self, id: &Digest) -> impl Iterator<Item = Digest> + '_ {
        self.inner.children(id)
    }
    fn headers(&self) -> impl Iterator<Item = Cow<'_, Header>> + '_ {
        self.inner.headers()
    }
    fn len(&self) -> usize {
        self.inner.len()
    }
    fn put(&mut self, header: Header) -> Result<(), Unwritten> {
        if self.inner.len() >= self.room {
            return Err(Unwritten);
        }
        self.inner.put(header)
    }
}

/// A write the store refuses leaves the index as it was: each insert answers
/// `Refusal::Unwritten`, and the held bytes, the frontier, the ids and the tracker are those
/// before it. Once the store has room the same headers are admitted, and the tracker equals the
/// projection.
/// NEGATIVE CONTROL: with `Index::insert` adding the header's bytes to `held` and raising the
/// frontier before `put`: `insert 30: the index changed`.
#[test]
fn a_write_the_store_refuses_leaves_the_index_as_it_was() {
    let mut rng = Rng(77);
    let (headers, _) = small_history(&mut rng, 60);
    let store = Refusing {
        inner: Retained::new(),
        room: 30,
    };
    let mut index = Index::with_store(store, u64::MAX);
    assert!(index.tracker().pending().is_empty());
    for header in &headers[..30] {
        assert_eq!(index.insert(header.clone()), Ok(true));
    }
    let state = |index: &Index<Refusing>| {
        (
            index.held(),
            index.frontier().clone(),
            index.ids().collect::<Vec<_>>(),
            index.tracker().clone(),
        )
    };
    let before = state(&index);
    for (n, header) in headers.iter().enumerate().skip(30) {
        assert_eq!(index.insert(header.clone()), Err(Refusal::Unwritten));
        assert!(state(&index) == before, "insert {n}: the index changed");
    }
    index.records.room = headers.len();
    for header in &headers[30..] {
        assert_eq!(index.insert(header.clone()), Ok(true));
    }
    let p = index.project();
    assert_eq!(tracker_disagreement(&index, &p), None);
    assert_eq!(index.ids().count(), headers.len());
}

/// The reads one insert may make: 8 for the header and its dots, one per parent, two per child
/// of the inserted record, and two per child of each record it discharges; on an insert that
/// quarantines, for each withdrawn record 3, three per child and three per parent. Nothing in it
/// grows with the pending set.
fn read_bound(
    store: &Retained,
    header: &Header,
    discharged: &BTreeSet<Digest>,
    withdrawn: &BTreeSet<Digest>,
) -> u64 {
    let children = |id: &Digest| store.children(id).count() as u64;
    let parents = |id: &Digest| store.get(id).map_or(0, |h| h.parents.len() as u64);
    let mut bound = 8 + header.parents.len() as u64 + 2 * children(&header.id);
    for id in discharged {
        bound += 2 * children(id);
    }
    for id in withdrawn {
        bound += 3 + 3 * children(id) + 3 * parents(id);
    }
    bound
}

/// The reads one insert into `index` makes, against [`read_bound`], for each of `headers` in
/// turn: the first insert over the bound, if any.
fn read_breach(headers: &[Header]) -> Option<String> {
    let mut index = Index::with_store(Counted::default(), u64::MAX);
    for header in headers {
        let before: BTreeSet<Digest> = index.tracker().pending().keys().copied().collect();
        let reads = index.store().reads.get();
        if index.insert(header.clone()) != Ok(true) {
            continue;
        }
        let made = index.store().reads.get() - reads;
        let after = index.tracker().pending();
        let discharged: BTreeSet<Digest> = before
            .iter()
            .chain([&header.id])
            .filter(|id| !after.contains_key(*id))
            .copied()
            .collect();
        let withdrawn: BTreeSet<Digest> = after
            .keys()
            .filter(|id| !before.contains(*id) && **id != header.id)
            .copied()
            .collect();
        let bound = read_bound(&index.store().inner, header, &discharged, &withdrawn);
        if made > bound {
            return Some(format!(
                "insert of {:?}: {made} reads, bound {bound} (pending {})",
                &header.id[..4],
                after.len()
            ));
        }
    }
    None
}

/// Each insert of a 6,000-record history by 100 actors, with forks, bad links and parents that
/// never arrive (so hundreds of records stay pending), reads only the inserted record's
/// neighbourhood, what it discharges, and on a fork what it withdraws: never the retained set or
/// the pending set as a whole.
/// NEGATIVE CONTROL: with `inserted` reading every pending record's header on each insert:
/// `insert of [119, 0, 0, 0]: 9 reads, bound 8 (pending 3)`.
#[test]
fn a_tracker_insert_reads_only_its_neighbourhood_and_what_it_changes() {
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    let delivery = scale_history(&mut rng, 6000, 100);
    let mut seen = BTreeSet::new();
    let ordered: Vec<Header> = delivery
        .order
        .iter()
        .filter(|row| seen.insert(**row))
        .map(|row| delivery.headers[*row].clone())
        .collect();
    assert_eq!(read_breach(&ordered), None);
}

/// An actor of its own for the hub test's record `n`.
fn hub_actor(n: u64) -> Actor {
    let mut actor = [7; 48];
    actor[..8].copy_from_slice(&n.to_be_bytes());
    actor
}

/// A fork that withdraws a record naming R makes R a head again reading a fixed number of
/// records, however many pending records also name R: here 2,000 pending records name R (each
/// also names a parent that never arrives), and the fork's insert reads at most 32 records.
/// NEGATIVE CONTROL: with `withdraw` finding a parent's discharged children by scanning
/// `store.children(parent)` (the code before the named counts): `fork insert: 2011 reads`.
#[test]
fn a_fork_restores_a_head_without_reading_the_pending_records_that_name_it() {
    let hub = Header {
        id: id(0),
        actor: hub_actor(9_000),
        sequence: 1,
        previous: None,
        parents: Vec::new(),
    };
    let mut index = Index::with_store(Counted::default(), u64::MAX);
    assert!(index.tracker().pending().is_empty());
    assert_eq!(index.insert(hub.clone()), Ok(true));
    for n in 0..2000_u64 {
        let mut parents = Vec::from([hub.id, absent(1, n)]);
        parents.sort_unstable();
        let waiting = Header {
            id: id(1 + n as usize),
            actor: hub_actor(n),
            sequence: 1,
            previous: None,
            parents,
        };
        assert_eq!(index.insert(waiting), Ok(true));
    }
    let named = |n: usize| Header {
        id: id(n),
        actor: hub_actor(9_001),
        sequence: 1,
        previous: None,
        parents: Vec::from([hub.id]),
    };
    assert_eq!(index.insert(named(3000)), Ok(true));
    assert!(!index.tracker().heads().contains(&hub.id));
    let before = index.store().reads.get();
    assert_eq!(index.insert(named(3001)), Ok(true));
    let made = index.store().reads.get() - before;
    assert!(index.tracker().heads().contains(&hub.id));
    assert_eq!(index.tracker().pending().len(), 2002);
    let p = index.project();
    assert_eq!(tracker_disagreement(&index, &p), None);
    assert!(made <= 32, "fork insert: {made} reads");
}

/// An index over a store already holding records builds, on the first read of its tracker, the
/// tracker an index fed record by record keeps.
/// NEGATIVE CONTROL: with `rebuild` leaving the quarantine empty: `seed 1: heads: extra
/// [[14, 0, 0, 0], [87, 0, 0, 0], …], missing [[105, 0, 0, 0]]`.
#[test]
fn an_index_over_a_full_store_rebuilds_the_tracker_it_would_have_fed() {
    for seed in 1..=20 {
        let mut rng = Rng(seed * 7919);
        let (headers, _) = small_history(&mut rng, 200);
        let mut fed = Index::with_budget(u64::MAX);
        // Read before the first insert, so every insert feeds it.
        assert!(fed.tracker().pending().is_empty());
        let mut store = Retained::new();
        for header in &headers {
            assert_eq!(fed.insert(header.clone()), Ok(true));
            assert_eq!(store.put(header.clone()), Ok(()));
        }
        let rebuilt = Index::with_store(store, u64::MAX);
        let p = rebuilt.project();
        assert_eq!(
            tracker_disagreement(&rebuilt, &p).or_else(|| internal_breach(&rebuilt, &p)),
            None,
            "seed {seed}"
        );
        assert_eq!(rebuilt.tracker(), fed.tracker(), "seed {seed}");
        assert_eq!(rebuilt.frontier(), fed.frontier());
        assert_eq!(rebuilt.held(), fed.held());
    }
}

/// Per-insert wall time of a tracked index at 100,000 records by 1,000 actors (mean, p99 and
/// max), against the same headers put into the bare store and into a map of headers (what the
/// index held before), `project()` at 10,000 and 100,000, and reads per insert.
/// A measurement; no time is asserted.
#[test]
#[ignore = "isolated optimized tracker measurement"]
fn tracker_insert_measurement() {
    use std::time::Instant;
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let delivery = scale_history(&mut rng, 100_000, 1000);
    let mut seen = BTreeSet::new();
    let ordered: Vec<Header> = delivery
        .order
        .iter()
        .filter(|row| seen.insert(**row))
        .map(|row| delivery.headers[*row].clone())
        .collect();
    let mut index = Index::with_budget(u64::MAX);
    // Read before the first insert, so every insert feeds it.
    let _ = index.tracker();
    let mut each = Vec::with_capacity(ordered.len());
    let mut projected = Vec::new();
    for (n, header) in ordered.iter().enumerate() {
        let started = Instant::now();
        std::hint::black_box(index.insert(header.clone())).unwrap();
        each.push(started.elapsed().as_nanos());
        if n + 1 == 10_000 || n + 1 == ordered.len() {
            let started = Instant::now();
            std::hint::black_box(index.project());
            projected.push((n + 1, started.elapsed().as_micros()));
        }
    }
    let total: u128 = each.iter().sum();
    each.sort_unstable();
    let pick = |q: f64| each[((each.len() - 1) as f64 * q) as usize];
    eprintln!(
        "TRACKED inserts={} mean_ns={} p50_ns={} p99_ns={} max_ns={}",
        each.len(),
        total / each.len() as u128,
        pick(0.5),
        pick(0.99),
        pick(1.0)
    );
    let started = Instant::now();
    let mut store = Retained::new();
    for header in &ordered {
        store.put(std::hint::black_box(header.clone())).unwrap();
    }
    eprintln!(
        "STORE-ONLY mean_ns={}",
        started.elapsed().as_nanos() / ordered.len() as u128
    );
    let started = Instant::now();
    let mut map = BTreeMap::new();
    for header in &ordered {
        map.insert(header.id, std::hint::black_box(header.clone()));
    }
    eprintln!(
        "MAP-ONLY mean_ns={}",
        started.elapsed().as_nanos() / ordered.len() as u128
    );
    for (at, micros) in projected {
        eprintln!("PROJECT records={at} us={micros}");
    }
    let mut counted = Index::with_store(Counted::default(), u64::MAX);
    let _ = counted.tracker();
    for header in &ordered {
        counted.insert(header.clone()).unwrap();
    }
    eprintln!(
        "READS per_insert={:.2}",
        counted.store().reads.get() as f64 / ordered.len() as f64
    );
    eprintln!(
        "STATE pending={} heads={} quarantined={} tips={}",
        index.tracker().pending().len(),
        index.tracker().heads().len(),
        index.tracker().quarantined().len(),
        index.tracker().tips().len()
    );
}
