// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;

/// A deterministic xorshift, so a failing seed reruns as it failed.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }
}

fn id(n: usize) -> Digest {
    let mut id = [0; 32];
    // The first byte permutes the rows, so digest order is not causal order.
    id[0] = (n * 89 % 251) as u8;
    id[1..9].copy_from_slice(&(n as u64).to_be_bytes());
    id
}

/// `records` headers by four actors: dense chains, each naming its actor's previous record and
/// up to two other actors' heads as the author last heard them (often stale). Actor 3 writes
/// only from `forks_from` on and now and then signs a second record at its latest sequence (a
/// fork), so a cut drawn from the first `forks_from` records holds none of a forked actor's.
fn history(rng: &mut Rng, records: usize, forks_from: usize) -> Vec<Header> {
    let mut tips: BTreeMap<u8, (u64, Digest)> = BTreeMap::new();
    // What each actor last heard of each other actor, which lags the truth.
    let mut heard: BTreeMap<(u8, u8), Digest> = BTreeMap::new();
    let mut out: Vec<Header> = Vec::new();
    for n in 0..records {
        let actor = if n < forks_from {
            rng.below(3) as u8
        } else {
            rng.below(4) as u8
        };
        for other in 0..4 {
            if other != actor && rng.below(3) == 0 {
                if let Some((_, tip)) = tips.get(&other) {
                    heard.insert((actor, other), *tip);
                }
            }
        }
        let fork = actor == 3 && rng.below(6) == 0 && tips.contains_key(&actor);
        let (sequence, previous) = match tips.get(&actor) {
            Some(&(sequence, tip)) if fork => {
                let previous = out.iter().find(|h| h.id == tip).and_then(|h| h.previous);
                (sequence, previous)
            }
            Some(&(sequence, tip)) => (sequence + 1, Some(tip)),
            None => (1, None),
        };
        let mut parents: BTreeSet<Digest> = previous.into_iter().collect();
        for _ in 0..rng.below(3) {
            let other = rng.below(4) as u8;
            if let Some(seen) = heard.get(&(actor, other)) {
                parents.insert(*seen);
            }
        }
        let header = Header {
            id: id(n),
            actor: [actor; 48],
            sequence,
            previous,
            parents: parents.into_iter().collect(),
        };
        if !fork {
            tips.insert(actor, (sequence, header.id));
        }
        out.push(header);
    }
    out
}

/// The past of `roots` in `full`: down-closed by construction, as a checkpoint's cut is.
fn cut_of(full: &Index, roots: &[Digest]) -> BTreeSet<Digest> {
    let mut cut = BTreeSet::new();
    for root in roots {
        cut.insert(*root);
        cut.extend(full.ancestors(root));
    }
    cut
}

/// The cut's boundary (its maximal records, and the records in it that a record above it
/// names), each with its past as a version vector read from `full`.
fn boundary(full: &Index, headers: &[Header], cut: &BTreeSet<Digest>) -> Vec<FloorRecord> {
    let mut named = BTreeSet::new();
    for header in headers.iter().filter(|h| !cut.contains(&h.id)) {
        named.extend(header.parents.iter().filter(|p| cut.contains(*p)));
        named.extend(header.previous.iter().filter(|p| cut.contains(*p)));
    }
    for id in cut {
        let maximal = !headers
            .iter()
            .any(|h| cut.contains(&h.id) && h.parents.contains(id));
        if maximal {
            named.insert(*id);
        }
    }
    named
        .into_iter()
        .map(|id| {
            let header = full.get(&id).unwrap().clone();
            let mut past = BTreeMap::new();
            for ancestor in full.ancestors(&id).iter().chain([&id]) {
                let h = full.get(ancestor).unwrap();
                let at = past.entry(h.actor).or_insert(0);
                *at = (*at).max(h.sequence);
            }
            FloorRecord { header, past }
        })
        .collect()
}

/// On random histories with stale cross-actor parents and forks above the cut, an index holding
/// only the records above a cut, with the cut's boundary as floor records, projects as the full
/// index does above the cut: the same ordered set in a causal order, the same pending records,
/// heads and quarantines, and the same answer to every `observes` from an ordered record above
/// the cut, to records above it by `observes` and below it by `reaches`.
/// NEGATIVE CONTROL: with `project_excluding` not seeding the floor records' vectors, every
/// question below the floor answers false: `seed 1: observes … full true, floored false`.
#[test]
fn floored_index_projects_like_the_full_index_above_the_floor() {
    let mut crossings = 0;
    for seed in 1..=40_u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let headers = history(&mut rng, 90, 60);
        let mut full = Index::new(1024);
        for header in &headers {
            full.insert(header.clone()).unwrap();
        }
        // The cut: the past of three records among the first sixty.
        let roots: Vec<Digest> = (0..3).map(|_| headers[rng.below(60) as usize].id).collect();
        let cut = cut_of(&full, &roots);
        let mut floored = Index::new(1024);
        for header in headers.iter().filter(|h| !cut.contains(&h.id)) {
            floored.insert(header.clone()).unwrap();
        }
        for record in boundary(&full, &headers, &cut) {
            assert!(floored.insert_floor(record).unwrap());
        }
        let whole = full.project();
        let above = floored.project();

        let ordered_above: BTreeSet<Digest> = whole
            .ordered
            .iter()
            .filter(|id| !cut.contains(*id))
            .copied()
            .collect();
        assert_eq!(
            above.ordered.iter().copied().collect::<BTreeSet<_>>(),
            ordered_above,
            "seed {seed}: ordered"
        );
        let mut placed = BTreeSet::new();
        for id in &above.ordered {
            let header = floored.get(id).unwrap();
            for parent in &header.parents {
                assert!(
                    placed.contains(parent) || floored.floor().contains_key(parent),
                    "seed {seed}: {id:?} ordered before its parent"
                );
            }
            placed.insert(*id);
        }
        let pending_above: BTreeSet<Digest> = whole.pending.difference(&cut).copied().collect();
        assert_eq!(above.pending, pending_above, "seed {seed}: pending");
        assert_eq!(above.heads, whole.heads, "seed {seed}: heads");
        assert_eq!(
            above.quarantined, whole.quarantined,
            "seed {seed}: quarantined"
        );

        for later in &above.ordered {
            for earlier in &headers {
                let truth = whole.observes(&full, later, &earlier.id);
                let floor_answer = if cut.contains(&earlier.id) {
                    crossings += 1;
                    above.reaches(&floored, later, &earlier.actor, earlier.sequence)
                } else {
                    above.observes(&floored, later, &earlier.id)
                };
                assert_eq!(
                    floor_answer, truth,
                    "seed {seed}: observes {later:?} {:?}: full {truth}, floored {floor_answer}",
                    earlier.id
                );
            }
        }
    }
    assert!(crossings > 10_000, "{crossings} questions crossed a floor");
}

/// A floor record's past must include its own sequence, and a second, different floor record or
/// a retained record under the same id is a collision.
#[test]
fn a_floor_record_is_shaped_and_never_contradicts_what_the_index_holds() {
    let header = Header {
        id: id(1),
        actor: [1; 48],
        sequence: 3,
        previous: Some(id(0)),
        parents: vec![id(0)],
    };
    let past = BTreeMap::from([([1; 48], 3)]);
    let mut index = Index::new(8);
    assert_eq!(
        index.insert_floor(FloorRecord {
            header: header.clone(),
            past: BTreeMap::from([([1; 48], 2)]),
        }),
        Err(Refusal::Shape)
    );
    let record = FloorRecord {
        header: header.clone(),
        past: past.clone(),
    };
    assert_eq!(index.insert_floor(record.clone()), Ok(true));
    assert_eq!(index.insert_floor(record), Ok(false));
    let mut wider = past;
    wider.insert([2; 48], 9);
    assert_eq!(
        index.insert_floor(FloorRecord {
            header: header.clone(),
            past: wider,
        }),
        Err(Refusal::DigestCollision)
    );
    // The floor stands apart from what the index retains.
    assert_eq!(index.inventory().count(), 0);
}

/// A final checkpoint is final: a fork found after it withdraws its actor's records above the
/// floor and every record that depends on one, never the floor record, whose effects the
/// checkpoint's state already holds, nor a record that names only the floor record.
#[test]
fn a_fork_above_the_floor_withdraws_only_what_is_above_it() {
    let actor = |n: u8| [n; 48];
    let floor = Header {
        id: id(10),
        actor: actor(1),
        sequence: 5,
        previous: Some(id(9)),
        parents: vec![id(9)],
    };
    let above = |n: usize, by: u8, sequence: u64, previous: Option<Digest>, parents: &[Digest]| {
        let mut named: BTreeSet<Digest> = parents.iter().copied().collect();
        named.extend(previous);
        Header {
            id: id(n),
            actor: actor(by),
            sequence,
            previous,
            parents: named.into_iter().collect(),
        }
    };
    let seven = Header {
        id: id(16),
        actor: actor(2),
        sequence: 7,
        previous: Some(id(8)),
        parents: vec![id(8)],
    };
    let mut index = Index::new(16);
    index
        .insert_floor(FloorRecord {
            header: floor.clone(),
            past: BTreeMap::from([(actor(1), 5), (actor(2), 6)]),
        })
        .unwrap();
    index
        .insert_floor(FloorRecord {
            header: seven.clone(),
            past: BTreeMap::from([(actor(2), 7)]),
        })
        .unwrap();
    // Actor 1 forks at sequence 6; actor 2 builds on the floor record, and on one branch.
    let left = above(11, 1, 6, Some(floor.id), &[]);
    let right = above(12, 1, 6, Some(floor.id), &[id(13)]);
    let on_floor = above(14, 2, 8, Some(seven.id), &[floor.id]);
    let on_fork = above(15, 2, 9, Some(on_floor.id), &[left.id]);
    for header in [&left, &right, &on_floor, &on_fork] {
        index.insert(header.clone()).unwrap();
    }
    let view = index.project();
    assert!(view.quarantined.contains(&actor(1)));
    assert_eq!(view.ordered, vec![on_floor.id]);
    assert_eq!(
        view.pending,
        BTreeSet::from([left.id, right.id, on_fork.id])
    );
    // The floor record is not withdrawn: what names only it still observes it.
    assert!(view.observes(&index, &on_floor.id, &floor.id));
    assert!(view.reaches(&index, &on_floor.id, &actor(2), 7));
    assert!(!view.reaches(&index, &on_floor.id, &actor(2), 9));
}
