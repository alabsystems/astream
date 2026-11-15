// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;

/// A distinct digest per generated row; its first byte permutes the rows, so digest
/// order is not causal order.
fn id(row: usize) -> Digest {
    let mut id = [0; 32];
    id[0] = (row * 97 % 251) as u8;
    id[1] = row as u8;
    id
}

/// A digest no generated row takes (no row's first byte reaches 255).
fn missing(k: u8) -> Digest {
    let mut id = [255; 32];
    id[1] = k;
    id
}

fn header(
    id: Digest,
    actor: u8,
    sequence: u64,
    previous: Option<Digest>,
    extra: &[Digest],
) -> Header {
    let mut parents: BTreeSet<Digest> = extra.iter().copied().collect();
    parents.extend(previous);
    Header {
        id,
        actor: [actor; 48],
        sequence,
        previous,
        parents: parents.into_iter().collect(),
    }
}

/// A generated history row: its actor, how it follows that actor's tip, the earlier
/// rows (and the missing digests) it names besides its predecessor, whether the index
/// retains it, and whether the policy excludes it.
type Row = (u8, u8, Vec<(bool, u16)>, u8, u8);

/// Headers of a history over four actors: mostly each actor's dense chain, with a fork
/// (a second record at the tip's sequence, the branch the chain then follows), a gap (a
/// predecessor never written), cross-actor parents and parents nobody retains.
fn history(rows: &[Row]) -> Vec<Header> {
    let mut tips = [None::<(Digest, u64, Option<Digest>)>; 4];
    let mut out = Vec::new();
    for (row, (actor, step, extra, _, _)) in rows.iter().enumerate() {
        let actor = actor % 4;
        let tip = &mut tips[usize::from(actor)];
        let (sequence, previous) = match (*tip, step % 8) {
            (None, _) => (1, None),
            (Some((_, sequence, previous)), 0) => (sequence, previous),
            (Some((_, sequence, _)), 1) => (sequence + 2, Some(missing(row as u8))),
            (Some((tip, sequence, _)), _) => (sequence + 1, Some(tip)),
        };
        let extra: Vec<Digest> = extra
            .iter()
            .filter_map(|(gone, pick)| {
                if *gone {
                    Some(missing(*pick as u8 % 4))
                } else {
                    (row > 0).then(|| id(usize::from(*pick) % row))
                }
            })
            .collect();
        let h = header(id(row), actor, sequence, previous, &extra);
        *tip = Some((h.id, h.sequence, h.previous));
        out.push(h);
    }
    out
}

/// The first pair of `ids` on which the projection's `observes` and the index's DFS
/// disagree.
fn observation_breach(
    view: &Projection,
    index: &Index,
    ids: &[Digest],
) -> Option<(Digest, Digest)> {
    ids.iter()
        .flat_map(|later| ids.iter().map(move |earlier| (*later, *earlier)))
        .find(|(later, earlier)| {
            view.observes(index, later, earlier) != index.observes(later, earlier)
        })
}

proptest::proptest! {
    #[test]
    fn projection_observes_matches_dfs(
        rows in proptest::collection::vec(
            (
                0u8..4,
                0u8..16,
                proptest::collection::vec((proptest::bool::weighted(0.15), 0u16..64), 0..3),
                0u8..6,
                0u8..8,
            ),
            1..40,
        ),
        order in proptest::strategy::Strategy::prop_shuffle(
            proptest::strategy::Just((0..40).collect::<Vec<usize>>()),
        ),
    ) {
        let headers = history(&rows);
        let mut index = Index::new(headers.len());
        for at in order.iter().filter(|at| **at < headers.len()) {
            // A row the generator marks unretained leaves a missing intermediate.
            if rows[*at].3 != 0 {
                proptest::prop_assert_eq!(index.insert(headers[*at].clone()), Ok(true));
            }
        }
        let excluded: BTreeSet<Digest> = rows
            .iter()
            .enumerate()
            .filter(|(_, row)| row.4 == 0)
            .map(|(at, _)| id(at))
            .collect();
        let mut ids: Vec<Digest> = headers.iter().map(|h| h.id).collect();
        ids.push(missing(0));
        let empty = Index::new(0);
        for policy in [BTreeSet::new(), excluded] {
            let view = index.project_excluding(&policy);
            proptest::prop_assert_eq!(observation_breach(&view, &index, &ids), None);
            for later in &view.ordered {
                // A discharged `later` is answered by the vectors alone: an index that
                // retains nothing gives its walk nothing to read.
                for earlier in &ids {
                    proptest::prop_assert_eq!(
                        view.observes(&empty, later, earlier),
                        index.observes(later, earlier)
                    );
                }
            }
        }
        for later in &ids {
            let walked: BTreeSet<Digest> = index
                .inventory()
                .filter(|earlier| *earlier != later && index.observes(later, earlier))
                .copied()
                .collect();
            proptest::prop_assert_eq!(index.ancestors(later), walked);
        }
        let mut highest = BTreeMap::<Actor, u64>::new();
        for h in index.inventory().filter_map(|id| index.get(id)) {
            let at = highest.entry(h.actor).or_default();
            *at = (*at).max(h.sequence);
        }
        proptest::prop_assert_eq!(index.frontier(), &highest);
    }
}

/// Two writers whose chains cross, a third forked, a dependent of the fork, a record past
/// a gap, and the record that names it.
fn crossing() -> (Index, Vec<Digest>) {
    let d = |n: u8| [n; 32];
    let headers = [
        header(d(1), 1, 1, None, &[]),
        header(d(2), 2, 1, None, &[d(1)]),
        header(d(3), 1, 2, Some(d(1)), &[d(2)]),
        header(d(4), 2, 2, Some(d(2)), &[d(3)]),
        header(d(5), 1, 3, Some(d(3)), &[]),
        header(d(6), 3, 1, None, &[]),
        header(d(7), 3, 1, None, &[d(1)]),
        header(d(8), 2, 3, Some(d(4)), &[d(7)]),
        header(d(9), 4, 2, Some(d(30)), &[d(30)]),
        header(d(10), 5, 1, None, &[d(5), d(9)]),
    ];
    let mut index = Index::new(16);
    for h in headers {
        index.insert(h).unwrap();
    }
    let mut ids: Vec<Digest> = index.inventory().copied().collect();
    ids.push(d(30));
    (index, ids)
}

#[test]
fn projection_observes_answers_discharged_pairs_from_vectors() {
    let (index, ids) = crossing();
    let view = index.project();
    let d = |n: u8| [n; 32];
    assert_eq!(view.ordered, [1, 2, 3, 4, 5].map(d));
    assert_eq!(observation_breach(&view, &index, &ids), None);
    let empty = Index::new(0);
    assert!(
        view.observes(&empty, &d(4), &d(1)),
        "4 reaches 1 through 3 and 2; with no index to walk, the vectors answer"
    );
    assert!(view.observes(&empty, &d(5), &d(2)));
    assert!(!view.observes(&empty, &d(5), &d(4)));
    assert!(view.observes(&empty, &d(5), &d(5)));
    // A pending `later` walks: 10 waits on 9, whose predecessor is missing.
    assert!(view.observes(&index, &d(10), &d(2)));
    assert!(view.observes(&index, &d(10), &d(9)));
    assert!(
        !view.observes(&empty, &d(10), &d(2)),
        "10 is not discharged"
    );
    // A forked actor's dependent walks into the discharged history below it.
    assert!(view.observes(&index, &d(8), &d(7)));
    assert!(view.observes(&index, &d(8), &d(1)));
    assert!(!view.observes(&index, &d(4), &d(7)));
    assert_eq!(index.ancestors(&d(10)), [1, 2, 3, 5, 9].map(d).into());
    assert_eq!(index.ancestors(&d(30)), BTreeSet::new());
    assert_eq!(
        index.frontier(),
        &BTreeMap::from([
            ([1; 48], 3),
            ([2; 48], 3),
            ([3; 48], 1),
            ([4; 48], 2),
            ([5; 48], 1)
        ])
    );
}

#[test]
fn the_vector_law_catches_a_vector_that_forgets_a_transitive_ancestor() {
    let (index, ids) = crossing();
    let mut view = index.project();
    // Planted: 4's vector forgets actor 1 (ordinal 0, its row's first entry), which 4
    // reaches only through its parents 3 and 2.
    let dot = view.vectors.dots[view.vectors.rows[&[4; 32]]];
    assert_eq!(view.vectors.ordinals[dot.start], 0);
    view.vectors.sequences[dot.start] = 0;
    assert_eq!(
        observation_breach(&view, &index, &ids),
        Some(([4; 32], [1; 32])),
        "NEGATIVE CONTROL: the law misses a vector that lost an ancestor"
    );
}

#[test]
fn ancestors_end_on_a_cycle_and_skip_unretained_parents() {
    let d = |n: u8| [n; 32];
    let mut index = Index::new(4);
    index
        .insert(header(d(1), 1, 1, None, &[d(2), d(9)]))
        .unwrap();
    index.insert(header(d(2), 2, 1, None, &[d(1)])).unwrap();
    assert_eq!(index.ancestors(&d(1)), BTreeSet::from([d(2)]));
    assert!(index.observes(&d(1), &d(1)));
    let view = index.project();
    assert!(view.ordered.is_empty());
    assert_eq!(observation_breach(&view, &index, &[d(1), d(2), d(9)]), None);
}

#[test]
fn the_frontier_ignores_refusals_and_duplicates() {
    let d = |n: u8| [n; 32];
    let mut index = Index::new(2);
    index.insert(header(d(2), 1, 2, Some(d(1)), &[])).unwrap();
    assert_eq!(index.insert(header(d(2), 1, 2, Some(d(1)), &[])), Ok(false));
    assert_eq!(
        index.insert(header(d(3), 1, 0, None, &[])),
        Err(Refusal::Shape)
    );
    assert_eq!(
        index.insert(header(d(2), 7, 9, Some(d(1)), &[])),
        Err(Refusal::DigestCollision)
    );
    index.insert(header(d(1), 1, 1, None, &[])).unwrap();
    assert_eq!(
        index.insert(header(d(4), 1, 3, Some(d(2)), &[])),
        Err(Refusal::Capacity)
    );
    assert_eq!(index.frontier(), &BTreeMap::from([([1; 48], 2)]));
}

#[test]
fn vectors_past_their_budget_leave_the_rest_to_the_walk() {
    // 200 writers in one chain, each naming the one before: the row of the n-th holds n
    // entries, so the rows pass 64 entries per record near the 160th, and every record
    // after that walks.
    let mut index = Index::new(200);
    for row in 0..200usize {
        let parents: Vec<Digest> = row.checked_sub(1).map(id).into_iter().collect();
        index
            .insert(header(id(row), row as u8, 1, None, &parents))
            .unwrap();
    }
    let view = index.project();
    assert_eq!(view.ordered.len(), 200);
    let held = view.vectors.rows.len();
    assert!((150..200).contains(&held), "{held} rows");
    assert!(view.vectors.ordinals.len() <= 200 * VECTOR_ENTRIES_PER_RECORD);
    assert!(!view.vectors.rows.contains_key(&id(199)));
    let ids: Vec<Digest> = (0..200).map(id).collect();
    assert_eq!(observation_breach(&view, &index, &ids), None);
    assert!(view.observes(&index, &id(199), &id(0)));
    assert!(
        !view.observes(&Index::new(0), &id(199), &id(0)),
        "199 has no row"
    );
    assert!(view.observes(&Index::new(0), &id(100), &id(0)));
}
