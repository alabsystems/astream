// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use std::collections::BTreeSet;

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

/// Actor `n`; its first byte permutes the actors, so key order is not ordinal order.
fn actor(n: usize) -> Actor {
    let mut actor = [0; 48];
    actor[0] = (n * 89 % 251) as u8;
    actor[1..9].copy_from_slice(&(n as u64).to_be_bytes());
    actor
}

/// Node positions on the paths of `ordinals` in a map `height` levels tall: what a merge
/// that differs from its inputs in exactly those entries has to write.
fn touched(ordinals: &BTreeSet<usize>, height: u8) -> usize {
    (1..=u32::from(height))
        .map(|level| {
            let prefixes: BTreeSet<usize> = ordinals.iter().map(|at| at >> (4 * level)).collect();
            prefixes.len()
        })
        .sum()
}

/// Nodes offered for a name and slots written on this thread so far.
fn work_done() -> (usize, usize) {
    WORK.with(std::cell::Cell::get)
}

/// What an answer can read of a store: every node under its name and each actor's ordinal.
type Held = (Vec<[u64; FAN]>, Vec<[u32; FAN]>, BTreeMap<Actor, u32>);

/// The nodes and ordinals of `reach`, each node found again by its own search.
fn held(reach: &Reach) -> Held {
    for (at, node) in reach.leaves.held.iter().enumerate() {
        assert_eq!(
            reach.leaves.seek(node).map(|(_, name)| name as usize),
            Some(at + 1)
        );
    }
    for (at, node) in reach.branches.held.iter().enumerate() {
        assert_eq!(
            reach.branches.seek(node).map(|(_, name)| name as usize),
            Some(at + 1)
        );
    }
    (
        reach.leaves.held.clone(),
        reach.branches.held.clone(),
        reach.actors.clone(),
    )
}

/// Among 10,000 actors a past is four levels tall (three hold 4,096), and every question,
/// "the highest sequence of this actor in that record's past", reads four nodes and answers as
/// the whole vector does. A record that joins 64 heads adds nodes only on the paths of the
/// entries in which the heads differ, and of its own, and offers no other node for a name: 11
/// nodes here, where one whole vector is 669. The 64 heads are themselves 64 records that each joined the same 64 earlier heads, so
/// they agree by content and not by descent: the first wrote the joined nodes and each of the
/// other 63 found them by hash and added its own path alone. Each actor starts at a sequence
/// of its own, as above a floor, so no two leaves here hold the same sixteen sequences and
/// every count below is exact.
/// NEGATIVE CONTROL: with `Nodes::name` pushing every node without seeking it, so that a name
/// is a position and not a content, the second of those records fails with `head 1 adds its
/// own path alone: left 11, right 4`. With `span` answering 8 for every ordinal, so that every
/// past is as tall as an ordinal is wide and every question reads 8 nodes, it fails at the
/// tip's height with `left: 8, right: 4`. With `merge` descending where one past stands alone
/// (its `[one], None` arm gone), every node is found again and none is added, and it fails with
/// `head 0 offers the nodes on the paths that differ, and no other: left 669, right 11`.
#[test]
fn reach_among_10000_actors_answers_in_4_node_reads_and_a_join_of_64_heads_adds_nodes_only_where_they_differ(
) {
    const ACTORS: usize = 10_000;
    const HEADS: usize = 64;
    let mut reach = Reach::with_budget(8 << 20);
    // Actor `n`'s first record here, and so its second.
    let first = |n: usize| n as u64 + 1;
    let second = |n: usize| n as u64 + 2;

    // Each actor's first record, in one chain: the tip reaches every actor's first.
    let mut tip = Past::EMPTY;
    for n in 0..ACTORS {
        tip = reach
            .record(&actor(n), first(n), &[tip])
            .expect("within budget");
        assert_eq!(
            reach.actors[&actor(n)] as usize,
            n,
            "ordinals are first-seen order"
        );
    }
    let base: Vec<u64> = (0..ACTORS).map(first).collect();
    assert_eq!(tip.height, 4);
    assert!(16_usize.pow(u32::from(tip.height) - 1) < ACTORS);
    assert!(reach.nodes() <= ACTORS * 4, "at most one path a record");

    // 64 concurrent records on the tip, each by its own actor.
    let early: Vec<usize> = (2_000..2_000 + HEADS).collect();
    let early_pasts: Vec<Past> = early
        .iter()
        .map(|n| {
            reach
                .record(&actor(*n), second(*n), &[tip])
                .expect("within budget")
        })
        .collect();

    // 64 more, each by its own actor and each naming all 64 of those as parents.
    let authors: Vec<usize> = (5_000..5_000 + HEADS).collect();
    let mut heads = Vec::new();
    let mut vectors = Vec::new();
    for (k, n) in authors.iter().enumerate() {
        let (before, worked) = (reach.nodes(), work_done().0);
        heads.push(
            reach
                .record(&actor(*n), second(*n), &early_pasts)
                .expect("within budget"),
        );
        let added = reach.nodes() - before;
        let written: BTreeSet<usize> = early.iter().chain([n]).copied().collect();
        assert_eq!(
            work_done().0 - worked,
            touched(&written, tip.height),
            "head {k} offers the nodes on the paths that differ, and no other"
        );
        if k == 0 {
            assert_eq!(added, touched(&written, tip.height));
        } else {
            assert_eq!(added, 4, "head {k} adds its own path alone");
        }
        let mut vector = base.clone();
        for at in early.iter().chain([n]) {
            vector[*at] = second(*at);
        }
        vectors.push(vector);
    }

    // The record that joins the 64 heads.
    let joiner = ACTORS - 1;
    let (before, worked) = (reach.nodes(), work_done().0);
    let joined = reach
        .record(&actor(joiner), second(joiner), &heads)
        .expect("within budget");
    let added = reach.nodes() - before;
    let offered = work_done().0 - worked;
    let mut differ: BTreeSet<usize> = (0..ACTORS)
        .filter(|at| vectors.iter().any(|vector| vector[*at] != vectors[0][*at]))
        .collect();
    assert_eq!(differ.len(), HEADS);
    differ.insert(joiner);
    assert_eq!(added, touched(&differ, joined.height));
    assert_eq!(added, 11);
    assert_eq!(
        offered, 11,
        "the joining record offers no node off those paths"
    );
    assert_eq!(touched(&(0..ACTORS).collect(), joined.height), 669);

    // Every question of the joining record reads four nodes and answers as the vector does.
    let mut whole = base.clone();
    for at in early.iter().chain(&authors).chain([&joiner]) {
        whole[*at] = second(*at);
    }
    for (n, sequence) in whole.iter().enumerate() {
        let seen = reach.seen(joined, &actor(n));
        assert_eq!(seen.sequence, *sequence, "actor {n}");
        assert_eq!(seen.nodes, 4, "actor {n} is read in 4 nodes");
        assert!(reach.reaches(joined, &actor(n), *sequence));
        assert!(!reach.reaches(joined, &actor(n), *sequence + 1));
    }
    // One record in the past of another, both ways.
    for (k, head) in heads.iter().enumerate() {
        assert!(reach.reaches(joined, &actor(authors[k]), second(authors[k])));
        assert!(!reach.reaches(*head, &actor(joiner), second(joiner)));
        assert_eq!(reach.seen(*head, &actor(joiner)).nodes, 4);
        assert!(reach.reaches(*head, &actor(early[k]), second(early[k])));
        let other = authors[(k + 1) % HEADS];
        assert!(reach.reaches(*head, &actor(other), first(other)));
        assert!(!reach.reaches(*head, &actor(other), second(other)));
        for (n, sequence) in vectors[k].iter().enumerate().step_by(7) {
            assert_eq!(reach.seen(*head, &actor(n)).sequence, *sequence);
        }
    }
    // The heads' join is the joining record's past without the joiner's own entry. The record
    // wrote every node in which the heads differ, so the join adds its root and nothing else.
    let before = reach.nodes();
    let frontier = reach.join(&heads).expect("within budget");
    assert_eq!(reach.nodes(), before + 1, "the join adds its root alone");
    assert!(reach.reaches(frontier, &actor(authors[0]), second(authors[0])));
    assert!(reach.reaches(frontier, &actor(joiner), first(joiner)));
    assert!(!reach.reaches(frontier, &actor(joiner), second(joiner)));
    // An actor the store never saw is in no past, and costs no read.
    assert_eq!(reach.seen(joined, &actor(ACTORS)), Seen::default());
    assert_eq!(reach.actors(), ACTORS);
    assert!(reach.bytes() <= reach.budget());
}

/// One record of a random history: its author, sequence and parents (earlier records).
struct Step {
    author: usize,
    sequence: u64,
    parents: Vec<usize>,
}

/// A random history whose actors arrive as it goes, up to `actors`: each record names its
/// author's previous record and up to three other earlier records, stale ones included.
fn history(rng: &mut Rng, records: usize, actors: usize) -> Vec<Step> {
    let mut steps: Vec<Step> = Vec::new();
    let mut last: Vec<Option<usize>> = Vec::new();
    for at in 0..records {
        let arrive = last.len() < actors && (last.is_empty() || rng.below(4) == 0);
        let author = if arrive {
            last.push(None);
            last.len() - 1
        } else {
            rng.below(last.len() as u64) as usize
        };
        let mut parents: BTreeSet<usize> = last[author].into_iter().collect();
        if at > 0 {
            for _ in 0..rng.below(4) {
                parents.insert(rng.below(at as u64) as usize);
            }
        }
        let sequence = last[author].map_or(1, |previous| steps[previous].sequence + 1);
        last[author] = Some(at);
        steps.push(Step {
            author,
            sequence,
            parents: parents.into_iter().collect(),
        });
    }
    steps
}

/// The whole vector of each record of `steps`, by the definition: its parents' entrywise
/// maximum with its own sequence at its author.
fn vectors(steps: &[Step]) -> Vec<BTreeMap<usize, u64>> {
    let mut vectors: Vec<BTreeMap<usize, u64>> = Vec::new();
    for step in steps {
        let mut vector = BTreeMap::new();
        for parent in &step.parents {
            for (author, sequence) in &vectors[*parent] {
                let seen = vector.entry(*author).or_insert(0);
                *seen = (*seen).max(*sequence);
            }
        }
        vector.insert(step.author, step.sequence);
        vectors.push(vector);
    }
    vectors
}

fn maximum(vectors: &[&BTreeMap<usize, u64>]) -> BTreeMap<usize, u64> {
    let mut joined = BTreeMap::new();
    for (author, sequence) in vectors.iter().flat_map(|vector| vector.iter()) {
        let seen = joined.entry(*author).or_insert(0);
        *seen = (*seen).max(*sequence);
    }
    joined
}

/// On random histories whose actors arrive as they go (so pasts of one and two levels meet in
/// one record), every past answers for every actor as the record's whole vector does;
/// a join answers as the entrywise maximum; and two pasts are equal exactly when their
/// vectors are, whatever order and grouping made them.
/// NEGATIVE CONTROL: with `kids` giving a shorter subtree no place (so a merge drops every past
/// shorter than its tallest), it fails with `seed 1: record 62 sees actor 0: left 0, right 10`.
#[test]
fn pasts_answer_as_whole_vectors_do_while_actors_arrive() {
    for seed in 1..=12_u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let steps = history(&mut rng, 700, 300);
        let vectors = vectors(&steps);
        let mut reach = Reach::with_budget(usize::MAX);
        let mut pasts: Vec<Past> = Vec::new();
        let mut named: BTreeMap<BTreeMap<usize, u64>, Past> = BTreeMap::new();
        let mut holds: BTreeMap<Past, BTreeMap<usize, u64>> = BTreeMap::new();
        let mut check = |past: Past, vector: &BTreeMap<usize, u64>, what: &str| {
            assert_eq!(
                *named.entry(vector.clone()).or_insert(past),
                past,
                "seed {seed}: {what}: one vector under two names"
            );
            assert_eq!(
                holds.entry(past).or_insert_with(|| vector.clone()),
                vector,
                "seed {seed}: {what}: one name for two vectors"
            );
        };
        for (at, step) in steps.iter().enumerate() {
            let parents: Vec<Past> = step.parents.iter().map(|parent| pasts[*parent]).collect();
            let past = reach
                .record(&actor(step.author), step.sequence, &parents)
                .expect("no budget to pass");
            for author in 0..reach.actors() {
                let expected = vectors[at].get(&author).copied().unwrap_or(0);
                let seen = reach.seen(past, &actor(author));
                assert_eq!(
                    seen.sequence, expected,
                    "seed {seed}: record {at} sees actor {author}"
                );
                assert!(seen.nodes <= u32::from(span(reach.actors() as u32 - 1)));
                assert_eq!(reach.reaches(past, &actor(author), expected), expected > 0);
                assert!(!reach.reaches(past, &actor(author), expected + 1));
            }
            check(past, &vectors[at], "record");
            pasts.push(past);

            // A join of three earlier records, flat and in both groupings.
            let picks: Vec<usize> = (0..3).map(|_| rng.below(at as u64 + 1) as usize).collect();
            let (a, b, c) = (pasts[picks[0]], pasts[picks[1]], pasts[picks[2]]);
            let expected = maximum(&[&vectors[picks[0]], &vectors[picks[1]], &vectors[picks[2]]]);
            let flat = reach.join(&[a, b, c]).expect("no budget to pass");
            let left = reach.join(&[a, b]).and_then(|ab| reach.join(&[ab, c]));
            let right = reach.join(&[c, b]).and_then(|cb| reach.join(&[a, cb]));
            assert_eq!(left, Ok(flat), "seed {seed}: at {at}");
            assert_eq!(right, Ok(flat), "seed {seed}: at {at}");
            for author in 0..reach.actors() {
                let sequence = expected.get(&author).copied().unwrap_or(0);
                assert_eq!(
                    reach.seen(flat, &actor(author)).sequence,
                    sequence,
                    "seed {seed}"
                );
            }
            check(flat, &expected, "join");
            // A record joined with its own parents is the record.
            let mut with_parents = parents.clone();
            with_parents.push(past);
            assert_eq!(reach.join(&with_parents), Ok(past), "seed {seed}: at {at}");
        }
        assert_eq!(reach.join(&[]), Ok(Past::EMPTY));
        assert!(
            Past::EMPTY.is_empty() && !pasts[0].is_empty(),
            "seed {seed}"
        );
    }
}

/// Under every budget from nothing to enough, a refused record leaves every node, name and
/// ordinal as it was and every node found by its own search, the store never holds more than
/// its budget, and every record it does take answers as its whole vector does. Records after a refused one
/// that do not name it are still tried, so refusals fall at every size of the slot tables.
/// NEGATIVE CONTROL: with `settle` leaving a refused merge's nodes held, it fails with
/// `budget 9652: record 62 is refused and changes nothing`.
#[test]
fn a_refused_record_changes_nothing_under_any_budget() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let steps = history(&mut rng, 160, 40);
    let vectors = vectors(&steps);
    let mut full = Reach::with_budget(usize::MAX);
    let mut pasts: Vec<Past> = Vec::new();
    for step in &steps {
        let parents: Vec<Past> = step.parents.iter().map(|parent| pasts[*parent]).collect();
        pasts.push(
            full.record(&actor(step.author), step.sequence, &parents)
                .expect("no budget to pass"),
        );
    }
    let enough = full.bytes();
    let mut refusals = 0;
    for budget in (0..enough).step_by(127).chain([enough]) {
        let mut reach = Reach::with_budget(budget);
        let mut pasts: Vec<Option<Past>> = Vec::new();
        for (at, step) in steps.iter().enumerate() {
            let parents: Option<Vec<Past>> =
                step.parents.iter().map(|parent| pasts[*parent]).collect();
            let Some(parents) = parents else {
                pasts.push(None);
                continue;
            };
            let before = held(&reach);
            let made = reach.record(&actor(step.author), step.sequence, &parents);
            assert!(reach.bytes() <= budget, "budget {budget}: record {at}");
            match made {
                Ok(past) => {
                    for (author, sequence) in &vectors[at] {
                        assert!(reach.reaches(past, &actor(*author), *sequence));
                        assert!(!reach.reaches(past, &actor(*author), *sequence + 1));
                    }
                }
                Err(refusal) => {
                    assert_eq!(refusal, Refusal::Budget);
                    assert!(
                        held(&reach) == before,
                        "budget {budget}: record {at} is refused and changes nothing"
                    );
                    refusals += 1;
                }
            }
            pasts.push(made.ok());
        }
        assert_eq!(
            budget == enough,
            pasts.iter().all(Option::is_some),
            "budget {budget}"
        );
        if budget == enough {
            assert!(
                held(&reach) == held(&full) && reach.bytes() == enough,
                "the same records make the same store"
            );
        }
    }
    assert!(refusals > 1_000, "refusals: {refusals}");
}

#[test]
fn a_record_its_parents_already_reach_is_refused_as_misshapen() {
    let mut reach = Reach::with_budget(usize::MAX);
    let first = reach.record(&actor(1), 1, &[]).expect("no budget to pass");
    let second = reach
        .record(&actor(1), 2, &[first])
        .expect("no budget to pass");
    let other = reach
        .record(&actor(2), 1, &[second])
        .expect("no budget to pass");
    let before = held(&reach);
    let stated = format!("{reach:?}");
    assert_eq!(reach.record(&actor(1), 0, &[]), Err(Refusal::Shape));
    assert_eq!(reach.record(&actor(3), 0, &[other]), Err(Refusal::Shape));
    assert_eq!(reach.record(&actor(1), 2, &[other]), Err(Refusal::Shape));
    assert_eq!(reach.record(&actor(1), 1, &[first]), Err(Refusal::Shape));
    assert!(held(&reach) == before);
    // The same sequence with parents that do not reach it is a record of its own.
    assert_eq!(reach.record(&actor(1), 2, &[first]), Ok(second));
    assert_eq!(format!("{reach:?}"), stated);
}

/// Pasts two and three levels apart meet whole: a one-level past joined with a three-level
/// one and with a four-level one, and a record four levels up whose one parent is one level
/// tall, each hold every entry of both sides and nothing else.
/// NEGATIVE CONTROL: with `kids` placing a shorter subtree only when it is one level shorter,
/// it fails with `one level with three: actor 3: left 0, right 7`. With `lift` wrapping once
/// and not until the height is reached, it fails with `one level with four: actor 3: left 0,
/// right 7`.
#[test]
fn pasts_levels_apart_meet_whole() {
    const ACTORS: usize = 4_097;
    let mut reach = Reach::with_budget(usize::MAX);
    let alone: Vec<Past> = (0..ACTORS)
        .map(|n| reach.record(&actor(n), 7, &[]).expect("no budget to pass"))
        .collect();
    let heights = [alone[3].height, alone[300].height, alone[4_096].height];
    assert_eq!(heights, [1, 3, 4]);
    let near = reach.join(&[alone[3], alone[300]]);
    let far = reach.join(&[alone[4_096], alone[3]]);
    let above = reach.record(&actor(4_096), 8, &[alone[3]]);
    for (what, past, holds) in [
        ("one level with three", near, [(3, 7), (300, 7)]),
        ("one level with four", far, [(3, 7), (4_096, 7)]),
        ("a record four levels up", above, [(3, 7), (4_096, 8)]),
    ] {
        let past = past.expect("no budget to pass");
        for n in 0..ACTORS {
            let expected = holds
                .iter()
                .find(|(at, _)| *at == n)
                .map_or(0, |(_, seen)| *seen);
            assert_eq!(
                reach.seen(past, &actor(n)).sequence,
                expected,
                "{what}: actor {n}"
            );
        }
    }
}

/// A store whose next node would double a slot table past its budget refuses the record
/// before it takes any room: a hundred offers write no slot and offer one node each, where a
/// table rebuilt and rolled back would write every slot twice an offer. One more byte than
/// the doubling needs, and the record is held.
/// NEGATIVE CONTROL: with `name` charging nothing for the slots it is about to take, it
/// fails with `offer 0: left Ok(Past { root: 4097, height: 1 }), right Err(Budget)`.
#[test]
fn a_store_full_at_a_slot_doubling_refuses_without_writing_a_slot() {
    const HELD: u64 = 4_096;
    let fill = |budget: usize| {
        let mut reach = Reach::with_budget(budget);
        let mut tip = Past::EMPTY;
        for sequence in 1..=HELD {
            tip = reach
                .record(&actor(0), sequence, &[tip])
                .expect("within budget");
        }
        (reach, tip)
    };
    let (full, _) = fill(usize::MAX);
    assert_eq!(full.leaves.held.len() as u64, HELD);
    assert_eq!(full.leaves.slots.len() as u64, 2 * HELD);
    let doubling = full.leaves.slots.len() * size_of::<u32>();

    let (mut reach, tip) = fill(full.bytes() + doubling - 1);
    let (before, bytes, worked) = (held(&reach), reach.bytes(), work_done());
    for offer in 0..100 {
        let made = reach.record(&actor(0), HELD + 1, &[tip]);
        assert_eq!(made, Err(Refusal::Budget), "offer {offer}");
    }
    let (named, placed) = work_done();
    assert_eq!((named - worked.0, placed - worked.1), (100, 0));
    assert_eq!(reach.bytes(), bytes);
    assert!(held(&reach) == before);

    let (mut reach, tip) = fill(full.bytes() + doubling);
    let made = reach.record(&actor(0), HELD + 1, &[tip]);
    assert!(made.is_ok() && reach.bytes() == reach.budget());
}

/// The hash that finds a node is SipHash: under the reference key it gives the reference
/// outputs of SipHash-2-4 for the reference messages of no, eight and sixteen bytes.
#[test]
fn the_hash_that_finds_a_node_gives_the_siphash_reference_outputs() {
    let key = [0x0706_0504_0302_0100, 0x0f0e_0d0c_0b0a_0908];
    let outputs = [
        0x726f_db47_dd0e_0e31_u64,
        0x93f5_f579_9a93_2462,
        0x3f2a_cc7f_57c2_9bdb,
    ];
    for (words, output) in outputs.iter().enumerate() {
        let message = key.iter().copied().take(words);
        assert_eq!(sip_hash(key, message, 2, 4), *output, "{words} words");
    }
}
