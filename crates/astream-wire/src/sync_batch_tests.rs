// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;

fn header(id: u8) -> Header {
    Header {
        id: [id; 32],
        actor: [id; 48],
        sequence: 1,
        previous: None,
        parents: Vec::new(),
    }
}

/// Compare with the existing mutating admission semantics over every short sequence,
/// including duplicate proposed headers, collisions, malformed headers, and full indexes.
#[test]
fn batch_preflight_matches_sequential_insertion_without_retaining_proposals() {
    let mut collision = header(2);
    collision.actor = [9; 48];
    let mut malformed = header(4);
    malformed.sequence = 0;
    let choices = [header(1), header(2), collision, header(3), malformed];
    for capacity in 0..=4 {
        for retained in 0..=capacity.min(2) {
            let mut index = Index::new(capacity);
            for id in 1..=retained {
                index.insert(header(id as u8)).unwrap();
            }
            let before: Vec<_> = index.inventory().copied().collect();
            for length in 0..=4 {
                for mut word in 0..choices.len().pow(length) {
                    let proposed: Vec<_> = (0..length)
                        .map(|_| {
                            let next = &choices[word % choices.len()];
                            word /= choices.len();
                            next
                        })
                        .collect();
                    let mut sequential = index.clone();
                    let expected = proposed.iter().try_fold(0, |added, header| {
                        sequential
                            .insert((*header).clone())
                            .map(|new| added + usize::from(new))
                    });
                    assert_eq!(index.check_insert_many(proposed.iter().copied()), expected);
                    assert_eq!(index.inventory().copied().collect::<Vec<_>>(), before);
                }
            }
        }
    }
}

#[test]
fn batch_preflight_counts_only_distinct_additions_and_rechecks_capacity() {
    let mut index = Index::new(2);
    let first = header(1);
    let second = header(2);
    let third = header(3);
    index.insert(first.clone()).unwrap();
    for _ in 0..2 {
        assert_eq!(index.check_insert_many([&first, &second, &second]), Ok(1));
        assert_eq!(
            index.check_insert_many([&second, &third]),
            Err(Refusal::Capacity)
        );
    }
    assert_eq!(index.inventory().count(), 1);
    index.insert(third).unwrap();
    assert_eq!(
        index.check_insert_many([&first, &second]),
        Err(Refusal::Capacity)
    );
    assert_eq!(index.check_insert_many([&first, &first]), Ok(0));
}

/// Unlike all-or-error preflight, a partial batch continues after each refusal.
/// Every answer and running charge must match actual sequential insertions,
/// including a collision with an earlier proposal and a duplicate at capacity.
#[test]
fn incremental_proposals_match_sequential_insertion_after_every_refusal() {
    let mut collision = header(2);
    collision.actor = [9; 48];
    let mut malformed = header(1);
    malformed.sequence = 0;
    let choices = [header(1), header(2), collision, header(3), malformed];
    let mut seen = Vec::new();
    for capacity in 0..=4 {
        for retained in 0..=capacity.min(2) {
            let mut index = Index::new(capacity);
            for id in 1..=retained {
                index.insert(header(id as u8)).unwrap();
            }
            let before: Vec<_> = index.inventory().copied().collect();
            for length in 0..=4 {
                for mut word in 0..choices.len().pow(length) {
                    let mut sequential = index.clone();
                    let mut proposal = index.proposal();
                    let mut added = 0;
                    for _ in 0..length {
                        let next = &choices[word % choices.len()];
                        word /= choices.len();
                        let expected = sequential.insert(next.clone());
                        added += usize::from(expected == Ok(true));
                        assert_eq!(proposal.check_insert(next), expected);
                        assert_eq!(proposal.new_records(), added);
                        if !seen.contains(&expected) {
                            seen.push(expected);
                        }
                    }
                    assert_eq!(index.inventory().copied().collect::<Vec<_>>(), before);
                }
            }
        }
    }
    for outcome in [
        Ok(true),
        Ok(false),
        Err(Refusal::Shape),
        Err(Refusal::DigestCollision),
        Err(Refusal::Capacity),
    ] {
        assert!(seen.contains(&outcome), "unexercised outcome: {outcome:?}");
    }
}
