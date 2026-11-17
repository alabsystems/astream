// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::super::tests::{chain, digest, index};
use super::*;

#[derive(Default, Debug)]
struct Traffic {
    bytes: usize,
    requests: usize,
    refinements: usize,
}

fn limits() -> Limits {
    Limits {
        remote_records: 100_000,
        messages: 100_000,
    }
}

fn run(ours: Snapshot, theirs: Snapshot) -> (Difference, Difference, Traffic) {
    let our_ids: BTreeSet<_> = ours.ids().copied().collect();
    let their_ids: BTreeSet<_> = theirs.ids().copied().collect();
    let expected_send: Vec<_> = our_ids.difference(&their_ids).copied().collect();
    let expected_want: Vec<_> = their_ids.difference(&our_ids).copied().collect();
    let mut responder = Responder::new(Arc::new(theirs), limits()).unwrap();
    let mut traffic = Traffic::default();
    assert!(responder.difference().is_none());
    let result = reconcile(Arc::new(ours), limits(), |request| {
        let wire = request.encode()?;
        // Include an outer u32 frame length in BOTH directions, not just codec payloads.
        traffic.bytes += 4 + wire.len();
        traffic.requests += 1;
        let request = Message::decode(&wire)?;
        if request == Message::Refine {
            traffic.refinements += 1;
        }
        let finishing = matches!(request, Message::Finish { .. });
        let reply = responder.answer(request)?;
        if !finishing {
            assert!(responder.difference().is_none());
        }
        let wire = reply.encode()?;
        traffic.bytes += 4 + wire.len();
        Message::decode(&wire)
    })
    .unwrap();
    assert_eq!(result.send, expected_send);
    assert_eq!(result.want, expected_want);
    let peer = responder.difference().unwrap().clone();
    assert_eq!(peer.send, expected_want);
    assert_eq!(peer.want, expected_send);
    // Once completed, a later refused request cannot revoke the completed result.
    assert_eq!(responder.answer(Message::Accepted), Err(Error::Phase));
    assert_eq!(responder.difference(), Some(&peer));
    (result, peer, traffic)
}

#[test]
fn rbsr_finds_exact_difference() {
    // Distributed identities without ANY actor-prefix shortcut exercise the range path.
    let common: BTreeSet<_> = (1..=8176).map(digest).collect();
    let mut ours = common.clone();
    let mut theirs = common;
    ours.extend((8177..=8192).map(digest));
    theirs.extend((8193..=8208).map(digest));
    let (difference, _, traffic) = run(Snapshot::new(ours), Snapshot::new(theirs));
    assert_eq!((difference.send.len(), difference.want.len()), (16, 16));
    println!("8192 identities, d=16 each, no actor shortcut: {traffic:?}");
    assert!(traffic.bytes < 8192, "{traffic:?}");
}

#[test]
fn dense_actor_frontiers_narrow_the_wire_without_hiding_gaps_or_forks() {
    let mut ours = Vec::new();
    let mut theirs = Vec::new();
    for actor in 1..=4 {
        let headers = chain(actor, 2052);
        let (ours_count, theirs_count) = if actor <= 2 {
            (2052, 2044)
        } else {
            (2044, 2052)
        };
        ours.extend(headers[..ours_count].iter().cloned());
        theirs.extend(headers[..theirs_count].iter().cloned());
    }
    assert_eq!((ours.len(), theirs.len()), (8192, 8192));
    let (_, _, traffic) = run(
        Snapshot::from_index(&index(ours)),
        Snapshot::from_index(&index(theirs)),
    );
    println!("8192 identities, d=16 each, four actor frontiers: {traffic:?}");
    assert!(traffic.bytes < 8192, "{traffic:?}");

    let headers = chain(7, 32);
    let mut alternate = headers[15].clone();
    alternate.id = digest(123_456_789);
    let gapped = headers
        .iter()
        .filter(|header| header.sequence != 8)
        .cloned();
    let forked = headers.iter().cloned().chain([alternate]);
    run(
        Snapshot::from_index(&index(gapped)),
        Snapshot::from_index(&index(forked)),
    );
}

#[test]
fn full_conservation_really_refines_a_compact_probe_collision() {
    let ours: BTreeSet<_> = (0..64u8)
        .map(|number| {
            let mut id = [0; 32];
            id[31] = number;
            id
        })
        .collect();
    let mut theirs = ours.clone();
    let removed = *theirs.last().unwrap();
    theirs.remove(&removed);
    let mut changed = removed;
    changed[20] = 1; // Same low 32-bit sum and child count, different FULL root sum.
    theirs.insert(changed);
    let (difference, _, traffic) = run(Snapshot::new(ours), Snapshot::new(theirs));
    assert_eq!(
        (difference.send, difference.want),
        (vec![removed], vec![changed])
    );
    assert_eq!(
        traffic.refinements, 1,
        "a short match must not close the exchange"
    );
}

#[test]
fn whole_differences_page_beyond_sixty_four_in_both_directions() {
    run(
        Snapshot::new(BTreeSet::new()),
        Snapshot::new(BTreeSet::new()),
    );
    run(
        Snapshot::new((1..=512).map(digest).collect()),
        Snapshot::new(BTreeSet::new()),
    );
    run(
        Snapshot::new(BTreeSet::new()),
        Snapshot::new((1..=512).map(digest).collect()),
    );
    let (_, _, traffic) = run(
        Snapshot::new((1..=512).map(digest).collect()),
        Snapshot::new((513..=1024).map(digest).collect()),
    );
    assert!(traffic.requests > 16);
}

fn through_setup(responder: &mut Responder, ours: Fingerprint) {
    let Message::Root(theirs) = responder.answer(Message::Root(ours)).unwrap() else {
        panic!("root response");
    };
    if ours == theirs {
        return;
    }
    assert!(matches!(
        responder.answer(Message::Frontiers {
            items: Vec::new(),
            done: true
        }),
        Ok(Message::Frontiers { done: true, .. })
    ));
    assert!(matches!(
        responder.answer(Message::Prefixes {
            items: Vec::new(),
            done: true
        }),
        Ok(Message::Prefixes { done: true, .. })
    ));
}

#[test]
fn malformed_phases_pages_and_completion_never_expose_tentative_results() {
    let snapshot = Arc::new(Snapshot::new((1..=8).map(digest).collect()));
    let root = root(&snapshot).unwrap();
    let mut peer = Responder::new(Arc::clone(&snapshot), limits()).unwrap();
    assert_eq!(peer.answer(Message::Accepted), Err(Error::Phase));
    assert_eq!(peer.answer(Message::Root(root)), Err(Error::Phase));
    assert!(peer.difference().is_none());

    let mut peer = Responder::new(Arc::clone(&snapshot), limits()).unwrap();
    through_setup(&mut peer, root);
    assert_eq!(peer.answer(Message::Refine), Ok(Message::Accepted));
    assert_eq!(peer.answer(Message::Refine), Err(Error::Phase));
    assert!(peer.difference().is_none());

    let mut peer = Responder::new(Arc::clone(&snapshot), limits()).unwrap();
    through_setup(&mut peer, root);
    peer.answer(Message::Refine).unwrap();
    assert_eq!(
        peer.answer(Message::Split {
            range: Range::ROOT,
            children: Box::new([Probe::Compact(0, [0; 4]); 16])
        }),
        Err(Error::Phase)
    );
    assert!(peer.difference().is_none());

    let mut peer = Responder::new(snapshot, limits()).unwrap();
    through_setup(&mut peer, root);
    assert_eq!(
        peer.answer(Message::Difference {
            ids: Vec::new(),
            done: true,
            local_only: false
        }),
        Err(Error::Phase)
    );
    assert!(peer.difference().is_none());
}

#[test]
fn transport_errors_and_explicit_resource_budgets_are_preserved() {
    let snapshot = Arc::new(Snapshot::new((1..=8).map(digest).collect()));
    let failed = reconcile(Arc::clone(&snapshot), limits(), |_| Err("transport broke"));
    assert_eq!(failed, Err(ExchangeError::Transport("transport broke")));
    let mut peer = Responder::new(Arc::clone(&snapshot), limits()).unwrap();
    let limited = Limits {
        messages: 3,
        ..limits()
    };
    let failed = reconcile(Arc::clone(&snapshot), limited, |message| {
        peer.answer(message)
    });
    assert_eq!(failed, Err(ExchangeError::Protocol(Error::Budget)));
    assert!(peer.difference().is_none());
    let mut peer = Responder::new(
        snapshot,
        Limits {
            remote_records: 7,
            ..limits()
        },
    )
    .unwrap();
    assert_eq!(
        peer.answer(Message::Root(Fingerprint {
            count: 8,
            sum: digest(3)
        })),
        Err(Error::Budget)
    );
    assert!(peer.difference().is_none());
}

#[test]
fn validly_encoded_but_stale_or_inconsistent_replies_never_complete() {
    for fault in ["range", "cursor", "count", "root", "finish"] {
        let ours = Arc::new(Snapshot::new(BTreeSet::new()));
        let theirs = Arc::new(Snapshot::new((1..=512).map(digest).collect()));
        let mut peer = Responder::new(theirs, limits()).unwrap();
        let mut injected = false;
        let result = reconcile(ours, limits(), |request| {
            let cursor = match &request {
                Message::ListRequest { after, .. } => *after,
                _ => None,
            };
            let mut reply = peer.answer(Message::decode(&request.encode()?)?)?;
            if !injected {
                match (&mut reply, fault) {
                    (Message::List { range, ids, done }, "range") => {
                        *range = Range::ROOT.children().unwrap()[15];
                        *ids = vec![[255; 32]];
                        *done = true;
                        injected = true;
                    }
                    (Message::List { ids, .. }, "cursor") if cursor.is_some() => {
                        ids[0] = cursor.unwrap();
                        injected = true;
                    }
                    (Message::List { ids, done, .. }, "count") => {
                        ids.clear();
                        *done = true;
                        injected = true;
                    }
                    (Message::Root(root), "root") => {
                        *root = Fingerprint::default();
                        injected = true;
                    }
                    (Message::Finish { remote_only, .. }, "finish") => {
                        remote_only.sum[0] ^= 1;
                        injected = true;
                    }
                    _ => {}
                }
            }
            // These replies must pass the REAL codec: their error is protocol state,
            // not a test that bypassed the decoder's shape checks.
            Message::decode(&reply.encode()?)
        });
        assert!(injected, "{fault}");
        assert!(result.is_err(), "accepted {fault}");
        if fault != "finish" {
            assert!(peer.difference().is_none(), "{fault}");
        }
        // A transport corrupting the final reply cannot revoke the responder's
        // already-validated result; the initiator still returns no result.
    }
}

#[test]
fn ordering_is_checked_across_actor_and_difference_page_boundaries() {
    let headers: Vec<_> = (1..=100).flat_map(|actor| chain(actor, 1)).collect();
    let ours = Arc::new(Snapshot::from_index(&index(headers[..99].iter().cloned())));
    let snapshot = Arc::new(Snapshot::from_index(&index(headers)));
    let mut peer = Responder::new(Arc::clone(&snapshot), limits()).unwrap();
    let mut pages = 0;
    let result = reconcile(ours, limits(), |request| {
        let mut reply = peer.answer(request)?;
        if let Message::Frontiers { items, .. } = &mut reply {
            pages += 1;
            if pages == 2 {
                items[0].actor = [1; 48];
            }
        }
        Message::decode(&reply.encode()?)
    });
    assert_eq!(result, Err(ExchangeError::Protocol(Error::Prefix)));
    assert!(peer.difference().is_none());

    let empty = Arc::new(Snapshot::new(BTreeSet::new()));
    let mut peer = Responder::new(Arc::clone(&empty), limits()).unwrap();
    peer.answer(Message::Root(Fingerprint {
        count: 100,
        sum: digest(1),
    }))
    .unwrap();
    let anchors: Vec<_> = (1..=64)
        .map(|actor| Frontier {
            actor: [actor; 48],
            sequence: 1,
            id: digest(u64::from(actor)),
        })
        .collect();
    peer.answer(Message::Frontiers {
        items: anchors.clone(),
        done: false,
    })
    .unwrap();
    assert_eq!(
        peer.answer(Message::Frontiers {
            items: vec![anchors[0]],
            done: true
        }),
        Err(Error::Prefix)
    );
    assert!(peer.difference().is_none());

    let ids: Vec<_> = (1..=128)
        .map(digest)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut peer = Responder::new(empty, limits()).unwrap();
    through_setup(&mut peer, contribution(ids.iter().copied()).unwrap());
    peer.answer(Message::Difference {
        ids: ids[..PAGE].to_vec(),
        done: false,
        local_only: true,
    })
    .unwrap();
    assert_eq!(
        peer.answer(Message::Difference {
            ids: vec![ids[0]],
            done: true,
            local_only: true
        }),
        Err(Error::Wire)
    );
    assert!(peer.difference().is_none());
}

#[test]
fn exact_differences_agree_with_set_subtraction_across_small_shapes() {
    for seed in 1..=64u64 {
        let ours = (1..=128)
            .filter(|number| (number + seed) % 3 != 0)
            .map(|number| digest(seed * 10_000 + number))
            .collect();
        let theirs = (1..=160)
            .filter(|number| (number + seed * 7) % 5 != 0)
            .map(|number| digest(seed * 10_000 + number))
            .collect();
        run(Snapshot::new(ours), Snapshot::new(theirs));
    }
}

#[test]
fn unchanged_populated_inventory_uses_constant_wire_without_actor_pages() {
    let headers: Vec<_> = (1..=4).flat_map(|actor| chain(actor, 2048)).collect();
    let snapshot = Snapshot::from_index(&index(headers));
    let (difference, _, traffic) = run(snapshot.clone(), snapshot);
    assert_eq!(difference, Difference::default());
    println!("unchanged inventory of 8192 identities: {traffic:?}");
    assert!(
        traffic.bytes < 256,
        "unchanged inventory must not exchange actor pages: {traffic:?}"
    );
}

/// The `index`-th identity of a large inventory: spread over the whole digest space, as
/// content identities are, and distinct for each index.
fn spread(index: u64) -> Digest {
    let mut id = [0; 32];
    let mut word = index;
    for chunk in id.as_chunks_mut::<8>().0 {
        // SplitMix64, a bijection of its state at each step.
        word = word.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = word;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        *chunk = (z ^ (z >> 31)).to_be_bytes();
    }
    id
}

/// LT-E78. Two replicas that share 5,000,000 records, with 300 more held only here and 400
/// only at the peer, reconcile as a remainder under a budget of 1,000 remote records: neither root is
/// refused, no frontier or prefix message crosses, both sides hold the exact difference,
/// and the traffic follows the 700 records of difference (2,735 requests, 307,468 bytes).
/// The budget counts the difference held: 399 refuses the initiator, which would hold 400,
/// and 299 refuses the responder, which would hold 300, each with [`Error::Budget`] and no
/// difference; 400 and 300 pass. A whole-inventory exchange under the same 1,000
/// still refuses the peer's root, as the membership log's own bound.
///
/// Negative control, run once: with `validate_root` given the limit in a remainder
/// exchange as in a whole one, the test fails at its first exchange with
/// `Protocol(Budget)`.
#[test]
fn a_peer_whose_root_counts_5000000_records_is_not_refused_and_the_budget_counts_only_the_difference_held(
) {
    const SHARED: u64 = 5_000_000;
    let here: BTreeSet<Digest> = (0..SHARED + 300).map(spread).collect();
    let there: BTreeSet<Digest> = (0..SHARED)
        .chain(2 * SHARED..2 * SHARED + 400)
        .map(spread)
        .collect();
    let expected_send: Vec<Digest> = here.difference(&there).copied().collect();
    let expected_want: Vec<Digest> = there.difference(&here).copied().collect();
    assert_eq!((here.len(), there.len()), (5_000_300, 5_000_400));
    assert_eq!((expected_send.len(), expected_want.len()), (300, 400));
    let here = Arc::new(Snapshot::new(here));
    let there = Arc::new(Snapshot::new(there));
    let budget = |remote_records| Limits {
        remote_records,
        messages: 100_000,
    };

    let mut peer = Responder::remainder(Arc::clone(&there), budget(1_000)).unwrap();
    let mut requests = 0u64;
    let mut bytes = 0usize;
    let found = reconcile_remainder(Arc::clone(&here), budget(1_000), |request| {
        assert!(
            !matches!(
                request,
                Message::Frontiers { .. } | Message::Prefixes { .. }
            ),
            "a remainder exchange has no frontier stage"
        );
        let wire = request.encode()?;
        requests += 1;
        bytes += 4 + wire.len();
        let reply = peer.answer(Message::decode(&wire)?)?;
        let wire = reply.encode()?;
        bytes += 4 + wire.len();
        Message::decode(&wire)
    })
    .expect("a remainder exchange between two replicas of 5,000,000 records");
    assert_eq!(found.send, expected_send);
    assert_eq!(found.want, expected_want);
    let theirs = peer.difference().expect("the peer's difference");
    assert_eq!(theirs.send, expected_want);
    assert_eq!(theirs.want, expected_send);
    // The traffic follows the 700 records of difference, not the 10,000,000 held.
    // Measured: 2,735 requests and 307,468 bytes both ways.
    assert!(requests < 6 * 700, "{requests} requests");
    assert!(bytes < 1 << 19, "{bytes} bytes");

    // The budget's edges, on two replicas that share 50,000 records and differ by the same
    // 300 and 400.
    let near: BTreeSet<Digest> = (0..50_300).map(spread).collect();
    let far: BTreeSet<Digest> = (0..50_000)
        .chain(2 * SHARED..2 * SHARED + 400)
        .map(spread)
        .collect();
    let near = Arc::new(Snapshot::new(near));
    let far = Arc::new(Snapshot::new(far));

    // One record fewer than the initiator would hold.
    let mut peer = Responder::remainder(Arc::clone(&far), budget(1_000)).unwrap();
    let refused = reconcile_remainder(Arc::clone(&near), budget(399), |request| {
        peer.answer(request)
    });
    assert_eq!(refused, Err(ExchangeError::Protocol(Error::Budget)));
    assert!(peer.difference().is_none());

    // One record fewer than the responder would hold: its refusal reaches the initiator as
    // its transport's error, and neither side has a difference.
    let mut peer = Responder::remainder(Arc::clone(&far), budget(299)).unwrap();
    let refused = reconcile_remainder(Arc::clone(&near), budget(1_000), |request| {
        peer.answer(request)
    });
    assert_eq!(refused, Err(ExchangeError::Transport(Error::Budget)));
    assert!(peer.difference().is_none());

    // Exactly what each would hold passes.
    let mut peer = Responder::remainder(far, budget(300)).unwrap();
    let found = reconcile_remainder(near, budget(400), |request| peer.answer(request))
        .expect("a budget of exactly the difference");
    assert_eq!((found.send.len(), found.want.len()), (300, 400));
    assert_eq!(
        peer.difference().map(|d| (d.send.len(), d.want.len())),
        Some((400, 300))
    );

    // A whole-inventory exchange keeps its bound on the inventory a peer states: the
    // initiator refuses the responder's root, and the responder the initiator's.
    let mut peer = Responder::new(Arc::clone(&there), budget(u64::MAX)).unwrap();
    let refused = reconcile(Arc::clone(&here), budget(1_000), |request| {
        peer.answer(request)
    });
    assert_eq!(refused, Err(ExchangeError::Protocol(Error::Budget)));
    let mut peer = Responder::new(there, budget(1_000)).unwrap();
    assert_eq!(
        peer.answer(Message::Root(here.fingerprint().unwrap())),
        Err(Error::Budget)
    );

    // An initiator with a frontier stage does not complete against a remainder responder.
    // The responder refuses its first frontier page.
    let small = Arc::new(Snapshot::new((1..=8).map(digest).collect()));
    let other = Arc::new(Snapshot::new((5..=12).map(digest).collect()));
    let mut peer = Responder::remainder(other, budget(1_000)).unwrap();
    let mixed = reconcile(small, budget(1_000), |request| peer.answer(request));
    assert_eq!(mixed, Err(ExchangeError::Transport(Error::Phase)));
    assert!(peer.difference().is_none());
}
