// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use crate::sync::Header;

pub(super) fn digest(mut seed: u64) -> Digest {
    let mut id = [0; 32];
    for byte in &mut id {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        *byte = seed as u8;
    }
    id
}

pub(super) fn chain(actor: u8, count: u64) -> Vec<Header> {
    let mut previous = None;
    (1..=count)
        .map(|sequence| {
            let id = digest(u64::from(actor) * 1_000_000 + sequence);
            let header = Header {
                id,
                actor: [actor; 48],
                sequence,
                previous,
                parents: previous.into_iter().collect(),
            };
            previous = Some(id);
            header
        })
        .collect()
}

pub(super) fn index(headers: impl IntoIterator<Item = Header>) -> Index {
    let mut index = Index::new(100_000);
    for header in headers {
        index.insert(header).unwrap();
    }
    index
}

#[test]
fn fingerprints_preserve_full_modular_arithmetic_and_detect_short_probe_collisions() {
    let high = Fingerprint {
        count: 1,
        sum: [255; 32],
    };
    let mut one = Fingerprint {
        count: 1,
        ..Fingerprint::default()
    };
    one.sum[31] = 1;
    let wrapped = high.plus(one).unwrap();
    assert_eq!(wrapped.sum, [0; 32]);
    assert_eq!(wrapped.count, 2);
    assert_eq!(wrapped.minus(one), Ok(high));
    assert_eq!(one.minus(high).unwrap().sum[31], 2);
    assert_eq!(one.minus(wrapped), Err(Error::Count));
    assert_eq!(
        Fingerprint {
            count: u64::MAX,
            ..one
        }
        .plus(one),
        Err(Error::Count)
    );

    let mut collision = one;
    collision.sum[0] = 7;
    assert_eq!(collision.probe(), one.probe());
    assert_ne!(collision, one, "a short probe cannot close reconciliation");
    let common = Fingerprint {
        count: 16,
        sum: digest(19),
    };
    assert_ne!(
        common.plus(collision).unwrap().minus(one).unwrap(),
        common,
        "full-summary conservation catches an omitted short-probe difference"
    );
}

#[test]
fn sixteen_way_ranges_partition_every_depth_without_overflow_or_overlap() {
    let ids: Vec<_> = (1..=512).map(digest).collect();
    let snapshot = Snapshot::new(ids.iter().copied().collect());
    let total = snapshot.range_fingerprint(None, None).unwrap();
    assert_eq!(total.count, 512);
    for id in ids {
        let mut range = Range::ROOT;
        for _ in 0..64 {
            assert!(range.contains(&id));
            let children = range.children().unwrap();
            let matching: Vec<_> = children
                .iter()
                .filter(|child| child.contains(&id))
                .collect();
            assert_eq!(matching.len(), 1);
            assert_eq!(children[0].prefix().0, range.prefix().0);
            for pair in children.windows(2) {
                assert_eq!(pair[0].upper(), Some(pair[1].prefix().0));
            }
            assert_eq!(children[15].upper(), range.upper());
            range = *matching[0];
        }
        assert_eq!(range.prefix().0, id);
        assert!(range.children().is_none());
    }
    let mut sum = Fingerprint::default();
    for child in Range::ROOT.children().unwrap() {
        sum = sum
            .plus(
                snapshot
                    .range_fingerprint(Some(child.prefix().0), child.upper())
                    .unwrap(),
            )
            .unwrap();
    }
    assert_eq!(sum, total);
    assert_eq!(Range::new([1; 32], 0), Err(Error::Range));
    assert_eq!(Range::new([0; 32], 65), Err(Error::Range));
    assert_eq!(Range::new([255; 32], 64).unwrap().upper(), None);
    assert_eq!(
        snapshot.range_fingerprint(Some([255; 32]), Some([0; 32])),
        Err(Error::Range)
    );
}

#[test]
fn actor_frontiers_skip_only_shared_dense_unforked_prefixes() {
    let headers = chain(1, 8);
    let short = Snapshot::from_index(&index(headers[..5].iter().cloned()));
    let long = Snapshot::from_index(&index(headers.iter().cloned()));
    let short_frontiers: Vec<_> = short.frontiers().collect();
    let long_frontiers: Vec<_> = long.frontiers().collect();
    assert_eq!(short_frontiers[0].sequence, 5);
    assert_eq!(long_frontiers[0].sequence, 8);
    assert_eq!(
        long.shared_prefixes(&short_frontiers).unwrap(),
        short_frontiers
    );
    assert!(short.shared_prefixes(&long_frontiers).unwrap().is_empty());
    assert_eq!(
        short
            .without_prefixes(&short_frontiers)
            .unwrap()
            .ids()
            .count(),
        0
    );
    assert_eq!(
        long.without_prefixes(&short_frontiers)
            .unwrap()
            .ids()
            .count(),
        3
    );

    let gapped = Snapshot::from_index(&index(
        headers
            .iter()
            .filter(|header| header.sequence != 3)
            .cloned(),
    ));
    let anchor: Vec<_> = gapped.frontiers().collect();
    assert_eq!(anchor[0].sequence, 2);
    assert_eq!(gapped.without_prefixes(&anchor).unwrap().ids().count(), 5);
    assert!(gapped.shared_prefixes(&long_frontiers).unwrap().is_empty());
    assert_eq!(
        gapped.without_prefixes(&short_frontiers).unwrap_err(),
        Error::Prefix
    );

    let mut fork = headers[1].clone();
    fork.id = digest(123_456);
    let forked = Snapshot::from_index(&index(headers.into_iter().chain([fork])));
    assert!(forked.frontiers().next().is_none());
    assert_eq!(
        forked.ids().count(),
        9,
        "a fork is inventory, not a watermark"
    );
    assert!(forked.shared_prefixes(&short_frontiers).unwrap().is_empty());
}

#[test]
fn prefix_partition_keeps_every_unshared_gapped_and_forked_identity() {
    let first = chain(1, 16);
    let second = chain(2, 7);
    let third: Vec<_> = chain(3, 9)
        .into_iter()
        .filter(|header| header.sequence != 4)
        .collect();
    let mut fourth = chain(4, 8);
    let mut fork = fourth[2].clone();
    fork.id = digest(999_999);
    fourth.push(fork);
    let headers: Vec<_> = first
        .iter()
        .chain(&second)
        .chain(&third)
        .chain(&fourth)
        .cloned()
        .collect();
    let snapshot = Snapshot::from_index(&index(headers.iter().cloned()));
    assert_eq!(
        snapshot.ids.len(),
        snapshot.unprefixed.len()
            + snapshot
                .prefixes
                .iter()
                .map(|(_, prefix)| prefix.len())
                .sum::<usize>()
    );
    assert_eq!(
        snapshot.without_prefixes(&[]).unwrap().ids,
        snapshot.ids,
        "the cached partition must preserve the entire initial inventory"
    );
    let shared: Vec<_> = [&first[9], &second[6], &third[2]]
        .into_iter()
        .map(|header| Frontier {
            actor: header.actor,
            sequence: header.sequence,
            id: header.id,
        })
        .collect();
    let expected: BTreeSet<_> = headers
        .iter()
        .filter(|header| {
            !shared
                .iter()
                .any(|cut| cut.actor == header.actor && header.sequence <= cut.sequence)
        })
        .map(|header| header.id)
        .collect();
    assert_eq!(
        identities(&snapshot.without_prefixes(&shared).unwrap()),
        expected
    );
    assert_eq!(
        snapshot
            .without_prefixes(&[shared[0], shared[0]])
            .unwrap_err(),
        Error::Prefix
    );
}

#[test]
fn physical_inventory_survives_missing_metadata_and_excludes_certificate_only_sources() {
    let records = chain(9, 6);
    let physical: BTreeSet<_> = records.iter().map(|header| header.id).collect();
    let extra_source = chain(10, 1).pop().unwrap();
    let mut metadata = index([
        records[0].clone(),
        records[1].clone(),
        records[3].clone(),
        records[5].clone(),
        extra_source.clone(),
    ]);
    let snapshot = Snapshot::from_inventory(physical.clone(), &metadata);
    assert_eq!(identities(&snapshot), physical);
    assert!(!snapshot.contains(&extra_source.id));
    let anchors: Vec<_> = snapshot.frontiers().collect();
    assert_eq!(anchors.len(), 1);
    assert_eq!((anchors[0].actor, anchors[0].sequence), ([9; 48], 2));
    assert_eq!(
        identities(&snapshot.without_prefixes(&anchors).unwrap()),
        records[2..]
            .iter()
            .map(|header| header.id)
            .collect::<BTreeSet<_>>()
    );

    // A certificate may name another signed branch without holding its payload.
    // That source remains restrictive evidence, never a new payload inventory ID.
    let mut fork_source = records[3].clone();
    fork_source.id = digest(987_654_321);
    metadata.insert(fork_source).unwrap();
    let snapshot = Snapshot::from_inventory(physical.clone(), &metadata);
    assert_eq!(identities(&snapshot), physical);
    assert!(snapshot.frontiers().next().is_none());
    assert_eq!(
        identities(&snapshot.without_prefixes(&[]).unwrap()),
        physical
    );
}

fn identities(snapshot: &Snapshot) -> BTreeSet<Digest> {
    snapshot.ids().copied().collect()
}

#[test]
fn snapshot_storage_is_shareable_and_charges_prefix_metadata() {
    let records = chain(3, 8192);
    let plain = Snapshot::new(records.iter().map(|header| header.id).collect());
    let indexed = Snapshot::from_index(&index(records.iter().cloned()));
    let plain_bytes = plain.retained_bytes();
    let indexed_bytes = indexed.retained_bytes();
    assert!(plain_bytes >= 8192 * size_of::<Digest>());
    assert!(indexed_bytes >= 2 * 8192 * size_of::<Digest>());
    assert!(indexed_bytes > plain_bytes);
    let mostly_unknown = Snapshot::from_inventory(identities(&plain), &index([records[0].clone()]));
    assert!(mostly_unknown.retained_bytes() >= (2 * 8192 - 1) * size_of::<Digest>());
    let unknown = Snapshot::from_inventory(identities(&plain), &Index::new(0));
    assert_eq!(unknown.retained_bytes(), plain_bytes);
    charge_grows_after_reserving(&indexed, |snapshot| {
        snapshot
            .prefixes
            .reserve_exact(snapshot.prefixes.capacity() + 1);
    });
    charge_grows_after_reserving(&indexed, |snapshot| {
        let prefix = &mut snapshot.prefixes[0].1;
        prefix.reserve_exact(prefix.capacity() + 1);
    });
    charge_grows_after_reserving(&mostly_unknown, |snapshot| {
        snapshot
            .unprefixed
            .reserve_exact(snapshot.unprefixed.capacity() + 1);
    });
    let root = indexed.fingerprint().unwrap();
    assert_eq!(indexed.retained_bytes(), indexed_bytes);
    let unsliced = indexed.without_prefixes(&[]).unwrap();
    assert!(Arc::ptr_eq(&indexed.ids, &unsliced.ids));
    assert_eq!(unsliced.fingerprint().unwrap(), root);
    assert_eq!(unsliced.retained_bytes(), plain_bytes);
}

fn charge_grows_after_reserving(snapshot: &Snapshot, reserve: impl FnOnce(&mut Snapshot)) {
    let mut expanded = snapshot.clone();
    let before = expanded.retained_bytes();
    reserve(&mut expanded);
    assert!(expanded.retained_bytes() > before);
    assert_eq!(identities(&expanded), identities(snapshot));
    assert_eq!(expanded.fingerprint(), snapshot.fingerprint());
}
