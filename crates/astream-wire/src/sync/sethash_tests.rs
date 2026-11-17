// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use astream_digest::Sha256;
use std::cell::Cell;

fn sha256(bytes: &[u8]) -> Digest {
    Sha256::digest_slice(bytes)
}

thread_local! {
    /// Hashes this thread ran through [`counted`], and the bytes they read.
    static WORK: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
}

fn counted(bytes: &[u8]) -> Digest {
    WORK.with(|work| {
        let (calls, read) = work.get();
        work.set((calls + 1, read + bytes.len() as u64));
    });
    sha256(bytes)
}

/// The `index`-th entry's digest: distinct for each index, as a map with unique keys gives.
fn entry(index: u64) -> Digest {
    let mut digest = [0; 32];
    digest[..8].copy_from_slice(&index.to_le_bytes());
    digest
}

/// The hash of the entries `0..count`, one [`SetHash::plus`] an entry. Each of `parts`
/// threads takes the entries `pick` gives it, in the order `pick` gives them, and the
/// threads' hashes are summed in the order `sum` names.
fn built(
    count: u64,
    parts: u64,
    pick: impl Fn(u64, u64) -> Box<dyn Iterator<Item = u64>> + Sync,
    sum: impl Fn(u64) -> u64,
) -> SetHash {
    let pick = &pick;
    let hashes: Vec<SetHash> = std::thread::scope(|scope| {
        let threads: Vec<_> = (0..parts)
            .map(|part| {
                scope.spawn(move || {
                    let mut hash = SetHash::EMPTY;
                    for index in pick(part, count) {
                        hash.plus(sha256, &entry(index));
                    }
                    hash
                })
            })
            .collect();
        threads
            .into_iter()
            .map(|thread| thread.join().expect("a builder"))
            .collect()
    });
    let mut whole = SetHash::EMPTY;
    for at in 0..parts {
        whole.plus_set(&hashes[sum(at) as usize]);
    }
    whole
}

/// Every order of `0..n`, by Heap's algorithm.
fn orders(n: usize) -> Vec<Vec<u64>> {
    fn go(k: usize, items: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        if k <= 1 {
            out.push(items.clone());
            return;
        }
        for i in 0..k {
            go(k - 1, items, out);
            items.swap(if k % 2 == 0 { i } else { 0 }, k - 1);
        }
    }
    let mut out = Vec::new();
    go(n, &mut (0..n as u64).collect(), &mut out);
    out
}

/// LT-E50. The hash of a million entries is the same 2,048 bytes whatever order they were
/// added in and however the work was split, an entry is added or removed with sixty-four
/// hashes of 55 bytes at that size, and adding entries and removing them again, or removing
/// members and adding them back, returns the same bytes.
///
/// The small case has references the large one cannot afford: seven entries in each of
/// their 5,040 orders, and each of their 128 subsets reached by removal against the same
/// subset built from nothing.
///
/// Negative control, run once: with `minus` adding where it subtracts, the test fails at
/// the first removal, "a subset reached by removal is the subset built".
#[test]
fn a_set_hash_of_1000000_entries_is_the_same_2048_bytes_built_in_any_order_or_by_adding_and_removing(
) {
    const COUNT: u64 = 1_000_000;
    let parts = std::thread::available_parallelism()
        .map_or(4, |n| n.get() as u64)
        .clamp(2, 16);

    // Seven entries, every order, every subset.
    let all: Vec<u64> = (0..7).collect();
    let of = |indices: &[u64]| {
        let mut hash = SetHash::EMPTY;
        for index in indices {
            hash.plus(sha256, &entry(*index));
        }
        hash
    };
    let seven = of(&all);
    let seen = orders(7);
    assert_eq!(seen.len(), 5_040);
    for order in &seen {
        assert_eq!(of(order), seven, "an order of seven entries: {order:?}");
    }
    for subset in 0u32..128 {
        let (kept, dropped): (Vec<u64>, Vec<u64>) =
            all.iter().partition(|index| subset >> **index & 1 == 1);
        let mut hash = seven.clone();
        for index in dropped.iter().rev() {
            hash.minus(sha256, &entry(*index));
        }
        assert_eq!(
            hash,
            of(&kept),
            "a subset reached by removal is the subset built"
        );
        assert_eq!(
            hash == SetHash::EMPTY,
            kept.is_empty(),
            "only no entries hash as none"
        );
    }

    // A million entries: ascending in contiguous runs, then descending in stripes with the
    // threads' hashes summed last first.
    let ascending = built(
        COUNT,
        parts,
        |part, count| {
            let run = count.div_ceil(parts);
            Box::new(part * run..((part + 1) * run).min(count))
        },
        |at| at,
    );
    let striped = built(
        COUNT,
        parts,
        |part, count| Box::new((0..count).rev().filter(move |index| index % parts == part)),
        |at| parts - 1 - at,
    );
    assert_eq!(ascending.to_bytes().len(), 2_048);
    assert!(
        ascending.to_bytes() == striped.to_bytes(),
        "two orders of a million entries"
    );
    assert_eq!(ascending.digest(sha256), striped.digest(sha256));
    assert_eq!(SetHash::from_bytes(&ascending.to_bytes()), ascending);
    assert_ne!(ascending.digest(sha256), SetHash::EMPTY.digest(sha256));

    // One entry at a million costs what it costs at none: sixty-four hashes of 55 bytes.
    for start in [&SetHash::EMPTY, &ascending] {
        let mut hash = start.clone();
        WORK.set((0, 0));
        hash.plus(counted, &entry(COUNT));
        assert_eq!(
            WORK.get(),
            (64, 64 * 55),
            "hashes and bytes to add one entry"
        );
        assert_ne!(&hash, start, "one more entry is another set");
        WORK.set((0, 0));
        hash.minus(counted, &entry(COUNT));
        assert_eq!(
            WORK.get(),
            (64, 64 * 55),
            "hashes and bytes to remove one entry"
        );
        assert_eq!(&hash, start, "an entry added and removed leaves the set");
    }

    // A thousand entries added then removed in another order, and a thousand members
    // removed then added back, against the same thousand as a set of their own.
    let mut hash = ascending.clone();
    for index in COUNT..COUNT + 1_000 {
        hash.plus(sha256, &entry(index));
    }
    assert_ne!(hash, ascending);
    for index in (COUNT..COUNT + 1_000).rev() {
        hash.minus(sha256, &entry(index));
    }
    assert!(
        hash == ascending,
        "a thousand entries added to a million and removed"
    );

    let members: Vec<u64> = (0..1_000).map(|k| k * 997 + 3).collect();
    let thousand = of(&members);
    for index in &members {
        hash.minus(sha256, &entry(*index));
    }
    let mut without = ascending.clone();
    without.minus_set(&thousand);
    assert!(hash == without, "members removed one by one, and as a set");
    assert_ne!(hash, ascending);
    for index in members.iter().rev() {
        hash.plus(sha256, &entry(*index));
    }
    assert!(
        hash == striped,
        "a thousand members removed from a million and added back"
    );

    // A set that differs in one entry differs.
    let mut other = ascending.clone();
    other.minus(sha256, &entry(0));
    other.plus(sha256, &entry(COUNT));
    assert_ne!(other.to_bytes(), ascending.to_bytes());
    assert_ne!(other.digest(sha256), ascending.digest(sha256));

    // Why the caller holds a set: an entry added 65,536 times is in no lane.
    let mut many = of(&[42]);
    assert_ne!(many, SetHash::EMPTY);
    for _ in 0..16 {
        let half = many.clone();
        many.plus_set(&half);
    }
    assert_eq!(many, SetHash::EMPTY, "65,536 copies of one entry");
}
