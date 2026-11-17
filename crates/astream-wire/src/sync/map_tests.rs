// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use astream_digest::Sha256;
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};

fn sha256(bytes: &[u8]) -> Digest {
    Sha256::digest_slice(bytes)
}

static HASHED: AtomicU64 = AtomicU64::new(0);

/// SHA-256 that counts its calls, for the one test that reads the count.
fn counted(bytes: &[u8]) -> Digest {
    HASHED.fetch_add(1, Ordering::Relaxed);
    sha256(bytes)
}

/// An evenly spread key: four splitmix64 words.
fn key(row: u64) -> Digest {
    let mut state = row;
    let mut key = [0; 32];
    for word in key.as_chunks_mut::<8>().0 {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut mixed = state;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        *word = (mixed ^ (mixed >> 31)).to_be_bytes();
    }
    key
}

/// A deterministic xorshift, so a failing seed reruns as it failed.
struct Rng(u64);

impl Rng {
    fn below(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % bound
    }

    /// A key from three crowded prefixes, so sets split leaves three levels down and
    /// removes fold them back.
    fn crowded(&mut self) -> Digest {
        let mut key = [0; 32];
        key[0] = [0x00, 0x01, 0xA0][self.below(3) as usize];
        key[1] = self.below(256) as u8;
        key[31] = self.below(2) as u8;
        key
    }

    fn value(&mut self) -> Vec<u8> {
        vec![self.below(256) as u8; self.below(40) as usize]
    }
}

/// The 33 keys that share their first `shared` nibbles and differ in the two after.
fn sharing(shared: usize) -> Vec<Digest> {
    (0..33u8)
        .map(|row| {
            let mut key = [0x55; 32];
            if shared % 2 == 0 {
                key[shared / 2] = row;
            } else {
                key[shared / 2] = 0x50 | (row >> 4);
                key[shared / 2 + 1] = (row << 4) | 5;
            }
            key
        })
        .collect()
}

fn built<'a>(rows: impl IntoIterator<Item = (&'a Digest, &'a Vec<u8>)>) -> Map {
    let mut map = Map::new(sha256, usize::MAX);
    for (key, value) in rows {
        map.set(*key, value).unwrap();
    }
    map
}

fn listed(map: &Map, range: Range, after: Option<Digest>) -> Vec<(Digest, Vec<u8>)> {
    map.rows(range, after)
        .map(|row| row.map(|(key, value)| (*key, value.to_vec())).unwrap())
        .collect()
}

/// Every page of `map`, by hash, as a store would hold them; and how many there are.
fn stored(map: &Map) -> HashMap<Digest, Vec<u8>> {
    let mut store = HashMap::new();
    for (range, hash) in map.written(&Map::new(sha256, 0)) {
        let page = map.page(range).unwrap();
        assert!(store.insert(hash, page).is_none(), "{range:?} twice");
    }
    store
}

/// Run `ask`, admitting from `store` each page it reports missing; the answer and the
/// pages read.
fn fetching<T>(
    map: &mut Map,
    store: &HashMap<Digest, Vec<u8>>,
    mut ask: impl FnMut(&mut Map) -> Result<T, Error>,
) -> (T, usize) {
    let mut pages = 0;
    loop {
        match ask(map) {
            Err(Error::Missing(range, hash)) => {
                map.admit(range, &store[&hash]).unwrap();
                pages += 1;
            }
            answer => return (answer.unwrap(), pages),
        }
    }
}

/// The shape rule and the counters at every held page: a leaf has at most 32 ordered
/// rows of its own range, anything larger is interior, and each node's rows and bytes
/// are what its rows or children add up to.
fn check(node: &Node, range: Range) {
    let (rows, held) = match &node.body {
        Body::Absent(_) => {
            assert!(node.rows > 0, "{range:?}: an empty page is never absent");
            (node.rows, NODE)
        }
        Body::Leaf(rows) => {
            assert!(rows.len() <= LEAF_ROWS, "{range:?}");
            assert!(rows.windows(2).all(|pair| pair[0].key < pair[1].key));
            assert!(rows.iter().all(|row| range.contains(&row.key)), "{range:?}");
            let values: usize = rows.iter().map(|row| row.value.len()).sum();
            (rows.len() as u64, NODE + rows.len() * ROW + values)
        }
        Body::Interior(children) => {
            assert!(node.rows > LEAF_ROWS as u64, "{range:?}");
            for (child, range) in children.iter().zip(range.children().unwrap()) {
                check(child, range);
            }
            (
                children.iter().map(|child| child.rows).sum(),
                NODE + children.iter().map(|child| child.held).sum::<usize>(),
            )
        }
    };
    assert_eq!((node.rows, node.held), (rows, held), "{range:?}");
}

/// A leaf page written out by hand from the design's table, and the hash that names it.
fn leaf_page(rows: &[(Digest, &[u8])]) -> (Vec<u8>, Digest) {
    let mut page = b"ATPG1\x02".to_vec();
    let mut named = page.clone();
    page.extend((rows.len() as u16).to_be_bytes());
    named.extend((rows.len() as u16).to_be_bytes());
    for (key, value) in rows {
        let row = [&key[..], &(value.len() as u16).to_be_bytes(), value].concat();
        named.extend(sha256(&row));
        page.extend(row);
    }
    (page, sha256(&named))
}

fn interior_page(children: &[(Digest, u64); 16]) -> Vec<u8> {
    let mut page = b"ATPG1\x01".to_vec();
    for (hash, rows) in children {
        page.extend(hash);
        page.extend(rows.to_be_bytes());
    }
    page
}

/// The exit test of the package. 1,000,000 evenly spread rows of 16 bytes; then the row
/// whose proof is the largest any row of this map can have (the leaf whose depth and row
/// count cost the most bytes: a full leaf under four levels here, though a few small
/// leaves sit under five) is rewritten as a seat row of the design's 360 bytes, and that
/// one change is counted: pages a store must write, hashes computed, bytes of its proof.
///
/// NEGATIVE CONTROL: with a leaf named by the hash of its bytes, so that a proof must
/// carry the leaf's other rows whole (50 bytes each here) in place of their 32-byte
/// hashes, the same row's proof is 4318 bytes and the test fails:
/// `the proof of one row must stay under 4096 bytes: 4318 bytes, 4 levels, 32 rows in its leaf`.
#[test]
fn a_map_of_1000000_rows_changes_one_row_in_under_8_pages_and_proves_it_in_under_4096_bytes() {
    const ROWS: u64 = 1_000_000;
    const SEAT: usize = 360 - 32 - 2;
    let mut map = Map::new(counted, usize::MAX);
    for row in 0..ROWS {
        let value = [row.to_be_bytes(), (!row).to_be_bytes()].concat();
        map.set(key(row), &value).unwrap();
    }
    assert_eq!(map.len(), ROWS);
    let root = map.root();

    // Every leaf, by the bytes a seat row in it needs for its proof.
    let (mut leaves, mut worst) = (0u64, (0, Range::ROOT, 0, 0));
    let mut walk = vec![Range::ROOT];
    while let Some(range) = walk.pop() {
        let rows = map.node(range).unwrap().1 as usize;
        if rows > LEAF_ROWS {
            walk.extend(range.children().unwrap());
        } else if rows > 0 {
            let levels = usize::from(range.prefix().1);
            let proof = 5 + 3 + 32 + 2 + SEAT + 32 * (rows - 1) + 600 * levels;
            leaves += 1;
            worst = worst.max((proof, range, levels, rows));
        }
    }
    let (expected, range, levels, rows) = worst;
    let target = *map.rows(range, None).next().unwrap().unwrap().0;
    let old = map.get(&target).unwrap().unwrap().to_vec();

    let before = map.clone();
    let hashed = HASHED.load(Ordering::Relaxed);
    map.set(target, &[0xA7; SEAT]).unwrap();
    let changed = map.root();
    let hashes = HASHED.load(Ordering::Relaxed) - hashed;
    let pages: Vec<u8> = map
        .written(&before)
        .iter()
        .map(|(range, _)| range.prefix().1)
        .collect();
    let proof = map.prove(&target).unwrap().unwrap().encode();
    println!(
        "1000000 rows in {leaves} leaves: one row changed writes {} pages and computes \
         {hashes} hashes; its proof is {} bytes, {levels} levels, {rows} rows in its leaf",
        pages.len(),
        proof.len()
    );

    assert!(
        pages.len() < 8,
        "one changed row must rewrite under 8 pages: {pages:?}"
    );
    assert!(
        proof.len() < 4096,
        "the proof of one row must stay under 4096 bytes: {} bytes, {levels} levels, {rows} rows in its leaf",
        proof.len()
    );
    let path: Vec<u8> = (0..=levels as u8).rev().collect();
    assert_eq!(pages, path, "the leaf, then each ancestor up to the root");
    assert_eq!(hashes as usize, pages.len() + 1, "the row and each page");
    assert_eq!(proof.len(), expected, "the largest proof the walk found");
    let read = Proof::decode(&proof, 4096).unwrap();
    assert_eq!(read.root(sha256), Ok((changed, ROWS)));
    assert_eq!((read.key(), read.value()), (&target, &[0xA7; SEAT][..]));

    // The state before the change still stands, and proves the old row under the old root.
    assert_ne!(changed, root);
    assert_eq!(before.root(), root);
    assert_eq!(before.get(&target), Ok(Some(&old[..])));
    let earlier = before.prove(&target).unwrap().unwrap();
    assert_eq!(earlier.root(sha256), Ok((root, ROWS)));
    assert_eq!(earlier.value(), old);
}

#[test]
fn the_root_is_a_function_of_the_rows_whatever_order_set_and_removed_them() {
    for seed in 1..=16u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut model = BTreeMap::new();
        let mut map = Map::new(sha256, usize::MAX);
        for step in 1..=900 {
            let key = rng.crowded();
            if rng.below(3) == 0 {
                let removed = map.remove(&key).unwrap();
                assert_eq!(removed, model.remove(&key).is_some(), "seed {seed}");
            } else {
                let value = rng.value();
                map.set(key, &value).unwrap();
                model.insert(key, value);
            }
            if step % 150 != 0 {
                continue;
            }
            check(&map.root, Range::ROOT);
            let fresh = built(&model);
            assert_eq!(map.root(), fresh.root(), "seed {seed} step {step}");
            assert_eq!(map.len(), model.len() as u64);
            assert_eq!(map.retained_bytes(), fresh.retained_bytes());
            assert_eq!(
                map.written(&fresh),
                [],
                "seed {seed}: the same rows, the same pages"
            );
            let rows: Vec<_> = model
                .iter()
                .map(|(key, value)| (*key, value.clone()))
                .collect();
            assert_eq!(listed(&map, Range::ROOT, None), rows, "seed {seed}");
            for (key, value) in &model {
                assert_eq!(map.get(key), Ok(Some(&value[..])));
                let proof = map.prove(key).unwrap().unwrap();
                assert_eq!(proof.root(sha256), Ok((map.root(), map.len())));
            }
            assert_eq!(map.prove(&[0xEE; 32]), Ok(None));
        }
    }
}

#[test]
fn pages_and_roots_are_the_bytes_the_design_states() {
    let (empty_page, empty) = leaf_page(&[]);
    let mut map = Map::new(sha256, usize::MAX);
    assert_eq!(map.root(), empty);
    assert_eq!(map.page(Range::ROOT).unwrap(), empty_page);

    let first = [0x20; 32];
    map.set(first, b"abc").unwrap();
    let (page, named) = leaf_page(&[(first, b"abc")]);
    assert_eq!(page.len(), 8 + 32 + 2 + 3);
    assert_eq!((map.page(Range::ROOT).unwrap(), map.root()), (page, named));

    // 33 rows whose first bytes are 0x00..=0x20: sixteen under nibble 0, sixteen under
    // nibble 1, one under nibble 2, and thirteen empty children.
    let keys: Vec<Digest> = (0..33u8).map(|row| [row; 32]).collect();
    let values: Vec<Vec<u8>> = (0..33u8).map(|row| vec![row; usize::from(row)]).collect();
    let map = built(keys.iter().zip(&values));
    let rows: Vec<(Digest, &[u8])> = keys
        .iter()
        .copied()
        .zip(values.iter().map(|v| &v[..]))
        .collect();
    let mut children = [(empty, 0); 16];
    children[0] = (leaf_page(&rows[..16]).1, 16);
    children[1] = (leaf_page(&rows[16..32]).1, 16);
    children[2] = (leaf_page(&rows[32..]).1, 1);
    let page = interior_page(&children);
    assert_eq!(page.len(), 6 + 16 * 40);
    assert_eq!(map.root(), sha256(&page));
    assert_eq!(map.page(Range::ROOT).unwrap(), page);
    let second = Range::ROOT.children().unwrap()[1];
    assert_eq!(map.page(second).unwrap(), leaf_page(&rows[16..32]).0);
    assert_eq!(map.node(second), Ok(children[1]));
    assert_eq!(stored(&map).len(), 4, "the empty leaf is never written");
}

#[test]
fn a_map_opened_from_its_root_reads_each_page_once_and_takes_no_other_bytes() {
    let mut rng = Rng(7);
    let model: BTreeMap<Digest, Vec<u8>> = (0..700).map(|_| (rng.crowded(), rng.value())).collect();
    let full = built(&model);
    let store = stored(&full);
    let (root, rows) = (full.root(), full.len());
    let mut map = Map::from_root(sha256, usize::MAX, root, rows).unwrap();
    assert_eq!((map.root(), map.len()), (root, rows));
    assert_eq!(map.retained_bytes(), NODE);

    // One row, cold: the pages on its path and no more; warm: none.
    let (key, value) = model.iter().next().unwrap();
    assert_eq!(map.get(key), Err(Error::Missing(Range::ROOT, root)));
    let (found, cold) = fetching(&mut map, &store, |map| {
        Ok(map.get(key)?.map(<[u8]>::to_vec))
    });
    assert_eq!(found.as_ref(), Some(value));
    assert_eq!(cold, map.prove(key).unwrap().unwrap().levels.len() + 1);
    let (_, warm) = fetching(&mut map, &store, |map| {
        Ok(map.get(key)?.map(<[u8]>::to_vec))
    });
    assert_eq!(warm, 0);

    // A wrong page is refused wherever it is offered, and nothing changes.
    let Err(Error::Missing(range, hash)) = map.rows(Range::ROOT, Some(*key)).last().unwrap() else {
        panic!("a page of the listing is still to read");
    };
    let held = map.retained_bytes();
    let mut flipped = store[&hash].clone();
    *flipped.last_mut().unwrap() ^= 1;
    assert_eq!(map.admit(range, &flipped), Err(Error::Page));
    assert_eq!(map.admit(range, &store[&root]), Err(Error::Page));
    assert_eq!(map.admit(range, &store[&hash][1..]), Err(Error::Page));
    assert_eq!(map.admit(Range::ROOT, &store[&root]), Err(Error::Range));
    let inside = prefix(key, 60);
    assert_eq!(map.admit(inside, &store[&hash]), Err(Error::Range));
    assert_eq!(map.release(inside), Err(Error::Range));
    assert_eq!((map.root(), map.retained_bytes()), (root, held));

    // The whole listing reads every page exactly once, then the map is the full one.
    let mut read = cold;
    let mut rows = Vec::new();
    loop {
        let after = rows.last().map(|(key, _)| *key);
        let (page, pages) = fetching(&mut map, &store, |map| {
            map.rows(Range::ROOT, after)
                .take(50)
                .map(|row| row.map(|(key, value)| (*key, value.to_vec())))
                .collect::<Result<Vec<_>, _>>()
        });
        read += pages;
        if page.is_empty() {
            break;
        }
        rows.extend(page);
    }
    assert_eq!(rows, listed(&full, Range::ROOT, None));
    assert_eq!(read, store.len());
    check(&map.root, Range::ROOT);
    assert_eq!(map.retained_bytes(), full.retained_bytes());

    // Changes on a map with pages released match the same changes on the full one.
    let mut full = full;
    let mut cold = Map::from_root(sha256, usize::MAX, root, full.len()).unwrap();
    for _ in 0..600 {
        let key = rng.crowded();
        if rng.below(2) == 0 {
            let value = rng.value();
            full.set(key, &value).unwrap();
            fetching(&mut cold, &store, |map| map.set(key, &value));
        } else {
            let removed = full.remove(&key).unwrap();
            assert_eq!(
                fetching(&mut cold, &store, |map| map.remove(&key)).0,
                removed
            );
        }
    }
    check(&cold.root, Range::ROOT);
    assert_eq!((cold.root(), cold.len()), (full.root(), full.len()));
    assert!(cold.retained_bytes() <= full.retained_bytes());
}

#[test]
fn a_page_that_lies_about_its_rows_its_place_or_its_shape_is_refused() {
    let empty = leaf_page(&[]).1;
    let row = |first: u8| ([first; 32], &b"v"[..]);
    let open = |page: &[u8], named: Digest, rows: u64| {
        let mut map = Map::from_root(sha256, usize::MAX, named, rows).unwrap();
        (map.admit(Range::ROOT, page), map)
    };
    assert_eq!(
        Map::from_root(sha256, 0, [1; 32], 0).unwrap_err(),
        Error::Page
    );
    assert!(Map::from_root(sha256, 0, empty, 0).unwrap().is_empty());

    // Leaves: the rows the parent counts, in order, once each, at most 32, nothing after.
    let (page, named) = leaf_page(&[row(1), row(2)]);
    assert_eq!(open(&page, named, 2).0, Ok(()));
    assert_eq!(open(&page, named, 3).0, Err(Error::Page));
    assert_eq!(
        open(&[&page[..], &[0]].concat(), named, 2).0,
        Err(Error::Page)
    );
    assert_eq!(open(&page[..page.len() - 1], named, 2).0, Err(Error::Page));
    for rows in [
        vec![row(2), row(1)],
        vec![row(1), row(1)],
        (0..33).map(row).collect(),
    ] {
        let (page, named) = leaf_page(&rows);
        assert_eq!(open(&page, named, rows.len() as u64).0, Err(Error::Page));
    }
    let mut other = page.clone();
    other[4] = b'2';
    assert_eq!(open(&other, named, 2).0, Err(Error::Page));
    other[4..6].copy_from_slice(b"1\x03");
    assert_eq!(open(&other, named, 2).0, Err(Error::Page));

    // Interiors: more than 32 rows, the children's counts adding up to them, and a
    // child with no rows named as the empty leaf.
    let child = leaf_page(&[row(0x10)]);
    let mut children = [(empty, 0); 16];
    children[1] = (child.1, 1);
    children[2] = ([9; 32], 40);
    let page = interior_page(&children);
    let (admitted, mut map) = open(&page, sha256(&page), 41);
    assert_eq!(admitted, Ok(()));
    assert_eq!(open(&page, sha256(&page), 42).0, Err(Error::Page));
    assert_eq!(open(&page, [3; 32], 41).0, Err(Error::Page));
    let mut small = children;
    small[2].1 = 31;
    let page = interior_page(&small);
    assert_eq!(open(&page, sha256(&page), 32).0, Err(Error::Page));
    let mut unnamed = children;
    unnamed[5].0 = [7; 32];
    let page = interior_page(&unnamed);
    assert_eq!(open(&page, sha256(&page), 41).0, Err(Error::Page));
    let mut wrapped = children;
    wrapped[3].1 = u64::MAX;
    let page = interior_page(&wrapped);
    assert_eq!(open(&page, sha256(&page), 40).0, Err(Error::Page));

    // The empty leaf's name with rows under it, at a root or in a page, names nothing.
    assert_eq!(
        Map::from_root(sha256, 0, empty, 5).unwrap_err(),
        Error::Page
    );
    let mut hollow = children;
    hollow[4] = (empty, 7);
    let page = interior_page(&hollow);
    assert_eq!(open(&page, sha256(&page), 48).0, Err(Error::Page));

    // A child cannot count more rows than there are keys under it: sixteen, one nibble
    // from the end of the key. The pages above it are a chain down one key's path.
    for (counts, answer) in [([16, 16, 16], Ok(())), ([20, 12, 16], Err(Error::Page))] {
        let mut children = [(empty, 0); 16];
        for (child, count) in children.iter_mut().zip(counts) {
            *child = ([9; 32], count);
        }
        let mut pages = vec![interior_page(&children)];
        for _ in 0..62 {
            let mut children = [(empty, 0); 16];
            children[5] = (sha256(pages.last().unwrap()), 48);
            pages.push(interior_page(&children));
        }
        pages.reverse();
        let mut map = Map::from_root(sha256, usize::MAX, sha256(&pages[0]), 48).unwrap();
        for (depth, page) in pages.iter().enumerate() {
            let admitted = map.admit(prefix(&[0x55; 32], depth), page);
            assert_eq!(
                admitted,
                if depth < 62 { Ok(()) } else { answer },
                "depth {depth}"
            );
        }
        check(&map.root, Range::ROOT);
    }

    // A map that counts u64::MAX rows takes no new row, and still changes the ones it has.
    let mut children = [(empty, 0); 16];
    children[1] = (child.1, 1);
    children[2] = ([9; 32], u64::MAX - 1);
    let page = interior_page(&children);
    let (_, mut most) = open(&page, sha256(&page), u64::MAX);
    most.admit(Range::ROOT.children().unwrap()[1], &child.0)
        .unwrap();
    let before = (most.root(), most.len(), most.retained_bytes());
    assert_eq!(most.set([0x11; 32], b"w"), Err(Error::Count));
    assert_eq!((most.root(), most.len(), most.retained_bytes()), before);
    assert_eq!(most.set([0x10; 32], b"w"), Ok(()));
    assert_eq!(most.remove(&[0x10; 32]), Ok(true));
    assert_eq!(most.set([0x11; 32], b"w"), Ok(()));
    assert_eq!(most.len(), u64::MAX);

    // A leaf whose row belongs under another child is not that child's page.
    let ranges = Range::ROOT.children().unwrap();
    let astray = leaf_page(&[row(0x30)]);
    let mut children = [(empty, 0); 16];
    children[1] = (astray.1, 1);
    children[2] = ([9; 32], 40);
    let page = interior_page(&children);
    let (_, mut lied) = open(&page, sha256(&page), 41);
    assert_eq!(lied.admit(ranges[1], &astray.0), Err(Error::Page));
    assert_eq!(map.admit(ranges[1], &child.0), Ok(()));
    assert_eq!(map.get(&[0x10; 32]), Ok(Some(&b"v"[..])));
    assert_eq!(
        map.get(&[0x20; 32]),
        Err(Error::Missing(ranges[2], [9; 32]))
    );
    check(&map.root, Range::ROOT);
}

#[test]
fn a_byte_budget_refuses_growth_and_releasing_stored_pages_makes_room() {
    for seed in 1..=8u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let budget = 15_000 + 5_000 * seed as usize;
        let mut map = Map::new(sha256, budget);
        let mut model = BTreeMap::new();
        let mut refused = 0;
        for step in 0..1_500u64 {
            let key = rng.crowded();
            let value = rng.value();
            let before = (map.root(), map.retained_bytes(), map.len());
            match map.set(key, &value) {
                Ok(()) => {
                    model.insert(key, value);
                }
                Err(error) => {
                    assert_eq!(error, Error::Budget, "seed {seed}");
                    assert_eq!((map.root(), map.retained_bytes(), map.len()), before);
                    refused += 1;
                    // Shrinking is never refused.
                    if let Some(old) = model.get_mut(&key).filter(|old| !old.is_empty()) {
                        old.pop();
                        map.set(key, old).unwrap();
                    }
                }
            }
            assert!(map.retained_bytes() <= budget, "seed {seed} step {step}");
        }
        assert!(
            refused > 100,
            "seed {seed}: the budget was reached, {refused}"
        );
        check(&map.root, Range::ROOT);
        assert_eq!(map.root(), built(&model).root(), "seed {seed}");

        // Store the pages, release one child of the root, and there is room again.
        let store = stored(&map);
        let ranges = Range::ROOT.children().unwrap();
        let (held, root) = (map.retained_bytes(), map.root());
        map.release(ranges[0]).unwrap();
        assert!(map.retained_bytes() < held, "seed {seed}");
        assert_eq!(map.root(), root);
        let far = [0xF0; 32];
        map.set(far, &[1; 64]).unwrap();
        model.insert(far, vec![1; 64]);
        assert_eq!(map.root(), built(&model).root());
        let gone = map.get(&[0; 32]).unwrap_err();
        assert_eq!(
            gone,
            Error::Missing(ranges[0], map.node(ranges[0]).unwrap().0)
        );
        map.release(ranges[0]).unwrap();

        // A page is admitted against the same budget.
        let mut tight = Map::from_root(sha256, 3 * NODE, root, model.len() as u64 - 1).unwrap();
        assert_eq!(tight.admit(Range::ROOT, &store[&root]), Err(Error::Budget));
        assert_eq!(tight.retained_bytes(), NODE);
        assert_eq!(tight.budget(), 3 * NODE);
    }
    // The key that splits a leaf costs its row and sixteen children for each page the
    // split adds, known to the byte before anything changes.
    for shared in [0, 3, 20] {
        let keys = sharing(shared);
        let whole = built(keys.iter().zip(&vec![vec![7u8; 5]; 33])).retained_bytes();
        for (budget, answer) in [(whole - 1, Err(Error::Budget)), (whole, Ok(()))] {
            let mut map = Map::new(sha256, budget);
            for key in &keys[..32] {
                map.set(*key, &[7; 5]).unwrap();
            }
            assert_eq!(
                map.set(keys[32], &[7; 5]),
                answer,
                "{shared} shared nibbles"
            );
            assert_eq!(map.retained_bytes() == whole, answer.is_ok());
            check(&map.root, Range::ROOT);
        }
    }
    let mut map = Map::new(sha256, usize::MAX);
    assert_eq!(map.set([0; 32], &[0; VALUE_BYTES + 1]), Err(Error::Value));
    assert_eq!(map.set([0; 32], &[0; VALUE_BYTES]), Ok(()));
    assert_eq!(
        map.prove(&[0; 32]).unwrap().unwrap().root(sha256),
        Ok((map.root(), 1))
    );
}

#[test]
fn a_proof_folds_to_one_root_and_a_hostile_one_is_refused_before_it_is_read() {
    let mut rng = Rng(11);
    let model: BTreeMap<Digest, Vec<u8>> = (0..500).map(|_| (rng.crowded(), rng.value())).collect();
    let map = built(&model);
    let answer = Ok((map.root(), map.len()));
    for (key, value) in model.iter().step_by(7) {
        let proof = map.prove(key).unwrap().unwrap();
        let bytes = proof.encode();
        let levels = proof.levels.len();
        assert_eq!(
            bytes.len(),
            42 + value.len() + 32 * proof.others.len() + 600 * levels
        );
        let read = Proof::decode(&bytes, bytes.len()).unwrap();
        assert_eq!(read, proof);
        assert_eq!(read.root(sha256), answer);

        // Any one byte changed is another proof of another root, or no proof.
        for at in (0..bytes.len())
            .step_by(13)
            .chain([5, 6, 7, bytes.len() - 1])
        {
            let mut changed = bytes.clone();
            changed[at] ^= 0x10;
            let folded = Proof::decode(&changed, usize::MAX).and_then(|proof| proof.root(sha256));
            assert_ne!(folded, answer, "byte {at} of {}", bytes.len());
        }
        assert_eq!(Proof::decode(&bytes, bytes.len() - 1), Err(Error::Budget));
        assert_eq!(Proof::decode(&bytes[1..], usize::MAX), Err(Error::Proof));
        assert_eq!(
            Proof::decode(&[&bytes[..], &[0]].concat(), usize::MAX),
            Err(Error::Proof)
        );
    }

    // A header is judged alone: 65 levels, no row, 33 rows, or a place past the leaf.
    let key = *model.keys().next().unwrap();
    let bytes = map.prove(&key).unwrap().unwrap().encode();
    let (levels, rows) = (usize::from(bytes[5]), usize::from(bytes[6]));
    let hostile = [
        (5, 65, 600 * (65 - levels)),
        (6, 0, 0),
        (6, 33, 32 * (33 - rows)),
        (7, 32, 0),
    ];
    for (at, value, grown) in hostile {
        let mut hostile = bytes.clone();
        hostile[at] = value;
        hostile.resize(bytes.len() + grown, 0);
        assert_eq!(
            Proof::decode(&hostile, usize::MAX),
            Err(Error::Proof),
            "byte {at}"
        );
    }
    assert_eq!(Proof::decode(&bytes[..41], usize::MAX), Err(Error::Proof));
    let mut alone = built([(&key, &vec![1u8])])
        .prove(&key)
        .unwrap()
        .unwrap()
        .encode();
    alone[7] = 1;
    assert_eq!(
        Proof::decode(&alone, usize::MAX),
        Err(Error::Proof),
        "a place past one row"
    );
    let mut proof = map.prove(&key).unwrap().unwrap();
    proof.levels[0][0].1 = u64::MAX;
    assert_eq!(proof.root(sha256), Err(Error::Count));
    // The same bounds hold for a proof that was never decoded.
    let mut deep = map.prove(&key).unwrap().unwrap();
    deep.levels = vec![deep.levels[0]; 65];
    assert_eq!(deep.root(sha256), Err(Error::Proof));
    let mut wide = map.prove(&key).unwrap().unwrap();
    (wide.others, wide.at) = (vec![[3; 32]; 32], 0);
    assert_eq!(wide.root(sha256), Err(Error::Proof));

    // A changed map has another root; the old proof still folds to the old one.
    let old = map.prove(&key).unwrap().unwrap();
    let mut next = map.clone();
    next.set(key, b"changed").unwrap();
    assert_eq!(old.root(sha256), answer);
    assert_ne!(Ok((next.root(), next.len())), answer);
    assert_eq!(
        next.prove(&key).unwrap().unwrap().root(sha256),
        Ok((next.root(), next.len()))
    );
}

/// At every depth toward `toward`: the range's count and rows are the model's, a range
/// of at most 32 rows names the page those rows alone would make, and a listing in
/// pages of seven, each continuing after the last key of the one before, is the same rows.
fn ranges_agree(map: &Map, model: &BTreeMap<Digest, Vec<u8>>, toward: &Digest) {
    for depth in 0..=64 {
        let range = prefix(toward, depth);
        let within: Vec<_> = model
            .iter()
            .filter(|(key, _)| range.contains(key))
            .map(|(key, value)| (*key, value.clone()))
            .collect();
        let (hash, rows) = map.node(range).unwrap();
        assert_eq!(rows, within.len() as u64, "depth {depth}");
        assert_eq!(listed(map, range, None), within, "depth {depth}");
        if within.len() <= LEAF_ROWS {
            let alone = built(within.iter().map(|(key, value)| (key, value)));
            assert_eq!(hash, alone.root(), "depth {depth}");
            assert_eq!(map.page(range), alone.page(Range::ROOT));
            assert_eq!(alone.node(range), Ok((hash, rows)), "depth {depth}");
        }
        let mut paged = Vec::new();
        loop {
            let after = paged.last().map(|(key, _)| *key);
            let page: Vec<_> = listed(map, range, after).into_iter().take(7).collect();
            if page.is_empty() {
                break;
            }
            paged.extend(page);
        }
        assert_eq!(paged, within, "depth {depth}");
    }
}

#[test]
fn a_range_names_the_page_its_rows_alone_would_make_and_lists_them_in_pages() {
    let mut rng = Rng(3);
    let model: BTreeMap<Digest, Vec<u8>> = (0..400).map(|_| (rng.crowded(), rng.value())).collect();
    let map = built(&model);
    let first = *model.keys().next().unwrap();
    ranges_agree(&map, &model, &first);
    // The same rows under 0x0, and far more rows elsewhere: another shape above them.
    let mut wider = map.clone();
    for row in 0..2_000 {
        let mut key = key(row);
        key[0] |= 0x20;
        wider.set(key, b"elsewhere").unwrap();
    }
    for depth in 1..=64 {
        let range = prefix(&first, depth);
        assert_eq!(wider.node(range), map.node(range), "depth {depth}");
    }

    // The top of the key space, where a range has no upper end to compare with.
    let mut model = BTreeMap::new();
    for row in 0..40u8 {
        let mut near = [0xFF; 32];
        near[31] = 0xD8 + row;
        let mut far = [0; 32];
        (far[0], far[31]) = (0xFF, row);
        model.insert(near, vec![row; 3]);
        model.insert(far, vec![row; 2]);
    }
    let map = built(&model);
    ranges_agree(&map, &model, &[0xFF; 32]);
    let mut last = [0xFF; 32];
    last[31] = 0xFE;
    assert_eq!(
        listed(&map, Range::ROOT, Some(last)),
        [([0xFF; 32], vec![39; 3])]
    );
    assert!(listed(&map, Range::ROOT, Some([0xFF; 32])).is_empty());
}

/// 33 rows whose keys are one byte repeated, 0x00..=0x20, five bytes each: a root page
/// over leaves of sixteen, sixteen and one rows.
fn three_leaves() -> (Map, Vec<Digest>, [Range; 16]) {
    let keys: Vec<Digest> = (0..33u8).map(|row| [row; 32]).collect();
    let map = built(keys.iter().zip(&vec![vec![7u8; 5]; 33]));
    (map, keys, Range::ROOT.children().unwrap())
}

#[test]
fn a_page_not_held_is_named_by_whatever_needs_it_and_listing_stops_there() {
    let (full, keys, ranges) = three_leaves();
    let (root, whole) = (full.root(), full.retained_bytes());
    let store = stored(&full);
    let first = full.node(ranges[0]).unwrap().0;

    // Nothing held: every question that must read the root page names it.
    let mut cold = Map::from_root(sha256, usize::MAX, root, 33).unwrap();
    let missing = Err(Error::Missing(Range::ROOT, root));
    assert_eq!(cold.prove(&keys[0]), Err(Error::Missing(Range::ROOT, root)));
    assert_eq!(cold.node(ranges[0]), Err(Error::Missing(Range::ROOT, root)));
    assert_eq!(cold.page(ranges[0]), Err(Error::Missing(Range::ROOT, root)));
    assert_eq!(cold.admit(ranges[0], &store[&first]), missing);
    assert_eq!(cold.release(ranges[0]), missing);
    assert_eq!(cold.node(Range::ROOT), Ok((root, 33)));

    // One leaf released: what is under it names it, what is beside it does not.
    let mut map = full.clone();
    map.release(ranges[0]).unwrap();
    check(&map.root, Range::ROOT);
    assert_eq!(map.retained_bytes(), whole - 16 * (ROW + 5));
    let missing = Error::Missing(ranges[0], first);
    assert_eq!(map.page(ranges[0]), Err(missing));
    assert_eq!(map.prove(&keys[0]), Err(missing));
    assert_eq!(map.node(ranges[0].children().unwrap()[3]), Err(missing));
    assert_eq!(map.node(ranges[0]), Ok((first, 16)));
    assert_eq!(listed(&map, ranges[1], None).len(), 16);
    let after: Vec<Digest> = listed(&map, Range::ROOT, Some(keys[16]))
        .into_iter()
        .map(|row| row.0)
        .collect();
    assert_eq!(after, keys[17..]);
    let listing: Vec<_> = map.rows(Range::ROOT, None).collect();
    assert_eq!(listing, [Err(missing)]);

    // A store is asked for the pages still held; a range with no rows has no page to
    // release, and takes a row afterwards.
    let asked: Vec<Range> = map
        .written(&Map::new(sha256, 0))
        .into_iter()
        .map(|(range, _)| range)
        .collect();
    assert_eq!(asked, [ranges[1], ranges[2], Range::ROOT]);
    map.release(ranges[5]).unwrap();
    assert_eq!(map.get(&[0x50; 32]), Ok(None));
    assert_eq!(map.set([0x50; 32], b"v"), Ok(()));
    check(&map.root, Range::ROOT);

    // Each page admitted is charged against the budget, the unheld ones a node each.
    for (budget, last) in [(whole, Ok(())), (whole - 1, Err(Error::Budget))] {
        let mut map = Map::from_root(sha256, budget, root, 33).unwrap();
        map.admit(Range::ROOT, &store[&root]).unwrap();
        for range in &ranges[..2] {
            map.admit(
                *range,
                &map.node(*range)
                    .map(|(hash, _)| store[&hash].clone())
                    .unwrap(),
            )
            .unwrap();
        }
        let before = map.retained_bytes();
        let third = &store[&map.node(ranges[2]).unwrap().0];
        assert_eq!(map.admit(ranges[2], third), last);
        assert_eq!(
            map.retained_bytes(),
            if last.is_ok() { whole } else { before }
        );
        check(&map.root, Range::ROOT);
    }

    // A root kept without its count opens from its root page, which states it.
    let opened = Map::open(sha256, usize::MAX, root, &store[&root]).unwrap();
    assert_eq!((opened.root(), opened.len()), (root, 33));
    assert_eq!(
        opened.get(&keys[32]),
        Err(Error::Missing(ranges[2], full.node(ranges[2]).unwrap().0))
    );
    assert_eq!(
        Map::open(sha256, usize::MAX, root, &store[&first]).unwrap_err(),
        Error::Page
    );
    assert_eq!(
        Map::open(sha256, 2 * NODE, root, &store[&root]).unwrap_err(),
        Error::Budget
    );
    let small = built(keys.iter().take(3).zip(&vec![vec![1u8]; 3]));
    let leaf = small.page(Range::ROOT).unwrap();
    let opened = Map::open(sha256, usize::MAX, small.root(), &leaf).unwrap();
    assert_eq!(
        (opened.len(), opened.get(&keys[2])),
        (3, Ok(Some(&[1u8][..])))
    );
    let (page, empty) = leaf_page(&[]);
    assert!(Map::open(sha256, 0, empty, &page).unwrap().is_empty());
    assert_eq!(
        Map::open(sha256, 0, empty, &interior_page(&[(empty, 0); 16])).unwrap_err(),
        Error::Page
    );
}

#[test]
fn a_store_is_asked_to_write_only_the_pages_it_lacks() {
    let mut rng = Rng(7);
    let model: BTreeMap<Digest, Vec<u8>> = (0..700).map(|_| (rng.crowded(), rng.value())).collect();
    let full = built(&model);
    let store = stored(&full);
    let count = |map: &Map, base: &Map| map.written(base);

    // A map read from the store page by page has nothing to write, and one row changed
    // in it writes the leaf and its ancestors, not the pages it read to get there.
    let base = Map::from_root(sha256, usize::MAX, full.root(), full.len()).unwrap();
    let mut map = base.clone();
    let read = fetching(&mut map, &store, |map| {
        map.rows(Range::ROOT, None)
            .try_for_each(|row| row.map(|_| ()))
    });
    assert_eq!(read.1, store.len());
    assert!(count(&map, &base).is_empty());
    let key = *model.keys().nth(300).unwrap();
    let levels = map.prove(&key).unwrap().unwrap().levels.len();
    map.set(key, b"changed").unwrap();
    let pages = count(&map, &base);
    assert_eq!(pages.len(), levels + 1, "{pages:?}");
    assert!(
        pages.iter().all(|(_, hash)| !store.contains_key(hash)),
        "{pages:?}"
    );
    assert_eq!(pages.last(), Some(&(Range::ROOT, map.root())));
    // The same against the state before the change, held in memory.
    assert_eq!(count(&map, &full).len(), levels + 1);
    let mut next = full.clone();
    next.set(key, b"changed").unwrap();
    assert_eq!(count(&next, &full), pages);
    assert!(count(&next, &next.clone()).is_empty());

    // Each state's pages are named by its own hash, whatever the other's is.
    fn other(bytes: &[u8]) -> Digest {
        let mut hash = sha256(bytes);
        hash[0] ^= 1;
        hash
    }
    let mut theirs = Map::new(other, usize::MAX);
    let mut fresh = Map::new(other, usize::MAX);
    for map in [&mut theirs, &mut fresh] {
        map.set(key, b"changed").unwrap();
    }
    assert_eq!(count(&next, &theirs).len(), store.len());
    assert_eq!(theirs.root(), fresh.root());
}

#[test]
fn keys_that_share_a_prefix_deepen_one_path_and_removing_one_folds_it_back() {
    for shared in [0, 1, 10, 31, 62] {
        let keys = sharing(shared);
        let values = vec![vec![1u8; 8]; 33];
        let mut map = built(keys.iter().zip(&values));
        check(&map.root, Range::ROOT);
        // One interior page for each shared nibble and one where the keys part.
        let proof = map.prove(&keys[0]).unwrap().unwrap();
        assert_eq!(proof.levels.len(), shared + 1, "{shared} shared nibbles");
        let bytes = proof.encode();
        assert_eq!(
            Proof::decode(&bytes, bytes.len()).unwrap().root(sha256),
            Ok((map.root(), 33))
        );
        let interior = map
            .written(&Map::new(sha256, 0))
            .iter()
            .filter(|(range, _)| map.node(*range).unwrap().1 > LEAF_ROWS as u64)
            .count();
        assert_eq!(interior, shared + 1);
        assert_eq!(map.node(prefix(&keys[0], shared)).unwrap().1, 33);

        // 32 rows are one leaf again, whichever row leaves.
        let all = map.clone();
        for gone in [0, 16, 32] {
            let mut map = all.clone();
            assert_eq!(map.remove(&keys[gone]), Ok(true));
            assert_eq!(map.remove(&keys[gone]), Ok(false));
            let left = keys
                .iter()
                .zip(&values)
                .filter(|(key, _)| **key != keys[gone]);
            let fresh = built(left);
            assert_eq!(
                (map.root(), map.retained_bytes()),
                (fresh.root(), fresh.retained_bytes())
            );
            assert_eq!(map.prove(&keys[1]).unwrap().unwrap().levels.len(), 0);
            check(&map.root, Range::ROOT);
        }
        // Folding needs every row of the leaf it makes: a released child is named.
        let store = stored(&map);
        let parted = prefix(&keys[0], shared);
        let child = parted.children().unwrap()[nibble(&keys[32], shared)];
        map.release(child).unwrap();
        let missing = map.node(child).unwrap().0;
        assert_eq!(map.remove(&keys[0]), Err(Error::Missing(child, missing)));
        assert_eq!(map.len(), 33);
        assert!(fetching(&mut map, &store, |map| map.remove(&keys[0])).0);
        check(&map.root, Range::ROOT);
    }
}
