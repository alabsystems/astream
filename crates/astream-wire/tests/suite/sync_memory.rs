// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The memory an `astream_wire::sync::Index` holds while it reads a store whose headers come
//! back owned, as a store on disk returns them: opening one, finding its forks, rebuilding its
//! tracker, asking the tracked fields under exclusions, and holding records without a tracker.
//! Each test counts the bytes its own thread holds allocated at once ([`peak`]), so tests on
//! other threads add nothing to it.

use astream_wire::sync::{Actor, Digest, Header, Headers, Index, Retained, Unwritten};
use std::alloc::{GlobalAlloc, Layout, System};
use std::borrow::Cow;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

thread_local! {
    /// Whether this thread's allocations are counted.
    static WATCH: Cell<bool> = const { Cell::new(false) };
    /// Bytes this thread allocated less bytes it freed since counting began.
    static LIVE: Cell<i64> = const { Cell::new(0) };
    /// The most `LIVE` has been since counting began.
    static TOP: Cell<i64> = const { Cell::new(0) };
}

/// Add `delta` to this thread's count, if it is counting.
fn note(delta: i64) {
    let _ = WATCH.try_with(|watch| {
        if watch.get() {
            let live = LIVE.get() + delta;
            LIVE.set(live);
            TOP.set(TOP.get().max(live));
        }
    });
}

/// The system allocator, counting what a watching thread allocates and frees.
struct Counting;

// SAFETY: every method forwards its arguments unchanged to `System`, which upholds
// `GlobalAlloc`'s contract; the count is bookkeeping beside it and never touches memory.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract for `alloc` is `System.alloc`'s.
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            note(layout.size() as i64);
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract for `alloc_zeroed` is `System.alloc_zeroed`'s.
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            note(layout.size() as i64);
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from this allocator (so from `System`) with `layout`.
        unsafe { System.dealloc(ptr, layout) };
        note(-(layout.size() as i64));
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: `ptr` came from this allocator (so from `System`) with `layout`, and the
        // caller's contract for `new_size` is `System.realloc`'s.
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            note(new_size as i64 - layout.size() as i64);
        }
        p
    }
}

#[global_allocator]
static COUNTING: Counting = Counting;

/// `f`'s result and the most bytes this thread held allocated at once while it ran, above what
/// it held when `f` began.
fn peak<T>(f: impl FnOnce() -> T) -> (T, i64) {
    LIVE.set(0);
    TOP.set(0);
    WATCH.set(true);
    let out = f();
    WATCH.set(false);
    (out, TOP.get())
}

/// A store that answers every header owned, as one that reads them from disk does.
#[derive(Default)]
struct Owned(Retained);

impl Headers for Owned {
    fn header(&self, id: &Digest) -> Option<Cow<'_, Header>> {
        self.0.get(id).cloned().map(Cow::Owned)
    }
    fn contains(&self, id: &Digest) -> bool {
        self.0.contains(id)
    }
    fn at(&self, actor: &Actor, sequence: u64) -> Option<Digest> {
        self.0.at(actor, sequence)
    }
    fn children(&self, id: &Digest) -> impl Iterator<Item = Digest> + '_ {
        self.0.children(id)
    }
    fn headers(&self) -> impl Iterator<Item = Cow<'_, Header>> + '_ {
        self.0.values().cloned().map(Cow::Owned)
    }
    fn len(&self) -> usize {
        self.0.len()
    }
    fn put(&mut self, header: Header) -> Result<(), Unwritten> {
        self.0.put(header)
    }
}

fn digest(n: u64) -> Digest {
    let mut id = [0; 32];
    // The first byte permutes the rows, so digest order is not causal order.
    id[0] = (n * 89 % 251) as u8;
    id[1..9].copy_from_slice(&n.to_be_bytes());
    id
}

/// `records` headers by four actors in dense chains, each naming its predecessor and up to
/// `width - 1` of the records just before it, so each header owns about `32 * width` bytes of
/// parents.
fn chains(records: u64, width: u64) -> Vec<Header> {
    let mut tips: BTreeMap<u8, (u64, Digest)> = BTreeMap::new();
    let mut out = Vec::new();
    for n in 0..records {
        let actor = (n % 4) as u8;
        let (sequence, previous) = match tips.get(&actor) {
            Some((sequence, tip)) => (sequence + 1, Some(*tip)),
            None => (1, None),
        };
        let mut parents: BTreeSet<Digest> = (n.saturating_sub(width - 1)..n).map(digest).collect();
        parents.extend(previous);
        let header = Header {
            id: digest(n),
            actor: [actor; 48],
            sequence,
            previous,
            parents: parents.into_iter().collect(),
        };
        tips.insert(actor, (sequence, header.id));
        out.push(header);
    }
    out
}

/// A store holding `headers`.
fn owned(headers: &[Header]) -> Owned {
    let mut store = Owned::default();
    for header in headers {
        assert_eq!(store.put(header.clone()), Ok(()));
    }
    // The store's own maps by dot and by parent are built here, not in what a test measures.
    let _ = store.at(&[0; 48], 1);
    let _ = store.children(&[0; 32]).count();
    store
}

/// Opening an index over 4,000 owned headers of about 2 KB each, and asking its forks when
/// there are none, each hold at most 16 KB, a few headers: neither keeps the headers it reads
/// (measured: 2,648 and 4,032 bytes). Rebuilding its tracker holds at most 400 bytes a record,
/// its own maps and not the 2 KB headers (measured: 391,104 bytes, 98 a record).
/// NEGATIVE CONTROLS, observed with the code before this test: `with_store` rebuilding the
/// tracker by collecting `store.headers()` into a vector: `with_store: 8983336 bytes`; with
/// that removed, `Index::forks` collecting every header: `forks: 8641504 bytes`.
#[test]
fn an_index_over_owned_headers_holds_one_header_at_a_time() {
    let store = owned(&chains(4000, 64));
    let (index, opened) = peak(|| Index::with_store(store, u64::MAX));
    let (forks, found) = peak(|| index.forks());
    assert!(forks.is_empty());
    let (pending, rebuilt) = peak(|| index.tracker().pending().len());
    assert_eq!(pending, 0);
    assert!(opened <= 16_384, "with_store: {opened} bytes");
    assert!(found <= 16_384, "forks: {found} bytes");
    assert!(rebuilt <= 400 * 4000, "tracker rebuild: {rebuilt} bytes");
}

/// An index of 2,000 discharged records by four actors and 2,000 pending records, each of an
/// actor of its own and naming a parent that never arrives.
fn half_pending() -> Index {
    let mut index = Index::with_budget(u64::MAX);
    for header in chains(2000, 3) {
        assert_eq!(index.insert(header), Ok(true));
    }
    for n in 0..2000_u64 {
        let mut actor = [9; 48];
        actor[..8].copy_from_slice(&n.to_be_bytes());
        let mut missing = [0xEE; 32];
        missing[1..9].copy_from_slice(&n.to_be_bytes());
        let header = Header {
            id: digest(10_000 + n),
            actor,
            sequence: 1,
            previous: None,
            parents: Vec::from([missing]),
        };
        assert_eq!(index.insert(header), Ok(true));
    }
    index
}

/// The tracked fields under no exclusion, and under the exclusion of one head, cost at most
/// 8 KB however many records are pending: here 2,000 are (measured: 0 and 3,984 bytes).
/// NEGATIVE CONTROL: with `Tracker::excluding` starting from a clone of the whole tracker (the
/// code before this test): `no exclusion: 158608 bytes`.
#[test]
fn the_tracked_fields_under_exclusions_cost_what_the_exclusion_withdraws() {
    let index = half_pending();
    assert_eq!(index.tracker().pending().len(), 2000);
    let leaf = digest(1999);
    assert!(index.tracker().heads().contains(&leaf));
    let (_, none) = peak(|| index.tracked_excluding(&BTreeSet::new()));
    let excluded = BTreeSet::from([leaf]);
    let (_, one) = peak(|| index.tracked_excluding(&excluded));
    assert!(none <= 8192, "no exclusion: {none} bytes");
    assert!(one <= 8192, "one head excluded: {one} bytes");
}

/// An index whose tracker nobody reads holds its records and little else: inserting 4,000
/// headers holds at most an eighth more than a map of the same headers by id, the map the index
/// held before it had a tracker.
/// (measured: 1,547,328 bytes against 1,546,696).
/// NEGATIVE CONTROL: with `Index::insert` feeding a tracker built at `with_budget`, and the
/// store keeping its maps by dot and by parent from the first record (the code before this
/// test): `index 3088416 bytes, map 1546696 bytes`.
#[test]
fn an_index_that_never_reads_its_tracker_holds_about_what_a_map_of_its_headers_holds() {
    let headers = chains(4000, 3);
    let (_, map) = peak(|| {
        let mut map = BTreeMap::new();
        for header in &headers {
            map.insert(header.id, header.clone());
        }
        map
    });
    let (_, index) = peak(|| {
        let mut index = Index::with_budget(u64::MAX);
        for header in &headers {
            assert_eq!(index.insert(header.clone()), Ok(true));
        }
        index
    });
    assert!(
        index <= map + map / 8,
        "index {index} bytes, map {map} bytes"
    );
}
