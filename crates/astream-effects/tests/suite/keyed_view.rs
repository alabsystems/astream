// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `effects.keyed-view`: a [`KeyedView`] answers "what had this door
//! replied to this request once the program had read N records?" with the LATEST
//! matching exchange among those N — never a later one, and never the record a
//! replay that has read N is about to read — and a miss is a typed `Unrecorded`,
//! never a live call. Lookups never consume and never depend on the order they are
//! asked in (every lookup here is asked forwards, backwards and twice, with the
//! same answers), only `Exchange` records are indexed, and the view leaves the
//! tape untouched for an in-order replay beside it.

use std::sync::Arc;

use astream_effects::{
    converse, EffectRecord, EffectSeam, EffectsLog, KeyedIndex, KeyedReply, KeyedView,
    ReplayDivergence, ReplaySeam,
};

fn exchange(door: &str, request: &str, reply: &str) -> EffectRecord {
    EffectRecord::Exchange {
        door: door.into(),
        request: request.as_bytes().to_vec(),
        reply: reply.as_bytes().to_vec(),
    }
}

/// A tape where one question is asked three times with three answers, beside
/// other doors, other requests, and records of other kinds that carry the same
/// bytes.
fn tape() -> Vec<EffectRecord> {
    vec![
        EffectRecord::Mono(10),                  // 0
        exchange("probe.git", "/repo", "clean"), // 1
        exchange("ctl", "status", "idle"),       // 2
        EffectRecord::Emit {
            door: "probe.git".into(),
            bytes: b"/repo".to_vec(),
        }, // 3: same door and bytes as a request, but an output
        exchange("probe.git", "/repo", "dirty"), // 4
        exchange("probe.git", "/other", "clean"), // 5
        EffectRecord::Raised {
            door: "stop".into(),
            false_reads: 0,
        }, // 6
        exchange("ctl", "/repo", "not a git answer"), // 7: same request, other door
        exchange("probe.git", "/repo", "conflicted"), // 8
    ]
}

/// Every (door, request, seen) a test asks, with the answer expected:
/// `Some((position, reply))` or `None` for `Unrecorded`.
type Case = (
    &'static str,
    &'static str,
    usize,
    Option<(usize, &'static str)>,
);

const CASES: &[Case] = &[
    // Nothing read: the tape knows nothing yet.
    ("probe.git", "/repo", 0, None),
    // Only the record before the first exchange read: the exchange at 1 is
    // the NEXT record, not yet an answer.
    ("probe.git", "/repo", 1, None),
    // Once the first exchange is read, and until the second is.
    ("probe.git", "/repo", 2, Some((1, "clean"))),
    ("probe.git", "/repo", 4, Some((1, "clean"))),
    // The latest among what was read: the second answer once 4 is read, the
    // third once 8 is.
    ("probe.git", "/repo", 5, Some((4, "dirty"))),
    ("probe.git", "/repo", 8, Some((4, "dirty"))),
    ("probe.git", "/repo", 9, Some((8, "conflicted"))),
    // Past the end means anywhere: the last answer.
    ("probe.git", "/repo", usize::MAX, Some((8, "conflicted"))),
    // Another request through the same door, and the same request through
    // another door, are other questions.
    ("probe.git", "/other", 9, Some((5, "clean"))),
    ("probe.git", "/other", 5, None),
    ("ctl", "/repo", 9, Some((7, "not a git answer"))),
    ("ctl", "status", 9, Some((2, "idle"))),
    // Never asked at all.
    ("probe.git", "/nowhere", usize::MAX, None),
    ("teller", "status", usize::MAX, None),
    // Outputs and flags are not answers.
    ("stop", "", usize::MAX, None),
];

fn ask(view: &KeyedView<'_>, case: &Case) -> Result<(usize, Vec<u8>), ReplayDivergence> {
    let (door, request, at, _) = *case;
    view.lookup(door, request.as_bytes(), at)
        .map(|KeyedReply { position, reply }| (position, reply.to_vec()))
}

fn expected(case: &Case) -> Result<(usize, Vec<u8>), ReplayDivergence> {
    let (door, request, _, want) = *case;
    want.map(|(p, r)| (p, r.as_bytes().to_vec()))
        .ok_or(ReplayDivergence::Unrecorded {
            door: door.into(),
            request: request.as_bytes().to_vec(),
        })
}

#[test]
fn a_lookup_is_the_latest_matching_exchange_among_the_records_read() {
    let records = tape();
    let view = KeyedView::new(&records);
    assert_eq!(view.len(), 6, "only the six exchanges are indexed");
    for case in CASES {
        assert_eq!(ask(&view, case), expected(case), "{case:?}");
    }
}

#[test]
fn lookups_are_order_insensitive_and_never_consume() {
    let records = tape();
    let view = KeyedView::new(&records);
    let forwards: Vec<_> = CASES.iter().map(|c| ask(&view, c)).collect();
    let backwards: Vec<_> = {
        let mut b: Vec<_> = CASES.iter().rev().map(|c| ask(&view, c)).collect();
        b.reverse();
        b
    };
    // Interleaved: each case asked twice in a row, the second time right after
    // a lookup that HIT the same key — a consuming reader would move on.
    let twice: Vec<_> = CASES
        .iter()
        .map(|c| {
            let first = ask(&view, c);
            assert_eq!(ask(&view, c), first, "asked again: {c:?}");
            first
        })
        .collect();
    let want: Vec<_> = CASES.iter().map(expected).collect();
    assert_eq!(forwards, want);
    assert_eq!(backwards, want);
    assert_eq!(twice, want);
}

#[test]
fn a_view_beside_an_in_order_replay_leaves_the_tape_untouched() {
    // Record a real program, index its tape, look its exchange up, then replay
    // the same records in order: the view's reads change nothing the replay
    // sees.
    let mut rec = astream_effects::RecordingSeam::new(Fixed);
    let mut peer = |q: &[u8]| q.iter().rev().copied().collect::<Vec<u8>>();
    let Ok(digest) = converse(&mut rec, "/f", &mut peer, &mut || false);
    let log = rec.into_log();
    let view = KeyedView::new(&log.0);
    let (request, reply) = log
        .0
        .iter()
        .find_map(|r| match r {
            EffectRecord::Exchange { request, reply, .. } => Some((request, reply)),
            _ => None,
        })
        .expect("converse asks once");
    let hit = view
        .lookup("peer", request, usize::MAX)
        .expect("the question is on the tape");
    assert_eq!(hit.reply, reply.as_slice());
    let replayed = converse(
        &mut ReplaySeam::new(EffectsLog(log.0.clone())),
        "/f",
        &mut |_| panic!("replay called the live peer"),
        &mut || panic!("replay read the live flag"),
    );
    assert_eq!(replayed, Ok(digest));
}

#[test]
fn an_empty_tape_knows_nothing() {
    let view = KeyedView::new(&[]);
    assert!(view.is_empty());
    assert_eq!(
        view.lookup("ctl", b"status", usize::MAX),
        Err(ReplayDivergence::Unrecorded {
            door: "ctl".into(),
            request: b"status".to_vec(),
        })
    );
}

/// A deterministic backend for the replay-beside test.
struct Fixed;

impl astream_effects::RealEffects for Fixed {
    fn real_now_nanos(&mut self) -> u64 {
        1
    }
    fn real_now_mono_nanos(&mut self) -> u64 {
        2
    }
    fn real_next_rand(&mut self) -> u64 {
        3
    }
    fn real_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        Ok(path.as_bytes().to_vec())
    }
}

#[test]
fn a_lookup_at_a_replay_cursor_sees_only_what_that_replay_consumed() {
    // The natural call for a second reader standing where a replay has got
    // to is `lookup(.., replay.position())`, and `position()` is the index of
    // the NEXT record — the one the replay has not read. That call must never
    // hand back that record: the recorded program had not received it yet.
    // Before the replay has read anything, the view knows nothing.
    let records = vec![
        EffectRecord::Mono(1),
        exchange("probe", "q", "answer"),
        EffectRecord::Mono(2),
    ];
    let view = KeyedView::new(&records);
    let mut rep = ReplaySeam::new(EffectsLog(records.clone()));
    let unrecorded = Err(ReplayDivergence::Unrecorded {
        door: "probe".into(),
        request: b"q".to_vec(),
    });
    assert_eq!(view.lookup("probe", b"q", rep.position()), unrecorded);
    assert_eq!(rep.mono_nanos(), Ok(1));
    // The exchange is next: unread, so not yet an answer.
    assert_eq!(rep.position(), 1);
    assert_eq!(view.lookup("probe", b"q", rep.position()), unrecorded);
    let mut no_peer = |_: &[u8]| -> Vec<u8> { panic!("replay called the live peer") };
    assert_eq!(
        rep.exchange("probe", b"q", &mut no_peer),
        Ok(b"answer".to_vec())
    );
    // Read: the answer the replay was just given, at the record it came from.
    assert_eq!(
        view.lookup("probe", b"q", rep.position()),
        Ok(KeyedReply {
            position: 1,
            reply: b"answer",
        })
    );

    // And over the whole fixed tape: at every bound from nothing read to all
    // of it, every key's hit lies strictly before the bound.
    let records = tape();
    let view = KeyedView::new(&records);
    for seen in 0..=records.len() {
        for (door, request, _, _) in CASES {
            if let Ok(hit) = view.lookup(door, request.as_bytes(), seen) {
                assert!(
                    hit.position < seen,
                    "{door} {request} with {seen} read answered from record {}",
                    hit.position
                );
            }
        }
    }
}

/// Every case asked of `ask` forwards, backwards and each twice in a row: the
/// answers `expected` gives, whatever the order.
fn holds_every_case(ask: impl Fn(&Case) -> Result<(usize, Vec<u8>), ReplayDivergence>) {
    let want: Vec<_> = CASES.iter().map(expected).collect();
    let forwards: Vec<_> = CASES.iter().map(&ask).collect();
    let mut backwards: Vec<_> = CASES.iter().rev().map(&ask).collect();
    backwards.reverse();
    let twice: Vec<_> = CASES
        .iter()
        .map(|c| {
            let first = ask(c);
            assert_eq!(ask(c), first, "asked again: {c:?}");
            first
        })
        .collect();
    assert_eq!(forwards, want);
    assert_eq!(backwards, want);
    assert_eq!(twice, want);
}

/// A [`KeyedIndex`] answers every case as the view does, whatever holds its
/// records — a `Vec`, a `Box`, an `Arc` — and asked in any order, any number
/// of times.
#[test]
fn an_index_that_holds_its_records_answers_as_the_view_does() {
    fn asked<R: AsRef<[EffectRecord]>>(
        index: &KeyedIndex<R>,
    ) -> impl Fn(&Case) -> Result<(usize, Vec<u8>), ReplayDivergence> + '_ {
        move |&(door, request, at, _)| {
            index
                .lookup(door, request.as_bytes(), at)
                .map(|KeyedReply { position, reply }| (position, reply.to_vec()))
        }
    }
    let owned = KeyedIndex::new(tape());
    assert_eq!(owned.len(), 6, "only the six exchanges are indexed");
    assert_eq!(
        owned.records(),
        tape().as_slice(),
        "it keeps what it was given"
    );
    holds_every_case(asked(&owned));
    holds_every_case(asked(&KeyedIndex::new(tape().into_boxed_slice())));
    let shared: Arc<[EffectRecord]> = tape().into();
    holds_every_case(asked(&KeyedIndex::new(Arc::clone(&shared))));
    let records = tape();
    let view = KeyedView::new(&records);
    holds_every_case(|c| ask(&view, c));
}

/// ONE INDEX, MANY READERS: an index over an `Arc` of the records is itself
/// `Send + Sync + 'static`, so it is built once and handed, behind an `Arc`,
/// to every reader — here threads, each asking every case — with no borrow of
/// the tape to keep alive.
#[test]
fn one_index_over_shared_records_serves_every_reader() {
    fn shareable<T: Send + Sync + 'static>(_: &T) {}
    let records: Arc<[EffectRecord]> = tape().into();
    let index = Arc::new(KeyedIndex::new(Arc::clone(&records)));
    shareable(&index);
    let readers: Vec<_> = (0..4)
        .map(|_| {
            let index = Arc::clone(&index);
            std::thread::spawn(move || {
                CASES
                    .iter()
                    .map(|&(door, request, at, _)| {
                        index
                            .lookup(door, request.as_bytes(), at)
                            .map(|KeyedReply { position, reply }| (position, reply.to_vec()))
                    })
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    let want: Vec<_> = CASES.iter().map(expected).collect();
    for reader in readers {
        assert_eq!(reader.join().expect("a reader"), want);
    }
}

/// The kind of a record, one number per `EffectRecord` variant. The match has
/// no catch-all, so a new variant does not compile here until it is given a
/// number and [`mixed_tape`] is made to write it.
fn kind(record: &EffectRecord) -> usize {
    match record {
        EffectRecord::Clock(_) => 0,
        EffectRecord::Rand(_) => 1,
        EffectRecord::File { .. } => 2,
        EffectRecord::FileErr { .. } => 3,
        EffectRecord::Mono(_) => 4,
        EffectRecord::Exchange { .. } => 5,
        EffectRecord::Emit { .. } => 6,
        EffectRecord::Raised { .. } => 7,
    }
}
const KINDS: usize = 8;

/// A long tape of every record kind, deterministic: `len` records over five
/// doors and seven requests, half of them exchanges (most of a key already
/// asked), and the other half the seven other kinds — a clock, a random word,
/// a file read and a failed one whose path is a door an exchange goes through
/// and whose bytes are a request (what an index that keyed a file read by its
/// path would take for that exchange), a monotonic read, and an `Emit` or a
/// `Raised` carrying a door and bytes an exchange uses.
fn mixed_tape(len: usize) -> Vec<EffectRecord> {
    const DOORS: [&str; 5] = [
        "ctl",
        "probe.git_view",
        "probe.hidden_twin",
        "host.wants",
        "out",
    ];
    const REQUESTS: [&str; 7] = [
        "",
        "status",
        "/repo",
        "/repo/a",
        "text --json",
        "who",
        "\0\u{ff}",
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    let mut next = move || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) as usize
    };
    (0..len)
        .map(|i| {
            let (door, request) = (
                DOORS[next() % DOORS.len()],
                REQUESTS[next() % REQUESTS.len()],
            );
            match next() % 14 {
                0 => EffectRecord::Clock(i as u64),
                1 => EffectRecord::Rand((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)),
                2 => EffectRecord::File {
                    path: door.into(),
                    bytes: request.as_bytes().to_vec(),
                },
                3 => EffectRecord::FileErr {
                    path: door.into(),
                    kind: std::io::ErrorKind::NotFound,
                },
                4 => EffectRecord::Mono(i as u64),
                5 => EffectRecord::Emit {
                    door: door.into(),
                    bytes: request.as_bytes().to_vec(),
                },
                6 => EffectRecord::Raised {
                    door: door.into(),
                    false_reads: 0,
                },
                _ => exchange(door, request, &format!("reply {i}")),
            }
        })
        .collect()
}

/// A lookup's hit as a scan states one.
fn got(r: Result<KeyedReply<'_>, ReplayDivergence>) -> Option<(usize, &[u8])> {
    r.ok().map(|h| (h.position, h.reply))
}

/// The answer a reader must give, by a scan: the last exchange through `door`
/// with exactly `request` at a position below `seen`.
fn scanned<'a>(
    records: &'a [EffectRecord],
    door: &str,
    request: &[u8],
    seen: usize,
) -> Option<(usize, &'a [u8])> {
    records[..seen.min(records.len())]
        .iter()
        .enumerate()
        .rev()
        .find_map(|(p, r)| match r {
            EffectRecord::Exchange {
                door: d,
                request: q,
                reply,
            } if d == door && q.as_slice() == request => Some((p, reply.as_slice())),
            _ => None,
        })
}

/// Every key of [`mixed_tape`]'s, and two it never asks, at every bound.
fn keys() -> Vec<(&'static str, &'static [u8])> {
    let mut keys = Vec::new();
    for door in [
        "ctl",
        "probe.git_view",
        "probe.hidden_twin",
        "host.wants",
        "out",
        "never",
    ] {
        for request in [
            "",
            "status",
            "/repo",
            "/repo/a",
            "text --json",
            "who",
            "\0\u{ff}",
            "never",
        ] {
            keys.push((door, request.as_bytes()));
        }
    }
    keys
}

/// THE VIEW AND THE INDEX AGREE WITH A SCAN, AT EVERY BOUND: over a long
/// tape of every record kind (checked: a kind the tape lacks fails the test)
/// and keys asked many times, every (door,
/// request) — two never asked among them — at every bound from nothing read
/// to past the end is answered by the view and by an index over an `Arc` of
/// the same records exactly as a backwards scan of the records read answers
/// it. NEGATIVE CONTROL: a scan that admits the record AT the bound (an
/// inclusive cutoff, the off-by-one the count rules out) disagrees with them
/// somewhere on this tape, so the agreement is not vacuous.
#[test]
fn the_view_and_the_index_agree_with_a_scan_at_every_bound() {
    let records = mixed_tape(1_500);
    let mut held = [0usize; KINDS];
    for record in &records {
        held[kind(record)] += 1;
    }
    assert!(
        held.iter().all(|&n| n > 0),
        "the tape holds every record kind: {held:?}"
    );
    let view = KeyedView::new(&records);
    let shared: Arc<[EffectRecord]> = records.clone().into();
    let index = KeyedIndex::new(Arc::clone(&shared));
    let exchanges = records
        .iter()
        .filter(|r| matches!(r, EffectRecord::Exchange { .. }))
        .count();
    assert_eq!((view.len(), index.len()), (exchanges, exchanges));
    let mut inclusive_differs = 0usize;
    for (door, request) in keys() {
        for seen in 0..=records.len() + 1 {
            let want = scanned(&records, door, request, seen);
            assert_eq!(
                got(view.lookup(door, request, seen)),
                want,
                "view: {door} {request:?} {seen}"
            );
            assert_eq!(
                got(index.lookup(door, request, seen)),
                want,
                "index: {door} {request:?} {seen}"
            );
            if scanned(&records, door, request, seen.saturating_add(1)) != want {
                inclusive_differs += 1;
            }
        }
    }
    assert!(
        inclusive_differs > 0,
        "the inclusive scan is caught somewhere"
    );
}

#[test]
fn an_empty_index_knows_nothing() {
    let index = KeyedIndex::new(Vec::new());
    assert!(index.is_empty());
    assert_eq!(
        index.lookup("ctl", b"status", usize::MAX),
        Err(ReplayDivergence::Unrecorded {
            door: "ctl".into(),
            request: b"status".to_vec(),
        })
    );
}
