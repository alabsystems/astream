//! Evidence for `term.fleet.consistent-cut-replay`: a Chandy-Lamport consistent
//! cut over two fleet sessions, with deterministic per-partition replay.
//!
//! An orchestrator session's Out causes a child session's injected In (recorded
//! as a CrossEdge of real Offsets built OVER the two logs — not a wire field,
//! not client_seq). The cut consistency predicate rejects an effect-without-cause
//! (orphaned injection) and admits a cause-without-effect (in-flight); replaying
//! each partition from the cut re-folds byte-equal to its truncated live screen —
//! over the fixed scenario and, by proptest, over two partitions' arbitrary Out
//! vectors with arbitrary (possibly absent) cut offsets. `is_consistent` agrees
//! with an oracle that has its OWN cut lookup, over cuts that may omit or
//! duplicate partitions. A decode error before the cut is an error, not a
//! shorter screen.

use astream_engine::{
    is_consistent, replay_to_cut, CrossEdge, Cut, Log, MemDisk, Offset, Partition, ReadError,
    Seeded, Session,
};
use astream_term::{screen, Record, Screen};
use proptest::prelude::*;
use std::collections::HashMap;

const COLS: u16 = 40;
const ROWS: u16 = 8;
const ORCH: u64 = 99;
const O: Partition = Partition(0);
const C: Partition = Partition(1);

fn decode(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

/// Replay to the cut and return the screen (the cut is expected to be readable).
fn replay(cut: &Cut, p: Partition, log: &[u8]) -> Screen {
    replay_to_cut(cut, p, log, COLS, ROWS).unwrap().screen
}

/// Two-session fleet with a cross-injection: orchestrator O boots and dispatches,
/// then injects "make" into child C, whose Out echoes the injected command (so
/// the child's screen genuinely depends on the injection — real causality).
fn fleet() -> (Vec<u8>, Vec<u8>, CrossEdge) {
    let mut o = Session::new(Seeded::new(1));
    o.append_output(b"orchestrator boot\r\n".to_vec()).unwrap(); // O offset 0
    let cause = o.append_output(b"dispatch: make\r\n".to_vec()).unwrap(); // O offset 1 (CAUSE)

    let mut c = Session::new(Seeded::new(2));
    c.append_output(b"child boot\r\n".to_vec()).unwrap(); // C offset 0
    let effect = c.apply_input(ORCH, 1, b"make\n".to_vec()).unwrap().unwrap(); // C offset 1 (EFFECT)
    c.append_output(b"make\r\nBUILD OK: 0 errors\r\n".to_vec())
        .unwrap(); // C offset 2 (echo)

    let edge = CrossEdge {
        cause: (O, cause),
        effect: (C, effect),
    };
    (o.log_bytes(), c.log_bytes(), edge)
}

#[test]
fn full_cut_is_consistent_and_replays_each_partition() {
    let (o_log, c_log, edge) = fleet();
    let o_live = screen::fold(COLS, ROWS, &decode(&o_log));
    let c_live = screen::fold(COLS, ROWS, &decode(&c_log));

    let cut = Cut {
        offsets: vec![(O, Offset(1)), (C, Offset(2))],
    };
    assert!(is_consistent(&cut, &[edge]));
    let o_replay = replay_to_cut(&cut, O, &o_log, COLS, ROWS).unwrap();
    assert_eq!(o_replay.screen.serialize(), o_live.serialize());
    assert_eq!(o_replay.folded_through, Some(Offset(1)), "reached the cut");
    let c_replay = replay_to_cut(&cut, C, &c_log, COLS, ROWS).unwrap();
    assert_eq!(c_replay.screen.serialize(), c_live.serialize());
    assert_eq!(c_replay.folded_through, Some(Offset(2)));
    // Real causality: the child's screen shows the injected command echoed.
    assert!(
        c_live.line_text(1).contains("make"),
        "the child screen reflects the orchestrator-injected command"
    );
}

#[test]
fn orphan_cut_effect_without_cause_is_rejected() {
    let (_o, _c, edge) = fleet();
    // C admits the injected In (offset 1); O excludes the dispatch cause (offset 1).
    let cut = Cut {
        offsets: vec![(O, Offset(0)), (C, Offset(1))],
    };
    assert!(
        !is_consistent(&cut, &[edge]),
        "an effect-without-cause cut is causally impossible and must be rejected"
    );
}

#[test]
fn in_flight_cut_cause_without_effect_is_consistent() {
    let (o_log, c_log, edge) = fleet();
    // O includes the cause (offset 1); C excludes the injected In (cut at offset 0).
    let cut = Cut {
        offsets: vec![(O, Offset(1)), (C, Offset(0))],
    };
    assert!(
        is_consistent(&cut, &[edge]),
        "an in-flight (sent-not-yet-delivered) cut is consistent"
    );
    // C replays only its boot line — the truncated live screen at that cut.
    let c_truncated = screen::fold(COLS, ROWS, &decode(&c_log)[..1]);
    assert_eq!(replay(&cut, C, &c_log).serialize(), c_truncated.serialize());
    assert_eq!(
        replay(&cut, O, &o_log).serialize(),
        screen::fold(COLS, ROWS, &decode(&o_log)).serialize()
    );
}

#[test]
fn replay_surfaces_damage_before_the_cut_and_ignores_bytes_after_it() {
    let (_o, c_log, _edge) = fleet();
    // Flip a byte inside record 1 (the injected In): a cut that admits offset 1
    // cannot be replayed — it is an error, never a valid-looking shorter screen.
    let mut damaged = c_log.clone();
    let end0 = frame_end(&c_log, 0);
    damaged[end0 + 14] ^= 0x01;
    let cut = Cut {
        offsets: vec![(C, Offset(2))],
    };
    assert!(matches!(
        replay_to_cut(&cut, C, &damaged, COLS, ROWS),
        Err(ReadError::Frame(_))
    ));
    // The same damage past the cut is never read: the cut at offset 0 replays.
    let cut0 = Cut {
        offsets: vec![(C, Offset(0))],
    };
    let r = replay_to_cut(&cut0, C, &damaged, COLS, ROWS).unwrap();
    assert_eq!(r.folded_through, Some(Offset(0)));
    assert_eq!(
        r.screen.serialize(),
        screen::fold(COLS, ROWS, &decode(&c_log)[..1]).serialize()
    );
    // A cut past the end of the log reports how far it got.
    let far = Cut {
        offsets: vec![(C, Offset(50))],
    };
    let r = replay_to_cut(&far, C, &c_log, COLS, ROWS).unwrap();
    assert_eq!(
        r.folded_through,
        Some(Offset(2)),
        "the log ended before the cut"
    );
    // A partition the cut does not name folds empty and reaches nothing.
    let r = replay_to_cut(&far, O, &c_log, COLS, ROWS).unwrap();
    assert_eq!(r.folded_through, None);
    assert_eq!(
        r.screen.serialize(),
        screen::fold(COLS, ROWS, &[]).serialize()
    );
}

/// The byte offset where frame `i` of `bytes` ends.
fn frame_end(bytes: &[u8], i: usize) -> usize {
    let mut pos = 0;
    for _ in 0..=i {
        let d = astream_wire::Frame::decode(&bytes[pos..]).unwrap().unwrap();
        pos += d.consumed;
    }
    pos
}

/// An independently-coded reference predicate, structurally different from
/// `is_consistent` (scan for any orphan and short-circuit) and with its OWN cut
/// lookup — a first-entry-wins map built here, never `Cut::offset_of` — so a
/// bug in the production lookup (e.g. a duplicated partition resolving to the
/// wrong entry) is visible to the differential test. The
/// `wire.router.matches-independent-oracle` pattern.
fn ref_consistent(cut: &Cut, edges: &[CrossEdge]) -> bool {
    let mut lookup: HashMap<u64, u64> = HashMap::new();
    for (p, o) in &cut.offsets {
        lookup.entry(p.0).or_insert(o.0);
    }
    let admits = |p: Partition, at: Offset| lookup.get(&p.0).is_some_and(|&o| at.0 <= o);
    for e in edges {
        if admits(e.effect.0, e.effect.1) && !admits(e.cause.0, e.cause.1) {
            return false;
        }
    }
    true
}

/// Record `bodies` as Out records in a fresh session and return (log, records).
fn out_session(seed: u64, bodies: &[Vec<u8>]) -> (Vec<u8>, Vec<Record>) {
    let mut s = Session::new(Seeded::new(seed));
    for b in bodies {
        s.append_output(b.clone()).unwrap();
    }
    let recs = bodies.iter().map(|b| Record::Out(b.clone())).collect();
    (s.log_bytes(), recs)
}

proptest! {
    /// Replaying a partition to any cut offset equals the prefix fold of its log
    /// (the resume.rs every-offset idiom, lifted to the fleet replay path), for
    /// TWO partitions with independent Out vectors and independent cut offsets;
    /// the second partition is sometimes absent from the cut (folds empty).
    #[test]
    fn replay_to_cut_equals_the_prefix_fold_per_partition(
        bodies_o in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..10), 1..6),
        bodies_c in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..10), 1..6),
        k_o in 0u64..8,
        k_c in 0u64..8,
        name_c in any::<bool>(),
    ) {
        let (log_o, recs_o) = out_session(7, &bodies_o);
        let (log_c, recs_c) = out_session(8, &bodies_c);
        let mut offsets = vec![(O, Offset(k_o))];
        if name_c {
            offsets.push((C, Offset(k_c)));
        }
        let cut = Cut { offsets };
        for (p, recs, log, k, named) in [
            (O, &recs_o, &log_o, k_o, true),
            (C, &recs_c, &log_c, k_c, name_c),
        ] {
            let r = replay_to_cut(&cut, p, log, COLS, ROWS).unwrap();
            if named {
                let n = (k as usize + 1).min(recs.len());
                prop_assert_eq!(r.screen.serialize(), screen::fold(COLS, ROWS, &recs[..n]).serialize());
                prop_assert_eq!(r.folded_through, Some(Offset(n as u64 - 1)));
            } else {
                prop_assert_eq!(r.screen.serialize(), screen::fold(COLS, ROWS, &[]).serialize());
                prop_assert_eq!(r.folded_through, None);
            }
        }
    }

    /// `is_consistent` agrees with the independent reference oracle over arbitrary
    /// edge sets and cuts — cuts that may omit a partition (admits nothing) or
    /// list one twice (the first entry counts), and edges over a partition the
    /// cut never names.
    #[test]
    fn is_consistent_agrees_with_an_independent_oracle(
        edges_raw in prop::collection::vec((0u64..3, 0u64..5, 0u64..3, 0u64..5), 0..6),
        cut_raw in prop::collection::vec((0u64..3, 0u64..6), 0..5),
    ) {
        let edges: Vec<CrossEdge> = edges_raw.iter().map(|(cp, co, ep, eo)| CrossEdge {
            cause: (Partition(*cp), Offset(*co)),
            effect: (Partition(*ep), Offset(*eo)),
        }).collect();
        let cut = Cut { offsets: cut_raw.iter().map(|(p, o)| (Partition(*p), Offset(*o))).collect() };
        prop_assert_eq!(is_consistent(&cut, &edges), ref_consistent(&cut, &edges));
    }
}
