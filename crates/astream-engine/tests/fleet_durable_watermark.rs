//! Evidence for `term.fleet.durable-watermark`: a child's injected `In` stamps the
//! orchestrator `Out` that caused it DURABLY in its envelope header. After the live
//! sessions are dropped, the fleet's consistent-cut machinery is rebuilt from the
//! stored log bytes ALONE — proven equal to the edge the producers' returned
//! offsets describe (an independent path), with negative controls showing the
//! decoded `caused_by` bytes are load-bearing. `replay_to_cut` over the same
//! bytes re-folds the child screen byte-equal to a direct prefix fold at a cut
//! that excludes a later record, and the durable edge scan stops at the same
//! out-of-sequence boundary the replay reports.

use astream_engine::{
    cross_edges_from_logs, is_consistent, recover, replay_to_cut, CausedBy, CrossEdge, Cut,
    FaultKind, Log, Offset, Partition, ReadError, Seeded, Session, Tail,
};
use astream_term::{screen, Record};

const ORCH: Partition = Partition(1);
const CHILD: Partition = Partition(2);
const COLS: u16 = 40;
const ROWS: u16 = 6;

fn decode(bytes: &[u8]) -> Vec<Record> {
    Log::read_bytes(bytes, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

/// The fleet: the orchestrator's dispatch offset, the child's injected-In offset,
/// and both stored logs. The child's log has THREE records — In@0 (caused by the
/// dispatch), Out@1, Out@2 — so a cut at C@1 is load-bearing.
fn fleet() -> (Offset, Offset, Vec<u8>, Vec<u8>) {
    // The orchestrator dispatches; its `append` RETURNS the dispatch offset.
    let mut orch = Session::new(Seeded::new(1));
    orch.append_output(b"boot\r\n".to_vec()).unwrap();
    let cause_off = orch
        .append_output(b"dispatch child: run\r\n".to_vec())
        .unwrap(); // O@1

    // The child records the injected input, stamping the dispatch as its cause.
    let mut child = Session::new(Seeded::new(2));
    let eff_off = child
        .apply_input_caused(
            7,
            1,
            b"run\n".to_vec(),
            CausedBy {
                partition: Some(ORCH.0),
                offset: cause_off.0,
            },
        )
        .unwrap()
        .unwrap(); // C@0
    child.append_output(b"running\r\n".to_vec()).unwrap(); // C@1
    child.append_output(b"later\r\n".to_vec()).unwrap(); // C@2
    (cause_off, eff_off, orch.log_bytes(), child.log_bytes())
}

#[test]
fn cross_edges_rebuild_from_log_bytes_and_drive_the_consistent_cut() {
    let (cause_off, eff_off, orch_bytes, child_bytes) = fleet();

    // DURABLE rebuild: from the stored bytes alone (no in-memory edge).
    let durable = cross_edges_from_logs(&[(ORCH, &orch_bytes), (CHILD, &child_bytes)]);

    // INDEPENDENT oracle: the edge built ONLY from the offsets the appends RETURNED
    // — a path that never touched the decode.
    let edge_live = CrossEdge {
        cause: (ORCH, cause_off),
        effect: (CHILD, eff_off),
    };
    assert_eq!(
        durable,
        vec![edge_live],
        "the byte-rebuilt edge equals the producer-returned edge"
    );

    // NEGATIVE CONTROL 1: the same input with NO cause stamped -> no edge.
    let mut child_none = Session::new(Seeded::new(2));
    child_none.apply_input(7, 1, b"run\n".to_vec()).unwrap();
    assert!(
        cross_edges_from_logs(&[(ORCH, &orch_bytes), (CHILD, &child_none.log_bytes())]).is_empty(),
        "without the caused_by bytes there is no edge"
    );

    // NEGATIVE CONTROL 2: a DIFFERENT decoded cause offset -> a different edge set.
    let mut child_diff = Session::new(Seeded::new(2));
    child_diff
        .apply_input_caused(
            7,
            1,
            b"run\n".to_vec(),
            CausedBy {
                partition: Some(ORCH.0),
                offset: cause_off.0 + 99,
            },
        )
        .unwrap();
    assert_ne!(
        cross_edges_from_logs(&[(ORCH, &orch_bytes), (CHILD, &child_diff.log_bytes())]),
        durable,
        "the decoded cause offset is load-bearing, not incidental"
    );

    // The byte-rebuilt edge drives the consistency predicate identically to a live one.
    let full = Cut {
        offsets: vec![(ORCH, cause_off), (CHILD, eff_off)],
    };
    assert!(is_consistent(&full, &durable), "the full cut is consistent");
    let orphan = Cut {
        offsets: vec![(ORCH, Offset(0)), (CHILD, eff_off)], // effect admitted, cause excluded
    };
    assert!(
        !is_consistent(&orphan, &durable),
        "an orphaned injection is rejected"
    );
    let in_flight = Cut {
        offsets: vec![(ORCH, cause_off)], // cause admitted, effect not named
    };
    assert!(
        is_consistent(&in_flight, &durable),
        "an in-flight cause is admitted"
    );

    // replay_to_cut re-folds the child's screen BYTE-EQUAL to a direct fold of
    // the records the cut admits — and the cut is load-bearing: C@2 ("later")
    // is excluded, so folding the whole log would differ.
    let cut2 = Cut {
        offsets: vec![(ORCH, cause_off), (CHILD, Offset(1))],
    };
    let child_recs = decode(&child_bytes);
    let replayed = replay_to_cut(&cut2, CHILD, &child_bytes, COLS, ROWS).unwrap();
    let direct = screen::fold(COLS, ROWS, &child_recs[..=1]);
    assert_eq!(replayed.screen.serialize(), direct.serialize());
    assert_eq!(replayed.folded_through, Some(Offset(1)));
    assert!(replayed.screen.line_text(0).contains("running"));
    assert_ne!(
        replayed.screen.serialize(),
        screen::fold(COLS, ROWS, &child_recs).serialize(),
        "the cut excluded C@2"
    );
}

#[test]
fn the_durable_edge_scan_stops_where_replay_and_recover_stop() {
    let (_cause_off, _eff_off, orch_bytes, child_bytes) = fleet();

    // A child log whose writer restarted at seq 0 (the log's bytes twice over):
    // seq 0,1,2,0,1,2. Every reader defines the intact prefix as the first three.
    let mut regressed = child_bytes.clone();
    regressed.extend_from_slice(&child_bytes);
    let report = recover(&regressed);
    assert_eq!(report.records, 3);
    assert!(matches!(
        report.tail,
        Tail::Fault {
            kind: FaultKind::OutOfOrder {
                expected: 3,
                found: 0
            },
            ..
        }
    ));

    // The edge scan emits the ONE edge in the intact prefix — never one for the
    // regressed copy of the injected In, whose offset a replay could not reach.
    let edges = cross_edges_from_logs(&[(ORCH, &orch_bytes), (CHILD, &regressed)]);
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].effect, (CHILD, Offset(0)));

    // And a replay that has to cross the boundary reports it as an error.
    let past = Cut {
        offsets: vec![(CHILD, Offset(5))],
    };
    assert_eq!(
        replay_to_cut(&past, CHILD, &regressed, COLS, ROWS)
            .expect_err("the seq regression surfaces"),
        ReadError::SeqMismatch {
            expected: Offset(3),
            found: Offset(0)
        }
    );
    // A cut inside the intact prefix replays fine over the same bytes.
    let inside = Cut {
        offsets: vec![(CHILD, Offset(2))],
    };
    assert_eq!(
        replay_to_cut(&inside, CHILD, &regressed, COLS, ROWS)
            .unwrap()
            .folded_through,
        Some(Offset(2))
    );
}
