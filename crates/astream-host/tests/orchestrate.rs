//! Evidence for `term.fleet.orchestrate-n`: one orchestrator drives THREE real
//! heterogeneous child terminals — each its own single-writer partition — every
//! child session independently replayable, and the orchestrator's cross-injection
//! edges forming a Chandy-Lamport consistent cut.

#![cfg(unix)]

use astream_engine::{
    is_consistent, CrossEdge, Cut, Log, MemDisk, Offset, Partition, Seeded, Session,
};
use astream_host::{Driver, Pty};
use astream_term::{screen, Record};
use std::time::{Duration, Instant};

const COLS: u16 = 40;
const ROWS: u16 = 8;
const ORCH_CLIENT: u64 = 99;

fn decode(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

/// The real offset of a child log's first injected `In` — a log with NO `In`
/// (a driver that wrote to the pty but never recorded the injection) is a test
/// failure, never a silent `Offset::ZERO` that the cut assertions would accept.
fn first_in_offset(records: &[Record]) -> Offset {
    records
        .iter()
        .position(|r| matches!(r, Record::In { .. }))
        .map(|i| Offset(i as u64))
        .expect("the child log records the orchestrator's injected In")
}

fn in_count(records: &[Record]) -> usize {
    records
        .iter()
        .filter(|r| matches!(r, Record::In { .. }))
        .count()
}

fn head(bytes: &[u8]) -> Offset {
    Offset((decode(bytes).len() as u64).saturating_sub(1))
}

#[test]
fn orchestrator_drives_three_children_with_a_consistent_cut() {
    let pty_child = env!("CARGO_BIN_EXE_pty_child"); // non-interactive
    let echo_child = env!("CARGO_BIN_EXE_echo_child"); // interactive

    let worker = std::thread::spawn(move || {
        // The orchestrator's own log (partition 0) records its dispatch decisions.
        let mut orch = Session::new(Seeded::new(0));
        orch.append_output(b"orchestrator boot\r\n".to_vec())
            .unwrap(); // O@0

        // Child A — non-interactive. Partition 1.
        let mut a = Driver::new(
            Pty::spawn(pty_child, &[], COLS, ROWS).unwrap(),
            Seeded::new(1),
        );
        let a_out = a.drain_to_eof().unwrap();
        let _ = a.reap();

        // Child B — interactive, dispatched "alpha". Partition 2.
        let cause_b = orch
            .append_output(b"dispatch B: alpha\r\n".to_vec())
            .unwrap(); // O@1
        let mut b = Driver::new(
            Pty::spawn(echo_child, &[], COLS, ROWS).unwrap(),
            Seeded::new(2),
        );
        b.drive_input(ORCH_CLIENT, 1, b"alpha\n".to_vec()).unwrap();
        b.drive_input(ORCH_CLIENT, 2, b"quit\n".to_vec()).unwrap();
        let b_out = b.drain_to_eof().unwrap();
        let _ = b.reap();

        // Child C — interactive, dispatched "beta". Partition 3.
        let cause_c = orch
            .append_output(b"dispatch C: beta\r\n".to_vec())
            .unwrap(); // O@2
        let mut c = Driver::new(
            Pty::spawn(echo_child, &[], COLS, ROWS).unwrap(),
            Seeded::new(3),
        );
        c.drive_input(ORCH_CLIENT, 1, b"beta\n".to_vec()).unwrap();
        c.drive_input(ORCH_CLIENT, 2, b"quit\n".to_vec()).unwrap();
        let c_out = c.drain_to_eof().unwrap();
        let _ = c.reap();

        (
            orch.log_bytes(),
            a.log_bytes(),
            b.log_bytes(),
            c.log_bytes(),
            a_out,
            b_out,
            c_out,
            cause_b,
            cause_c,
        )
    });

    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(30),
            "orchestration timed out"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let (o_log, a_log, b_log, c_log, a_out, b_out, c_out, cause_b, cause_c) =
        worker.join().expect("worker panicked");

    // (1) Each child's stored log re-folds to the SAME screen the kernel's live
    // output produced (not fold-vs-itself), AND that screen actually shows the
    // child's known content (a `needle` the kernel emitted). The equality catches
    // a divergent fold; the content assertion catches a blank/broken fold that
    // would make both sides collapse to the same empty screen. (fold ignores
    // In/Exit and the children emit no Resize, so folding the whole log equals
    // folding only the Out bytes, which are exactly the collected live output.)
    for (log, live, needle) in [
        (&a_log, &a_out, "ERR"),       // pty_child's KNOWN_OUTPUT
        (&b_log, &b_out, "GOT:alpha"), // echo_child B's response
        (&c_log, &c_out, "GOT:beta"),  // echo_child C's response
    ] {
        let from_log = screen::fold(COLS, ROWS, &decode(log));
        let from_live = screen::fold(COLS, ROWS, &[Record::Out(live.clone())]);
        assert_eq!(
            from_log.serialize(),
            from_live.serialize(),
            "the recorded In+Out log re-folds to the child's live screen"
        );
        let text = (0..ROWS)
            .map(|r| from_log.line_text(r))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            text.contains(needle),
            "the re-folded screen shows the child's output {needle:?}; got {text:?}"
        );
    }
    assert!(
        !a_out.is_empty(),
        "the non-interactive child produced output"
    );
    assert!(
        String::from_utf8_lossy(&b_out).contains("GOT:alpha"),
        "child B echoed its dispatch"
    );
    assert!(
        String::from_utf8_lossy(&c_out).contains("GOT:beta"),
        "child C echoed its dispatch"
    );

    // (2) Each interactive child's log holds exactly its two injected Ins (the
    // dispatch and quit) — so the edge effects below are REAL recorded offsets,
    // not a fallback that any cut would trivially satisfy.
    assert_eq!(
        in_count(&decode(&b_log)),
        2,
        "child B recorded its two injected Ins"
    );
    assert_eq!(
        in_count(&decode(&c_log)),
        2,
        "child C recorded its two injected Ins"
    );
    assert_eq!(
        in_count(&decode(&a_log)),
        0,
        "the non-interactive child was driven nothing"
    );

    // (3) The cross-injection edges form a consistent cut.
    const O: Partition = Partition(0);
    const B: Partition = Partition(2);
    const C: Partition = Partition(3);
    let edges = [
        CrossEdge {
            cause: (O, cause_b),
            effect: (B, first_in_offset(&decode(&b_log))),
        },
        CrossEdge {
            cause: (O, cause_c),
            effect: (C, first_in_offset(&decode(&c_log))),
        },
    ];

    // Full cut — every partition at head — is consistent.
    let full = Cut {
        offsets: vec![
            (O, head(&o_log)),
            (Partition(1), head(&a_log)),
            (B, head(&b_log)),
            (C, head(&c_log)),
        ],
    };
    assert!(
        is_consistent(&full, &edges),
        "the full fleet cut is consistent"
    );

    // Orphan cut — child B's injected effect admitted, the orchestrator's cause
    // excluded — is mechanically rejected.
    let orphan = Cut {
        offsets: vec![(O, Offset(0)), (B, first_in_offset(&decode(&b_log)))],
    };
    assert!(
        !is_consistent(&orphan, &edges),
        "an orphaned-injection cut is rejected"
    );
}
