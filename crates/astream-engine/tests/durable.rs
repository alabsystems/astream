//! Evidence for durable execution (`engine.durable.exactly-once-resume`): a
//! workflow survives a crash and resumes exactly. A crash is modeled as the
//! process dying after fsyncing some prefix of step records (the journal is
//! dropped); reopening recovers that prefix and resumes. The proof: across a
//! crash at EVERY inter-step boundary — and across arbitrary REPEATED crashes
//! (proptest) — each step runs exactly once, in order, no committed step re-runs,
//! and the outputs equal a never-crashed run. The honest boundary (a mid-step
//! crash before the fsync re-runs that one step — at-least-once) is witnessed by
//! its own test, not hidden.
//!
//! Recovery is exercised on the real file: a torn or CRC-corrupt final record
//! (a crash mid-commit) is truncated DURABLY (the on-disk length is asserted)
//! and the prefix resumes; a mid-journal fault — a corrupt record with commits
//! after it, an out-of-order step, an unreadable step version — REFUSES to open
//! (the file untouched, the error naming the byte offset), so committed side
//! effects are never silently re-executed; the explicit `open_truncating` is the
//! operator's repair.

use astream_engine::{FaultKind, LogFault, Tail, WorkflowJournal, STEP_VERSION};
use astream_wire::Frame;
use proptest::prelude::*;
use std::cell::RefCell;
use std::path::PathBuf;

/// Removes its file when dropped, so a test leaves nothing behind whether it passes
/// or panics. Bind it before whatever uses the file, so it drops after that.
struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn tmp(name: &str) -> (Cleanup, PathBuf) {
    let p = std::env::temp_dir().join(format!(
        "astream_durable_{}_{}.log",
        std::process::id(),
        name
    ));
    let _ = std::fs::remove_file(&p);
    (Cleanup(p.clone()), p)
}

/// A step record written by hand from the documented format — version | step
/// u64 LE | len u32 LE | output, in a CRC frame — independently of the encoder.
fn step_frame(version: u8, step: u64, output: &[u8]) -> Vec<u8> {
    let mut p = vec![version];
    p.extend_from_slice(&step.to_le_bytes());
    p.extend_from_slice(&(output.len() as u32).to_le_bytes());
    p.extend_from_slice(output);
    Frame::new(p).encode().unwrap()
}

fn file_len(path: &PathBuf) -> u64 {
    std::fs::metadata(path).unwrap().len()
}

/// The byte offset where each frame in `bytes` ends.
fn frame_ends(bytes: &[u8]) -> Vec<usize> {
    let mut ends = Vec::new();
    let mut pos = 0;
    while let Ok(Some(d)) = Frame::decode(&bytes[pos..]) {
        pos += d.consumed;
        ends.push(pos);
    }
    ends
}

fn fault_of(err: &std::io::Error) -> LogFault {
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    err.get_ref()
        .and_then(|e| e.downcast_ref::<LogFault>())
        .cloned()
        .expect("a LogFault inside the io::Error")
}

#[test]
fn workflow_resumes_exactly_once_across_a_crash_at_every_boundary() {
    const N: u64 = 10;
    for crash_at in 0..=N {
        let (_tmp, path) = tmp(&format!("boundary_{crash_at}"));

        // `invoked` records which step indices actually executed (the side effect).
        let invoked = RefCell::new(Vec::<u64>::new());
        let step = |i: u64| {
            invoked.borrow_mut().push(i);
            format!("out-{i}").into_bytes()
        };

        // Session 1: run up to the crash point, then "crash" (drop the journal).
        {
            let mut j = WorkflowJournal::open(&path).unwrap();
            let _ = j.run(crash_at, &step).unwrap();
            assert_eq!(j.committed_count(), crash_at as usize);
        } // <- journal dropped == process death after fsyncing `crash_at` steps

        // Session 2: reopen (recover the committed prefix) and finish the workflow.
        let outputs = {
            let mut j = WorkflowJournal::open(&path).unwrap();
            assert_eq!(
                j.committed_count(),
                crash_at as usize,
                "recovered the committed prefix"
            );
            assert_eq!(j.recovery().tail, Tail::Clean);
            j.run(N, &step).unwrap()
        };

        // Exactly-once: every step ran once, in order, none re-ran.
        let invoked = invoked.into_inner();
        let expected: Vec<u64> = (0..N).collect();
        assert_eq!(
            invoked, expected,
            "each step ran exactly once (crash_at={crash_at})"
        );
        // Outputs equal the never-crashed result.
        let want: Vec<Vec<u8>> = (0..N).map(|i| format!("out-{i}").into_bytes()).collect();
        assert_eq!(outputs, want);
    }
}

#[test]
fn mid_step_crash_re_runs_the_uncommitted_step_the_documented_caveat() {
    let (_tmp, path) = tmp("caveat");
    let invoked = RefCell::new(Vec::<u64>::new());
    let step = |i: u64| {
        invoked.borrow_mut().push(i);
        format!("out-{i}").into_bytes()
    };

    // "Crash" MID-step 0: its side effect runs but is NOT committed (no fsync).
    {
        let _j = WorkflowJournal::open(&path).unwrap();
        let _ = step(0); // side effect happened; we drop before committing it
    }
    // Resume: step 0 is uncommitted, so it RE-RUNS (at-least-once — the caveat).
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        assert_eq!(j.committed_count(), 0, "nothing was committed");
        j.run(2, &step).unwrap();
    }
    // step 0 ran twice (the documented mid-step caveat), step 1 once.
    assert_eq!(invoked.into_inner(), vec![0, 0, 1]);
}

#[test]
fn a_torn_or_corrupt_final_record_is_truncated_durably_and_the_prefix_resumes() {
    let step = |i: u64| format!("out-{i}").into_bytes();

    // TORN: three committed steps, then a crash mid-commit leaves half a frame.
    let (_tmp, path) = tmp("torn");
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        j.run(3, step).unwrap();
    }
    let clean_len = file_len(&path);
    let half = step_frame(STEP_VERSION, 3, b"out-3");
    {
        use std::io::Write;
        let mut raw = std::fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap();
        raw.write_all(&half[..half.len() / 2]).unwrap();
        raw.sync_all().unwrap();
    }
    assert!(file_len(&path) > clean_len);
    let invoked = RefCell::new(Vec::<u64>::new());
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        assert_eq!(j.committed_count(), 3);
        assert_eq!(j.recovery().tail, Tail::Torn);
        assert_eq!(j.recovery().valid_len as u64, clean_len);
        assert_eq!(
            file_len(&path),
            clean_len,
            "the torn tail is truncated on disk before anything is appended"
        );
        j.run(5, |i| {
            invoked.borrow_mut().push(i);
            step(i)
        })
        .unwrap();
    }
    assert_eq!(
        invoked.into_inner(),
        vec![3, 4],
        "only the uncommitted steps ran"
    );
    let _ = std::fs::remove_file(&path);

    // CORRUPT FINAL RECORD: the last committed frame's payload is damaged and
    // nothing decodable follows — indistinguishable from a torn write, so it is
    // dropped and that one step re-runs (the at-least-once caveat, at the tail).
    let (_tmp, path) = tmp("corrupt_final");
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        j.run(3, step).unwrap();
    }
    let mut bytes = std::fs::read(&path).unwrap();
    let ends = frame_ends(&bytes);
    let last = bytes.len() - 1;
    bytes[last] ^= 0xFF;
    std::fs::write(&path, &bytes).unwrap();
    let invoked = RefCell::new(Vec::<u64>::new());
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        assert_eq!(j.committed_count(), 2);
        assert_eq!(j.recovery().tail, Tail::Torn);
        assert_eq!(file_len(&path), ends[1] as u64, "truncated on disk");
        j.run(3, |i| {
            invoked.borrow_mut().push(i);
            step(i)
        })
        .unwrap();
    }
    assert_eq!(invoked.into_inner(), vec![2]);
}

#[test]
fn a_mid_journal_fault_refuses_to_open_and_never_re_runs_committed_steps() {
    let step = |i: u64| format!("out-{i}").into_bytes();

    // (1) Bit rot in step 1's frame with three fsync'd commits after it.
    let (_tmp, path) = tmp("fault_rot");
    {
        let mut j = WorkflowJournal::open(&path).unwrap();
        j.run(4, step).unwrap();
    }
    let mut bytes = std::fs::read(&path).unwrap();
    let ends = frame_ends(&bytes);
    bytes[ends[0] + 14] ^= 0x01;
    std::fs::write(&path, &bytes).unwrap();
    let err = WorkflowJournal::open(&path).unwrap_err();
    let fault = fault_of(&err);
    assert_eq!(
        fault.at, ends[0],
        "the error names the faulting frame's byte offset"
    );
    assert!(matches!(fault.kind, FaultKind::CorruptFrame(_)));
    assert!(
        err.to_string().contains(&format!("byte {}", ends[0])),
        "{err}"
    );
    assert_eq!(
        std::fs::read(&path).unwrap(),
        bytes,
        "the file is untouched"
    );
    // The explicit repair keeps the intact prefix; the operator chose to re-run
    // from the fault on.
    let invoked = RefCell::new(Vec::<u64>::new());
    {
        let mut j = WorkflowJournal::open_truncating(&path).unwrap();
        assert_eq!(j.committed_count(), 1);
        assert!(matches!(j.recovery().tail, Tail::Fault { at, .. } if at == ends[0]));
        assert_eq!(file_len(&path), ends[0] as u64, "truncated on disk");
        j.run(4, |i| {
            invoked.borrow_mut().push(i);
            step(i)
        })
        .unwrap();
    }
    assert_eq!(invoked.into_inner(), vec![1, 2, 3]);
    assert!(
        WorkflowJournal::open(&path).is_ok(),
        "repaired: a plain open works"
    );
    let _ = std::fs::remove_file(&path);

    // (2) An out-of-order step record (a gap: 0, 1, 5) — refused, untouched.
    let (_tmp, path) = tmp("fault_order");
    let mut bytes = step_frame(STEP_VERSION, 0, b"a");
    bytes.extend_from_slice(&step_frame(STEP_VERSION, 1, b"b"));
    let at = bytes.len();
    bytes.extend_from_slice(&step_frame(STEP_VERSION, 5, b"c"));
    std::fs::write(&path, &bytes).unwrap();
    let err = WorkflowJournal::open(&path).unwrap_err();
    assert_eq!(
        fault_of(&err),
        LogFault {
            at,
            kind: FaultKind::OutOfOrder {
                expected: 2,
                found: 5
            }
        }
    );
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
    let _ = std::fs::remove_file(&path);

    // (3) A step record under another STEP_VERSION — refused, untouched.
    let (_tmp, path) = tmp("fault_version");
    let mut bytes = step_frame(STEP_VERSION, 0, b"a");
    let at = bytes.len();
    bytes.extend_from_slice(&step_frame(STEP_VERSION + 1, 1, b"b"));
    std::fs::write(&path, &bytes).unwrap();
    let err = WorkflowJournal::open(&path).unwrap_err();
    assert_eq!(
        fault_of(&err),
        LogFault {
            at,
            kind: FaultKind::BadStep
        }
    );
    assert_eq!(std::fs::read(&path).unwrap(), bytes);
}

proptest! {
    /// Across ARBITRARY repeated crashes at arbitrary points, each step still runs
    /// exactly once and the outputs equal a never-crashed run.
    #[test]
    fn exactly_once_across_arbitrary_repeated_crashes(
        total in 1u64..16,
        crashes in prop::collection::vec(0u64..16, 0..6),
    ) {
        let (_tmp, path) = tmp("prop");
        let invoked = RefCell::new(Vec::<u64>::new());
        let step = |i: u64| {
            invoked.borrow_mut().push(i);
            format!("o{i}").into_bytes()
        };

        // Each "crash" resumes up to a checkpoint (clamped to total) then drops.
        for c in &crashes {
            let upto = (*c).min(total);
            let mut j = WorkflowJournal::open(&path).unwrap();
            let _ = j.run(upto, &step).unwrap();
            // journal dropped here == crash
        }
        // Final session: finish the workflow.
        let outputs = {
            let mut j = WorkflowJournal::open(&path).unwrap();
            j.run(total, &step).unwrap()
        };

        let invoked = invoked.into_inner();
        let expected: Vec<u64> = (0..total).collect();
        prop_assert_eq!(invoked, expected); // exactly-once despite repeated restarts
        let want: Vec<Vec<u8>> = (0..total).map(|i| format!("o{i}").into_bytes()).collect();
        prop_assert_eq!(outputs, want);
    }
}
