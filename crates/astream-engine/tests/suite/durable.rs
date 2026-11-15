//! Evidence for durable execution (`engine.durable.exactly-once-resume`): a
//! workflow survives a crash and resumes exactly. A crash is modeled as the
//! process dying after fsyncing some prefix of step records (the journal is
//! dropped); reopening recovers that prefix and resumes. The proof: across a
//! crash at EVERY inter-step boundary — and across every sequence of up to two
//! REPEATED crashes at every checkpoint — each step runs exactly once, in order,
//! no committed step re-runs, and the outputs equal a never-crashed run. The
//! honest boundary (a mid-step crash before the fsync re-runs that one step —
//! at-least-once) is witnessed by its own test, not hidden.
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

/// Across REPEATED crashes, each step still runs exactly once and the outputs equal a
/// never-crashed run. Every sequence of up to two crashes, each at any checkpoint from
/// before the first step to past the last (clamped to the workflow's length), for
/// workflows of one to three steps: no crash, one, the same point twice, a later
/// point then an earlier one, and the reverse.
#[test]
fn exactly_once_across_repeated_crashes_at_every_pair_of_points() {
    for total in 1u64..=3 {
        let points: Vec<u64> = (0..=total + 1).collect();
        let mut sequences: Vec<Vec<u64>> = vec![Vec::new()];
        sequences.extend(points.iter().map(|&a| vec![a]));
        for &a in &points {
            sequences.extend(points.iter().map(|&b| vec![a, b]));
        }
        for crashes in sequences {
            let case = format!("total {total}, crashes at {crashes:?}");
            let tag: Vec<String> = crashes.iter().map(u64::to_string).collect();
            let (_tmp, path) = tmp(&format!("repeat_{total}_{}", tag.join("_")));
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

            let expected: Vec<u64> = (0..total).collect();
            assert_eq!(invoked.into_inner(), expected, "{case}: exactly once");
            let want: Vec<Vec<u8>> = (0..total).map(|i| format!("o{i}").into_bytes()).collect();
            assert_eq!(outputs, want, "{case}: the outputs of a never-crashed run");
        }
    }
}

#[test]
fn clean_origin_durable_journal_step_admission_kernel_enforces_tla_invariants() {
    use astream_engine::durable::{
        journal_admit_step_commit, journal_committed_monotone, journal_step_match_or_keep,
        step_matches_next,
    };

    assert!(step_matches_next(3, 3));
    assert!(!step_matches_next(3, 4));
    assert_eq!(journal_committed_monotone(3, 4), 4);
    assert_eq!(journal_committed_monotone(3, 2), 3);
    assert_eq!(journal_step_match_or_keep(3, 3, 4), 4);
    assert_eq!(journal_step_match_or_keep(5, 3, 6), 3);
    // Unpoisoned (0) + matching step index (3 == 3) + monotone advance (3 < 4) -> 4
    assert_eq!(journal_admit_step_commit(0, 3, 3, 4), 4);
    // Poisoned (1) -> retains 3
    assert_eq!(journal_admit_step_commit(1, 3, 3, 4), 3);
    // Mismatched step index (5 != 3) -> retains 3
    assert_eq!(journal_admit_step_commit(0, 3, 5, 6), 3);
}

// `journal_admit_step_commit` is hand-written Rust, not compiled from Clean: it answers as
// `journal_admit_step_commit_isl`, the island's composition of `journal_step_match_or_keep`
// and `journal_committed_monotone`, on every tuple of a grid of boundary operands.
#[test]
fn journal_admit_step_commit_answers_as_its_island_composition() {
    use astream_engine::durable::{
        journal_admit_step_commit, journal_committed_monotone, journal_step_match_or_keep,
    };

    const GRID: [u64; 5] = [0, 1, 2, u64::MAX - 1, u64::MAX];
    let (mut poison_kept, mut mismatch_kept) = (false, false);
    for poisoned in GRID {
        for cur in GRID {
            for index in GRID {
                for next in GRID {
                    let advanced = journal_committed_monotone(cur, next);
                    let island = if poisoned == 0 {
                        journal_step_match_or_keep(index, cur, advanced)
                    } else {
                        cur
                    };
                    assert_eq!(
                        journal_admit_step_commit(poisoned, cur, index, next),
                        island,
                        "journal_admit_step_commit({poisoned}, {cur}, {index}, {next})"
                    );
                    let held = island != advanced;
                    poison_kept |= held && poisoned != 0 && index == cur;
                    mismatch_kept |= held && poisoned == 0 && index != cur;
                }
            }
        }
    }
    // Not vacuous: the grid reaches an advance the poison holds back, and one a step
    // index other than the next holds back.
    assert!(poison_kept && mismatch_kept);
}

#[test]
fn step_dag_resumes_diamond_and_fan_in_workflows_exactly_once_across_all_crash_pairs() {
    use astream_engine::{
        dag_committed_advance, dag_deps_satisfied, DagError, DagJournal, DagJournalFault, DagSpec,
        DagStep,
    };

    // 5-node fan-out / diamond / fan-in DAG:
    //   0 (root) -> 1, 2
    //   1, 2     -> 3 (join)
    //   0, 3     -> 4 (final sink)
    let spec = DagSpec::new(vec![
        DagStep::new(0, vec![]),
        DagStep::new(1, vec![0]),
        DagStep::new(2, vec![0]),
        DagStep::new(3, vec![2, 1]),
        DagStep::new(4, vec![0, 3]),
    ])
    .unwrap();
    assert_eq!(spec.topological_order(), &[0, 1, 2, 3, 4]);
    assert!(dag_deps_satisfied(0));
    assert!(!dag_deps_satisfied(1));
    assert_eq!(dag_committed_advance(2, 4), 4);
    assert_eq!(dag_committed_advance(4, 2), 4);

    let exec_node = |id: u64, parents: &[(u64, &[u8])]| -> Vec<u8> {
        let mut s = format!("n{id}(");
        for (idx, (pid, pbytes)) in parents.iter().enumerate() {
            if idx > 0 {
                s.push(',');
            }
            s.push_str(&format!("{pid}:{}", std::str::from_utf8(pbytes).unwrap()));
        }
        s.push(')');
        s.into_bytes()
    };

    // Baseline never-crashed run.
    let (_base_tmp, base_path) = tmp("dag_baseline");
    let baseline = {
        let mut j = DagJournal::open(&base_path, spec.clone()).unwrap();
        assert_eq!(j.ready_steps(), vec![0]);
        j.run(&exec_node).unwrap()
    };
    assert_eq!(
        std::str::from_utf8(&baseline[4]).unwrap(),
        "n4(0:n0(),3:n3(2:n2(0:n0()),1:n1(0:n0())))"
    );

    // Every pair of crash checkpoints `(c1, c2)` in `0..=6` runs each DAG node
    // ONCE and produces byte-identical outputs to `baseline`.
    let total = spec.node_count() as u64;
    for c1 in 0..=total + 1 {
        for c2 in 0..=total + 1 {
            let (_t, path) = tmp(&format!("dag_pair_{c1}_{c2}"));
            let invoked = RefCell::new(Vec::<u64>::new());
            let record_exec = |id: u64, parents: &[(u64, &[u8])]| -> Vec<u8> {
                invoked.borrow_mut().push(id);
                exec_node(id, parents)
            };
            {
                let mut j = DagJournal::open(&path, spec.clone()).unwrap();
                let _ = j.run_up_to(c1, &record_exec).unwrap();
            }
            {
                let mut j = DagJournal::open(&path, spec.clone()).unwrap();
                let _ = j.run_up_to(c2, &record_exec).unwrap();
            }
            let got = {
                let mut j = DagJournal::open(&path, spec.clone()).unwrap();
                j.run(&record_exec).unwrap()
            };
            assert_eq!(
                invoked.into_inner(),
                vec![0, 1, 2, 3, 4],
                "crashes ({c1}, {c2}): every DAG node must run once"
            );
            assert_eq!(
                got, baseline,
                "crashes ({c1}, {c2}): exact parent-fed outputs"
            );
        }
    }

    // Static cycle, self-dep, unknown-dep, duplicate-dep, and non-dense ID rejection.
    assert_eq!(
        DagSpec::new(vec![DagStep::new(0, vec![1]), DagStep::new(1, vec![0])]),
        Err(DagError::Cycle {
            remaining_nodes: vec![0, 1]
        })
    );
    assert_eq!(
        DagSpec::new(vec![DagStep::new(0, vec![0])]),
        Err(DagError::SelfDependency { step: 0 })
    );
    assert_eq!(
        DagSpec::new(vec![DagStep::new(0, vec![9])]),
        Err(DagError::UnknownDependency { step: 0, dep: 9 })
    );
    assert_eq!(
        DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0, 0])]),
        Err(DagError::DuplicateDependency { step: 1, dep: 0 })
    );
    assert_eq!(
        DagSpec::new(vec![DagStep::new(3, vec![])]),
        Err(DagError::NonDenseId {
            expected: 0,
            found: 3
        })
    );

    // Spec-drift refusal: commit nodes 0..3 under `spec`, then reopen with node 2's
    // dependency changed from `[0]` to `[0, 1]` -> refused fail-closed with SpecMismatch!
    let (_drift_tmp, drift_path) = tmp("dag_spec_drift");
    {
        let mut j = DagJournal::open(&drift_path, spec.clone()).unwrap();
        let _ = j.run_up_to(3, &exec_node).unwrap();
    }
    let drifted_spec = DagSpec::new(vec![
        DagStep::new(0, vec![]),
        DagStep::new(1, vec![0]),
        DagStep::new(2, vec![0, 1]),
        DagStep::new(3, vec![2, 1]),
        DagStep::new(4, vec![0, 3]),
    ])
    .unwrap();
    let before_bytes = std::fs::read(&drift_path).unwrap();
    let err = DagJournal::open(&drift_path, drifted_spec.clone()).unwrap_err();
    let dag_fault = err
        .get_ref()
        .and_then(|e| e.downcast_ref::<DagJournalFault>())
        .cloned()
        .expect("DagJournalFault on spec drift");
    assert!(matches!(
        dag_fault,
        DagJournalFault::SpecMismatch { node_id: 2, .. }
    ));
    assert_eq!(
        std::fs::read(&drift_path).unwrap(),
        before_bytes,
        "spec-drift refusal leaves journal untouched"
    );

    // Explicit `open_truncating` repairs from node 2 onward and finishes under `drifted_spec`.
    {
        let mut repaired = DagJournal::open_truncating(&drift_path, drifted_spec).unwrap();
        assert_eq!(repaired.committed_order(), &[0, 1]);
        let outs = repaired.run(&exec_node).unwrap();
        assert_eq!(
            std::str::from_utf8(&outs[2]).unwrap(),
            "n2(0:n0(),1:n1(0:n0()))"
        );
    }
}
