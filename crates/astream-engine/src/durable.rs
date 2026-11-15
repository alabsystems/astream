//! Rung: durable execution — a crash-resumable workflow whose steps run exactly
//! once across restarts.
//!
//! A workflow is a fixed ordered sequence of steps. [`WorkflowJournal`] commits
//! each step's output to a Strict (fsync-per-append) file as a CRC-framed step
//! record; [`WorkflowJournal::run`] runs only the steps **not yet committed** —
//! so a process that dies and restarts resumes from the last committed step,
//! re-running none of them. This is the durable-execution capability ("a workflow
//! survives a crash and resumes exactly") built on the same `astream_wire::Frame`
//! codec and Strict durability as the log. The step record itself is astream's
//! generic opaque record, [`astream_wire::steps`]: its own [`STEP_VERSION`]
//! (which versions the layout and is no stream-kind tag: the cognition
//! `COG_VERSION` is 1 too), with the torn-tail-or-fault classifier this journal
//! recovers by. It lives in the
//! zero-dependency wire crate so an embedder that keeps step records somewhere
//! other than a file (a shared-memory region bounded by a commit word) reads
//! them with the same scanner, without linking this engine and its VT fold.
//!
//! ## Exactly-once boundary (honest)
//!
//! A crash **between** commits is exactly-once: every committed step is skipped on
//! resume and every uncommitted step runs once. A crash **mid-step** — after the
//! step's side effect but before its fsync — re-runs that step on resume
//! (at-least-once), so a step's side effect must be idempotent or be the commit
//! itself. This is the stated durable-execution idempotency caveat, and the test
//! suite *witnesses* it rather than hiding it.
//!
//! ## Recovery posture
//!
//! The same as the log's ([`crate::store`]): on open the longest intact,
//! in-order step prefix is kept. A **torn tail** (an incomplete or corrupt final
//! frame with nothing decodable after it — a crash mid-commit) is truncated
//! away durably. A **fault** — a step record this build cannot read, an
//! out-of-order step, or a corrupt frame with intact frames after it — makes
//! [`open`](WorkflowJournal::open) refuse (naming the byte offset), because
//! truncating there would discard fsync'd commits and make `run` re-execute
//! their side effects; [`open_truncating`](WorkflowJournal::open_truncating) is
//! the explicit operator repair.
//!
//! One crash reads as a fault rather than a torn tail: a step whose output
//! itself holds an encoded astream frame (a record of this or any astream
//! stream), cut by the crash after that nested frame's last byte. The classifier
//! cannot tell a frame nested in the partial record from one that follows a
//! rotted length ([`astream_wire::steps`] says why), so `open` refuses that
//! journal although nothing past its committed prefix was ever acknowledged, and
//! the workflow does not resume until an operator runs `open_truncating`. The
//! error is only ever this strict one: a nested frame never makes `open` drop a
//! committed step.

use crate::store::{self, RecoverReport, Tail};
use astream_wire::steps;
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "durable_island.rs"]
mod durable_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{journal_committed_monotone, journal_step_match_or_keep};
#[cfg(clean_islands)]
pub use durable_island::{journal_committed_monotone, journal_step_match_or_keep};

contract_fn! {
    /// Kernel-certified check that a decoded journal record's step index `found_step`
    /// equals the next expected dense step index `expected_step`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `step_matches_next_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn step_matches_next(expected_step: u64, found_step: u64) -> bool
    clauses [ensures result == (expected_step == found_step)]
    {
        expected_step == found_step
    }
}

/// Multi-condition durable workflow step-commit protocol kernel:
/// admits advancing `cur_steps` to `next_steps` only when `poisoned == 0`,
/// `step_index == cur_steps`, and `cur_steps < next_steps`.
///
/// Hand-written plain Rust, not compiled from Clean: it restates
/// `Astream.Engine.TlaDurableJournal.journal_admit_step_commit_isl`, the island's
/// composition of the Clean-Origin (`I5`) transition functions
/// [`journal_step_match_or_keep`] and [`journal_committed_monotone`], and the `durable`
/// suite holds it to that composition over a grid of boundary operands.
#[must_use]
pub const fn journal_admit_step_commit(
    poisoned: u64,
    cur_steps: u64,
    step_index: u64,
    next_steps: u64,
) -> u64 {
    if poisoned == 0 && step_index == cur_steps && cur_steps < next_steps {
        next_steps
    } else {
        cur_steps
    }
}

/// Step-record format version. The record is defined in [`astream_wire::steps`],
/// whose doc of this constant says what it does and does not tell a reader (it
/// versions the layout; it equals the cognition `COG_VERSION`, so it names no
/// kind of stream); it is re-exported here, where the journal's users have
/// always found it.
pub use astream_wire::steps::STEP_VERSION;

/// The outcome of scanning a journal's bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepScan {
    /// The committed step outputs: the longest intact, in-order prefix.
    pub committed: Vec<Vec<u8>>,
    /// Byte length of that prefix.
    pub valid_len: usize,
    /// What ended it (see [`Tail`]).
    pub tail: Tail,
}

/// Scan a journal's bytes into the committed step outputs (the longest intact,
/// in-order prefix), the byte length of that prefix, and what ended it — a
/// torn tail or a fault, classified exactly like [`crate::recover`]. A step is
/// accepted only if its index is exactly the next expected one (a gap-free,
/// in-order spine, like the log's offset spine). Pure and panic-free.
///
/// The scan is [`astream_wire::steps::scan_steps_from`] from step 0; this maps
/// its body ranges to owned outputs and its end onto the log's [`Tail`].
pub fn scan_steps(bytes: &[u8]) -> StepScan {
    let scan = steps::scan_steps_from(bytes, 0);
    // Every range is a body the scan found inside these same bytes, so the
    // slice is in bounds.
    let step_len = scan.steps.len();
    let cap = if step_len < 4096 { step_len } else { 4096 };
    let mut committed = Vec::with_capacity(cap);
    for (_, body) in scan.steps {
        committed.push(bytes.get(body).unwrap_or(&[]).to_vec());
    }
    StepScan {
        committed,
        valid_len: scan.valid_len,
        tail: store::tail_of(scan.end),
    }
}

/// A Strict, crash-resumable workflow journal.
#[derive(Debug)]
pub struct WorkflowJournal {
    file: File,
    /// The durably-acked file length (where the next step frame is written).
    len: u64,
    committed: Vec<Vec<u8>>,
    poisoned: bool,
    recovery: RecoverReport,
}

impl WorkflowJournal {
    /// Open (creating if absent) the journal at `path`, recovering the committed
    /// step prefix and durably truncating a torn tail. A [`Tail::Fault`] is
    /// refused (an `InvalidData` error downcastable to [`crate::LogFault`],
    /// naming the byte offset) and the file left untouched — see the module doc.
    pub fn open(path: impl AsRef<Path>) -> io::Result<WorkflowJournal> {
        Self::open_with(path.as_ref(), false)
    }

    /// Operator repair: like [`open`](Self::open), but a [`Tail::Fault`] is
    /// truncated away too, durably. The committed prefix before the fault is
    /// kept; `run` will re-execute every step from the fault on.
    pub fn open_truncating(path: impl AsRef<Path>) -> io::Result<WorkflowJournal> {
        Self::open_with(path.as_ref(), true)
    }

    fn open_with(path: &Path, truncate_faults: bool) -> io::Result<WorkflowJournal> {
        let mut file = store::open_log_file(path)?;
        let mut existing = Vec::new();
        file.read_to_end(&mut existing)?;
        let scan = scan_steps(&existing);
        if let Tail::Fault { at, kind } = &scan.tail {
            if !truncate_faults {
                return Err(store::LogFault {
                    at: *at,
                    kind: kind.clone(),
                }
                .into_io());
            }
        }
        store::truncate_to(&mut file, scan.valid_len)?;
        let recovery = RecoverReport {
            valid_len: scan.valid_len,
            records: scan.committed.len() as u64,
            torn: scan.tail != Tail::Clean,
            tail: scan.tail,
        };
        Ok(WorkflowJournal {
            file,
            len: scan.valid_len as u64,
            committed: scan.committed,
            poisoned: false,
            recovery,
        })
    }

    /// What `open` found: the intact prefix length, the committed step count,
    /// and what ended the prefix (a torn tail it truncated, or — only via
    /// [`open_truncating`](Self::open_truncating) — a fault it truncated).
    pub fn recovery(&self) -> &RecoverReport {
        &self.recovery
    }

    /// The number of steps already committed — where a resume continues from.
    pub fn committed_count(&self) -> usize {
        self.committed.len()
    }

    /// The committed step outputs, in order.
    pub fn outputs(&self) -> &[Vec<u8>] {
        &self.committed
    }

    /// Whether a write or fsync error has poisoned this handle (see
    /// [`crate::FileLog::is_poisoned`]); appends are refused until reopened.
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Run the workflow to `total` steps. Steps already committed are skipped; each
    /// remaining step `i` is run via `step(i)` exactly once and its output committed
    /// durably (fsync) before the next step. Returns all `total` outputs in order.
    pub fn run<F>(&mut self, total: u64, mut step: F) -> io::Result<Vec<Vec<u8>>>
    where
        F: FnMut(u64) -> Vec<u8>,
    {
        let start = self.committed.len() as u64;
        let target = journal_committed_monotone(start, total);
        let mut committed_steps = start;
        for i in start..target {
            let output = step(i);
            let frame = steps::encode_step(i, &output)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "step output too large"))?;
            self.append(&frame)?;
            self.committed.push(output);
            committed_steps = journal_admit_step_commit(
                u64::from(self.poisoned),
                committed_steps,
                i,
                i.saturating_add(1),
            );
        }
        let _ = committed_steps;
        let take = usize::try_from(total)
            .unwrap_or(usize::MAX)
            .min(self.committed.len());
        Ok(self.committed.iter().take(take).cloned().collect())
    }

    /// Durable append under the log store's discipline, shared: a write or fsync
    /// error poisons the journal (every later append is refused until a reopen
    /// recovers it) after truncating the failed frame's bytes away, best effort.
    fn append(&mut self, frame_bytes: &[u8]) -> io::Result<()> {
        store::append_frame(&mut self.file, self.len, &mut self.poisoned, frame_bytes)?;
        self.len = self.len.saturating_add(frame_bytes.len() as u64);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::FaultKind;
    use astream_wire::steps::{decode_step, encode_step};
    use astream_wire::Frame;

    #[test]
    fn step_record_round_trips() {
        let bytes = encode_step(3, b"hello").unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(
            decode_step(&decoded.frame.payload),
            Some((3, &b"hello"[..]))
        );
    }

    #[test]
    fn scan_classifies_out_of_order_as_a_fault_and_a_torn_frame_as_torn() {
        // Two in-order steps, then a gap (step 5 instead of 2): the intact in-order
        // prefix is kept and the gap is a FAULT (not a crash's signature).
        let mut log = encode_step(0, b"a").unwrap();
        log.extend_from_slice(&encode_step(1, b"b").unwrap());
        let gap_at = log.len();
        log.extend_from_slice(&encode_step(5, b"c").unwrap());
        let scan = scan_steps(&log);
        assert_eq!(scan.committed, vec![b"a".to_vec(), b"b".to_vec()]);
        assert_eq!(
            scan.valid_len, gap_at,
            "the out-of-order record is excluded"
        );
        assert_eq!(
            scan.tail,
            Tail::Fault {
                at: gap_at,
                kind: FaultKind::OutOfOrder {
                    expected: 2,
                    found: 5
                }
            }
        );
        // A torn final frame is dropped, the prefix retained: a torn tail.
        let mut torn = encode_step(0, b"x").unwrap();
        let full = encode_step(1, b"y").unwrap();
        torn.extend_from_slice(&full[..full.len() - 1]);
        let scan = scan_steps(&torn);
        assert_eq!(scan.committed, vec![b"x".to_vec()]);
        assert_eq!(scan.tail, Tail::Torn);

        // An unreadable step record (another STEP_VERSION) is a fault at its offset.
        let mut versioned = encode_step(0, b"x").unwrap();
        let at = versioned.len();
        let mut p = vec![STEP_VERSION + 1];
        p.extend_from_slice(&1u64.to_le_bytes());
        p.extend_from_slice(&0u32.to_le_bytes());
        versioned.extend_from_slice(&Frame::new(p).encode().unwrap());
        let scan = scan_steps(&versioned);
        assert_eq!(scan.committed, vec![b"x".to_vec()]);
        assert_eq!(
            scan.tail,
            Tail::Fault {
                at,
                kind: FaultKind::BadStep
            }
        );

        // A clean journal ends clean.
        assert_eq!(scan_steps(&encode_step(0, b"x").unwrap()).tail, Tail::Clean);
    }

    #[test]
    fn a_rotted_step_length_with_commits_after_it_is_a_fault() {
        // Step 1's frame length now runs past the end of the journal, but step 2
        // is intact behind it: a corrupt header, not a torn commit. Truncating
        // would make `run` re-execute two committed side effects.
        let mut log = encode_step(0, b"a").unwrap();
        let at = log.len();
        log.extend_from_slice(&encode_step(1, b"b").unwrap());
        log.extend_from_slice(&encode_step(2, b"c").unwrap());
        let past_end = 2 * log.len() as u32;
        log[at + 4..at + 8].copy_from_slice(&past_end.to_le_bytes());
        let scan = scan_steps(&log);
        assert_eq!((scan.committed.len(), scan.valid_len), (1, at));
        assert_eq!(
            scan.tail,
            Tail::Fault {
                at,
                kind: FaultKind::LengthPastEnd
            }
        );
    }
}
