//! Rung: durable execution — a crash-resumable workflow whose steps run exactly
//! once across restarts.
//!
//! A workflow is a fixed ordered sequence of steps. [`WorkflowJournal`] commits
//! each step's output to a Strict (fsync-per-append) file as a CRC-framed step
//! record; [`WorkflowJournal::run`] runs only the steps **not yet committed** —
//! so a process that dies and restarts resumes from the last committed step,
//! re-running none of them. This is the durable-execution capability ("a workflow
//! survives a crash and resumes exactly") built on the same `astream_wire::Frame`
//! codec and Strict durability as the log; the step record format is its own
//! `STEP_VERSION`, disjoint from the VT `ENV_VERSION` and the cognition `COG_VERSION`.
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

use crate::store::{self, FaultKind, RecoverReport, Tail};
use astream_wire::{Frame, FrameError};
use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

/// Step-record format version (disjoint from the VT `ENV_VERSION` and `COG_VERSION`).
pub const STEP_VERSION: u8 = 1;

/// Fixed step-record header: version(1) + step(8) + len(4).
const STEP_HEADER: usize = 13;

/// Encode one committed step: payload = version | step:u64 LE | len:u32 LE | output,
/// wrapped in a CRC [`Frame`]. A body larger than `u32` is [`FrameError::TooLarge`].
fn encode_step(step: u64, output: &[u8]) -> Result<Vec<u8>, FrameError> {
    let mut p = Vec::with_capacity(STEP_HEADER + output.len());
    p.push(STEP_VERSION);
    p.extend_from_slice(&step.to_le_bytes());
    let len = u32::try_from(output.len()).map_err(|_| FrameError::TooLarge)?;
    p.extend_from_slice(&len.to_le_bytes());
    p.extend_from_slice(output);
    Frame::new(p).encode()
}

/// Decode one step payload (bounds-checked, panic-free). Returns `(step, output)`.
fn decode_step(payload: &[u8]) -> Option<(u64, Vec<u8>)> {
    if payload.len() < STEP_HEADER || payload[0] != STEP_VERSION {
        return None;
    }
    let step = u64::from_le_bytes(payload[1..9].try_into().ok()?);
    let len = u32::from_le_bytes(payload[9..13].try_into().ok()?) as usize;
    let end = STEP_HEADER.checked_add(len)?;
    let out = payload.get(STEP_HEADER..end)?.to_vec();
    Some((step, out))
}

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
pub fn scan_steps(bytes: &[u8]) -> StepScan {
    let mut committed: Vec<Vec<u8>> = Vec::new();
    let mut pos = 0usize;
    let tail = loop {
        match Frame::decode(&bytes[pos..]) {
            Ok(None) => break store::end_tail(bytes, pos),
            Err(e) => break store::corrupt_frame_tail(bytes, pos, e),
            Ok(Some(d)) => match decode_step(&d.frame.payload) {
                None => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::BadStep,
                    }
                }
                Some((step, _)) if step != committed.len() as u64 => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::OutOfOrder {
                            expected: committed.len() as u64,
                            found: step,
                        },
                    }
                }
                Some((_, output)) => {
                    committed.push(output);
                    pos += d.consumed;
                }
            },
        }
    };
    StepScan {
        committed,
        valid_len: pos,
        tail,
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
        let mut file = store::open_segment(path)?;
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

    /// Whether a failed rollback has poisoned this handle (see
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
        for i in start..total {
            let output = step(i);
            let frame = encode_step(i, &output)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "step output too large"))?;
            self.append(&frame)?;
            self.committed.push(output);
        }
        let take = usize::try_from(total)
            .unwrap_or(usize::MAX)
            .min(self.committed.len());
        Ok(self.committed[..take].to_vec())
    }

    /// Atomic durable append: rolls back a partial frame on a write/fsync error so
    /// the on-disk journal stays a clean prefix of committed steps, and poisons
    /// the journal if the rollback fails (the log store's discipline, shared).
    fn append(&mut self, frame_bytes: &[u8]) -> io::Result<()> {
        store::append_frame(&mut self.file, self.len, &mut self.poisoned, frame_bytes)?;
        self.len += frame_bytes.len() as u64;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_record_round_trips() {
        let bytes = encode_step(3, b"hello").unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(
            decode_step(&decoded.frame.payload),
            Some((3, b"hello".to_vec()))
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
