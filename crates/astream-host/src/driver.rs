//! The interactive driver: input flows to a real PTY **exactly once**.
//!
//! A [`Driver`] pairs a live [`Pty`] with a single-writer [`Session`]. Each input
//! proposal is deduped by `(client_id, client_seq)` at the one ingest point: a
//! *new* proposal is recorded as an `In` and written to the PTY master; a re-sent
//! proposal is a no-op. So a keystroke re-sent after a reconnect reaches the child
//! process **at most once** — and the session log is the auditable action trace.

use crate::host::{HostError, Pty};
use astream_engine::{Effects, Session};
use std::io;

/// A live PTY plus the single-writer session that dedups input to it.
pub struct Driver<E: Effects> {
    pty: Pty,
    session: Session<E>,
}

impl<E: Effects> Driver<E> {
    /// Wrap a spawned [`Pty`] and a fresh session over the seam `fx`.
    pub fn new(pty: Pty, fx: E) -> Driver<E> {
        Driver {
            pty,
            session: Session::new(fx),
        }
    }

    /// Apply an input proposal exactly once. A new `(client_id, client_seq)` is
    /// written to the PTY master and then recorded as an `In` (`Ok(true)`); a
    /// duplicate is dropped (`Ok(false)`) — it never reaches the child a second time.
    ///
    /// The PTY write happens **before** the `In` is recorded, so the audit log
    /// never overstates delivery: if the write fails, the error propagates with
    /// the dedup high-water unbumped, leaving the keystroke re-sendable. The
    /// at-most-once guarantee is preserved by the up-front
    /// [`precheck_input`](astream_engine::Session::precheck_input): it drops a
    /// re-sent proposal before any write, and it refuses a proposal whose `In`
    /// could not be committed (a body over the frame payload cap, or an
    /// exhausted offset space) **before** the bytes reach the child — so the
    /// commit after a delivery cannot fail and leave the high-water unbumped
    /// (which would let a re-send deliver the keystroke a second time).
    ///
    /// Any number of proposals may be driven before a drain: while the pty's
    /// kernel input queue is full the write drains the child's output
    /// concurrently (held for [`read_chunk`](Driver::read_chunk) /
    /// [`drain_to_eof`](Driver::drain_to_eof)), so a burst larger than the
    /// queues cannot deadlock the orchestrator against an echoing child. That
    /// concurrent drain is bounded ([`PENDING_MAX`](crate::host::PENDING_MAX),
    /// 8 MiB): a child that never reads its input while flooding the master
    /// fails the write rather than growing the orchestrator's memory without
    /// limit.
    pub fn drive_input(
        &mut self,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
    ) -> Result<bool, HostError> {
        if !self
            .session
            .precheck_input(client_id, client_seq, bytes.len())?
        {
            return Ok(false);
        }
        // Deliver to the real child first; only commit the In once it is actually written.
        self.pty.write_input(&bytes)?;
        self.session.apply_input(client_id, client_seq, bytes)?;
        Ok(true)
    }

    /// Read one chunk of the child's output.
    pub fn read_chunk(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.pty.read_chunk(buf)
    }

    /// Drain the child's output to end of session, **recording each chunk as an
    /// `Out`** in the session log (so the session replays to the child's screen),
    /// and returning the collected bytes.
    pub fn drain_to_eof(&mut self) -> Result<Vec<u8>, HostError> {
        let mut collected = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            let n = self.pty.read_chunk(&mut buf)?;
            if n == 0 {
                break;
            }
            self.session.append_output(buf[..n].to_vec())?;
            collected.extend_from_slice(&buf[..n]);
        }
        Ok(collected)
    }

    /// Reap the child, returning its exit code.
    pub fn reap(&mut self) -> io::Result<i32> {
        self.pty.reap()
    }

    /// The recorded session log (the auditable input trace, for replay).
    pub fn log_bytes(&mut self) -> Vec<u8> {
        self.session.log_bytes()
    }
}
