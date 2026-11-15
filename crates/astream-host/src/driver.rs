//! The interactive driver: input flows to a real PTY **exactly once**.
//!
//! A [`Driver`] pairs a live [`Pty`] with a single-writer [`Session`]. Each input
//! proposal is deduped by `(client_id, client_seq)` at the one ingest point: a
//! *new* proposal is recorded as an `In` and written to the PTY master; a re-sent
//! proposal is a no-op. So a keystroke re-sent after a reconnect reaches the child
//! process **at most once** — and the session log is the auditable action trace.

use crate::host::{HostError, Pty};
use astream_engine::{CausedBy, ControlToken, Effects, Offset, Session};
use std::io;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "driver_island.rs"]
mod driver_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{pty_drain_cap_select, pty_pending_clamp};
#[cfg(clean_islands)]
pub use driver_island::{pty_drain_cap_select, pty_pending_clamp};

contract_fn! {
    /// Verified PTY pending-drain buffer cap check linked via `clean-kernel-defeq`
    /// to `pending_within_cap_isl`.
    #[must_use]
    pub const fn pending_within_cap(pending_len: u64, cap: u64) -> bool
    clauses [ensures result == (pending_len <= cap)]
    {
        pending_len <= cap
    }
}

/// Multi-condition PTY concurrent-drain admission kernel:
/// admits a drained master chunk (`1`) iff `proposed_total <= cap` and
/// `chunk_len > 0` (not EOF). Rejects (`0`) once `proposed_total > cap` so
/// a child flooding the master without reading input fails closed at 8 MiB.
///
/// Composes the Clean-Origin (`I5`) primitive `pty_drain_cap_select`, matching
/// `Astream.Host.TlaPtyDriver.pty_admit_drain_chunk_isl`.
#[must_use]
pub const fn pty_admit_drain_chunk(proposed_total: u64, cap: u64, chunk_len: u64) -> u64 {
    pty_drain_cap_select(
        cap,
        proposed_total,
        0,
        pty_drain_cap_select(0, chunk_len, 1, 0),
    )
}

/// Encode `(pending_len, cap, chunk_len)` into a 24-byte little-endian diagnostic
/// snapshot using bitwise shifts.
#[must_use]
pub const fn encode_pty_drain_state(pending_len: u64, cap: u64, chunk_len: u64) -> [u8; 24] {
    [
        (pending_len & 0xFF) as u8,
        ((pending_len >> 8) & 0xFF) as u8,
        ((pending_len >> 16) & 0xFF) as u8,
        ((pending_len >> 24) & 0xFF) as u8,
        ((pending_len >> 32) & 0xFF) as u8,
        ((pending_len >> 40) & 0xFF) as u8,
        ((pending_len >> 48) & 0xFF) as u8,
        ((pending_len >> 56) & 0xFF) as u8,
        (cap & 0xFF) as u8,
        ((cap >> 8) & 0xFF) as u8,
        ((cap >> 16) & 0xFF) as u8,
        ((cap >> 24) & 0xFF) as u8,
        ((cap >> 32) & 0xFF) as u8,
        ((cap >> 40) & 0xFF) as u8,
        ((cap >> 48) & 0xFF) as u8,
        ((cap >> 56) & 0xFF) as u8,
        (chunk_len & 0xFF) as u8,
        ((chunk_len >> 8) & 0xFF) as u8,
        ((chunk_len >> 16) & 0xFF) as u8,
        ((chunk_len >> 24) & 0xFF) as u8,
        ((chunk_len >> 32) & 0xFF) as u8,
        ((chunk_len >> 40) & 0xFF) as u8,
        ((chunk_len >> 48) & 0xFF) as u8,
        ((chunk_len >> 56) & 0xFF) as u8,
    ]
}

/// Decode a 24-byte little-endian PTY drain snapshot into `(pending_len, cap, chunk_len)`
/// using bitwise shifts.
#[must_use]
pub const fn decode_pty_drain_state(b: [u8; 24]) -> (u64, u64, u64) {
    let pending_len = (b[0] as u64)
        | ((b[1] as u64) << 8)
        | ((b[2] as u64) << 16)
        | ((b[3] as u64) << 24)
        | ((b[4] as u64) << 32)
        | ((b[5] as u64) << 40)
        | ((b[6] as u64) << 48)
        | ((b[7] as u64) << 56);
    let cap = (b[8] as u64)
        | ((b[9] as u64) << 8)
        | ((b[10] as u64) << 16)
        | ((b[11] as u64) << 24)
        | ((b[12] as u64) << 32)
        | ((b[13] as u64) << 40)
        | ((b[14] as u64) << 48)
        | ((b[15] as u64) << 56);
    let chunk_len = (b[16] as u64)
        | ((b[17] as u64) << 8)
        | ((b[18] as u64) << 16)
        | ((b[19] as u64) << 24)
        | ((b[20] as u64) << 32)
        | ((b[21] as u64) << 40)
        | ((b[22] as u64) << 48)
        | ((b[23] as u64) << 56);
    (pending_len, cap, chunk_len)
}

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

    /// [`drive_input`](Self::drive_input) **gated by the session's [`ControlToken`]**:
    /// only the holder's input is written to the PTY master and committed to the
    /// session log. A non-holder is refused with
    /// [`EngineError::NotHolder`](astream_engine::EngineError::NotHolder) **before**
    /// any byte touches the PTY master, the dedup high-water, or the session log.
    pub fn drive_input_as(
        &mut self,
        token: &ControlToken,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
    ) -> Result<bool, HostError> {
        if !self
            .session
            .precheck_input_as(token, client_id, client_seq, bytes.len())?
        {
            return Ok(false);
        }
        self.pty.write_input(&bytes)?;
        self.session
            .apply_input_as(token, client_id, client_seq, bytes)?;
        Ok(true)
    }

    /// [`drive_input`](Self::drive_input) stamped with a durable [`CausedBy`] pointer
    /// (for example, an orchestrator partition's `Out` offset that caused this
    /// injected `In`).
    pub fn drive_input_caused(
        &mut self,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
        caused_by: CausedBy,
    ) -> Result<bool, HostError> {
        if !self
            .session
            .precheck_input_caused(client_id, client_seq, bytes.len(), caused_by)?
        {
            return Ok(false);
        }
        self.pty.write_input(&bytes)?;
        self.session
            .apply_input_caused(client_id, client_seq, bytes, caused_by)?;
        Ok(true)
    }

    /// [`drive_input_caused`](Self::drive_input_caused) gated by the session's
    /// [`ControlToken`], exactly like [`drive_input_as`](Self::drive_input_as).
    pub fn drive_input_caused_as(
        &mut self,
        token: &ControlToken,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
        caused_by: CausedBy,
    ) -> Result<bool, HostError> {
        if !self.session.precheck_input_caused_as(
            token,
            client_id,
            client_seq,
            bytes.len(),
            caused_by,
        )? {
            return Ok(false);
        }
        self.pty.write_input(&bytes)?;
        self.session
            .apply_input_caused_as(token, client_id, client_seq, bytes, caused_by)?;
        Ok(true)
    }

    /// The offset of the most recent [`Record::In`](astream_term::Record::In)
    /// committed in this driver's session log, or `None` if no input has been
    /// driven yet.
    #[must_use]
    pub const fn last_in_offset(&self) -> Option<Offset> {
        self.session.last_in_offset()
    }

    fn record_output_chunk(&mut self, chunk: Vec<u8>) -> Result<Offset, HostError> {
        let off = match self.session.last_in_offset() {
            Some(in_off) => self.session.append_output_caused(
                chunk,
                CausedBy {
                    partition: None,
                    offset: in_off.0,
                },
            )?,
            None => self.session.append_output(chunk)?,
        };
        Ok(off)
    }

    /// Read one chunk of the child's output.
    pub fn read_chunk(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.pty.read_chunk(buf)
    }

    /// Read one chunk of the child's output and, when non-empty (`n > 0`), record it
    /// as an `Out` in the session log (stamped with same-log `caused_by` naming
    /// [`last_in_offset`](Self::last_in_offset) when an input has been driven) so
    /// live streaming, causal retirement, and session replay stay in lockstep.
    pub fn read_and_record_chunk(&mut self, buf: &mut [u8]) -> Result<usize, HostError> {
        let n = self.pty.read_chunk(buf)?;
        if let Some(chunk) = buf.get(..n) {
            if !chunk.is_empty() {
                self.record_output_chunk(chunk.to_vec())?;
            }
        }
        Ok(n)
    }

    /// Drain the child's output to end of session, **recording each chunk as an
    /// `Out`** in the session log (stamped with same-log `caused_by` naming
    /// [`last_in_offset`](Self::last_in_offset) when an input has been driven, so
    /// the session replays to the child's screen and preserves write→read causal
    /// pointers), and returning the collected bytes.
    pub fn drain_to_eof(&mut self) -> Result<Vec<u8>, HostError> {
        let mut collected = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            let n = self.pty.read_chunk(&mut buf)?;
            if n == 0 {
                break;
            }
            let Some(chunk) = buf.get(..n) else {
                break;
            };
            self.record_output_chunk(chunk.to_vec())?;
            collected.extend_from_slice(chunk);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::PENDING_MAX;

    #[test]
    fn clean_origin_pty_drain_kernels_enforce_8mib_cap() {
        let cap = PENDING_MAX as u64;
        assert_eq!(pty_pending_clamp(4096, cap), 4096);
        assert_eq!(pty_pending_clamp(cap + 4096, cap), cap);
        assert_eq!(pty_drain_cap_select(cap, 4096, 0, 1), 1);
        assert_eq!(pty_drain_cap_select(cap, cap + 1, 0, 1), 0);
        assert_eq!(pty_admit_drain_chunk(4096, cap, 4096), 1);
        assert_eq!(pty_admit_drain_chunk(cap, cap, 4096), 1);
        assert_eq!(pty_admit_drain_chunk(cap + 1, cap, 4096), 0);
        assert_eq!(pty_admit_drain_chunk(4096, cap, 0), 0);
        assert!(pending_within_cap(cap, cap));
        assert!(!pending_within_cap(cap + 1, cap));
        let enc = encode_pty_drain_state(4096, cap, 1024);
        assert_eq!(decode_pty_drain_state(enc), (4096, cap, 1024));
    }
}
