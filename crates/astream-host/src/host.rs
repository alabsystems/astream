//! The safe PTY host API. Spawns a child on a real pseudo-terminal, drains its
//! output into [`Record::Out`] on the engine `Log`, and reaps it into
//! [`Record::Exit`]. Calls the `sys` wrappers; contains no `unsafe` itself.

use crate::sys;
use astream_engine::{Effects, EngineError, Log};
use astream_term::Record;
use std::collections::VecDeque;
use std::io::{self, Read};
use std::os::raw::c_int;

#[cfg(clean_islands)]
#[path = "host_island.rs"]
mod host_island;
#[cfg(not(clean_islands))]
pub use crate::twins::pty_reap_state_advance;
#[cfg(clean_islands)]
pub use host_island::pty_reap_state_advance;

contract_fn! {
    /// Verified check that a PTY read returned a non-empty chunk (`n > 0`),
    /// linked via `clean-kernel-defeq` to `pty_chunk_non_empty_isl`.
    #[must_use]
    pub const fn pty_chunk_non_empty(n: usize) -> bool
    clauses [ensures result == (n > 0)]
    {
        n > 0
    }
}

/// Cap on the output held in [`Pty`]'s pending buffer while a
/// [`write_input`](Pty::write_input) waits for kernel input-queue space (8 MiB).
///
/// The wait is unbounded in TIME on purpose (a terminal waits for its reader),
/// so the buffer must be bounded in SPACE: a child that never consumes its
/// input while flooding the master would otherwise grow this without limit
/// until the orchestrator is OOM-killed.
pub const PENDING_MAX: usize = 8 << 20;

/// Encode a 10-byte PTY lifecycle state frame `(pid, reaped, exit_code)` in little-endian order.
#[must_use]
pub const fn encode_pty_lifecycle_state(
    pid: i32,
    reaped: bool,
    exit_code: Option<i32>,
) -> [u8; 10] {
    let p = pid as u32;
    let r = if reaped { 1u8 } else { 0u8 };
    let (has_code, code) = match exit_code {
        Some(c) => (1u8, c as u32),
        None => (0u8, 0u32),
    };
    [
        (p & 0xFF) as u8,
        ((p >> 8) & 0xFF) as u8,
        ((p >> 16) & 0xFF) as u8,
        ((p >> 24) & 0xFF) as u8,
        r,
        has_code,
        (code & 0xFF) as u8,
        ((code >> 8) & 0xFF) as u8,
        ((code >> 16) & 0xFF) as u8,
        ((code >> 24) & 0xFF) as u8,
    ]
}

/// Decode a 10-byte PTY lifecycle state frame `(pid, reaped, exit_code)` from little-endian order.
#[must_use]
pub const fn decode_pty_lifecycle_state(bytes: &[u8; 10]) -> Option<(i32, bool, Option<i32>)> {
    let p = (bytes[0] as u32)
        | ((bytes[1] as u32) << 8)
        | ((bytes[2] as u32) << 16)
        | ((bytes[3] as u32) << 24);
    let reaped = match bytes[4] {
        0 => false,
        1 => true,
        _ => return None,
    };
    let code = (bytes[6] as u32)
        | ((bytes[7] as u32) << 8)
        | ((bytes[8] as u32) << 16)
        | ((bytes[9] as u32) << 24);
    let exit_code = match bytes[5] {
        0 if code == 0 => None,
        1 if reaped => Some(code as i32),
        _ => return None,
    };
    Some((p as i32, reaped, exit_code))
}

/// An error from the host: an OS error, or an engine append error.
#[derive(Debug)]
pub enum HostError {
    /// A syscall failed.
    Io(io::Error),
    /// Appending a record to the log failed.
    Engine(EngineError),
}

impl std::fmt::Display for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostError::Io(e) => write!(f, "pty host io error: {e}"),
            HostError::Engine(e) => write!(f, "pty host engine error: {e}"),
        }
    }
}

impl std::error::Error for HostError {}

impl From<io::Error> for HostError {
    fn from(e: io::Error) -> Self {
        HostError::Io(e)
    }
}

impl From<EngineError> for HostError {
    fn from(e: EngineError) -> Self {
        HostError::Engine(e)
    }
}

/// A live pseudo-terminal running a child process.
pub struct Pty {
    master: c_int,
    pid: libc::pid_t,
    /// The pid is settled (reaped, or `ECHILD`): never wait for or signal it again.
    reaped: bool,
    /// The exit code, once reaped (`None` if the pid settled via `ECHILD`).
    exit_code: Option<i32>,
    /// Output drained off the master while a [`write_input`](Pty::write_input)
    /// was waiting for kernel input-queue space; served by
    /// [`read_chunk`](Pty::read_chunk) ahead of fresh master reads, in order. Bounded
    /// by [`PENDING_MAX`]: past it the waiting write fails instead of growing it.
    /// A deque, so serving it a chunk at a time is linear, not quadratic, in its size.
    pending: VecDeque<u8>,
}

impl Pty {
    /// Spawn `prog` (with `args`) on a fresh pty sized `(cols, rows)`. The child
    /// runs with the pty slave as its controlling terminal and stdio.
    ///
    /// A program that cannot be exec'd (missing, not executable, not a valid
    /// image) is an `Err` here — carrying the child's exec `errno`, e.g.
    /// `NotFound` — never an `Ok` whose session merely ends in `Exit { 127 }`.
    pub fn spawn(prog: &str, args: &[&str], cols: u16, rows: u16) -> io::Result<Pty> {
        let (master, slave) = sys::open_pty(cols, rows)?;
        // spawn_child consumes `slave` (closed in the parent on every path).
        match sys::spawn_child(slave, master, prog, args) {
            Ok(pid) => Ok(Pty {
                master,
                pid,
                reaped: false,
                exit_code: None,
                pending: VecDeque::new(),
            }),
            Err(e) => {
                sys::close(master);
                Err(e)
            }
        }
    }

    /// Read one chunk of master output. `Ok(0)` at end of session. Output that
    /// was drained while a [`write_input`](Pty::write_input) waited is delivered
    /// first, in arrival order.
    pub fn read_chunk(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if !self.pending.is_empty() {
            return self.pending.read(buf);
        }
        sys::read_master(self.master, buf)
    }

    /// Write input bytes to the master, delivering **all** of them. A single
    /// `write(2)` can short-write when the line-discipline input buffer is near
    /// full, so we loop until every byte is in — a recorded `In` then never
    /// overstates what reached the child. Returns the count (`== bytes.len()`).
    ///
    /// **No deadlock on a large burst.** The line discipline echoes input to the
    /// master's read side and the child answers there too; once that output
    /// queue fills (1 KiB on macOS, ~4 KiB on Linux) the child's own write
    /// blocks, it stops reading, the input queue fills, and a blocking master
    /// write would wedge forever. So while the input queue is full this drains
    /// the master concurrently, holding what it reads for
    /// [`read_chunk`](Pty::read_chunk). It still waits (indefinitely, like a
    /// terminal) only while the child itself is not consuming input.
    ///
    /// **Bounded, not unbounded.** Output drained while waiting is held in a
    /// buffer capped at [`PENDING_MAX`] (8 MiB); past it the write FAILS ("the
    /// drain buffer filled") instead of draining on. So a child that floods the
    /// master while consuming its input slowly or not at all costs a failed
    /// write, never the orchestrator's memory: the wait is unbounded in time,
    /// never in space. Bytes already drained stay readable through
    /// [`read_chunk`](Pty::read_chunk); how many of `bytes` reached the child
    /// before the failure is unknown, so the caller must not record the write as
    /// delivered.
    pub fn write_input(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let mut off = 0;
        while off < bytes.len() {
            let Some(tail) = bytes.get(off..) else {
                break;
            };
            match sys::write_master(self.master, tail) {
                Ok(0) => return Err(io::Error::from(io::ErrorKind::WriteZero)),
                Ok(n) => off = off.saturating_add(n),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    let (readable, _writable) = sys::wait_master(self.master, true)?;
                    if readable {
                        let mut buf = [0u8; 4096];
                        match sys::try_read_master(self.master, &mut buf)? {
                            Some(0) => {
                                return Err(io::Error::new(
                                    io::ErrorKind::BrokenPipe,
                                    "the child closed the pty before all input was delivered",
                                ))
                            }
                            Some(n) => {
                                let Some(chunk) = buf.get(..n) else {
                                    break;
                                };
                                let next_len =
                                    self.pending.len().saturating_add(chunk.len()) as u64;
                                self.pending.extend(chunk);
                                if crate::driver::pty_admit_drain_chunk(
                                    next_len,
                                    PENDING_MAX as u64,
                                    chunk.len() as u64,
                                ) == 0
                                    || !crate::driver::pending_within_cap(
                                        self.pending.len() as u64,
                                        PENDING_MAX as u64,
                                    )
                                {
                                    return Err(io::Error::other(
                                        "the drain buffer filled (8 MiB) while the child was not consuming its input",
                                    ));
                                }
                            }
                            None => {}
                        }
                    }
                }
                Err(e) => return Err(e),
            }
        }
        Ok(bytes.len())
    }

    /// Resize the terminal (`TIOCSWINSZ`).
    pub fn resize(&mut self, cols: u16, rows: u16) -> io::Result<()> {
        sys::set_winsize(self.master, cols, rows)
    }

    /// Reap the child, returning its exit code (`128 + signal` if killed).
    ///
    /// `ECHILD` (the kernel has no such un-reaped child of ours — e.g. the
    /// process runs with `SIGCHLD=SIG_IGN` and auto-reaps) is an error to the
    /// caller but still **settles** the child: the pid may already be recycled,
    /// so `Drop` must never `SIGKILL` it afterwards.
    ///
    /// Once the child is settled, later calls return the same outcome without
    /// calling `waitpid` again: a recycled pid could be another child of this
    /// process, whose exit status a second wait would steal.
    pub fn reap(&mut self) -> io::Result<i32> {
        if self.reaped {
            return match self.exit_code {
                Some(code) => Ok(code),
                None => Err(io::Error::from_raw_os_error(libc::ECHILD)),
            };
        }
        let outcome = sys::reap(self.pid);
        if sys::reap_settles(&outcome) {
            self.reaped = pty_reap_state_advance(u64::from(self.reaped), 1) != 0;
            self.exit_code = match &outcome {
                Ok(code) => Some(*code),
                Err(_) => None,
            };
        }
        outcome
    }

    /// Drive the recording to end of session: append each output chunk as
    /// `Record::Out` to the log through the seam, then reap and append
    /// `Record::Exit`. Returns the `Out` records in the order the kernel
    /// delivered them (for the live-screen oracle).
    ///
    /// This is the freeze point: once each chunk is appended, the session is a
    /// pure function of the stored log (`Log::append` reads `ts_logical` through
    /// the seam clock and frames the record onto the seam disk).
    pub fn record_to_eof<E: Effects>(
        &mut self,
        log: &mut Log,
        fx: &mut E,
    ) -> Result<Vec<Record>, HostError> {
        let mut chunks: Vec<Record> = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            let n = self.read_chunk(&mut buf)?;
            if !pty_chunk_non_empty(n) {
                break;
            }
            let Some(chunk) = buf.get(..n) else {
                break;
            };
            let rec = Record::Out(chunk.to_vec());
            log.append(fx, rec.clone())?;
            chunks.push(rec);
        }
        let code = self.reap()?;
        log.append(fx, Record::Exit { code })?;
        Ok(chunks)
    }
}

impl Drop for Pty {
    fn drop(&mut self) {
        sys::close(self.master);
        if !self.reaped {
            // Kill the child BEFORE reaping. `reap` uses a blocking `waitpid`, so
            // dropping a Pty whose long-running child has not exited (and does not
            // die from the master close / SIGHUP) would otherwise hang the
            // destructor forever. SIGKILL guarantees the child terminates, so the
            // best-effort reap returns promptly and no zombie is left behind.
            // Only reached while the pid is still ours (never after a reap that
            // settled — success or ECHILD — so a recycled pid is never signalled).
            sys::kill(self.pid, libc::SIGKILL);
            let _ = sys::reap(self.pid);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pty_lifecycle_state_roundtrips_and_validates() {
        let live = encode_pty_lifecycle_state(4242, false, None);
        assert_eq!(decode_pty_lifecycle_state(&live), Some((4242, false, None)));
        let exited = encode_pty_lifecycle_state(4242, true, Some(137));
        assert_eq!(
            decode_pty_lifecycle_state(&exited),
            Some((4242, true, Some(137)))
        );
        let echild = encode_pty_lifecycle_state(4242, true, None);
        assert_eq!(
            decode_pty_lifecycle_state(&echild),
            Some((4242, true, None))
        );
        let mut bad = live;
        bad[5] = 1; // exit_code present while reaped == false
        assert_eq!(decode_pty_lifecycle_state(&bad), None);
    }
}
