//! Durable storage and crash recovery (rung 1.5: the Strict durability dial).
//!
//! [`FileLog`] is one append-only file (no segments: it never rotates or splits)
//! that fsyncs every append (Strict: a record is acked only once it is on disk). On open it runs [`recover`], which scans
//! frames from the start, accepts the longest intact prefix — every fsync-acked
//! record — and classifies what ended it, the [`Tail`]:
//!
//! * a **torn tail** ([`Tail::Torn`]): an incomplete or corrupt final frame
//!   with nothing decodable after it — the on-disk state a `kill -9` mid-append
//!   leaves. `open` truncates it away, durably, and reports it.
//! * a **fault** ([`Tail::Fault`]): a frame that decodes but whose envelope this
//!   build cannot read (another `ENV_VERSION`), a record whose `seq` is out of
//!   sequence, or a corrupt or length-rotted frame that is *followed by* a
//!   decodable one (bit rot mid-log). None of these is a crash's signature, so
//!   `open` **refuses** with an error naming the byte offset, rather than
//!   fsync'ing a truncation that destroys acked records (or silently wipes a
//!   whole log written by another envelope version). An operator repairs with
//!   the explicit [`FileLog::open_truncating`]. (One crash does read as a fault:
//!   a record whose payload itself holds an encoded astream frame, cut after
//!   that nested frame's last byte, which no reader of the bytes can tell from a
//!   rotted length — [`astream_wire::steps`] has the case. It costs a refusal,
//!   never an acked record.)
//!
//! Recovery is a pure function of the stored bytes, so it is deterministic and
//! testable with no I/O; the file wrapper adds the real fsync and the truncate.
//! `open` also fsyncs the parent directory (Unix), so the file's directory
//! entry is as durable as the appends that follow.
//!
//! Any write or fsync error **poisons** the log: every later append is refused
//! with [`Poisoned`] until the file is reopened (and recovered). A failed fsync
//! cannot be retried into a durable one (the kernel may have dropped the pages it
//! could not write back, the last acked bytes' page among them), so after one the
//! process no longer knows what is on disk; only recovery against the file does.
//! The failed frame's bytes are truncated away first, best effort, so the reopen
//! is likelier to find a clean prefix.
//!
//! Deferred to a later rung: batched/Relaxed durability (fsync per batch rather
//! than per append), segment rotation, and compaction (so a log can start at a
//! non-zero offset — recovery here assumes the log begins at [`Offset::ZERO`]).

use crate::envelope::{EnvelopeError, EnvelopeMetadata};
use astream_wire::frame::decode_frame_slice;
use astream_wire::steps::{self, StepEnd, StepFault};
#[cfg(test)]
use astream_wire::Frame;
use astream_wire::{FrameError, Offset};
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "store_island.rs"]
mod store_island;
#[cfg(not(clean_islands))]
pub use crate::twins::store_advance_valid_len;
#[cfg(clean_islands)]
pub use store_island::store_advance_valid_len;

contract_fn! {
    /// Kernel-certified sequence-spine check during log recovery: returns `true`
    /// iff the decoded envelope's sequence number `found_seq` equals the expected
    /// dense offset `expected_seq`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `store_seq_matches_expected_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn store_seq_matches_expected(found_seq: u64, expected_seq: u64) -> bool
    clauses [ensures result == (found_seq == expected_seq)]
    {
        found_seq == expected_seq
    }
}

/// What ended the intact prefix of a stored log, and whether truncating there
/// is safe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tail {
    /// The bytes end exactly at a frame boundary: a clean log.
    Clean,
    /// Bytes beyond the prefix that hold no complete readable record: an
    /// incomplete or corrupt frame with nothing decodable after it. This is what
    /// a crash mid-append leaves, and truncating it is safe. (A rotted length
    /// field on the very last frame looks the same, and is truncated too.)
    Torn,
    /// Not a crash's signature: the frame at byte `at` is readable-but-wrong, or
    /// corrupt with intact frames after it. Truncating here would destroy acked
    /// records, so a plain open refuses. (The exception is a crash's partial
    /// frame whose payload nests a complete frame of its own; see the module
    /// doc.)
    Fault {
        /// Byte offset of the offending frame in the file.
        at: usize,
        /// Why it is a fault.
        kind: FaultKind,
    },
}

/// Why a frame is a [`Tail::Fault`] rather than a torn tail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FaultKind {
    /// The frame is corrupt (bad magic/version/flags/CRC) yet a complete frame
    /// decodes after it — damage inside the log, not at its end.
    CorruptFrame(FrameError),
    /// The frame's length runs past the end of the log, yet a complete frame
    /// decodes after it — a corrupt length field, not a torn write.
    LengthPastEnd,
    /// The frame is intact but its payload is not an envelope this build can
    /// read — typically a log written under a different `ENV_VERSION`.
    BadEnvelope(EnvelopeError),
    /// The frame is intact but its payload is not a step record this build
    /// understands (the workflow journal's analogue of `BadEnvelope`).
    BadStep,
    /// The record is intact but its stored sequence number is not the next
    /// expected one.
    OutOfOrder {
        /// The sequence number the scan expected.
        expected: u64,
        /// The sequence number stored in the record.
        found: u64,
    },
    /// The step record is intact but follows one at step `u64::MAX`, after which
    /// no step can come (the workflow journal's name for the wire's
    /// [`StepFault::PastLastStep`]). The journal counts from step 0, so it
    /// would take 2^64 records to see one; the variant exists so the map from
    /// the wire's verdicts stays total.
    ///
    /// It is the one change the move of the step codec into `astream-wire`
    /// made to this crate's public API, and a deliberate one: the alternative was
    /// to map the wire's verdict onto a variant that misnames it (`OutOfOrder`
    /// has no `expected` to report, and `BadStep` names a record this build
    /// cannot read, where this one reads). The enum
    /// stays exhaustive on purpose, as astream's decision enums are (the
    /// broker's `Transport` says why): a caller that decides per kind whether
    /// to repair or to refuse should be made by the compiler to decide on a new
    /// kind, not pass it through a wildcard arm.
    PastLastStep {
        /// The step stored in the record.
        found: u64,
    },
}

impl std::fmt::Display for FaultKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FaultKind::CorruptFrame(e) => {
                write!(f, "corrupt frame ({e}) followed by a decodable frame")
            }
            FaultKind::LengthPastEnd => write!(
                f,
                "frame length runs past the end of the log but a decodable frame follows it"
            ),
            FaultKind::BadEnvelope(e) => write!(f, "unreadable record envelope ({e})"),
            FaultKind::BadStep => write!(f, "unreadable step record"),
            FaultKind::OutOfOrder { expected, found } => {
                write!(f, "out-of-order record (seq {found}, expected {expected})")
            }
            FaultKind::PastLastStep { found } => write!(
                f,
                "step record after the last representable step (step {found} follows step {})",
                u64::MAX
            ),
        }
    }
}

/// The error a plain open returns for a [`Tail::Fault`]. It travels inside the
/// `io::Error` (kind `InvalidData`) so a caller can `downcast_ref` to it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LogFault {
    /// Byte offset of the offending frame.
    pub at: usize,
    /// Why it is a fault.
    pub kind: FaultKind,
}

impl std::fmt::Display for LogFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "log fault at byte {}: {} — not a torn tail, so open refuses to truncate it \
             (repair with the explicit open_truncating)",
            self.at, self.kind
        )
    }
}

impl std::error::Error for LogFault {}

impl LogFault {
    /// Wrap as the `io::Error` `open` returns.
    pub(crate) fn into_io(self) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, self)
    }
}

/// The outcome of scanning a (possibly torn) stored log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoverReport {
    /// Bytes of the longest intact prefix — where a clean log ends, and where a
    /// torn log must be truncated to.
    pub valid_len: usize,
    /// Number of intact records recovered.
    pub records: u64,
    /// Whether bytes beyond the intact prefix exist (`tail != Clean`). A plain
    /// open discards them only for a torn tail; a fault makes it refuse.
    pub torn: bool,
    /// What ended the intact prefix.
    pub tail: Tail,
}

/// Scan a stored byte log and report the longest intact, in-sequence prefix
/// and what ended it.
///
/// A frame is accepted only if it decodes (magic/version/length/CRC all valid),
/// its payload is a valid [`Envelope`](crate::Envelope), and its `seq` is exactly the next
/// expected offset. The first frame that fails any check ends the intact
/// prefix, classified as a torn tail or a fault (see [`Tail`]). Pure and
/// panic-free.
pub fn recover(bytes: &[u8]) -> RecoverReport {
    let mut pos = 0usize;
    let mut records = 0u64;
    let mut expected = Offset::ZERO;
    let tail = loop {
        let Some((_, tail)) = bytes.split_at_checked(pos) else {
            break end_tail(bytes, pos);
        };
        match decode_frame_slice(tail) {
            // No complete frame at `pos`: a clean end, a torn tail, or a rotted
            // length field.
            Ok(None) => break end_tail(bytes, pos),
            // A complete-but-corrupt frame (or an unreadable header).
            Err(e) => break corrupt_frame_tail(bytes, pos, e),
            Ok(Some((payload, consumed))) => match EnvelopeMetadata::from_payload(payload) {
                Err(e) => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::BadEnvelope(e),
                    }
                }
                Ok(env) if !store_seq_matches_expected(env.seq.0, expected.0) => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::OutOfOrder {
                            expected: expected.0,
                            found: env.seq.0,
                        },
                    }
                }
                Ok(_) => {
                    let next_pos = pos.saturating_add(consumed);
                    pos = store_advance_valid_len(pos as u64, next_pos as u64) as usize;
                    records = records.saturating_add(1);
                    match expected.checked_next() {
                        Some(n) => expected = n,
                        None => break end_tail(bytes, pos),
                    }
                }
            },
        }
    };
    RecoverReport {
        valid_len: pos,
        records,
        torn: tail != Tail::Clean,
        tail,
    }
}

/// The tail when no complete frame starts at `pos` (`Frame::decode` needs more
/// bytes than the log holds). Usually the incomplete final frame a crash
/// mid-append leaves; but if a complete frame decodes after `pos`, the frame's
/// length field is what is wrong, and truncating would destroy acked records.
///
/// The rule is [`astream_wire::steps::end_without_frame`], shared with every
/// reader of step records; this names its answer in the log's [`Tail`].
fn end_tail(bytes: &[u8], pos: usize) -> Tail {
    tail_of(steps::end_without_frame(bytes, pos))
}

/// The frame at `pos` failed to decode with `e`. If any complete frame decodes
/// somewhere after it, the damage is inside the log — a fault. If nothing after
/// it decodes, it is the tail a crash left, and truncating it is safe.
///
/// The rule is [`astream_wire::steps::end_at_corrupt_frame`] (and its byte-by-byte
/// [`astream_wire::steps::frame_decodes_after`]), shared with every reader of step
/// records.
fn corrupt_frame_tail(bytes: &[u8], pos: usize, e: FrameError) -> Tail {
    tail_of(steps::end_at_corrupt_frame(bytes, pos, e))
}

/// The log's name for what ended a run of frames. The wire's [`StepEnd`] and
/// [`StepFault`] are the same classification minus the one fault only an
/// envelope reader can find ([`FaultKind::BadEnvelope`]), so the map is total
/// and loses nothing.
pub(crate) const fn tail_of(end: StepEnd) -> Tail {
    match end {
        StepEnd::Clean => Tail::Clean,
        StepEnd::Torn => Tail::Torn,
        StepEnd::Fault { at, kind } => Tail::Fault {
            at,
            kind: fault_of(kind),
        },
    }
}

const fn fault_of(kind: StepFault) -> FaultKind {
    match kind {
        StepFault::CorruptFrame(e) => FaultKind::CorruptFrame(e),
        StepFault::LengthPastEnd => FaultKind::LengthPastEnd,
        StepFault::BadStep => FaultKind::BadStep,
        StepFault::OutOfOrder { expected, found } => FaultKind::OutOfOrder { expected, found },
        StepFault::PastLastStep { found } => FaultKind::PastLastStep { found },
    }
}

/// A single-file log with Strict (fsync-per-append) durability and
/// recover-on-open. Holds a byte mirror of the durable contents so a recovered
/// log can be replayed via [`crate::Log::read_bytes`] (or
/// [`crate::MemDisk::from_bytes`] + [`crate::Log::read_from`]).
#[derive(Debug)]
pub struct FileLog {
    file: File,
    mirror: Vec<u8>,
    poisoned: bool,
}

impl FileLog {
    /// Open (creating if absent) the log at `path`, recovering it: a torn tail
    /// is scanned off, and the file is truncated to the intact prefix and
    /// fsync'd (so records a dead writer wrote but never synced are durable
    /// before they are served). A
    /// [`Tail::Fault`] (an unreadable envelope version, an out-of-sequence
    /// record, a corrupt frame with intact frames after it) is **refused**: the
    /// error (kind `InvalidData`, downcastable to [`LogFault`]) names the byte
    /// offset and the file is left untouched. Returns the log positioned for
    /// appending plus the recovery report.
    pub fn open(path: impl AsRef<Path>) -> io::Result<(FileLog, RecoverReport)> {
        Self::open_with(path.as_ref(), false)
    }

    /// Operator repair: like [`open`](Self::open), but a [`Tail::Fault`] is
    /// truncated away too — everything from the faulting frame on is discarded,
    /// durably. Only for an explicit decision to keep the intact prefix.
    pub fn open_truncating(path: impl AsRef<Path>) -> io::Result<(FileLog, RecoverReport)> {
        Self::open_with(path.as_ref(), true)
    }

    fn open_with(path: &Path, truncate_faults: bool) -> io::Result<(FileLog, RecoverReport)> {
        let mut file = open_log_file(path)?;
        let mut existing = Vec::new();
        file.read_to_end(&mut existing)?;
        let report = recover(&existing);
        if let Tail::Fault { at, kind } = &report.tail {
            if !truncate_faults {
                return Err(LogFault {
                    at: *at,
                    kind: kind.clone(),
                }
                .into_io());
            }
        }
        truncate_to(&mut file, report.valid_len)?;
        existing.truncate(report.valid_len);
        Ok((
            FileLog {
                file,
                mirror: existing,
                poisoned: false,
            },
            report,
        ))
    }

    /// Append framed record bytes and fsync before returning (Strict durability:
    /// the bytes are on disk when this returns `Ok`).
    ///
    /// If the write or the fsync fails, nothing is acked, the mirror is
    /// unchanged, and the log is poisoned (see [`is_poisoned`](Self::is_poisoned)):
    /// every later append is refused with [`Poisoned`] until the file is reopened,
    /// because after a failed fsync the on-disk contents are unknown. The failed
    /// frame's bytes are truncated back to the last acked length (`mirror.len()`)
    /// first, best effort.
    pub fn append(&mut self, frame_bytes: &[u8]) -> io::Result<()> {
        append_frame(
            &mut self.file,
            self.mirror.len() as u64,
            &mut self.poisoned,
            frame_bytes,
        )?;
        self.mirror.extend_from_slice(frame_bytes);
        Ok(())
    }

    /// Whether a write or fsync error has poisoned this handle: the on-disk
    /// contents are unknown, so appends are refused until the file is reopened
    /// and recovered.
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// The durable contents (the recovered prefix plus anything appended since).
    pub fn bytes(&self) -> &[u8] {
        &self.mirror
    }
}

/// Open `path` read+write, creating it if absent, then fsync the parent
/// directory (Unix) so the entry survives a power loss: fsync'ing the file alone
/// does not make its directory entry durable.
pub(crate) fn open_log_file(path: &Path) -> io::Result<File> {
    open_log_file_with(path, sync_parent_dir)
}

/// [`open_log_file`] with the directory fsync injectable, so a test can see it.
fn open_log_file_with(path: &Path, sync_dir: fn(&Path) -> io::Result<()>) -> io::Result<File> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)?;
    // On every open, not only the one that creates the file: an earlier open
    // may have created it and then died (or failed) before its directory fsync.
    sync_dir(path)?;
    Ok(file)
}

/// Flush the directory that names `path`, tolerating NO error. This log and the broker's
/// Strict tier make the same promise (an acked record survives a power loss) and meet the
/// same volume: one whose directory entries cannot be flushed here
/// (`astream_sys::dir_flush_unavailable`: a volume that refuses to flush a directory, a
/// write-only directory). They choose differently there. The broker's `sync_parent_dir`
/// opens anyway, rather than refuse a log that works, and its `Durability::Strict` names
/// the entry a power loss can take. This log keeps the promise instead of the reach: an
/// open refuses where the entry cannot be made durable, so the caller learns the volume
/// cannot hold it rather than being acked into a file whose entry was never flushed.
#[cfg(unix)]
fn sync_parent_dir(path: &Path) -> io::Result<()> {
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    File::open(parent)?.sync_all()
}

#[cfg(not(unix))]
fn sync_parent_dir(_path: &Path) -> io::Result<()> {
    // A directory handle cannot be fsync'd portably here; the file data itself
    // is still fsync'd per append.
    Ok(())
}

/// Truncate `file` to the recovered `valid_len`, fsync, and leave the cursor at
/// EOF.
///
/// The fsync runs even when nothing was cut. A process that died between a
/// write and its fsync leaves complete frames it never acked, still only in the
/// page cache; recovery accepts them, so they must be durable before this
/// process builds on them (a dedup high-water, a skipped workflow step). When
/// something was cut, the same fsync keeps a power loss from resurrecting it.
pub(crate) fn truncate_to<W: LogFile>(file: &mut W, valid_len: usize) -> io::Result<()> {
    file.resize_file(valid_len as u64)?;
    file.sync_all()?;
    file.seek_end()
}

/// The handful of file operations the atomic append and the recovery truncate
/// need. Abstracted behind a trait so those paths can be exercised with injected
/// failures (a real `File` cannot be made to short-write on demand).
pub(crate) trait LogFile {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()>;
    fn sync_data(&mut self) -> io::Result<()>;
    fn sync_all(&mut self) -> io::Result<()>;
    fn resize_file(&mut self, size: u64) -> io::Result<()>;
    fn seek_end(&mut self) -> io::Result<()>;
}

impl LogFile for File {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        Write::write_all(self, buf)
    }
    fn sync_data(&mut self) -> io::Result<()> {
        File::sync_data(self)
    }
    fn sync_all(&mut self) -> io::Result<()> {
        File::sync_all(self)
    }
    fn resize_file(&mut self, size: u64) -> io::Result<()> {
        let op: fn(&File, u64) -> io::Result<()> = File::set_len;
        op(self, size)
    }
    fn seek_end(&mut self) -> io::Result<()> {
        fn file_seek_end(file: &mut File) -> io::Result<()> {
            match Seek::seek(file, SeekFrom::End(0)) {
                Ok(_) => Ok(()),
                Err(err) => Err(err),
            }
        }
        let op: fn(&mut File) -> io::Result<()> = file_seek_end;
        op(self)
    }
}

/// The refusal every append to a poisoned handle gets: an earlier write or fsync
/// failed, so what is on disk is no longer known to equal what was acked, and only
/// a reopen (which re-runs [`recover`] against the file) may append again.
///
/// It reaches the caller as the payload of an [`io::Error`] of kind
/// [`io::ErrorKind::Other`]; [`Poisoned::is`] tells it from any other error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Poisoned;

impl std::fmt::Display for Poisoned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(
            "log poisoned by an earlier write or fsync error (the on-disk tail is unknown); reopen to recover",
        )
    }
}

impl std::error::Error for Poisoned {}

impl Poisoned {
    /// Whether `err` is a poisoned handle's refusal.
    #[must_use]
    pub fn is(err: &io::Error) -> bool {
        err.get_ref().is_some_and(|inner| inner.is::<Poisoned>())
    }
}

/// Append `frame_bytes` durably; any write or fsync error poisons the handle.
///
/// `committed` is the last durably-acked file length, where the write cursor
/// sits; the caller advances it by `frame_bytes.len()` only when this returns
/// `Ok`.
///
/// On a `write_all` or `sync_data` error, `poisoned` is set and every later call
/// is refused with [`Poisoned`], whatever the rollback does. A failed fsync is
/// not retryable: the kernel may already have marked the pages it could not write
/// back clean and dropped them (PostgreSQL's "fsyncgate", 2018; Rebello et al.,
/// USENIX ATC '20), and the page holding the last acked bytes may be among them,
/// so a later fsync that succeeds proves nothing about what is on disk. Only a
/// reopen, which re-runs [`recover`] against the file, knows the acked prefix again.
///
/// Before returning the error, the bytes past `committed` are truncated away (not
/// fsynced) so a reopen is likelier to find the clean prefix; recovery does not
/// depend on it. The error keeps the original error's kind, and names a failed
/// rollback too.
pub(crate) fn append_frame<W: LogFile>(
    file: &mut W,
    committed: u64,
    poisoned: &mut bool,
    frame_bytes: &[u8],
) -> io::Result<()> {
    if *poisoned {
        return Err(io::Error::other(Poisoned));
    }
    if let Err(e) = file.write_all(frame_bytes).and_then(|()| file.sync_data()) {
        *poisoned = true;
        let rollback = match file.resize_file(committed).and_then(|()| file.seek_end()) {
            Ok(()) => String::new(),
            Err(rb) => format!("; rollback failed ({rb})"),
        };
        return Err(io::Error::new(
            e.kind(),
            format!("{e}{rollback}: the log is poisoned, reopen to recover"),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Removes its file when dropped, so a test leaves nothing behind whether it
    /// passes or panics.
    struct Cleanup(std::path::PathBuf);

    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    /// A file mock whose next write can be made to write `n` partial bytes and
    /// then fail, whose next `sync_data` can be made to fail (EIO: writeback lost,
    /// nothing reaches `durable`), and whose `set_len` can be made to fail — so the
    /// rollback and the poison on every write or fsync error are observable.
    /// `durable` is what a power loss would leave: `data` as of the last sync.
    struct FlakyFile {
        data: Vec<u8>,
        durable: Vec<u8>,
        fail_partial: Option<usize>,
        fail_sync: bool,
        fail_set_len: bool,
        set_len_calls: usize,
        writes: usize,
    }

    impl FlakyFile {
        fn new() -> Self {
            FlakyFile {
                data: Vec::new(),
                durable: Vec::new(),
                fail_partial: None,
                fail_sync: false,
                fail_set_len: false,
                set_len_calls: 0,
                writes: 0,
            }
        }
    }

    /// What `FileLog::append` does around `append_frame`: the acked mirror
    /// grows only when the append succeeded.
    fn append(
        f: &mut FlakyFile,
        mirror: &mut Vec<u8>,
        poisoned: &mut bool,
        bytes: &[u8],
    ) -> io::Result<()> {
        append_frame(f, mirror.len() as u64, poisoned, bytes)?;
        mirror.extend_from_slice(bytes);
        Ok(())
    }

    impl LogFile for FlakyFile {
        fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
            self.writes += 1;
            match self.fail_partial.take() {
                Some(n) => {
                    let part = n.min(buf.len());
                    self.data.extend_from_slice(&buf[..part]); // a torn partial frame
                    Err(io::Error::from(io::ErrorKind::StorageFull))
                }
                None => {
                    self.data.extend_from_slice(buf);
                    Ok(())
                }
            }
        }
        fn sync_data(&mut self) -> io::Result<()> {
            if std::mem::take(&mut self.fail_sync) {
                return Err(io::Error::from_raw_os_error(5)); // EIO
            }
            self.durable = self.data.clone();
            Ok(())
        }
        fn sync_all(&mut self) -> io::Result<()> {
            self.durable = self.data.clone();
            Ok(())
        }
        fn resize_file(&mut self, size: u64) -> io::Result<()> {
            self.set_len_calls += 1;
            if self.fail_set_len {
                return Err(io::Error::from(io::ErrorKind::Other));
            }
            self.data.truncate(size as usize);
            Ok(())
        }
        fn seek_end(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    /// Three small records under the seeded seam, and the byte offset where each
    /// frame ends.
    fn three_frames() -> (Vec<u8>, Vec<usize>) {
        use astream_term::Record;
        let bytes = crate::log::recorded(
            1,
            &[
                Record::Out(b"a".to_vec()),
                Record::Out(b"b".to_vec()),
                Record::Out(b"c".to_vec()),
            ],
        );
        let mut ends = Vec::new();
        let mut pos = 0;
        while let Ok(Some(d)) = Frame::decode(&bytes[pos..]) {
            pos += d.consumed;
            ends.push(pos);
        }
        (bytes, ends)
    }

    /// Overwrite the `u32` length field of the frame starting at `at`.
    fn set_frame_len(bytes: &mut [u8], at: usize, len: u32) {
        bytes[at + 4..at + 8].copy_from_slice(&len.to_le_bytes());
    }

    #[test]
    fn a_rotted_length_field_mid_log_is_a_fault_not_a_torn_tail() {
        let (stored, ends) = three_frames();
        // Frame 1's length now runs past the end of the file, so it reads as
        // "incomplete" -- but frame 2 is intact behind it: acked records follow.
        let mut rot = stored.clone();
        set_frame_len(&mut rot, ends[0], 2 * stored.len() as u32);
        let report = recover(&rot);
        assert_eq!((report.records, report.valid_len), (1, ends[0]));
        assert_eq!(
            report.tail,
            Tail::Fault {
                at: ends[0],
                kind: FaultKind::LengthPastEnd
            },
            "a rotted length with intact frames after it is a fault"
        );

        // The same rot on the LAST frame has nothing decodable after it: it is
        // indistinguishable from a torn write, and stays a torn tail.
        let mut last = stored.clone();
        set_frame_len(&mut last, ends[1], 2 * stored.len() as u32);
        let report = recover(&last);
        assert_eq!((report.records, report.tail), (2, Tail::Torn));

        // FileLog::open refuses the mid-log case and leaves the file untouched,
        // instead of truncating the acked record behind the rotted header away.
        let path = std::env::temp_dir().join(format!(
            "astream_store_rotted_len_{}.log",
            std::process::id()
        ));
        let _tmp = Cleanup(path.clone());
        std::fs::write(&path, &rot).unwrap();
        let err = FileLog::open(&path).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert_eq!(
            std::fs::read(&path).unwrap(),
            rot,
            "a refused open is untouched"
        );
    }

    #[test]
    fn recovery_makes_the_recovered_prefix_durable_even_when_nothing_is_cut() {
        // A process wrote two complete frames and died before its fsync: they
        // sit in the page cache, never acked. Recovery accepts both (they are
        // intact), so they must be on disk before anything is built on them --
        // a dedup high-water, a skipped workflow step.
        let (stored, _) = three_frames();
        let mut f = FlakyFile::new();
        f.data = stored.clone();
        truncate_to(&mut f, stored.len()).unwrap();
        assert_eq!(f.durable, stored, "the recovered prefix is durable");

        // And a cut is durable too.
        let mut f = FlakyFile::new();
        f.data = stored.clone();
        truncate_to(&mut f, 5).unwrap();
        assert_eq!(f.durable, &stored[..5]);
    }

    #[test]
    fn opening_an_existing_log_file_still_fsyncs_its_directory() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static SYNCS: AtomicUsize = AtomicUsize::new(0);
        fn counting(_: &Path) -> io::Result<()> {
            SYNCS.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }
        fn failing(_: &Path) -> io::Result<()> {
            Err(io::Error::other("injected directory fsync failure"))
        }
        let path =
            std::env::temp_dir().join(format!("astream_store_dirsync_{}.log", std::process::id()));
        let _ = std::fs::remove_file(&path);
        let _tmp = Cleanup(path.clone());

        // The first open creates the file but its directory fsync fails (or the
        // process dies right there): the entry may not be durable.
        assert!(open_log_file_with(&path, failing).is_err());
        assert!(path.exists(), "the file was created");

        // The next open finds the file already there. It must still fsync the
        // directory before any record is acked into the file, or a power loss
        // can take the file -- and every acked record -- with it.
        open_log_file_with(&path, counting).unwrap();
        assert_eq!(SYNCS.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn append_after_sync_error_is_refused() {
        let mut f = FlakyFile::new();
        let mut mirror = Vec::new();
        let mut poisoned = false;
        append(&mut f, &mut mirror, &mut poisoned, b"AAAA").unwrap();
        assert_eq!(f.durable, b"AAAA");

        // The frame is written, then its fsync fails: writeback was lost, and a
        // retried fsync could succeed without the lost pages ever reaching disk.
        f.fail_sync = true;
        let err = append(&mut f, &mut mirror, &mut poisoned, b"BBBB").unwrap_err();
        assert!(poisoned, "a failed fsync poisons the log");
        assert_eq!(
            err.kind(),
            io::Error::from_raw_os_error(5).kind(),
            "its kind kept"
        );
        assert!(err.to_string().contains("poisoned"), "{err}");
        assert!(
            !Poisoned::is(&err),
            "the failing append reports its own error"
        );
        assert_eq!(mirror, b"AAAA", "nothing was acked");
        assert_eq!(f.data, b"AAAA", "the unsynced frame is truncated away");
        assert_eq!(f.set_len_calls, 1);

        // The next append is refused with Poisoned and touches nothing: the
        // device just said it lost writes, so nothing more is acked until a
        // reopen recovers against what is actually on disk.
        let writes = f.writes;
        let err = append(&mut f, &mut mirror, &mut poisoned, b"CCCC").unwrap_err();
        assert!(Poisoned::is(&err), "refused with Poisoned: {err}");
        assert_eq!(f.writes, writes, "a poisoned log takes no writes");
        assert_eq!(f.data, b"AAAA");
        assert_eq!(f.durable, b"AAAA");
        assert_eq!(mirror, b"AAAA");
        assert_eq!(f.set_len_calls, 1, "and attempts no rollback");
    }

    #[test]
    fn a_partial_write_is_rolled_back_and_poisons_the_log() {
        let mut f = FlakyFile::new();
        let mut mirror = Vec::new();
        let mut poisoned = false;

        // A clean append: file and mirror agree.
        append(&mut f, &mut mirror, &mut poisoned, b"AAAA").unwrap();
        assert_eq!(f.data, b"AAAA");
        assert_eq!(mirror, b"AAAA");

        // An append that writes 2 partial bytes then fails is truncated back (no
        // torn frame left for a reopen to find) and poisons the log all the same.
        f.fail_partial = Some(2);
        let err = append(&mut f, &mut mirror, &mut poisoned, b"BBBB").unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::StorageFull, "the original kind");
        assert!(!err.to_string().contains("rollback failed"), "{err}");
        assert_eq!(f.data, b"AAAA", "partial frame truncated back");
        assert_eq!(mirror, b"AAAA", "mirror unchanged on failure");
        assert!(
            poisoned,
            "a write error poisons even when the rollback succeeds"
        );

        let err = append(&mut f, &mut mirror, &mut poisoned, b"CCCC").unwrap_err();
        assert!(Poisoned::is(&err), "{err}");
        assert_eq!(f.data, b"AAAA");
        assert_eq!(mirror, b"AAAA");
    }

    #[test]
    fn a_failed_rollback_poisons_the_log_so_nothing_is_acked_after_the_torn_frame() {
        let mut f = FlakyFile::new();
        let mut mirror = Vec::new();
        let mut poisoned = false;
        append(&mut f, &mut mirror, &mut poisoned, b"AAAA").unwrap();

        // The write tears AND the rollback truncate fails (e.g. EIO on a failing
        // device): the partial frame stays on disk.
        f.fail_partial = Some(2);
        f.fail_set_len = true;
        let err = append(&mut f, &mut mirror, &mut poisoned, b"BBBB").unwrap_err();
        assert_eq!(
            err.kind(),
            io::ErrorKind::StorageFull,
            "the original error kind"
        );
        assert!(
            err.to_string().contains("rollback failed"),
            "the error names the failed rollback: {err}"
        );
        assert_eq!(f.data, b"AAAABB", "the torn frame is still on disk");
        assert_eq!(mirror, b"AAAA", "mirror unchanged");
        assert!(poisoned);

        // Every later append is refused — nothing is written or acked after the
        // torn frame, so a later recover cannot lose records acked past it.
        f.fail_set_len = false;
        let err = append(&mut f, &mut mirror, &mut poisoned, b"CCCC").unwrap_err();
        assert!(Poisoned::is(&err), "{err}");
        assert_eq!(f.data, b"AAAABB", "a poisoned log takes no writes");
        assert_eq!(mirror, b"AAAA");
        assert_eq!(f.set_len_calls, 1, "no further rollback attempts either");
    }
}
