//! Durable storage and crash recovery (rung 1.5: the Strict durability dial).
//!
//! [`FileLog`] is a segment file that fsyncs every append (Strict: a record is
//! acked only once it is on disk). On open it runs [`recover`], which scans
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
//!   the explicit [`FileLog::open_truncating`].
//!
//! Recovery is a pure function of the stored bytes, so it is deterministic and
//! testable with no I/O; the file wrapper adds the real fsync and the truncate.
//! `open` also fsyncs the parent directory (Unix), so the file's directory
//! entry is as durable as the appends that follow.
//!
//! An append that fails mid-frame is rolled back to the last acked length. If
//! that rollback itself fails, the on-disk tail may be torn while the process
//! is still alive, so the log is **poisoned**: every later append is refused
//! until the file is reopened (and recovered), rather than acked onto a
//! corruption boundary that the next recover would truncate at.
//!
//! Deferred to a later rung: batched/Relaxed durability (fsync per batch rather
//! than per append), segment rotation, and compaction (so a log can start at a
//! non-zero offset — recovery here assumes the log begins at [`Offset::ZERO`]).

use crate::envelope::{Envelope, EnvelopeError};
use astream_wire::{Frame, FrameError, Offset};
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

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
    /// records, so a plain open refuses.
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
/// its payload is a valid [`Envelope`], and its `seq` is exactly the next
/// expected offset. The first frame that fails any check ends the intact
/// prefix, classified as a torn tail or a fault (see [`Tail`]). Pure and
/// panic-free.
pub fn recover(bytes: &[u8]) -> RecoverReport {
    let mut pos = 0usize;
    let mut records = 0u64;
    let mut expected = Offset::ZERO;
    let tail = loop {
        match Frame::decode(&bytes[pos..]) {
            // No complete frame at `pos`: a clean end, a torn tail, or a rotted
            // length field.
            Ok(None) => break end_tail(bytes, pos),
            // A complete-but-corrupt frame (or an unreadable header).
            Err(e) => break corrupt_frame_tail(bytes, pos, e),
            Ok(Some(decoded)) => match Envelope::from_payload(&decoded.frame.payload) {
                Err(e) => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::BadEnvelope(e),
                    }
                }
                Ok(env) if env.seq != expected => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::OutOfOrder {
                            expected: expected.0,
                            found: env.seq.0,
                        },
                    }
                }
                Ok(_) => {
                    pos += decoded.consumed;
                    records += 1;
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
pub(crate) fn end_tail(bytes: &[u8], pos: usize) -> Tail {
    if pos >= bytes.len() {
        Tail::Clean
    } else if frame_decodes_after(bytes, pos) {
        Tail::Fault {
            at: pos,
            kind: FaultKind::LengthPastEnd,
        }
    } else {
        Tail::Torn
    }
}

/// The frame at `pos` failed to decode with `e`. If any complete frame decodes
/// somewhere after it, the damage is inside the log — a fault. If nothing after
/// it decodes, it is the tail a crash left, and truncating it is safe.
pub(crate) fn corrupt_frame_tail(bytes: &[u8], pos: usize, e: FrameError) -> Tail {
    if frame_decodes_after(bytes, pos) {
        Tail::Fault {
            at: pos,
            kind: FaultKind::CorruptFrame(e),
        }
    } else {
        Tail::Torn
    }
}

/// Whether a complete, CRC-valid frame starts anywhere after `pos`. A crash
/// leaves nothing decodable behind its partial frame. (Scanning byte by byte is
/// the honest test: a damaged header carries no trustworthy length to skip by.)
fn frame_decodes_after(bytes: &[u8], pos: usize) -> bool {
    (pos.saturating_add(1)..bytes.len()).any(|q| matches!(Frame::decode(&bytes[q..]), Ok(Some(_))))
}

/// A segment-file log with Strict (fsync-per-append) durability and
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
        let mut file = open_segment(path)?;
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
    /// The append is **atomic against partial failure**: if the write or the
    /// fsync fails mid-frame, the file is rolled back to the last acked length
    /// (`mirror.len()`) so the on-disk log stays a clean prefix equal to the
    /// mirror. Without this, a partial frame left on disk would become a
    /// corruption boundary in front of every later acked record.
    /// If the rollback itself fails the log is poisoned (see
    /// [`is_poisoned`](Self::is_poisoned)) and every later append is refused.
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

    /// Whether a failed rollback has poisoned this handle: the on-disk tail may
    /// be torn, so appends are refused until the file is reopened and recovered.
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
pub(crate) fn open_segment(path: &Path) -> io::Result<File> {
    open_segment_with(path, sync_parent_dir)
}

/// [`open_segment`] with the directory fsync injectable, so a test can see it.
fn open_segment_with(path: &Path, sync_dir: fn(&Path) -> io::Result<()>) -> io::Result<File> {
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
pub(crate) fn truncate_to<W: SegmentFile>(file: &mut W, valid_len: usize) -> io::Result<()> {
    file.set_len(valid_len as u64)?;
    file.sync_all()?;
    file.seek_end()
}

/// The handful of file operations the atomic append and the recovery truncate
/// need. Abstracted behind a trait so those paths can be exercised with injected
/// failures (a real `File` cannot be made to short-write on demand).
pub(crate) trait SegmentFile {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()>;
    fn sync_data(&mut self) -> io::Result<()>;
    fn sync_all(&mut self) -> io::Result<()>;
    fn set_len(&mut self, size: u64) -> io::Result<()>;
    fn seek_end(&mut self) -> io::Result<()>;
}

impl SegmentFile for File {
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        Write::write_all(self, buf)
    }
    fn sync_data(&mut self) -> io::Result<()> {
        File::sync_data(self)
    }
    fn sync_all(&mut self) -> io::Result<()> {
        File::sync_all(self)
    }
    fn set_len(&mut self, size: u64) -> io::Result<()> {
        File::set_len(self, size)
    }
    fn seek_end(&mut self) -> io::Result<()> {
        Seek::seek(self, SeekFrom::End(0)).map(|_| ())
    }
}

fn poisoned_error() -> io::Error {
    io::Error::other(
        "log poisoned by a failed rollback (the on-disk tail may be torn); reopen to recover",
    )
}

/// Append `frame_bytes` durably, rolling back atomically on a write/fsync error.
///
/// `committed` is the last durably-acked file length, where the write cursor
/// sits; the caller advances it by `frame_bytes.len()` only when this returns
/// `Ok`. On error, any partially-written bytes are truncated back to
/// `committed` so the on-disk log stays a clean prefix of acked frames —
/// otherwise a torn frame becomes a corruption boundary in front of every
/// later acked record.
///
/// If the rollback fails, `poisoned` is set and every later call is refused
/// with an error: the file may now hold a torn frame, so acking anything after
/// it would be a durability lie. A poisoned log must be reopened (recovered).
pub(crate) fn append_frame<W: SegmentFile>(
    file: &mut W,
    committed: u64,
    poisoned: &mut bool,
    frame_bytes: &[u8],
) -> io::Result<()> {
    if *poisoned {
        return Err(poisoned_error());
    }
    if let Err(e) = file.write_all(frame_bytes).and_then(|()| file.sync_data()) {
        if let Err(rb) = file.set_len(committed).and_then(|()| file.seek_end()) {
            *poisoned = true;
            return Err(io::Error::new(
                e.kind(),
                format!("{e}; rollback failed ({rb}): the log is poisoned, reopen to recover"),
            ));
        }
        return Err(e);
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
    /// then fail, and whose `set_len` can be made to fail — so both the
    /// atomic-append rollback and the poison-on-failed-rollback are observable.
    /// `durable` is what a power loss would leave: `data` as of the last sync.
    struct FlakyFile {
        data: Vec<u8>,
        durable: Vec<u8>,
        fail_partial: Option<usize>,
        fail_set_len: bool,
        set_len_calls: usize,
    }

    impl FlakyFile {
        fn new() -> Self {
            FlakyFile {
                data: Vec::new(),
                durable: Vec::new(),
                fail_partial: None,
                fail_set_len: false,
                set_len_calls: 0,
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

    impl SegmentFile for FlakyFile {
        fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
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
            self.durable = self.data.clone();
            Ok(())
        }
        fn sync_all(&mut self) -> io::Result<()> {
            self.durable = self.data.clone();
            Ok(())
        }
        fn set_len(&mut self, size: u64) -> io::Result<()> {
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
        let bytes = crate::fork::record_session(
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
    fn opening_an_existing_segment_still_fsyncs_its_directory() {
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
        assert!(open_segment_with(&path, failing).is_err());
        assert!(path.exists(), "the file was created");

        // The next open finds the file already there. It must still fsync the
        // directory before any record is acked into the file, or a power loss
        // can take the file -- and every acked record -- with it.
        open_segment_with(&path, counting).unwrap();
        assert_eq!(SYNCS.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn append_rolls_back_a_partial_frame_and_stays_a_clean_prefix() {
        let mut f = FlakyFile::new();
        let mut mirror = Vec::new();
        let mut poisoned = false;

        // A clean append: file and mirror agree.
        append(&mut f, &mut mirror, &mut poisoned, b"AAAA").unwrap();
        assert_eq!(f.data, b"AAAA");
        assert_eq!(mirror, b"AAAA");

        // An append that writes 2 partial bytes then fails must roll back: no torn
        // frame on disk, mirror unchanged, so disk == mirror == the acked prefix.
        f.fail_partial = Some(2);
        assert!(append(&mut f, &mut mirror, &mut poisoned, b"BBBB").is_err());
        assert_eq!(f.data, b"AAAA", "partial frame truncated back");
        assert_eq!(mirror, b"AAAA", "mirror unchanged on failure");
        assert!(!poisoned, "a successful rollback does not poison");

        // The log is still appendable and lands the next frame right after the prefix
        // (a later recover would see [AAAA][CCCC], not a torn boundary).
        append(&mut f, &mut mirror, &mut poisoned, b"CCCC").unwrap();
        assert_eq!(f.data, b"AAAACCCC");
        assert_eq!(mirror, b"AAAACCCC");
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
        assert!(err.to_string().contains("poisoned"), "{err}");
        assert_eq!(f.data, b"AAAABB", "a poisoned log takes no writes");
        assert_eq!(mirror, b"AAAA");
        assert_eq!(f.set_len_calls, 1, "no further rollback attempts either");
    }
}
