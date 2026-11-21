// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE SEGMENTED LOG (aterm tracker LT-A8): a log whose records live in fixed-size segment
//! files, each named by its base offset, so that retention unlinks whole segments and copies
//! no record ([`OpenOptions::segment_bytes`](crate::OpenOptions::segment_bytes)).
//!
//! # The files
//!
//! | file | holds |
//! |---|---|
//! | `<log>` | the ANCHOR: [`ANCHOR_MAGIC`] and the segment size the log was created with. It is the file the open locks, and every sidecar is still named from it |
//! | `<log>.<base>.seg` | the records from offset `<base>` (twenty decimal digits) to the next segment's base, frame bytes as stored |
//!
//! The segments at or above the base (`<log>.base`) are the log, oldest first, read as one
//! byte range: the first byte of the oldest is byte 0, and a frame never crosses from one
//! segment into the next. Every in-memory byte position of the log (the tier's frame starts,
//! its durable length) is a position in that range, so a cut that drops the oldest segments
//! moves them down by exactly the bytes it drops, as a cut that copies the kept suffix to the
//! front of one file did. The newest segment is the ACTIVE one, the only one ever written.
//!
//! # Roll
//!
//! A batch (or a single append) that finds the active segment at or past the segment size
//! first ROLLS it: a full flush of the active segment (so nothing of it is left to lose once
//! a newer one exists), then the next segment created empty at the head's offset with the
//! log's permissions, then a flush of the directory. The batch is written to the new
//! segment. So a segment is closed at the first batch boundary at or past the size; a batch
//! is never split. A crash anywhere in a roll leaves the log it began with, and perhaps an
//! empty newest segment at the head, which is a whole log too.
//!
//! # Cut
//!
//! A cut keeps whole segments: its floor is the base of the newest segment at or below the
//! offset asked for (Kafka's rule), and the active segment is never dropped. Its durable
//! steps are the compaction's (`compact.rs`) with the copy taken out and the switch moved:
//!
//! 0. [`Step::Held`](crate::compact::Step::Held), as a copying cut.
//! 1. [`Step::State`](crate::compact::Step::State): the carried state staged at
//!    `<log>.state.next`.
//! 2. [`Step::Intent`](crate::compact::Step::Intent): the intent, of the unlinking kind.
//! 3. [`Step::Base`](crate::compact::Step::Base): `<log>.base` names the new base. THIS is
//!    the switch: the log is the segments at or above the base, so from here its first frame
//!    is the kept one, and nothing below is read again.
//! 4. [`Step::StateInstalled`](crate::compact::Step::StateInstalled), then
//!    [`Step::Watermark`](crate::compact::Step::Watermark), as a copying cut.
//! 5. [`Step::Unlink`](crate::compact::Step::Unlink): every segment below the base unlinked,
//!    then the directory flushed.
//! 6. [`Step::IntentRemoved`](crate::compact::Step::IntentRemoved).
//!
//! An open judges the intent as it judges a copying one: by the log's first frame, which is
//! the first frame of the segment at the base it reads. The OLD one: the base was never
//! moved, so the intent and the staged state are discarded and every segment is still there.
//! The NEW one: the open finishes steps 4 to 6, each idempotent. A segment below the base
//! that no intent names (a cut whose unlinks were made and whose intent removal was lost
//! cannot leave one: the unlinks are name changes made before it) is removed all the same.
//!
//! What the cut writes is the intent, the staged state and the base: no record. The kept
//! segments keep their files, their inodes and their bytes
//! (`segments_tests::retention_cut_unlinks_segments_without_copy`).
//!
//! # Not segmented
//!
//! A log on the simulated device, a log sealed at rest and an offline seal are refused with
//! segments: none of them is built for more than one file yet, and each refuses by name
//! rather than reading one segment as the log.

use crate::storage::{file_len, read_some_at, write_all_at};
use crate::store::{create_like_read_write, open_with_options, remove_file_path, sync_parent_dir};
use std::ffi::OsStr;
use std::fs::{File, OpenOptions as FsOpenOptions, Permissions};
#[cfg(test)]
use std::io::Write;
use std::io::{self, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// The anchor's magic and version: `<log>` of a segmented log holds this and the segment size
/// it was created with, and nothing else. A one-file log starts with a frame
/// (`astream_wire::frame::MAGIC`), so neither is ever read as the other.
pub(crate) const ANCHOR_MAGIC: &[u8; 5] = b"ASSG\x01";

/// The anchor's length: the magic and the segment size.
pub(crate) const ANCHOR_LEN: usize = ANCHOR_MAGIC.len() + 8;

/// The segment size a log takes when its options ask for segments and name none: the
/// journal design's figure (aterm `docs/design-commons-at-scale/journal.md`, "Journal files").
pub const DEFAULT_SEGMENT_BYTES: u64 = 64 << 20;

/// The smallest segment size an open takes. A segment closes at the first batch boundary at
/// or past its size, so a smaller one only means more files; this keeps a mistaken `1` from
/// making one file per record. Tests open logs with segments of a few records through
/// `SegmentBytes::exactly`.
pub const MIN_SEGMENT_BYTES: u64 = 4096;

/// The segment-name suffix.
const SUFFIX: &str = ".seg";

/// Digits in a segment's base: every `u64` fits, and names sort as their bases do.
const BASE_DIGITS: usize = 20;

/// What an open finds at `<log>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Found {
    /// An empty file: a log just created, or one whose open died before it wrote anything.
    Empty,
    /// A segmented log's anchor, naming the segment size it was created with.
    Anchor(u64),
    /// Anything else: a one-file log.
    OneFile,
}

/// Read what `<log>` is, through its own descriptor (positional reads; nothing moves).
pub(crate) fn probe(file: &File) -> io::Result<Found> {
    let len = file_len(file)?;
    if len == 0 {
        return Ok(Found::Empty);
    }
    if len != ANCHOR_LEN as u64 {
        return Ok(Found::OneFile);
    }
    let mut buf = [0u8; ANCHOR_LEN];
    if read_some_at(file, &mut buf, 0)? != ANCHOR_LEN {
        return Ok(Found::OneFile);
    }
    let (magic, size) = buf.split_at(ANCHOR_MAGIC.len());
    if magic != ANCHOR_MAGIC {
        return Ok(Found::OneFile);
    }
    let Ok(size) = <[u8; 8]>::try_from(size) else {
        return Ok(Found::OneFile);
    };
    Ok(Found::Anchor(u64::from_le_bytes(size)))
}

/// Whether the log at `path` is segmented, read without locking it: for the paths that refuse
/// a segmented log by name (`check_open`, the offline seal).
pub(crate) fn is_segmented(path: &Path) -> bool {
    match File::open(path) {
        Ok(f) => matches!(probe(&f), Ok(Found::Anchor(_))),
        Err(_) => false,
    }
}

/// Write the anchor into `<log>`, which the open just created and holds locked, and flush it:
/// before the first segment is created, so a segment never exists beside an anchor a power
/// loss can take back.
pub(crate) fn write_anchor(file: &File, path: &Path, segment_bytes: u64) -> io::Result<()> {
    let mut out = Vec::with_capacity(ANCHOR_LEN);
    out.extend_from_slice(ANCHOR_MAGIC);
    out.extend_from_slice(&segment_bytes.to_le_bytes());
    write_all_at(file, &out, 0)?;
    crate::store::flush_file(file, path)
}

/// The segment of the log at `log` whose first record is at offset `base`:
/// `<log>.<base, 20 digits>.seg`.
pub(crate) fn segment_path(log: &Path, base: u64) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string()
        .push(format!(".{base:0width$}{SUFFIX}", width = BASE_DIGITS));
    p
}

/// The base a directory entry `name` names as a segment of the log named `stem`, or `None`
/// when it is no segment of it.
fn base_of(stem: &OsStr, name: &OsStr) -> Option<u64> {
    let name = name.to_str()?;
    let stem = stem.to_str()?;
    let rest = name.strip_prefix(stem)?.strip_prefix('.')?;
    let digits = rest.strip_suffix(SUFFIX)?;
    if digits.len() != BASE_DIGITS || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// The bases of every segment beside the log at `log`, ascending. Only regular files count.
pub(crate) fn list(log: &Path) -> io::Result<Vec<u64>> {
    let Some(stem) = log.file_name() else {
        return Ok(Vec::new());
    };
    let dir = match log.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let Some(base) = base_of(stem, &entry.file_name()) else {
            continue;
        };
        if entry.file_type()?.is_file() {
            out.push(base);
        }
    }
    out.sort_unstable();
    Ok(out)
}

/// Remove every segment beside `log` whose base is below `base`, then flush the directory:
/// what a cut drops, and an open's clearing of what a cut left. How many were removed.
pub(crate) fn unlink_below(log: &Path, base: u64) -> io::Result<usize> {
    let mut n = 0usize;
    for b in list(log)? {
        if b >= base {
            break;
        }
        match remove_file_path(&segment_path(log, b)) {
            Ok(()) => n = n.saturating_add(1),
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e),
        }
    }
    if n > 0 {
        sync_parent_dir(log)?;
    }
    Ok(n)
}

/// A log this open CREATED carries none of a deleted predecessor's segments. A directory
/// that cannot be listed (write-only) shows none, and the open goes on as it did before
/// segments: a segmented open there is refused when it lists its own.
pub(crate) fn clear_created(log: &Path) -> io::Result<()> {
    match unlink_below(log, u64::MAX) {
        Err(e) if e.kind() == io::ErrorKind::PermissionDenied => Ok(()),
        res => res.map(|_| ()),
    }
}

/// A segment the log no longer writes: its base, where it starts in the log's byte range,
/// and its length. Its file is opened when a read reaches it.
#[derive(Debug, Clone, Copy)]
struct Sealed {
    base: u64,
    start: u64,
    len: u64,
}

/// The segment the log appends to.
struct Active {
    base: u64,
    start: u64,
    file: Arc<File>,
    path: PathBuf,
}

/// The segments of an open log, read as one byte range ([`Backing::Seg`](crate::storage::Backing)).
pub(crate) struct Segments {
    /// `<log>`, locked: what the lock and the permissions are read from.
    pub(crate) anchor: Arc<File>,
    log: PathBuf,
    /// Where the active segment rolls.
    roll_bytes: u64,
    sealed: Vec<Sealed>,
    active: Active,
    /// The sealed segment a read last reached, kept open for the next: an open scans the log
    /// in order, and a cold read tends to read near the last.
    cached: Mutex<Option<(u64, Arc<File>)>>,
}

/// The refusal of a segmented log whose files do not make one.
fn broken(log: &Path, why: String) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "{}: the segmented log is not whole: {why}; refusing to open, nothing touched",
            log.display()
        ),
    )
}

/// Open the segment at `path` to read and write, never through a link.
fn open_segment(path: &Path, write: bool) -> io::Result<File> {
    let meta = std::fs::symlink_metadata(path)?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{}: a segment is not a regular file", path.display()),
        ));
    }
    open_with_options(FsOpenOptions::new().read(true).write(write), path)
}

impl Segments {
    /// The segments of the log at `log`, from `base` (its base sidecar) on: the segment at the
    /// base must be there, every one above it is the log's, and the newest is the active one.
    /// A log with none at all (just created, or its open died before the first was) gets its
    /// first, empty, at `base`. The bases below `base` it found are returned beside it: a
    /// cut's, which the open removes once it has judged any intent.
    pub(crate) fn open(
        anchor: Arc<File>,
        log: &Path,
        roll_bytes: u64,
        base: u64,
    ) -> io::Result<(Segments, Vec<u64>)> {
        let all = list(log)?;
        let (below, kept): (Vec<u64>, Vec<u64>) = all.iter().partition(|&&b| b < base);
        if kept.is_empty() {
            if !below.is_empty() {
                return Err(broken(
                    log,
                    format!("no segment starts at the base {base}, and some are below it"),
                ));
            }
            let perms = anchor.metadata()?.permissions();
            let path = segment_path(log, base);
            let file = create_like_read_write(&path, &perms)?;
            sync_parent_dir(&path)?;
            let segs = Segments {
                anchor,
                log: log.to_path_buf(),
                roll_bytes,
                sealed: Vec::new(),
                active: Active {
                    base,
                    start: 0,
                    file: Arc::new(file),
                    path,
                },
                cached: Mutex::new(None),
            };
            return Ok((segs, below));
        }
        if kept.first() != Some(&base) {
            return Err(broken(log, format!("no segment starts at the base {base}")));
        }
        let mut sealed = Vec::new();
        let mut start = 0u64;
        let (last, older) = match kept.split_last() {
            Some(split) => split,
            None => return Err(broken(log, "no segment".into())),
        };
        for &b in older {
            let path = segment_path(log, b);
            let meta = std::fs::symlink_metadata(&path)?;
            if !meta.is_file() {
                return Err(broken(
                    log,
                    format!("{} is not a regular file", path.display()),
                ));
            }
            sealed.push(Sealed {
                base: b,
                start,
                len: meta.len(),
            });
            start = start.saturating_add(meta.len());
        }
        let path = segment_path(log, *last);
        let file = open_segment(&path, true)?;
        let segs = Segments {
            anchor,
            log: log.to_path_buf(),
            roll_bytes,
            sealed,
            active: Active {
                base: *last,
                start,
                file: Arc::new(file),
                path,
            },
            cached: Mutex::new(None),
        };
        Ok((segs, below))
    }

    /// `<log>`, locked.
    pub(crate) const fn anchor(&self) -> &Arc<File> {
        &self.anchor
    }

    /// The active segment's file, for the flushes and the batches taken outside the lock.
    pub(crate) const fn active_file(&self) -> &Arc<File> {
        &self.active.file
    }

    /// How many segment files the log has.
    pub(crate) fn count(&self) -> usize {
        self.sealed.len().saturating_add(1)
    }

    /// Every segment, oldest first: its base and where it starts.
    pub(crate) fn bounds(&self) -> Vec<(u64, u64)> {
        let mut out: Vec<(u64, u64)> = self.sealed.iter().map(|s| (s.base, s.start)).collect();
        out.push((self.active.base, self.active.start));
        out
    }

    /// The log's length in bytes: every sealed segment's, and the active one's as it stands.
    pub(crate) fn len(&self) -> io::Result<u64> {
        Ok(self
            .active
            .start
            .saturating_add(file_len(&self.active.file)?))
    }

    /// The sealed segment holding byte `pos`, as its index.
    fn sealed_at(&self, pos: u64) -> Option<usize> {
        if pos >= self.active.start {
            return None;
        }
        let i = self.sealed.partition_point(|s| s.start <= pos);
        i.checked_sub(1)
    }

    /// The open file of sealed segment `seg`, from the cache or opened now.
    fn sealed_file(&self, seg: Sealed) -> io::Result<Arc<File>> {
        let mut cached = self
            .cached
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some((b, f)) = cached.as_ref() {
            if *b == seg.base {
                return Ok(Arc::clone(f));
            }
        }
        let f = Arc::new(open_segment(&segment_path(&self.log, seg.base), false)?);
        *cached = Some((seg.base, Arc::clone(&f)));
        Ok(f)
    }

    /// Up to `buf.len()` bytes from byte `start` of the log's range, across segments, fewer
    /// only where the log ends: how many were read.
    pub(crate) fn read_some_at(&self, start: u64, buf: &mut [u8]) -> io::Result<usize> {
        let mut got = 0usize;
        let mut pos = start;
        while got < buf.len() {
            let Some(window) = buf.get_mut(got..) else {
                break;
            };
            let n = match self.sealed_at(pos) {
                Some(i) => {
                    let Some(&seg) = self.sealed.get(i) else {
                        break;
                    };
                    let end = seg.start.saturating_add(seg.len);
                    let room = usize::try_from(end.saturating_sub(pos)).unwrap_or(usize::MAX);
                    let take = window.len().min(room);
                    let Some(part) = window.get_mut(..take) else {
                        break;
                    };
                    let f = self.sealed_file(seg)?;
                    let n = read_some_at(&f, part, pos.saturating_sub(seg.start))?;
                    if n < take {
                        // A sealed segment shorter than the open found it: someone else
                        // changed the file. What was read is all there is.
                        got = got.saturating_add(n);
                        break;
                    }
                    n
                }
                None => {
                    let local = pos.saturating_sub(self.active.start);
                    let n = read_some_at(&self.active.file, window, local)?;
                    got = got.saturating_add(n);
                    break;
                }
            };
            got = got.saturating_add(n);
            pos = pos.saturating_add(n as u64);
        }
        Ok(got)
    }

    /// The whole log from byte 0, every segment in turn.
    pub(crate) fn read_to_end(&self, out: &mut Vec<u8>) -> io::Result<usize> {
        let before = out.len();
        for seg in &self.sealed {
            let mut f: &File = &*self.sealed_file(*seg)?;
            f.seek(SeekFrom::Start(0))?;
            f.read_to_end(out)?;
        }
        let mut f: &File = &self.active.file;
        f.seek(SeekFrom::Start(0))?;
        f.read_to_end(out)?;
        Ok(out.len().saturating_sub(before))
    }

    /// `bytes` at byte `at` of the log's range, which must be in the active segment: the only
    /// place the log ever writes.
    pub(crate) fn write_at(&self, bytes: &[u8], at: u64) -> io::Result<()> {
        let Some(local) = at.checked_sub(self.active.start) else {
            return Err(below_active(at, self.active.start));
        };
        write_all_at(&self.active.file, bytes, local)
    }

    /// The test-only cursor append (F24's negative control), into the active segment.
    #[cfg(test)]
    pub(crate) fn write_at_cursor(&self, bytes: &[u8]) -> io::Result<()> {
        (&*self.active.file).write_all(bytes)
    }

    /// Cut (or extend) the log to `len` bytes within the active segment: a batch's rollback,
    /// which never reaches below it (a roll comes before the batch). A cut below it is
    /// [`cut_back`](Self::cut_back)'s, and refused here.
    pub(crate) fn resize(&self, len: u64) -> io::Result<()> {
        let Some(local) = len.checked_sub(self.active.start) else {
            return Err(below_active(len, self.active.start));
        };
        self.active.file.set_len(local)
    }

    /// CUT BACK to `len` bytes of the log's range, below the active segment if need be: an
    /// open's cut of what it cannot keep (a repair's, below damage in a sealed segment or at
    /// a gap between segments) and a replica's truncation to its primary. The segment whose
    /// bytes run up to `len` is kept: the newest that starts BELOW it (the first, for a cut to
    /// 0). Every segment that starts at or past `len` is unlinked, NEWEST FIRST, so the files
    /// left at any point make a whole log (a crash leaves a longer one, which the next open
    /// cuts again), and the directory flushed; then the kept segment is cut to `len` and
    /// becomes the active one, so the next roll names the next segment for the head. A
    /// segment that starts at `len` holds nothing the cut keeps, and its name is not trusted
    /// (a repair at a gap meets the segment after the gap there). Its flush is the caller's,
    /// as a one-file log's cut's is.
    pub(crate) fn cut_back(&mut self, len: u64) -> io::Result<()> {
        if len > self.active.start || (len == self.active.start && self.sealed.is_empty()) {
            return self.resize(len);
        }
        let keep = if len == 0 {
            1
        } else {
            self.sealed.partition_point(|s| s.start < len)
        };
        let Some(target) = keep
            .checked_sub(1)
            .and_then(|i| self.sealed.get(i))
            .copied()
        else {
            return Err(below_active(len, self.active.start));
        };
        let gone = self.sealed.get(keep..).unwrap_or(&[]);
        let newest_first = std::iter::once(self.active.path.clone())
            .chain(gone.iter().rev().map(|s| segment_path(&self.log, s.base)));
        for path in newest_first {
            match remove_file_path(&path) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        }
        sync_parent_dir(&self.log)?;
        let path = segment_path(&self.log, target.base);
        let file = open_segment(&path, true)?;
        file.set_len(len.saturating_sub(target.start))?;
        self.sealed.truncate(keep.saturating_sub(1));
        self.active = Active {
            base: target.base,
            start: target.start,
            file: Arc::new(file),
            path,
        };
        *self
            .cached
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
        Ok(())
    }

    /// A full flush of the active segment's data.
    pub(crate) fn sync_data(&self) -> io::Result<()> {
        astream_sys::full_sync_data(&self.active.file)?;
        #[cfg(all(test, unix, feature = "retention"))]
        crate::power_loss::flushed(&self.active.path);
        Ok(())
    }

    /// A full flush of the active segment's data and metadata.
    pub(crate) fn sync_all(&self) -> io::Result<()> {
        astream_sys::full_sync(&self.active.file)?;
        #[cfg(all(test, unix, feature = "retention"))]
        crate::power_loss::flushed(&self.active.path);
        Ok(())
    }

    /// Whether the active segment is due to roll before `len` more bytes are appended at
    /// `durable` (the log's durable length): it holds something and has reached the size.
    pub(crate) fn roll_due(&self, durable: u64) -> bool {
        let held = durable.saturating_sub(self.active.start);
        held > 0 && held >= self.roll_bytes
    }

    /// ROLL: flush the active segment in full, create the next one, empty, at offset `next`
    /// (the head) and byte `durable` (the log's durable length, where the file ends), and
    /// flush the directory. The log as it was is whole at every step. `fail_sync` is the
    /// injected full-flush fault (`InjectedFaults::sync`).
    pub(crate) fn roll(
        &mut self,
        next: u64,
        durable: u64,
        fail_sync: bool,
    ) -> Result<(), RollError> {
        let len = file_len(&self.active.file).map_err(RollError::Create)?;
        if self.active.start.saturating_add(len) != durable || next <= self.active.base {
            return Err(RollError::After(io::Error::other(format!(
                "{}: the active segment cannot roll at offset {next}, byte {durable}",
                self.active.path.display()
            ))));
        }
        if fail_sync {
            return Err(RollError::Flush(io::Error::other("injected fsync fault")));
        }
        self.sync_data().map_err(RollError::Flush)?;
        let perms: Permissions = self
            .anchor
            .metadata()
            .map_err(RollError::Create)?
            .permissions();
        let path = segment_path(&self.log, next);
        let file = create_like_read_write(&path, &perms).map_err(RollError::Create)?;
        sync_parent_dir(&path).map_err(RollError::After)?;
        let old = std::mem::replace(
            &mut self.active,
            Active {
                base: next,
                start: durable,
                file: Arc::new(file),
                path,
            },
        );
        self.sealed.push(Sealed {
            base: old.base,
            start: old.start,
            len,
        });
        Ok(())
    }

    #[cfg(feature = "retention")]
    /// The floor a cut to `min` takes: the base of the newest segment at or below it.
    pub(crate) fn floor(&self, min: u64) -> u64 {
        if self.active.base <= min {
            return self.active.base;
        }
        let i = self.sealed.partition_point(|s| s.base <= min);
        match i.checked_sub(1).and_then(|i| self.sealed.get(i)) {
            Some(s) => s.base,
            None => self.sealed.first().map_or(self.active.base, |s| s.base),
        }
    }

    #[cfg(feature = "retention")]
    /// Where the segment at `base` starts in the log's byte range.
    pub(crate) fn start_of(&self, base: u64) -> Option<u64> {
        if base == self.active.base {
            return Some(self.active.start);
        }
        self.sealed.iter().find(|s| s.base == base).map(|s| s.start)
    }

    #[cfg(feature = "retention")]
    /// Forget every segment below `base` (a cut's switch, in memory): every position moves down
    /// by the bytes they held, which is returned.
    pub(crate) fn drop_below(&mut self, base: u64) -> u64 {
        let Some(cut) = self.start_of(base) else {
            return 0;
        };
        self.sealed.retain(|s| s.base >= base);
        for s in &mut self.sealed {
            s.start = s.start.saturating_sub(cut);
        }
        self.active.start = self.active.start.saturating_sub(cut);
        *self
            .cached
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = None;
        cut
    }

    /// Check the segments against what the open's scan found: the base of each names the
    /// record whose frame starts where the segment does (`at(i)`, the tier's frame start of
    /// the `i`th record from `base`), or, for the newest, the head when it is empty; and only
    /// the newest may be empty. `records` is how many the open kept, `keep` the bytes. When
    /// the open is `cutting` (it keeps less than the log holds), a segment that starts past
    /// `keep` is one the cut unlinks ([`cut_back`](Self::cut_back)); one that starts AT `keep`
    /// is unlinked too, and must still be named for the record the cut keeps next, unless the
    /// open is an explicit `repairing` one: a repair at a gap between segments (one missing
    /// or emptied) cuts where the segment after the gap starts, whose name is the gap's far
    /// side. Only a repair may drop records the classifier read past a gap; any other open
    /// that meets a misnamed or empty sealed segment refuses.
    pub(crate) fn check(
        &self,
        base: u64,
        records: usize,
        keep: u64,
        cutting: bool,
        repairing: bool,
        at: impl Fn(usize) -> Option<u64>,
    ) -> io::Result<()> {
        for (n, (seg_base, start)) in self.bounds().into_iter().enumerate() {
            let newest = n == self.sealed.len();
            if cutting && (start > keep || (repairing && start == keep && keep > 0)) {
                continue;
            }
            if !newest && self.sealed.get(n).is_some_and(|s| s.len == 0) {
                return Err(broken(
                    &self.log,
                    format!("the segment at {seg_base} is empty"),
                ));
            }
            let i = seg_base
                .checked_sub(base)
                .and_then(|i| usize::try_from(i).ok())
                .ok_or_else(|| {
                    broken(
                        &self.log,
                        format!("the segment at {seg_base} is below the base {base}"),
                    )
                })?;
            let whole = if i < records {
                at(i) == Some(start)
            } else {
                i == records && start == keep && (newest || cutting)
            };
            if !whole {
                return Err(broken(
                    &self.log,
                    format!(
                        "the segment named for offset {seg_base} does not start with that \
                         record (it starts at byte {start} of the log, which keeps {records} \
                         records from {base})"
                    ),
                ));
            }
        }
        Ok(())
    }
}

/// Why a roll failed, which says what the log does about it (`BrokerLog::roll_if_due`).
#[derive(Debug)]
pub(crate) enum RollError {
    /// The full flush of the active segment failed: what it was to cover may be gone, as
    /// after any failed full flush (the log is poisoned, its run recorded `Lossy`).
    Flush(io::Error),
    /// The next segment was not created (no descriptor, no space, no permission), or what it
    /// is created from could not be read. Nothing changed on disk or in memory, and the
    /// active segment is flushed whole: only the append or batch that asked for the roll is
    /// refused, and the next one asks again.
    Create(io::Error),
    /// The log is not what the roll found it, or the next segment's name was not flushed:
    /// the log is poisoned, and its reopen judges the files.
    After(io::Error),
}

/// A write or a cut below the active segment.
fn below_active(at: u64, start: u64) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        format!(
            "the segmented log writes only its active segment, which starts at byte {start}; \
             byte {at} is in a sealed one"
        ),
    )
}

/// What a batch is written and flushed through outside the lock on a segmented log: the
/// active segment's descriptor, shared, and where it starts.
#[derive(Clone)]
pub(crate) struct Out {
    pub(crate) file: Arc<File>,
    pub(crate) start: u64,
    #[cfg(all(test, unix, feature = "retention"))]
    pub(crate) path: PathBuf,
}

impl Out {
    pub(crate) fn of(segs: &Segments) -> Out {
        Out {
            file: Arc::clone(&segs.active.file),
            start: segs.active.start,
            #[cfg(all(test, unix, feature = "retention"))]
            path: segs.active.path.clone(),
        }
    }

    pub(crate) fn write_at(&self, bytes: &[u8], at: u64) -> io::Result<()> {
        let Some(local) = at.checked_sub(self.start) else {
            return Err(below_active(at, self.start));
        };
        write_all_at(&self.file, bytes, local)
    }

    /// The power-loss model learns a full flush of the active segment.
    pub(crate) fn flushed(&self) {
        #[cfg(all(test, unix, feature = "retention"))]
        crate::power_loss::flushed(&self.path);
    }
}

/// The segment size an open asks for ([`OpenOptions::segment_bytes`](crate::OpenOptions)).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SegmentBytes(pub(crate) u64);

impl SegmentBytes {
    /// Segments of `bytes`, at least [`MIN_SEGMENT_BYTES`].
    #[must_use]
    pub const fn new(bytes: u64) -> SegmentBytes {
        if bytes < MIN_SEGMENT_BYTES {
            SegmentBytes(MIN_SEGMENT_BYTES)
        } else {
            SegmentBytes(bytes)
        }
    }

    /// Segments of exactly `bytes`, however small: the tests' logs of a few records each.
    #[cfg(all(test, feature = "retention"))]
    pub(crate) const fn exactly(bytes: u64) -> SegmentBytes {
        SegmentBytes(bytes)
    }

    /// The size in bytes.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl Default for SegmentBytes {
    fn default() -> SegmentBytes {
        SegmentBytes(DEFAULT_SEGMENT_BYTES)
    }
}
