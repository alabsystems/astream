// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The durable log's STORAGE SEAM: every byte [`BrokerLog`](crate::BrokerLog) reads or
//! writes on its own file, and every read and atomic replacement of its identity
//! sidecar, goes through the two enums here.
//!
//! In a release build each has one variant — `Os`, a real `File` and the log's real
//! path — so every match compiles away to the call it wraps, and a build that gave one
//! another would not compile (the release-build check below, THE RELEASE BUILD HOLDS
//! THE REAL FILE ALONE, and `store.rs`'s on `Storage`). Under
//! `cfg(any(test, debug_assertions))` (aterm's seam rule: a dependent's tests see it
//! with no feature a dev-dependency would flip) each gains a `Sim` variant backed by the
//! simulated device (`sim_device.rs`), which is how the REAL writer (`stage_*` +
//! `commit_batch`) and the REAL open (recovery, the identity rules, both sidecar phases)
//! run unchanged against a device that can lose power after any operation: the crash
//! simulation's (`crash_sim.rs`), and an embedder's through
//! [`SimDevice`](crate::SimDevice). The seam covers the sidecar as well as the log on
//! purpose: a seam over the log alone would make a sidecar written in the wrong order
//! relative to the log's flush invisible, and that order is half of what recovery
//! rests on.
//!
//! Enums, not `dyn` traits: a caller-supplied `dyn` object here would be an open
//! principal for Trust's thread-spawn census (the same reason `Broker`'s `Shared` holds
//! no `dyn Fn`). Retention and anti-rollback stay `Os`-only and refuse `Unsupported` on
//! a simulated log, which the simulation never asks of them.

use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::store::{create_fresh, sync_parent_dir};

#[cfg(clean_islands)]
#[path = "storage_island.rs"]
mod storage_island;
#[cfg(not(clean_islands))]
pub use crate::twins::storage_len_advance;
#[cfg(clean_islands)]
pub use storage_island::storage_len_advance;

contract_fn! {
    /// Verified check that a storage truncation target does not exceed the current file length
    /// (`target <= current`), linked via `clean-kernel-defeq` to `storage_truncate_within_len_isl`.
    #[must_use]
    pub fn storage_truncate_within_len(target: u64, current: u64) -> bool
    clauses [ensures result == (target <= current)]
    {
        target <= current
    }
}

/// The log file itself.
pub(crate) enum Backing {
    /// The real file, exclusively locked by the open. SHARED — an `Arc`, never a second
    /// descriptor — with the [`FlushHandle`]s the writer takes to flush it outside the
    /// log's lock ([`flush_handle`](Self::flush_handle) says why).
    Os(Arc<File>),
    /// The simulated device.
    #[cfg(any(test, debug_assertions))]
    Sim(crate::sim_device::Sim),
}

/// THE RELEASE BUILD HOLDS THE REAL FILE ALONE: each match here names `Os` and nothing
/// else, so it compiles only while that is every variant — a release build in which the
/// seam's enums kept a simulated variant (or gained any other) stops compiling here.
#[cfg(not(any(test, debug_assertions)))]
const _: (fn(&Backing), fn(&HandleBacking), fn(&Dir)) = (
    |b| match b {
        Backing::Os(_) => {}
    },
    |h| match h {
        HandleBacking::Os(_) => {}
    },
    |d| match d {
        Dir::Os(_) => {}
    },
);

impl Drop for Backing {
    fn drop(&mut self) {
        // Release `flock(LOCK_UN)` explicitly whenever `Backing` drops (including on
        // early-return errors in `BrokerLog::open_core` before `BrokerLog` is constructed,
        // and on `compact_switch` replacement while `FlushHandle`s or concurrent
        // `fork`/`posix_spawn` children may still hold the open file description).
        self.unlock();
    }
}

impl Backing {
    /// The real file `file`.
    pub(crate) fn from_file(file: File) -> Backing {
        Backing::Os(Arc::new(file))
    }

    /// Read the whole file from its start.
    pub(crate) fn read_to_end(&mut self, out: &mut Vec<u8>) -> io::Result<usize> {
        match self {
            Backing::Os(f) => {
                let mut f: &File = f;
                f.seek(SeekFrom::Start(0))?;
                f.read_to_end(out)
            }
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => Ok(s.read_log(out)),
        }
    }

    /// Append `bytes` at byte `at`, the end the log tracks (its durable length), by a
    /// POSITIONAL write ([`write_all_at`]): the log only ever appends, and a rollback
    /// truncates back to that end with [`resize_file`](Self::resize_file), so the next
    /// append is written where the last one left off whatever moved the file cursor.
    pub(crate) fn write_at(&self, bytes: &[u8], at: u64) -> io::Result<()> {
        match self {
            Backing::Os(f) => write_all_at(f, bytes, at),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => {
                s.write_at(at, bytes);
                Ok(())
            }
        }
    }

    /// F24's NEGATIVE CONTROL: the append as it was before it was positional, at the file
    /// cursor (a real file's, or the simulated device's, which its reads move as
    /// Windows' `seek_read` moves a file's).
    #[cfg(test)]
    pub(crate) fn write_at_cursor(&self, bytes: &[u8]) -> io::Result<()> {
        match self {
            Backing::Os(f) => (&**f).write_all(bytes),
            Backing::Sim(s) => {
                s.write_at_cursor(bytes);
                Ok(())
            }
        }
    }

    /// Truncate (or extend with zeros) to `len` bytes.
    pub(crate) fn resize_file(&self, len: u64) -> io::Result<()> {
        match self {
            Backing::Os(f) => {
                let op: fn(&File, u64) -> io::Result<()> = File::set_len;
                op(f, len)
            }
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => {
                let op: fn(&crate::sim_device::Sim, u64) = crate::sim_device::Sim::set_len;
                op(s, len);
                Ok(())
            }
        }
    }

    /// A FULL flush of the file's data: `sync_data`, which on Apple is
    /// `F_FULLFSYNC` (the drive's cache emptied too) and elsewhere `fdatasync`.
    pub(crate) fn sync_data(&self) -> io::Result<()> {
        match self {
            Backing::Os(f) => astream_sys::full_sync_data(f),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => {
                s.full_flush();
                Ok(())
            }
        }
    }

    /// An ORDERING flush ([`astream_sys::barrier_sync`]): on Apple `F_BARRIERFSYNC`,
    /// which issues every write made so far to the device ahead of every write made
    /// after it, without waiting for the device to hold either; elsewhere a full flush.
    pub(crate) fn barrier(&self) -> io::Result<()> {
        match self {
            Backing::Os(f) => astream_sys::barrier_sync(f),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => {
                s.barrier();
                Ok(())
            }
        }
    }

    /// Whether this file can be asked for an ordering-only flush at all: a real file on
    /// Apple, where `F_BARRIERFSYNC` exists (whether its DEVICE honours it is the open's
    /// probe), and always the simulated device, which models one on every platform.
    pub(crate) fn barrier_exists(&self) -> bool {
        match self {
            Backing::Os(_) => cfg!(target_vendor = "apple"),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(_) => true,
        }
    }

    /// The device this file is on and whether its full flush ([`FlushHandle::full`],
    /// `F_FULLFSYNC` on Apple) drains it ([`LogDevice`](crate::LogDevice)), read by `fstat`
    /// on the file's own descriptor; `None` where that fails, off Unix, and for the
    /// simulated device, which shares no device with any other file.
    pub(crate) fn device(&self) -> Option<crate::LogDevice> {
        match self {
            #[cfg(unix)]
            Backing::Os(f) => {
                use std::os::unix::fs::MetadataExt as _;
                let meta = f.metadata().ok()?;
                Some(crate::LogDevice {
                    dev: meta.dev(),
                    flush_drains_device: cfg!(target_vendor = "apple"),
                })
            }
            #[cfg(not(unix))]
            Backing::Os(_) => None,
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(_) => None,
        }
    }

    /// A handle that flushes this file IN FULL from another place than the log's own
    /// lock: the file's own descriptor, shared, or the simulated device. `fail` stands in
    /// the fault-injection seam's failed fsync.
    ///
    /// SHARED, NOT DUPLICATED, so taking one cannot fail. It used to be a `try_clone` per
    /// flush — every escalated batch, every horizon (about once a second under traffic),
    /// every `flush_durable` — and a `dup` refused for want of a descriptor (`EMFILE`, a
    /// broker near the default 256 soft limit) was a full flush that could not be issued,
    /// so it was handled as a FAILED one: the run recorded lossy, the log latched, the
    /// waiting ops told "outcome unknown", though no flush had run and nothing could have
    /// been lost. The descriptor is the open file's; the `Arc` keeps it open for a flush
    /// in flight when retention replaces the file (the flush then reaches the unlinked
    /// original, which is harmless: see [`FlushHandle`]), exactly as the second
    /// descriptor did, and the exclusive lock rides the open file description either way.
    pub(crate) fn flush_handle(&self, fail: bool) -> FlushHandle {
        let backing = match self {
            Backing::Os(f) => HandleBacking::Os(Arc::clone(f)),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => HandleBacking::Sim(s.clone()),
        };
        FlushHandle { backing, fail }
    }

    /// What the writer writes and flushes a batch through with the log's lock RELEASED
    /// ([`BatchOut`]): the file's own descriptor, shared, or the simulated device.
    /// Shared for the reason a [`FlushHandle`] is ([`flush_handle`](Self::flush_handle)):
    /// taking one cannot fail and opens nothing, so a broker at its descriptor limit
    /// (`EMFILE`) fails no batch for it — where a `dup` per batch, or one kept and made
    /// again after every failed batch and every retention rewrite, could.
    pub(crate) fn batch_out(&self) -> BatchOut {
        BatchOut(match self {
            Backing::Os(f) => HandleBacking::Os(Arc::clone(f)),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => HandleBacking::Sim(s.clone()),
        })
    }

    /// A FULL flush of the file's data and metadata (`sync_all`).
    pub(crate) fn sync_all(&self) -> io::Result<()> {
        match self {
            Backing::Os(f) => astream_sys::full_sync(f),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => {
                s.full_flush();
                Ok(())
            }
        }
    }

    /// Release the exclusive advisory lock (the OS releases it at close anyway).
    pub(crate) fn unlock(&self) {
        match self {
            Backing::Os(f) => {
                let _ = f.unlock();
            }
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(_) => {}
        }
    }

    /// Exactly `len` bytes from byte `start`, by a POSITIONAL read: a cold record read
    /// under the log's shared borrow, and the newest frame a clean close fingerprints. On
    /// Windows the read (`seek_read`) leaves the file cursor at the end of what it read;
    /// no write depends on the cursor (every append is positional,
    /// [`write_at`](Self::write_at), [`BatchOut::write_at`]), so that is harmless.
    pub(crate) fn read_at(&self, start: u64, len: usize) -> io::Result<Vec<u8>> {
        match self {
            Backing::Os(f) => {
                let mut buf = vec![0u8; len];
                read_exact_at(f, &mut buf, start)?;
                Ok(buf)
            }
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => s
                .read_at(start, len)
                .ok_or_else(|| io::Error::from(io::ErrorKind::UnexpectedEof)),
        }
    }

    /// The file's length in bytes.
    pub(crate) fn len(&self) -> io::Result<u64> {
        match self {
            Backing::Os(f) => Ok(f.metadata()?.len()),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => Ok(s.log_len() as u64),
        }
    }

    /// Up to `buf.len()` bytes from byte `start`, by POSITIONAL reads, fewer only where the
    /// file ends: how many were read. The open's scan reads the log through it a window at
    /// a time (`open_scan.rs`), which on Windows moves the file cursor as
    /// [`read_at`](Self::read_at) does, as harmlessly.
    pub(crate) fn read_some_at(&self, start: u64, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Backing::Os(f) => read_some_at(f, buf, start),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(s) => Ok(s.read_log_at(start, buf)),
        }
    }

    /// The first `len` bytes of the file (fewer where it ends), read through the
    /// log's own descriptor. Reserve only the actual prefix, fallibly, rather than
    /// allocating the requested length before discovering a shorter file.
    pub(crate) fn stored(&self, len: u64) -> io::Result<Vec<u8>> {
        let len = len.min(self.len()?);
        let capacity =
            usize::try_from(len).map_err(|_| io::Error::from(io::ErrorKind::OutOfMemory))?;
        let mut out = stored_buffer(capacity)?;
        // No resize(len): each append is bounded by the stack buffer, and the
        // complete output fits the capacity already reserved without aborting.
        self.copy_stored(len, &mut out)?;
        Ok(out)
    }

    /// Copy up to `len` bytes through the log's own descriptor, with fixed scratch
    /// space. A short file ends the copy; read/write errors preserve their error.
    /// Every read is POSITIONAL, as cold reads and appends are on every OS.
    pub(crate) fn copy_stored<W: Write>(&self, len: u64, out: &mut W) -> io::Result<u64> {
        let mut buf = [0u8; STORED_CHUNK];
        let mut at = 0u64;
        while at < len {
            let remaining = len - at;
            let want = if remaining > STORED_CHUNK as u64 {
                STORED_CHUNK
            } else {
                remaining as usize
            };
            let window = buf
                .get_mut(..want)
                .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidData))?;
            let got = self.read_some_at(at, window)?;
            if got == 0 {
                break;
            }
            // Keep the positional-read contract local: even a bad byte count
            // cannot select outside the window or advance past the requested end.
            let bytes = window
                .get(..got)
                .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidData))?;
            let next = at
                .checked_add(got as u64)
                .ok_or_else(|| io::Error::from(io::ErrorKind::InvalidData))?;
            if next > len {
                return Err(io::Error::from(io::ErrorKind::InvalidData));
            }
            out.write_all(bytes)?;
            at = next;
        }
        Ok(at)
    }

    /// The real file, shared (the log's own descriptor, as the [`FlushHandle`]s share it),
    /// for the paths that exist only on disk (retention's rewrite, its copy and the
    /// permissions it copies); `Unsupported` on a simulated log.
    #[cfg_attr(not(feature = "retention"), allow(dead_code))]
    pub(crate) fn os(&self) -> io::Result<&Arc<File>> {
        match self {
            Backing::Os(f) => Ok(f),
            #[cfg(any(test, debug_assertions))]
            Backing::Sim(_) => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "not on a simulated log",
            )),
        }
    }
}

/// Inspection copies keep one fixed buffer regardless of the committed log's size.
const STORED_CHUNK: usize = 64 * 1024;

/// Fallible output reservation, kept separate so capacity overflow is testable
/// without manufacturing an enormous file or exhausting the process allocator.
fn stored_buffer(capacity: usize) -> io::Result<Vec<u8>> {
    let mut out = Vec::new();
    out.try_reserve_exact(capacity)
        .map_err(|_| io::Error::from(io::ErrorKind::OutOfMemory))?;
    Ok(out)
}

/// The length in bytes of `file` via `fstat` / `metadata`.
pub(crate) fn file_len(file: &File) -> io::Result<u64> {
    Ok(file.metadata()?.len())
}

/// Up to `buf.len()` bytes of `file` from byte `start`, by positional reads, fewer only
/// where the file ends: how many were read.
pub(crate) fn read_some_at(file: &File, mut buf: &mut [u8], mut start: u64) -> io::Result<usize> {
    let mut got = 0usize;
    while !buf.is_empty() {
        let n = match read_once_at(file, buf, start) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        };
        got = got.saturating_add(n);
        start = start.saturating_add(n as u64);
        let rest = std::mem::take(&mut buf);
        buf = rest.get_mut(n..).unwrap_or(&mut []);
    }
    Ok(got)
}

/// One positional read of `file` into `buf` from byte `start`.
#[cfg(unix)]
fn read_once_at(file: &File, buf: &mut [u8], start: u64) -> io::Result<usize> {
    use std::os::unix::fs::FileExt;
    file.read_at(buf, start)
}

/// One positional read of `file` into `buf` from byte `start` (`seek_read`, which leaves the
/// file cursor at the end of what it read; nothing writes at the cursor).
#[cfg(windows)]
fn read_once_at(file: &File, buf: &mut [u8], start: u64) -> io::Result<usize> {
    use std::os::windows::fs::FileExt;
    file.seek_read(buf, start)
}

/// The whole of `bytes` into `file` from byte `at`, by positional writes, looping on a
/// short one (and an interrupted one): `pwrite` on Unix.
///
/// WHY EVERY APPEND IS POSITIONAL (aterm F24). A cold read (`record_arc` →
/// [`Backing::read_at`]) and the open's scan ([`Backing::read_some_at`]) read by position,
/// and on Windows `seek_read` moves the file cursor to the end of what it read. An append
/// written AT THE CURSOR then lands inside the log: a cold read under the log's lock
/// followed by an un-batched append, or a cold read in the window where the writer
/// writes a batch with the lock released ([`BatchOut`]), overwrites retained frames with
/// the new ones — a torn log that the next open cuts or refuses. Writing every append at
/// the end the log already tracks (its durable length, which a failed write's rollback
/// truncates the file back to) makes no write depend on the cursor on any OS, and costs
/// what the cursor write cost: one call per append, no handle, no lock and no second
/// call. The alternatives each cost or miss something:
///
/// - AN APPEND-ONLY HANDLE (`FILE_APPEND_DATA` without `FILE_WRITE_DATA` on Windows;
///   `O_APPEND` on Unix) is a second open of the file: it can fail where taking the shared
///   descriptor cannot ([`Backing::flush_handle`] says why that matters), retention's
///   rewrite replaces the file under it, and on Windows the whole-file exclusive lock the
///   open takes (`LockFileEx` through the log's own handle, `lock_exclusive`) denies reads
///   and writes through any other handle of the file, this process's included. And it
///   writes at the FILE's end, not the log's: after a write that failed partway, the next
///   append lands past the torn bytes unless the rollback's truncate took, and on Windows
///   that truncate would have to go through the other handle, since one without
///   `FILE_WRITE_DATA` may not shorten the file (an `O_APPEND` descriptor on Unix may).
/// - A SEPARATE READ HANDLE for the cold reads and the scan is the same second open, with
///   the same lock in the way, and must be replaced in step with every retention rewrite.
///   That lock is why the live log is read through its own descriptor, and by position
///   wherever a read can overlap an append: the cold reads, the open's scan, retention's
///   copy (`compact::KeptCopy`, which reads with no lock held while the writer appends,
///   safe because no append depends on the cursor) and the inspection read
///   ([`Backing::stored`]). Two reads a Windows build makes are not positional reads
///   through it. One is [`Backing::read_to_end`], a cursor read through the log's own
///   descriptor, which a replica's tail truncation (`BrokerLog::truncate_replica_to`)
///   makes where nothing overlaps it: under `&mut` on a bare log, and on a broker behind
///   the compaction gate (`Broker::truncate_replica_to` takes it first), which the copy
///   holds. The other is an offline seal's check of the log it pins
///   (`offline_seal::changed_since`, which `settle` in the open and `pending` in
///   `check_open` run under their lock and before any append): it reads the newest frame
///   through a second open of the path, which on Windows succeeds and whose read the lock
///   refuses, so the open or the check fails there. Only a seal's marker and staged log
///   beside the log reach it, and the seal that writes them is Unix-only (it reads the
///   plaintext log through its name too, where the lock is advisory and refuses no read).
/// - A CURSOR RESTORE (seek back to the end after every read, under the lock) misses the
///   batch written OUTSIDE the lock: the batch's write can run between a reader's read
///   and its restore, at the cursor the read left, and a restore that runs while the
///   batch is half written seeks to the end as it stands mid-batch. It also costs a seek
///   per cold read and leaves a hazard every future reader of the file must remember.
#[cfg(unix)]
fn write_all_at(file: &File, bytes: &[u8], at: u64) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.write_all_at(bytes, at)
}

/// The whole of `bytes` into `file` from byte `at`, by `seek_write`s, looping on a short
/// one (and an interrupted one). The Unix arm says why every append is positional.
#[cfg(windows)]
fn write_all_at(file: &File, mut bytes: &[u8], mut at: u64) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !bytes.is_empty() {
        match file.seek_write(bytes, at) {
            Ok(0) => return Err(io::Error::from(io::ErrorKind::WriteZero)),
            Ok(n) => {
                bytes = bytes.get(n..).unwrap_or(&[]);
                at = at.saturating_add(n as u64);
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

/// `pread` the whole of `buf` from byte `start` of `file`.
#[cfg(unix)]
pub(crate) fn read_exact_at(file: &File, buf: &mut [u8], start: u64) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.read_exact_at(buf, start)
}

/// The whole of `buf` from byte `start` of `file`, by `seek_read`s, which leave the file
/// cursor at the end of what they read (nothing writes at the cursor).
#[cfg(windows)]
pub(crate) fn read_exact_at(file: &File, mut buf: &mut [u8], mut start: u64) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !buf.is_empty() {
        let n = file.seek_read(buf, start)?;
        if n == 0 {
            return Err(io::Error::from(io::ErrorKind::UnexpectedEof));
        }
        let rest = std::mem::take(&mut buf);
        buf = rest.get_mut(n..).unwrap_or(&mut []);
        start = start.saturating_add(n as u64);
    }
    Ok(())
}

/// A FULL flush of the log taken OUTSIDE its lock: what the writer issues for an
/// escalated record, for the durability horizon and for `flush_durable`
/// ([`BrokerLog::flush_handle`](crate::BrokerLog)), so that a reader asking for a page
/// never waits on a device flush.
///
/// It is the log's own descriptor, shared ([`Backing::flush_handle`]); a second
/// descriptor would be the same flush, since `F_FULLFSYNC` (and `fdatasync`) flush the
/// FILE — every dirty page of its vnode, through whichever descriptor wrote it — not the
/// descriptor. And why it is safe without the lock: the writer thread is the only
/// appender and it is the thread issuing this flush, so no `write()` overlaps it (a write
/// would block behind a flush of the same vnode); the one other thing that touches the
/// file, retention, replaces it with a copy it has itself flushed in full, so a flush of
/// the unlinked original afterwards is harmless and what it was meant to cover is
/// durable at the path either way.
pub(crate) struct FlushHandle {
    backing: HandleBacking,
    /// The fault-injection seam's failed fsync, as it stood when the handle was taken.
    fail: bool,
}

enum HandleBacking {
    Os(Arc<File>),
    #[cfg(any(test, debug_assertions))]
    Sim(crate::sim_device::Sim),
}

impl FlushHandle {
    /// Flush the file in full (`F_FULLFSYNC` on Apple, `fdatasync` elsewhere).
    pub(crate) fn full(&self) -> io::Result<()> {
        if self.fail {
            return Err(io::Error::other("injected fsync fault"));
        }
        match &self.backing {
            HandleBacking::Os(f) => astream_sys::full_sync_data(f),
            #[cfg(any(test, debug_assertions))]
            HandleBacking::Sim(s) => {
                s.full_flush();
                Ok(())
            }
        }
    }

    /// The crash simulation's negative control NC7: an ORDERING flush where the full one
    /// belongs, so the product believes durable what is only ordered.
    #[cfg(test)]
    pub(crate) fn barrier_instead(&self) {
        if let HandleBacking::Sim(s) = &self.backing {
            s.barrier();
        }
    }
}

/// What a batch is written and flushed through OUTSIDE the log's lock
/// ([`Backing::batch_out`], lent to a batch by `BrokerLog::commit_begin`): the broker's
/// writer thread writes and flushes every batch on it while readers take the lock.
///
/// WHY THE LOG'S OWN DESCRIPTOR, SHARED. The write lands exactly where a write under the
/// lock would: positionally, at the end the log tracks when the batch began (its durable
/// length, which a rollback truncates the file back to), and the flush — full, or the
/// ordering barrier — covers the vnode's dirty pages whichever descriptor wrote them, as
/// a [`FlushHandle`]'s does. Shared and not a second descriptor, so taking one cannot
/// fail and opens nothing ([`Backing::batch_out`]); and the `Arc` names the file the
/// batch began on, which is the log's file at its end too (see below).
///
/// WHY NOTHING ELSE WRITES THE FILE OR MOVES ITS END WHILE A BATCH IS WRITTEN. The writer
/// thread is the only appender, and it is the thread writing here. What else touches the
/// file under the lock refuses while a batch is staged — retention's rewrite (the one
/// thing that replaces the file), the un-batched retirement, the fenced replica append,
/// the clean close and its read-back of the newest frame (`staged` stays non-empty, and
/// `writing` set, from the batch's begin to its end) — and the broker's retention calls
/// also take the writer's batch lock first, so they wait for the batch instead. A cold
/// read ([`Backing::read_at`]) runs under the lock while a batch is written; it reads
/// below the batch's start, and the file cursor it moves on Windows is nowhere any write
/// lands ([`write_all_at`] says why every append is positional).
pub(crate) struct BatchOut(HandleBacking);

impl BatchOut {
    /// Append `bytes` at byte `at`, the end the log tracked when the batch began, by a
    /// positional write ([`write_all_at`]).
    pub(crate) fn write_at(&self, bytes: &[u8], at: u64) -> io::Result<()> {
        match &self.0 {
            HandleBacking::Os(f) => write_all_at(f, bytes, at),
            #[cfg(any(test, debug_assertions))]
            HandleBacking::Sim(s) => {
                s.write_at(at, bytes);
                Ok(())
            }
        }
    }

    /// F24's negative control: the batch's append at the file cursor, as
    /// [`Backing::write_at_cursor`].
    #[cfg(test)]
    pub(crate) fn write_at_cursor(&self, bytes: &[u8]) -> io::Result<()> {
        match &self.0 {
            HandleBacking::Os(f) => (&**f).write_all(bytes),
            HandleBacking::Sim(s) => {
                s.write_at_cursor(bytes);
                Ok(())
            }
        }
    }

    /// A FULL flush of the file's data, as [`Backing::sync_data`].
    pub(crate) fn sync_data(&self) -> io::Result<()> {
        match &self.0 {
            HandleBacking::Os(f) => astream_sys::full_sync_data(f),
            #[cfg(any(test, debug_assertions))]
            HandleBacking::Sim(s) => {
                s.full_flush();
                Ok(())
            }
        }
    }

    /// An ORDERING flush, as [`Backing::barrier`].
    pub(crate) fn barrier(&self) -> io::Result<()> {
        match &self.0 {
            HandleBacking::Os(f) => astream_sys::barrier_sync(f),
            #[cfg(any(test, debug_assertions))]
            HandleBacking::Sim(s) => {
                s.barrier();
                Ok(())
            }
        }
    }

    /// Whether this is `file`'s own descriptor — the same open file, not a second
    /// descriptor of it, and not another file's.
    #[cfg(test)]
    pub(crate) fn is_of(&self, file: &Backing) -> bool {
        match (&self.0, file) {
            (HandleBacking::Os(out), Backing::Os(f)) => Arc::ptr_eq(out, f),
            _ => false,
        }
    }
}

/// The log's directory, as far as the open's sidecar reads and atomic replacements go.
pub(crate) enum Dir {
    /// The real directory; holds the LOG's path, from which each sidecar's is derived.
    Os(PathBuf),
    /// The simulated device, which keeps the sidecar beside its log.
    #[cfg(any(test, debug_assertions))]
    Sim(crate::sim_device::Sim),
}

impl Dir {
    /// The log's path: the stem sidecar names derive from, and what messages name.
    pub(crate) fn log_path(&self) -> &Path {
        match self {
            Dir::Os(p) => p,
            #[cfg(any(test, debug_assertions))]
            Dir::Sim(s) => s.path(),
        }
    }

    /// Whether this is the real directory (the paths retention, anti-rollback, the
    /// replica marker and the base sidecar exist on).
    pub(crate) const fn is_os(&self) -> bool {
        matches!(self, Dir::Os(_))
    }

    /// The bytes of `<log>.id`, or `None` when there is none.
    pub(crate) fn read_id(&self) -> io::Result<Option<Vec<u8>>> {
        match self {
            Dir::Os(p) => match std::fs::read(crate::logid::identity_path(p)) {
                Ok(b) => Ok(Some(b)),
                Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
                Err(e) => Err(e),
            },
            #[cfg(any(test, debug_assertions))]
            Dir::Sim(s) => Ok(s.read_id()),
        }
    }

    /// Durably replace `<log>.id` with `bytes`: tmp file, fsync, rename, directory
    /// fsync, never following a link planted at either name. Durable when it returns.
    pub(crate) fn replace_id(&self, bytes: &[u8]) -> io::Result<()> {
        match self {
            Dir::Os(p) => {
                let path = crate::logid::identity_path(p);
                let mut tmp = path.clone();
                tmp.as_mut_os_string().push(".tmp");
                {
                    let mut f = create_fresh(&tmp, &mut OpenOptions::new())?;
                    f.write_all(bytes)?;
                    astream_sys::full_sync(&f)?;
                    // The power-loss model (`power_loss.rs`) learns the flush, as
                    // `flush_file` tells it: the offline seal's crash tests read it.
                    #[cfg(all(test, unix, feature = "retention"))]
                    crate::power_loss::flushed(&tmp);
                }
                crate::store::rename_path(&tmp, &path)?;
                sync_parent_dir(&path)
            }
            #[cfg(any(test, debug_assertions))]
            Dir::Sim(s) => {
                s.replace_id(bytes);
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod inspection_tests {
    use super::*;
    use crate::test_scratch::Scratch;

    fn backing(bytes: &[u8]) -> (Scratch, PathBuf, Backing) {
        let root = Scratch::new("inspection-storage");
        let path = root.path().join("log");
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        file.write_all(bytes).unwrap();
        (root, path, Backing::from_file(file))
    }

    #[test]
    fn enormous_requested_prefix_reserves_only_the_actual_file_length() {
        let (_root, _path, file) = backing(b"the whole short file");
        let bytes = file.stored(u64::MAX).unwrap();
        assert_eq!(bytes, b"the whole short file");
        assert!(bytes.capacity() < STORED_CHUNK);
        assert_eq!(file.stored(9).unwrap(), b"the whole");
        assert!(file.stored(0).unwrap().is_empty());
    }

    #[test]
    fn unrepresentable_reservation_returns_out_of_memory_without_panicking() {
        // Deterministic capacity overflow exercises the real fallible allocator
        // entry point without trying to exhaust the test process's heap.
        let error = stored_buffer(usize::MAX).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::OutOfMemory);
    }

    struct ShortWriter {
        bytes: Vec<u8>,
        fail_at: Option<usize>,
    }

    impl Write for ShortWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let room = self
                .fail_at
                .map_or(usize::MAX, |end| end.saturating_sub(self.bytes.len()));
            if room == 0 {
                return Err(io::Error::from(io::ErrorKind::BrokenPipe));
            }
            let count = bytes.len().min(997).min(room);
            self.bytes.extend_from_slice(&bytes[..count]);
            Ok(count)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn positional_copy_handles_short_writes_and_preserves_partial_errors() {
        let data: Vec<_> = (0..3 * STORED_CHUNK + 73).map(|i| i as u8).collect();
        let (_root, _path, file) = backing(&data);
        let mut out = ShortWriter {
            bytes: Vec::new(),
            fail_at: None,
        };
        assert_eq!(
            file.copy_stored(u64::MAX, &mut out).unwrap(),
            data.len() as u64
        );
        assert_eq!(out.bytes, data);
        assert_eq!(file.stored(u64::MAX).unwrap(), data);

        let partial = STORED_CHUNK + 123;
        let mut out = ShortWriter {
            bytes: Vec::new(),
            fail_at: Some(partial),
        };
        assert_eq!(
            file.copy_stored(u64::MAX, &mut out).unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(out.bytes, data[..partial]);
    }

    #[cfg(unix)]
    #[test]
    fn inspection_keeps_reading_the_original_descriptor_after_path_replacement() {
        let (_root, path, file) = backing(b"original inode");
        let renamed = path.with_extension("old");
        std::fs::rename(&path, &renamed).unwrap();
        std::fs::write(&path, b"replacement inode").unwrap();
        assert_eq!(file.stored(u64::MAX).unwrap(), b"original inode");
        let mut copied = Vec::new();
        file.copy_stored(u64::MAX, &mut copied).unwrap();
        assert_eq!(copied, b"original inode");
        assert_eq!(std::fs::read(&path).unwrap(), b"replacement inode");
    }

    #[test]
    #[ignore = "manual sparse-file inspection above 256 MiB, with fixed RAM"]
    fn inspection_streams_a_large_sparse_file_without_a_full_log_allocation() {
        const SIZE: u64 = (256 << 20) + 37;
        let (_root, _path, file) = backing(b"begin");
        file.resize_file(SIZE).unwrap();
        file.write_at(b"end", SIZE - 3).unwrap();
        struct Counter(u64);
        impl Write for Counter {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                assert!(bytes.len() <= STORED_CHUNK);
                if self.0 == 0 {
                    assert!(bytes.starts_with(b"begin"));
                }
                self.0 += bytes.len() as u64;
                if self.0 == SIZE {
                    assert!(bytes.ends_with(b"end"));
                }
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut out = Counter(0);
        assert_eq!(file.copy_stored(u64::MAX, &mut out).unwrap(), SIZE);
        assert_eq!(out.0, SIZE);
    }
}
