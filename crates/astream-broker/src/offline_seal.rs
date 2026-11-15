// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE OFFLINE SEAL of a plaintext log ([`BrokerLog::seal_plaintext`], feature `at-rest`,
//! unix), and THE SWITCH it ends with, which every open of a real log finishes or undoes
//! (every build).
//!
//! # What the seal does
//!
//! A log written without an at-rest key holds every record in the clear, and an open with a
//! key reads such a log as a legacy v1 sealed one and refuses it (its first record does not
//! authenticate). The seal turns it into a v2 sealed log, offline: no broker may serve it
//! while it runs, and none can, because it holds the log's lock throughout.
//!
//! 1. The plaintext log is opened (its recovery, its identity, its lock) and closed cleanly
//!    at once, so a seal that fails after its open leaves it as a clean stop, readable as
//!    before.
//! 2. A sealed copy is staged beside it under `<log>.sealing`: every retained frame's payload
//!    sealed under the key, bound to a fresh `<log>.seal` binding and to its own offset (the
//!    frames keep their offsets, the base and the batch marks byte for byte); the `.state`
//!    and `.held` sidecars sealed frame for frame the same way; `.base` as it is; the
//!    identity sidecar `.id` the plaintext log's own, closed at the same base and head
//!    (fingerprinting the sealed newest frame, so the next open finds the record it saw
//!    there and moves nothing); and the binding `.seal`. Every file is flushed, then the
//!    directory.
//! 3. The copy is READ BACK before anything of the plaintext log is touched: opened with
//!    the key, bound (`require_bound_at_rest`), its records, broker times, base, head,
//!    identity, lineage, carried state and held store compared with the plaintext log's,
//!    and every frame of the copy, its `.state` and its `.held` opened under the key and
//!    compared byte for byte with the plaintext payload it was sealed from. Any difference
//!    refuses the seal, the plaintext log untouched. The copy is closed cleanly.
//! 4. The switch's MARKER, `<log>.sealmove`, is made durable (tmp, flush, rename, directory
//!    flush): from here on the switch goes forward, over the plaintext log the marker pins
//!    (its length, its newest frame's fingerprint, and a fingerprint of each of its `.base`,
//!    `.state` and `.held`, or that it has none).
//! 5. THE SWITCH: each staged sidecar is renamed over the log's own (`.seal`, `.base`,
//!    `.state`, `.held`, `.id`, in that order), then the staged log over the log, the
//!    directory flushed, and the marker removed (and the directory flushed again).
//!
//! # Wholly plaintext or wholly sealed, after any crash
//!
//! Every open of a real log runs [`settle`] under the log's lock, after the embedder's
//! prepare and before it reads a byte (`BrokerLog::open_core`), so no reader ever meets the
//! switch half done:
//!
//! - the marker is durable: the switch is FINISHED, whatever part of it ran (each rename is
//!   taken only if its staged file is still there, so finishing it twice is finishing it
//!   once). The log is wholly sealed, under the identity it had.
//! - the marker is durable, but the staged log has not taken the name yet and the log there
//!   is no longer the one the marker pins: its length or its newest frame differs, a sidecar
//!   not yet replaced differs, or one it had none of has appeared. A build that does not
//!   settle (an older astream) opened it in the middle of the switch and wrote to it.
//!   Finishing the switch would drop what that build wrote (a record it acked, whose offset
//!   the sealed log would then hand out again under the same identity), and the sidecars
//!   already replaced cannot be put back with certainty, so the open REFUSES
//!   (`InvalidData`, naming the marker) and moves nothing.
//! - there is no marker: the staging is UNDONE (its sidecars removed, then the staged log),
//!   and the log is wholly plaintext, exactly as step 1 left it.
//!
//! Every build runs it, a keyless one too: a build without `at-rest` that met a switch half
//! done would read a sealed log under a plaintext `.id`, or the reverse. A keyless open that
//! finishes a switch then refuses the sealed log it finished, as it refuses every log a
//! `.seal` binding sits beside, before it reads `.state` or `.held`
//! (`refuse_keyless_sealed`, in `store.rs`). The bytes stay as they are.
//!
//! The lock makes the settle safe to run: the seal holds the plaintext log's lock from its
//! first step to its last, and the staged log's from the read-back on, and the staged log is
//! the log once it is renamed over it. So an open that takes the log's lock knows no seal of
//! it is running, and one that cannot is refused (`AlreadyExists`) before it looks. An open
//! that finishes a switch opens and locks the staged log BEFORE renaming it over the name,
//! and keeps that file as the log: the name is never unlocked between the open's lock on the
//! plaintext file and its hold on the sealed one, so no other open meets the switch's last
//! steps or runs its prepare in between.
//!
//! # Honest boundary
//!
//! - The plaintext bytes the switch replaces are UNLINKED, not erased. A filesystem
//!   snapshot, a backup, a copy, or the device's freed blocks can still hold them. The seal
//!   protects the file as it is named and everything written after it; it does not reach
//!   back into what the volume kept.
//! - The `<log>.health` snapshot stays as the last broker wrote it: it holds counts and an
//!   identity, never a record.
//! - It seals what the log retains. Retention's own work is not touched: the `.state` and
//!   `.held` sidecars are sealed frame for frame as they stand, never re-planned.
//! - A replica (`<log>.replica`) is refused: its log is its leader's spine. So is a log
//!   beside an anti-rollback watermark (`<log>.hw`), which a plaintext log never keeps.
//! - Unix only: the switch renames over the files the seal still holds open and locked.

use super::*;

/// The staged copy's name: `<log>.sealing`, its sidecars `<log>.sealing.<suffix>`.
const STAGED: &str = ".sealing";

/// The switch's marker: `<log>.sealmove`.
const MARKER: &str = ".sealmove";

/// The sidecars the switch moves, in the order it moves them, each with its bit in the
/// marker's mask. `.seal` and `.id` are always staged; the others when the log had them.
const MOVED: [(u8, &str); 5] = [
    (1, ".seal"),
    (2, ".base"),
    (4, ".state"),
    (8, ".held"),
    (16, ".id"),
];

/// The bits every marker carries: a sealed log always has its binding and its identity.
const ALWAYS: u8 = 1 | 16;

/// Every bit a marker of this build may carry.
const ALL: u8 = 1 | 2 | 4 | 8 | 16;

/// The sidecars the marker pins as the plaintext log had them, each with its [`MOVED`] bit:
/// the ones the switch replaces with sealed copies. (`.seal` and `.id` are not pinned: the
/// plaintext log has no `.seal`, and every open rewrites `.id`.)
const PINNED: [(u8, &str); 3] = [(2, ".base"), (4, ".state"), (8, ".held")];

/// The names the staging can leave beside `<log>.sealing` besides [`MOVED`]: the tmp files
/// the sidecar writers rename into place (`write_seal`, the identity's `replace_id`, the
/// held store's rewrite, `write_base`, the state's writer).
const STAGED_TMP: [&str; 5] = [
    ".seal.tmp",
    ".id.tmp",
    ".state.tmp",
    ".held.tmp",
    ".base.tmp",
];

/// The marker's payload begins with its magic and format ([`Marker::encode`]).
const MARKER_MAGIC: &[u8; 5] = b"ASMV\x01";

/// The marker's payload length: magic and format, mask, length, newest frame's start, its
/// fingerprint, and the three [`PINNED`] sidecars' fingerprints.
#[cfg(all(feature = "at-rest", unix))]
const MARKER_LEN: usize = 5 + 1 + 8 + 8 + 16 + 3 * 16;

/// What a switch's marker says: the sidecars staged, and the plaintext log it was written
/// for, which the switch is finished over only while the log is still that one
/// ([`changed_since`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Marker {
    /// The [`MOVED`] bits of the sidecars staged.
    mask: u8,
    /// The plaintext log's length in bytes.
    len: u64,
    /// Where its newest frame starts (`len` when it holds none).
    newest_at: u64,
    /// That frame's [`frame_print`] (zeros when it holds none).
    newest: [u8; 16],
    /// Each [`PINNED`] sidecar's [`sidecar_print`], in that order (zeros for one the log
    /// had none of, which its bit, clear in `mask`, says).
    sidecars: [[u8; 16]; 3],
}

impl Marker {
    /// The marker's payload.
    #[cfg(all(feature = "at-rest", unix))]
    fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MARKER_LEN);
        out.extend_from_slice(MARKER_MAGIC);
        out.push(self.mask);
        out.extend_from_slice(&encode_u64_le_bytes(self.len));
        out.extend_from_slice(&encode_u64_le_bytes(self.newest_at));
        out.extend_from_slice(&self.newest);
        for print in &self.sidecars {
            out.extend_from_slice(print);
        }
        out
    }

    /// The marker `payload` says, or `None` when this build does not read it.
    fn decode(payload: &[u8]) -> Option<Marker> {
        let (magic, rest) = payload.split_first_chunk::<5>()?;
        let (&[mask], rest) = rest.split_first_chunk::<1>()?;
        let (len, rest) = rest.split_first_chunk::<8>()?;
        let (newest_at, rest) = rest.split_first_chunk::<8>()?;
        let (newest, rest) = rest.split_first_chunk::<16>()?;
        let (base, rest) = rest.split_first_chunk::<16>()?;
        let (state, rest) = rest.split_first_chunk::<16>()?;
        let (held, rest) = rest.split_first_chunk::<16>()?;
        let m = Marker {
            mask,
            len: decode_u64_le_bytes(len),
            newest_at: decode_u64_le_bytes(newest_at),
            newest: *newest,
            sidecars: [*base, *state, *held],
        };
        let sound = magic == MARKER_MAGIC
            && rest.is_empty()
            && mask & ALWAYS == ALWAYS
            && mask & !ALL == 0
            && m.newest_at <= m.len;
        sound.then_some(m)
    }
}

/// The fingerprint the marker pins a stored frame by (zeros for no frame).
fn frame_print(frame: &[u8]) -> [u8; 16] {
    if frame.is_empty() {
        return [0; 16];
    }
    logid::fnv1a_128(&[b"astream-seal-move/frame/1", frame])
}

/// The fingerprint the marker pins a sidecar's whole content by.
fn sidecar_print(bytes: &[u8]) -> [u8; 16] {
    logid::fnv1a_128(&[b"astream-seal-move/sidecar/1", bytes])
}

/// `<log>` with `ext` appended to its name.
fn beside(log: &Path, ext: &str) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string().push(ext);
    p
}

/// Whether an entry holds `path` (a link counts: the switch never follows one).
fn present(path: &Path) -> io::Result<bool> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(e),
    }
}

/// Remove `path` when an entry holds it.
fn remove_present(path: &Path) -> io::Result<()> {
    match remove_file_path(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e),
    }
}

/// A durable step of the seal, after which its crash tests stop it dead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(
    not(all(test, unix, feature = "at-rest", feature = "retention")),
    allow(dead_code)
)]
pub(crate) enum Step {
    /// The staged log is written and flushed, its directory entry too.
    Staged,
    /// Every staged sidecar is written and flushed, and the directory.
    Sidecars,
    /// The staged copy read back whole, and closed cleanly.
    Verified,
    /// The marker is durable.
    Marker,
    /// The staged sidecar with this suffix was renamed over the log's (or the log's was
    /// removed, the copy having none).
    Moved(&'static str),
    /// The staged log was renamed over the log.
    LogMoved,
    /// The directory was flushed after the renames.
    Synced,
    /// The marker is gone, the directory flushed: the seal is done.
    Done,
}

/// WHAT EVERY OPEN OF A REAL LOG RUNS before it reads a byte, under its lock (after the
/// embedder's prepare): an offline seal's switch a crash interrupted is finished (its
/// marker is durable, and the log is still the one it pins), refused (the log changed
/// since), or its staging undone (no marker). See the module docs. `Some(file)` when it
/// renamed the staged log over `path`: the caller's descriptor then names the file that was
/// replaced, and `file` is the sealed log now at the name, opened for reading and writing
/// and locked BEFORE the rename, which the caller keeps as the log in its stead.
///
/// Two lookups when there is nothing to do, which is every open but one after a crash.
pub(super) fn settle(path: &Path) -> io::Result<Option<File>> {
    let marker = beside(path, MARKER);
    let staged = beside(path, STAGED);
    if present(&marker)? {
        let m = read_marker(&marker)?;
        // The staged log, locked before it takes the name: from the caller's lock on the file
        // at the name to its hold on this one, no other open can lock the name.
        let sealed = if present(&staged)? {
            let f = open_with_options(FsOpenOptions::new().read(true).write(true), &staged)?;
            lock_exclusive(&f, &staged)?;
            Some(f)
        } else {
            None
        };
        // A sealed log not handed back is let go by `LOCK_UN` before its close, on the error
        // path too: a `fork` in another thread holds the description until its `execve`.
        let replaced = complete(path, &m, &mut |_| Ok(()));
        if !matches!(replaced, Ok(true)) {
            if let Some(f) = &sealed {
                let _ = f.unlock();
            }
        }
        let replaced = replaced?;
        return Ok(sealed.filter(|_| replaced));
    }
    if present(&staged)? {
        undo(path)?;
    }
    Ok(None)
}

/// WHAT [`settle`] WOULD DO, judged without doing it, for a check that writes nothing
/// (`BrokerLog::check_open`, `check_open.rs`): `Ok(true)` when it would finish a switch (its
/// marker is durable and the log is still the one it pins), `Ok(false)` when it would do
/// nothing or only undo a staging no marker covers (which leaves the log and its own sidecars
/// as they stand), and the refusal it would make: a marker this build does not read, or a log
/// that changed since its marker ([`changed`]).
pub(super) fn pending(path: &Path) -> io::Result<bool> {
    let marker = beside(path, MARKER);
    if !present(&marker)? {
        return Ok(false);
    }
    let m = read_marker(&marker)?;
    if present(&beside(path, STAGED))? {
        if let Some(what) = changed_since(path, &m)? {
            return Err(changed(path, &what));
        }
    }
    Ok(true)
}

/// The refusal of a switch whose marker was made for a plaintext log that has since changed
/// (`what` names the change, [`changed_since`]).
fn changed(path: &Path, what: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "{}: the offline seal's switch this marker names was made for the plaintext log as \
             it stood then, and {what} has changed since: something that does not finish a \
             switch (an older astream) wrote to the log after the marker, or it was replaced. \
             Finishing it would drop what was written, and the sidecars it replaced already \
             cannot be put back with certainty, so the open refuses and moves nothing; the \
             staged copy {} is stale",
            beside(path, MARKER).display(),
            beside(path, STAGED).display()
        ),
    )
}

/// UNDO a staging no marker covers: its sidecars and tmp files first, the staged log last,
/// so a staged log is gone only once nothing staged is left beside it (and a crash in here
/// leaves a staging the next open undoes again). The plaintext log is not touched.
fn undo(path: &Path) -> io::Result<()> {
    let staged = beside(path, STAGED);
    for (_, sfx) in MOVED {
        remove_present(&beside(&staged, sfx))?;
    }
    for sfx in STAGED_TMP {
        remove_present(&beside(&staged, sfx))?;
    }
    remove_present(&beside(path, &format!("{MARKER}.tmp")))?;
    remove_present(&staged)?;
    sync_parent_dir(path)
}

/// FINISH the switch the marker `m` describes (see the module docs), calling `crash` after
/// each durable step (the seal's crash tests stop there; [`settle`] passes a no-op).
/// `Ok(true)` when it renamed the staged log over `path`. While the staged log has not
/// taken the name, the log there must still be the one `m` pins ([`changed_since`]): when
/// it is not, this refuses (`InvalidData`, naming the marker) before it moves anything.
fn complete(
    path: &Path,
    m: &Marker,
    crash: &mut dyn FnMut(Step) -> io::Result<()>,
) -> io::Result<bool> {
    let staged = beside(path, STAGED);
    if present(&staged)? {
        if let Some(what) = changed_since(path, m)? {
            return Err(changed(path, &what));
        }
    }
    let mask = m.mask;
    for (bit, sfx) in MOVED {
        let from = beside(&staged, sfx);
        let to = beside(path, sfx);
        if mask & bit != 0 {
            // Staged and not there any more: this switch moved it already.
            if present(&from)? {
                rename_path(&from, &to)?;
                crash(Step::Moved(sfx))?;
            }
        } else if present(&to)? {
            // The copy has none: the log's own must not outlive the switch.
            remove_file_path(&to)?;
            crash(Step::Moved(sfx))?;
        }
    }
    let replaced = present(&staged)?;
    if replaced {
        rename_path(&staged, path)?;
        crash(Step::LogMoved)?;
    }
    sync_parent_dir(path)?;
    crash(Step::Synced)?;
    for sfx in STAGED_TMP {
        remove_present(&beside(&staged, sfx))?;
    }
    remove_present(&beside(path, &format!("{MARKER}.tmp")))?;
    remove_file_path(&beside(path, MARKER))?;
    sync_parent_dir(path)?;
    crash(Step::Done)?;
    Ok(replaced)
}

/// What differs between the log at `path` and the plaintext log the marker `m` pins, or
/// `None` when nothing does: its length, its newest frame, a `.seal` beside it while the
/// staged one has not moved (the plaintext log had none), and each [`PINNED`] sidecar the
/// switch has not replaced yet (its staged copy still there, or the log had none of it).
/// `.id` is not compared: every open rewrites it, one that changed nothing too.
fn changed_since(path: &Path, m: &Marker) -> io::Result<Option<String>> {
    use std::io::{Read, Seek, SeekFrom};
    let staged = beside(path, STAGED);
    let meta = std::fs::symlink_metadata(path)?;
    if !meta.is_file() {
        return Ok(Some("the log (no longer a regular file)".into()));
    }
    if meta.len() != m.len {
        return Ok(Some("the log's length".into()));
    }
    let mut newest = Vec::new();
    if m.newest_at < m.len {
        let mut f = open_with_options(FsOpenOptions::new().read(true), path)?;
        f.seek(SeekFrom::Start(m.newest_at))?;
        f.take(m.len.saturating_sub(m.newest_at))
            .read_to_end(&mut newest)?;
    }
    if frame_print(&newest) != m.newest {
        return Ok(Some("the log's newest record".into()));
    }
    if present(&beside(&staged, ".seal"))? && present(&seal_path(path))? {
        return Ok(Some("`.seal`".into()));
    }
    for ((bit, sfx), want) in PINNED.into_iter().zip(&m.sidecars) {
        let staged_here = m.mask & bit != 0;
        if staged_here && !present(&beside(&staged, sfx))? {
            // Replaced already: the log's own is the sealed copy.
            continue;
        }
        let own = match std::fs::read(beside(path, sfx)) {
            Ok(bytes) => Some(sidecar_print(&bytes)),
            Err(e) if e.kind() == io::ErrorKind::NotFound => None,
            Err(e) => return Err(e),
        };
        if own != staged_here.then_some(*want) {
            return Ok(Some(format!("`{sfx}`")));
        }
    }
    Ok(None)
}

/// The marker at `marker`, or a refusal naming it: a marker this build cannot read names a
/// switch that can be neither finished nor undone with certainty, so nothing is touched.
fn read_marker(marker: &Path) -> io::Result<Marker> {
    let unread = || {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{}: an offline seal's switch marker this build does not read; the switch it \
                 names can be neither finished nor undone with certainty, so the open refuses \
                 and nothing beside the log is touched",
                marker.display()
            ),
        )
    };
    let meta = std::fs::symlink_metadata(marker)?;
    if !meta.is_file() || meta.len() > 256 {
        return Err(unread());
    }
    let bytes = std::fs::read(marker)?;
    let Ok(Some(d)) = Frame::decode(&bytes) else {
        return Err(unread());
    };
    if d.consumed != bytes.len() {
        return Err(unread());
    }
    Marker::decode(&d.frame.payload).ok_or_else(unread)
}

/// What [`BrokerLog::seal_plaintext`] sealed.
#[cfg(all(feature = "at-rest", unix))]
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedLog {
    /// The log's identity, the plaintext log's, unchanged.
    pub identity: crate::LogIdentity,
    /// The lowest retained offset, unchanged.
    pub base: Offset,
    /// The head, unchanged: the offset the next record takes.
    pub head: Offset,
    /// The sealed log's length in bytes.
    pub bytes: u64,
}

/// Where the read-back's tests plant a difference in the staged copy, sealed validly.
#[cfg(all(feature = "at-rest", unix))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(all(test, feature = "retention")), allow(dead_code))]
pub(crate) enum Alter {
    /// A record of the log.
    Record,
    /// A frame of `.held`.
    Held,
    /// The carried state, `.state`.
    State,
}

/// The seal's test seam: the crash tests stop it dead after a durable step (in a debug
/// build too, for [`BrokerLog::seal_plaintext_stopped_at_its_switch`]), and the read-back's
/// tests plant a difference in the staged copy (`alter`: where, and the bytes
/// whose first one is flipped before that payload is sealed).
#[cfg(all(feature = "at-rest", unix))]
#[derive(Default)]
pub(crate) struct Seam {
    #[cfg(any(test, debug_assertions))]
    pub(crate) crash_after: Option<Step>,
    #[cfg(test)]
    pub(crate) alter: Option<(Alter, &'static [u8])>,
}

#[cfg(all(feature = "at-rest", unix))]
impl Seam {
    #[cfg(any(test, debug_assertions))]
    fn crash(&self, step: Step) -> io::Result<()> {
        if self.crash_after == Some(step) {
            return Err(io::Error::other(format!("injected crash after {step:?}")));
        }
        Ok(())
    }
    #[cfg(not(any(test, debug_assertions)))]
    #[allow(clippy::unused_self)]
    const fn crash(&self, _step: Step) -> io::Result<()> {
        Ok(())
    }

    /// `payload`, or (planted at `at`) a copy with the first byte of the planted bytes
    /// flipped.
    #[cfg(test)]
    fn planted<'a>(&self, at: Alter, payload: &'a [u8]) -> std::borrow::Cow<'a, [u8]> {
        use std::borrow::Cow;
        let Some((here, needle)) = self.alter else {
            return Cow::Borrowed(payload);
        };
        if here != at || needle.is_empty() {
            return Cow::Borrowed(payload);
        }
        match payload.windows(needle.len()).position(|w| w == needle) {
            Some(i) => {
                let mut v = payload.to_vec();
                if let Some(b) = v.get_mut(i) {
                    *b ^= 1;
                }
                Cow::Owned(v)
            }
            None => Cow::Borrowed(payload),
        }
    }
    #[cfg(not(test))]
    #[allow(clippy::unused_self)]
    const fn planted<'a>(&self, _at: Alter, payload: &'a [u8]) -> std::borrow::Cow<'a, [u8]> {
        std::borrow::Cow::Borrowed(payload)
    }
}

#[cfg(all(feature = "at-rest", unix))]
impl BrokerLog {
    /// SEAL A PLAINTEXT LOG AT REST, offline: the log at `path`, written without an at-rest
    /// key, becomes a v2 log sealed under `key` (bound to a fresh `<log>.seal`), with its
    /// `.state` and `.held` sidecars sealed too — every retained record at its own offset,
    /// the base, the batch marks and the [`identity`](Self::identity) unchanged, so a
    /// client's persisted offsets stay good. Afterwards
    /// [`open_encrypted_bound`](Self::open_encrypted_bound) (or a broker opened with the key)
    /// reads it, and a keyless open refuses it. The module docs (`offline_seal.rs`) give the
    /// steps.
    ///
    /// It runs under the log's lock and needs no broker serving it: one that is refuses it
    /// (`AlreadyExists`). The plaintext log is replaced only after the sealed copy has been
    /// read back record for record and byte for byte; any failure before that leaves it in
    /// place and readable as before (closed cleanly, when its open succeeded), and a crash at
    /// any point leaves a log the next open finds wholly plaintext or wholly sealed, never a
    /// mix. A retry of a seal a crash stopped past its marker finds the log sealed already.
    ///
    /// # Errors
    ///
    /// - `NotFound` when there is no log at `path` (none is created).
    /// - `InvalidInput` when `path` is not a regular file (a link to one included: the seal
    ///   never follows one), or when a `.seal` binding sits beside the log: sealed already,
    ///   which a retry of a seal a crash stopped past its marker says too, its open having
    ///   finished that switch.
    /// - The plaintext open's refusal, said as such: `AlreadyExists` while a broker serves
    ///   it; `InvalidData` for a damaged log, or for an earlier seal's switch marker that
    ///   does not read or whose log changed after it.
    /// - `Unsupported` for a replica, a log beside an anti-rollback watermark, or (a build
    ///   without `retention`) a log with retention sidecars.
    /// - `InvalidData` when the plaintext log is not of the shape its open leaves (its
    ///   length is not what the open recovered, its frames are not one per retained record,
    ///   its `.state` is not one frame, or its `.held` frames do not read whole), and when
    ///   the copy does not read back as the log.
    /// - Any I/O error closing the plaintext log, writing the copy or switching it in.
    pub fn seal_plaintext(path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<SealedLog> {
        seal(path.as_ref(), key, &Seam::default())
    }
}

#[cfg(all(any(test, debug_assertions), feature = "at-rest", unix))]
impl BrokerLog {
    /// [`seal_plaintext`](Self::seal_plaintext) STOPPED DEAD once its marker
    /// (`<log>.sealmove`) is durable, in a test or debug build only and never behind a cargo
    /// feature: the log a crash at that moment leaves, a switch the next open finishes, which
    /// [`check_open`](Self::check_open) answers
    /// [`OpenCheck::Unsettled`]`(`[`InterruptedStep::SealSwitch`]`)`. An embedder's tests make
    /// that log with it (aterm tests its `--retire-log` refusal of one so).
    ///
    /// # Errors
    /// The seal's own error at a step before its marker ([`seal_plaintext`](Self::seal_plaintext)
    /// names them), or `InvalidData` when the seal left no switch for an open to finish.
    pub fn seal_plaintext_stopped_at_its_switch(
        path: impl AsRef<Path>,
        key: [u8; 32],
    ) -> io::Result<()> {
        let path = path.as_ref();
        let seam = Seam {
            crash_after: Some(Step::Marker),
            #[cfg(test)]
            alter: None,
        };
        match seal(path, key, &seam) {
            Err(_) if pending(path)? => Ok(()),
            Err(e) => Err(e),
            Ok(_) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: the seal left no switch to finish", path.display()),
            )),
        }
    }
}

/// [`BrokerLog::seal_plaintext`] with its crash seam.
#[cfg(all(feature = "at-rest", unix))]
pub(crate) fn seal(path: &Path, mut key: [u8; 32], seam: &Seam) -> io::Result<SealedLog> {
    let out = seal_keyed(path, &key, seam);
    key.fill(0);
    std::hint::black_box(&mut key);
    out
}

/// A refusal of the seal of `path`, of `kind`, saying `why`.
#[cfg(all(feature = "at-rest", unix))]
fn refused(path: &Path, kind: io::ErrorKind, why: &str) -> io::Error {
    io::Error::new(kind, format!("seal_plaintext: {}: {why}", path.display()))
}

/// Create `path` with the log's `perms`, write `bytes` and flush it.
#[cfg(all(feature = "at-rest", unix))]
fn write_flushed(path: &Path, perms: &std::fs::Permissions, bytes: &[u8]) -> io::Result<()> {
    let mut f = create_like(path, perms)?;
    f.write_all(bytes)?;
    flush_file(&f, path)
}

/// The sidecar at `path` whole, or `None` when there is none (never through a link).
#[cfg(all(feature = "at-rest", unix))]
fn read_sidecar(path: &Path, what: &str) -> io::Result<Option<Vec<u8>>> {
    use std::io::Read;
    let Some(mut f) = open_sidecar(path, u64::MAX, false, what)? else {
        return Ok(None);
    };
    let mut out = Vec::new();
    f.read_to_end(&mut out)?;
    Ok(Some(out))
}

/// Every frame's payload in `bytes`, in order, or `None` when they do not read whole.
#[cfg(all(feature = "at-rest", unix))]
fn payloads(bytes: &[u8]) -> Option<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    let mut pos = 0usize;
    while pos < bytes.len() {
        let rest = bytes.get(pos..)?;
        let Ok(Some(d)) = Frame::decode(rest) else {
            return None;
        };
        if d.consumed == 0 {
            return None;
        }
        pos = pos.checked_add(d.consumed)?;
        out.push(d.frame.payload);
    }
    Some(out)
}

/// `payload` framed, or `InvalidData` naming `what`.
#[cfg(all(feature = "at-rest", unix))]
fn framed(payload: Vec<u8>, what: &str) -> io::Result<Vec<u8>> {
    match Frame::new(payload).encode() {
        Ok(f) => Ok(f),
        Err(_) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("seal_plaintext: a sealed {what} frame exceeds the frame cap"),
        )),
    }
}

/// The plaintext sidecars a staged copy carries, read from the log at `path`.
#[cfg(all(feature = "at-rest", unix))]
struct Plain {
    log: Vec<u8>,
    base: Option<Vec<u8>>,
    state: Option<Vec<u8>>,
    held: Option<Vec<u8>>,
}

#[cfg(all(feature = "at-rest", unix))]
fn seal_keyed(path: &Path, key: &[u8; 32], seam: &Seam) -> io::Result<SealedLog> {
    match std::fs::symlink_metadata(path) {
        Ok(m) if m.is_file() => {}
        Ok(_) => {
            return Err(refused(
                path,
                io::ErrorKind::InvalidInput,
                "not a regular file",
            ))
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Err(refused(path, io::ErrorKind::NotFound, "no log here"));
        }
        Err(e) => return Err(e),
    }
    // A `.seal` binding beside it and no switch in flight: sealed already (or bound by a
    // keyed open once). Refused before any open: a keyless open of a sealed log refuses, and
    // refusing here reads nothing of it. With an earlier seal's marker beside it, its switch
    // is in flight, and the open below settles it first.
    let marker_at = beside(path, MARKER);
    let marked = present(&marker_at)?;
    if !marked && present(&seal_path(path))? {
        return Err(sealed_already(path, false));
    }
    // 1. THE PLAINTEXT LOG, under its lock from here to the end (its settle has run).
    let mut src = match BrokerLog::open_with(path, Durability::Strict) {
        Ok(log) => log,
        Err(e) => {
            // Its settle finished an earlier seal's switch, and then refused the sealed log as
            // every keyless open does: sealed already. (A broker serving it says so first.)
            if e.kind() != io::ErrorKind::AlreadyExists
                && !present(&marker_at)?
                && present(&seal_path(path))?
            {
                return Err(sealed_already(path, marked));
            }
            return Err(refused(
                path,
                e.kind(),
                &format!("it does not open as a plaintext log: {e}"),
            ));
        }
    };
    // Closed cleanly at once: every refusal from here on leaves a clean stop.
    src.close_clean()?;
    // A `.seal` beside a log the open read: sealed already all the same. (A keyless open
    // refuses a log a `.seal` sits beside, so this only backs that refusal up.)
    if present(&seal_path(path))? {
        return Err(sealed_already(path, marked));
    }
    if src.replica {
        return Err(refused(
            path,
            io::ErrorKind::Unsupported,
            "a replica's log is its leader's spine, and is not sealed here",
        ));
    }
    if present(&beside(path, ".hw"))? {
        return Err(refused(
            path,
            io::ErrorKind::Unsupported,
            "an anti-rollback watermark (`.hw`) sits beside it, which no plaintext log keeps",
        ));
    }
    #[cfg(not(feature = "retention"))]
    if present(&state_path(path))? || present(&beside(path, ".held"))? {
        return Err(refused(
            path,
            io::ErrorKind::Unsupported,
            "it has retention sidecars, which a build without `retention` cannot seal",
        ));
    }
    let (base, head) = (src.base, src.next);
    let perms = std::fs::metadata(path)?.permissions();
    let mut plain = read_plain(path, &src)?;
    // What the marker will pin of the plaintext log, taken before its bytes are let go.
    let pinned = pin(&plain);

    // 2. THE STAGED COPY.
    let staged = beside(path, STAGED);
    let seal_id = mint_seal_id(&staged, key);
    let kref = AtRestRef {
        key,
        seal_id: Some(seal_id),
    };
    // The payloads are what the read-back compares against; the bytes they came from are
    // let go (an offline seal of a large log holds as little twice as it can).
    let Some(frames) = payloads(&std::mem::take(&mut plain.log)) else {
        return Err(refused(
            path,
            io::ErrorKind::InvalidData,
            "its recovered frames do not read whole",
        ));
    };
    if frames.len() as u64 != head.0.saturating_sub(base.0) {
        return Err(refused(
            path,
            io::ErrorKind::InvalidData,
            "its frames are not one per retained record",
        ));
    }
    let mut sealed_log = Vec::new();
    let mut newest_at = 0usize;
    for (i, payload) in frames.iter().enumerate() {
        let at = base.0.saturating_add(i as u64);
        let sealed = astream_aead::seal(
            key,
            &record_bound_aad(seal_id, at),
            &seam.planted(Alter::Record, payload),
        );
        newest_at = sealed_log.len();
        sealed_log.extend_from_slice(&framed(sealed, "record")?);
    }
    write_flushed(&staged, &perms, &sealed_log)?;
    sync_parent_dir(&staged)?;
    seam.crash(Step::Staged)?;
    let sealed_len = sealed_log.len() as u64;
    let split_at = newest_at.min(sealed_log.len());
    let mut newest = Vec::new();
    if let Some(tail) = sealed_log.get(split_at..) {
        newest.extend_from_slice(tail);
    }
    drop(sealed_log);

    let mut mask = 0u8;
    write_seal(&staged, key, seal_id, Some(&perms))?;
    mask |= 1;
    if let Some(b) = &plain.base {
        write_flushed(&beside(&staged, ".base"), &perms, b)?;
        mask |= 2;
    }
    #[cfg(feature = "retention")]
    if let Some(s) = &plain.state {
        let Some(mut one) = payloads(s).filter(|p| p.len() == 1) else {
            return Err(refused(
                path,
                io::ErrorKind::InvalidData,
                "its `.state` is not one frame",
            ));
        };
        let raw = one.pop().unwrap_or_default();
        let sealed = seal_state_payload(Some(kref), seam.planted(Alter::State, &raw).to_vec());
        write_flushed(&state_path(&staged), &perms, &framed(sealed, "state")?)?;
        mask |= 4;
    }
    #[cfg(feature = "retention")]
    if let Some(h) = &plain.held {
        let Some(held) = payloads(h) else {
            return Err(refused(
                path,
                io::ErrorKind::InvalidData,
                "its `.held` frames do not read whole",
            ));
        };
        let mut out = Vec::with_capacity(h.len().saturating_add(held.len().saturating_mul(40)));
        for (i, p) in held.iter().enumerate() {
            let sealed = crate::held::seal(Some(kref), i as u64, &seam.planted(Alter::Held, p));
            out.extend_from_slice(&framed(sealed, "held")?);
        }
        write_flushed(&beside(&staged, ".held"), &perms, &out)?;
        mask |= 8;
    }
    #[cfg(not(feature = "retention"))]
    let _ = kref;
    let id = src.identity.closed(base.0, head.0, &newest);
    logid::write(&Dir::Os(staged.clone()), &id)?;
    mask |= 16;
    sync_parent_dir(&staged)?;
    seam.crash(Step::Sidecars)?;

    // 3. READ IT BACK, before anything of the plaintext log is touched.
    let mut ver = read_back(path, &src, &staged, key, seal_id, &plain, &frames)?;
    ver.close_clean()?;
    seam.crash(Step::Verified)?;

    // 4. THE MARKER: from here the switch goes forward, whoever finishes it, over the
    // plaintext log it pins.
    let marker = Marker { mask, ..pinned };
    write_marker(path, &marker, &perms)?;
    seam.crash(Step::Marker)?;

    // 5. THE SWITCH.
    complete(path, &marker, &mut |step| seam.crash(step))?;
    let sealed = SealedLog {
        identity: ver.identity(),
        base,
        head,
        bytes: sealed_len,
    };
    drop(ver);
    drop(src);
    Ok(sealed)
}

/// The plaintext log's bytes (read through its name, which its lock holds), every one of
/// them durable (its length is what its open recovered, which the marker pins), and its
/// sidecars.
#[cfg(all(feature = "at-rest", unix))]
fn read_plain(path: &Path, src: &BrokerLog) -> io::Result<Plain> {
    let log = std::fs::read(path)?;
    if log.len() as u64 != src.durable_len {
        return Err(refused(
            path,
            io::ErrorKind::InvalidData,
            "its length is not what its open recovered",
        ));
    }
    let base = match std::fs::read(base_path(path)) {
        Ok(b) => Some(b),
        Err(e) if e.kind() == io::ErrorKind::NotFound => None,
        Err(e) => return Err(e),
    };
    Ok(Plain {
        log,
        base,
        state: read_sidecar(&state_path(path), "state sidecar")?,
        held: read_sidecar(&beside(path, ".held"), "held store")?,
    })
}

/// What the switch's marker pins of the plaintext log `plain` (its mask still to be set):
/// its length, its newest frame, and its [`PINNED`] sidecars.
#[cfg(all(feature = "at-rest", unix))]
fn pin(plain: &Plain) -> Marker {
    let newest_at = logid::last_frame_start(&plain.log).unwrap_or(plain.log.len());
    let print = |s: &Option<Vec<u8>>| s.as_deref().map_or([0; 16], sidecar_print);
    Marker {
        mask: 0,
        len: plain.log.len() as u64,
        newest_at: newest_at as u64,
        newest: frame_print(plain.log.get(newest_at..).unwrap_or_default()),
        sidecars: [print(&plain.base), print(&plain.state), print(&plain.held)],
    }
}

/// A refusal of the seal of `path` as sealed already (`InvalidInput`): a `.seal` binding sits
/// beside it. `finished`: an earlier seal's switch, a crash having stopped it past its
/// marker, was finished by this seal's open.
#[cfg(all(feature = "at-rest", unix))]
fn sealed_already(path: &Path, finished: bool) -> io::Error {
    let why = if finished {
        "a `.seal` binding sits beside it: it is sealed already, an earlier seal's switch, \
         which a crash stopped past its marker, having been finished by this seal's open (a \
         log sealed at rest is not sealed again)"
    } else {
        "a `.seal` binding sits beside it: it is sealed already, or a keyed open bound it \
         once (a log sealed at rest is not sealed again)"
    };
    refused(path, io::ErrorKind::InvalidInput, why)
}

/// Durably write the switch's marker `m` beside `path`: tmp, flush, rename, directory flush.
#[cfg(all(feature = "at-rest", unix))]
fn write_marker(path: &Path, m: &Marker, perms: &std::fs::Permissions) -> io::Result<()> {
    let marker = beside(path, MARKER);
    let tmp = beside(path, &format!("{MARKER}.tmp"));
    write_flushed(&tmp, perms, &framed(m.encode(), "marker")?)?;
    rename_path(&tmp, &marker)?;
    sync_parent_dir(&marker)
}

/// THE READ-BACK: the staged copy at `staged`, opened with the key and bound, against the
/// plaintext log `src` it was sealed from. Every check is a refusal naming what differs.
#[cfg(all(feature = "at-rest", unix))]
#[allow(clippy::too_many_arguments)]
fn read_back(
    path: &Path,
    src: &BrokerLog,
    staged: &Path,
    key: &[u8; 32],
    seal_id: [u8; 16],
    plain: &Plain,
    frames: &[Vec<u8>],
) -> io::Result<BrokerLog> {
    let differs = |what: &str| {
        refused(
            path,
            io::ErrorKind::InvalidData,
            &format!(
                "the sealed copy does not read back as the log ({what} differs); the plaintext \
                 log is untouched"
            ),
        )
    };
    let mut opts = OpenOptions::new(Durability::Strict);
    opts.at_rest_key = Some(*key);
    opts.require_bound_at_rest = true;
    let ver = match BrokerLog::open_opts(staged, opts, BrokerLog::prepare_nothing) {
        Ok(v) => v,
        Err(e) => {
            return Err(refused(
                path,
                e.kind(),
                &format!(
                    "the sealed copy does not read back as the log (it does not open: {e}); the \
                     plaintext log is untouched"
                ),
            ))
        }
    };
    if ver.at_rest_seal_id() != Some(seal_id) {
        return Err(differs("the `.seal` binding"));
    }
    if (ver.base, ver.next) != (src.base, src.next) {
        return Err(differs("the base or the head"));
    }
    // A log that never held a record takes a fresh id at every open (`logid.rs`): nobody
    // can hold an offset into it, so there is no identity to keep.
    if src.next.0 > 0 && (ver.identity() != src.identity() || ver.lineage() != src.lineage()) {
        return Err(differs("the identity"));
    }
    if ver.tier.len() != src.tier.len()
        || (0..src.tier.len()).any(|i| match (ver.record_arc(i), src.record_arc(i)) {
            (Some(a), Some(b)) => *a != *b,
            _ => true,
        })
    {
        return Err(differs("a record"));
    }
    if (0..src.tier.len()).any(|i| ver.tier.bt(i) != src.tier.bt(i)) {
        return Err(differs("a broker time"));
    }
    if ver.carried_wills != src.carried_wills
        || ver.carried_last != src.carried_last
        || ver.carried_last_bt != src.carried_last_bt
        || ver.carried_charges != src.carried_charges
        || ver.uncarried_cut_tainted != src.uncarried_cut_tainted
        || ver.bind != src.bind
        || ver.group_commits != src.group_commits
        || ver.dedup != src.dedup
        || ver.last != src.last
    {
        return Err(differs("the carried state"));
    }
    #[cfg(feature = "retention")]
    {
        let (a, b) = (&ver.hold, &src.hold);
        let same_entries = a.entries.len() == b.entries.len()
            && a.entries
                .iter()
                .zip(&b.entries)
                .all(|((ka, ha), (kb, hb))| {
                    ka == kb && *ha.rec == *hb.rec && ha.at_ms == hb.at_ms && ha.bt_ms == hb.bt_ms
                });
        if !same_entries
            || a.rules != b.rules
            || a.floors != b.floors
            || a.spill != b.spill
            || a.floor_max != b.floor_max
            || a.since != b.since
            || a.stamps != b.stamps
        {
            return Err(differs("the held store"));
        }
    }
    // Byte for byte: every staged frame opens under the key to the payload it was sealed
    // from, read back from the files, not from what was handed to the writes.
    let kref = Some(AtRestRef {
        key,
        seal_id: Some(seal_id),
    });
    let Some(back) = payloads(&std::fs::read(staged)?) else {
        return Err(differs("a sealed frame"));
    };
    if back.len() != frames.len() {
        return Err(differs("the frame count"));
    }
    for (i, (sealed, want)) in back.into_iter().zip(frames).enumerate() {
        let at = src.base.0.saturating_add(i as u64);
        if open_disk_payload(kref, at, sealed).as_ref() != Some(want) {
            return Err(differs(&format!("the record at offset {at}")));
        }
    }
    if plain.base.as_deref() != read_sidecar(&base_path(staged), "base sidecar")?.as_deref() {
        return Err(differs("`.base`"));
    }
    #[cfg(feature = "retention")]
    {
        let state = read_sidecar(&state_path(staged), "state sidecar")?;
        match (&plain.state, state) {
            (None, None) => {}
            (Some(p), Some(s)) => {
                let (Some(p), Some(s)) = (payloads(p), payloads(&s)) else {
                    return Err(differs("`.state`"));
                };
                let opened: Vec<Option<Vec<u8>>> =
                    s.into_iter().map(|f| open_state_payload(kref, f)).collect();
                let want: Vec<Option<Vec<u8>>> = p.into_iter().map(Some).collect();
                if opened != want {
                    return Err(differs("`.state`"));
                }
            }
            _ => return Err(differs("`.state`")),
        }
        let held = read_sidecar(&beside(staged, ".held"), "held store")?;
        match (&plain.held, held) {
            (None, None) => {}
            (Some(p), Some(h)) => {
                let (Some(p), Some(h)) = (payloads(p), payloads(&h)) else {
                    return Err(differs("`.held`"));
                };
                if p.len() != h.len()
                    || h.into_iter().zip(&p).enumerate().any(|(i, (f, want))| {
                        crate::held::unseal(kref, i as u64, f).as_ref() != Some(want)
                    })
                {
                    return Err(differs("`.held`"));
                }
            }
            _ => return Err(differs("`.held`")),
        }
    }
    Ok(ver)
}

#[cfg(all(test, unix, feature = "at-rest", feature = "retention"))]
#[path = "offline_seal_tests.rs"]
mod tests;
