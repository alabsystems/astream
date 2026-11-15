// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! CRASH-SAFE, STREAMING COMPACTION: the retention rewrite of the durable log, done in an
//! order an open can recover from at any point, copied in bounded chunks, and split so
//! the bulk of the copy runs with no lock held (`REQUIREMENTS-fabric-operations` R4,
//! "Design (2026-10-19)").
//!
//! # The protocol
//!
//! A compaction to `min` keeps the records at offsets `min..` and drops the ones below.
//! Beside the log at `<log>` it writes:
//!
//! | file | holds | written by |
//! |---|---|---|
//! | `<log>.kept` | the kept suffix, frame bytes as stored | the unlocked copy and its flush, then the delta and its flush |
//! | `<log>.state.next` | the carried state at the new base (a carrying compaction) | tmp + flush + rename |
//! | `<log>.compact` | the INTENT: both bases, the old first frame's identity and the new one's | tmp + flush + rename |
//!
//! All three hold the log's records or bytes of them, so each is created with the log's
//! own permissions, set exactly past the umask (`create_like`).
//!
//! Its durable steps, in order, each a crash point of the [`Seam`]:
//!
//! 0. [`Step::Held`]: a log the retention rules retain (`retention.rs`) has its held
//!    store's frames for this compaction appended to `<log>.held` and flushed, each naming
//!    the new base, before anything else is written (`held.rs`). An open that finds them
//!    while the log's base is still the old one cuts them away: the records they carry are
//!    still in the log.
//! 1. [`Step::Copy`]: `<log>.kept` holds every byte of the log from the cut, flushed.
//! 2. [`Step::State`]: `<log>.state.next` is durable (a carrying compaction only).
//! 3. [`Step::Intent`]: `<log>.compact` is durable.
//! 4. [`Step::Rename`]: `<log>.kept` is renamed over `<log>`, and the directory flushed.
//! 5. [`Step::StateInstalled`]: `<log>.state.next` is renamed over `<log>.state`.
//! 6. [`Step::Base`]: `<log>.base` holds the new base.
//! 7. [`Step::Watermark`]: the anti-rollback watermark names the new first frame and base
//!    (an anti-rollback log only).
//! 8. [`Step::IntentRemoved`]: `<log>.compact` is gone.
//!
//! The kept copy is exclusively locked before step 4 and its exact descriptor
//! becomes the live log before any fallible post-rename work. A failed switch
//! therefore keeps the replacement owned until the poisoned log is dropped.
//! Openers recheck their locked descriptor against the current pathname before
//! reading sidecars, refusing an old inode detached while they acquired its lock.
//!
//! # Recovery
//!
//! An open ([`recover`]) that finds an intent compares its two identities with the log's
//! own first frame. The NEW one: the rename happened, so the open finishes steps 5 to 8,
//! each idempotent. The OLD one: it did not, so the open discards the intent, the copy
//! and the staged state, since the log, its base, its state and its watermark were never
//! touched. Neither: the log is not the one the intent was written for, and the open
//! refuses, touching nothing. With no intent, a copy or a staged state that a compaction
//! left when it died before writing its intent is removed. Before this protocol a crash
//! between the rename and the base write left a log whose first record disagreed with
//! its base, which every open refused, recoverable only from a backup.
//!
//! # Off the ack path
//!
//! Durable bytes are append-only: below the durable length nothing rewrites the file but a
//! compaction, and compactions are serialized. So [`KeptCopy::run`] copies
//! `[cut, the durable length when the compaction began)` and FLUSHES it with no lock held,
//! while the broker's writer commits batches, and the locked finish copies and flushes only
//! what was appended since ([`KeptCopy::extend_to`], [`KeptCopy::flush`]) before it switches
//! the files. The finish's other durable writes (the staged state, the intent, the switch)
//! are each a few bytes and a flush.
//!
//! # Streaming
//!
//! The copy reads through one buffer of [`COMPACT_CHUNK`] bytes, plus the two frames it
//! must hold whole for their identities (the log's first and the kept suffix's first):
//! never the log.

use crate::logid;
use crate::storage::read_exact_at;
use crate::store::{
    create_like, create_like_read_write, flush_file, log_identity, open_regular_sidecar, read_base,
    read_state_base, remove_file_path, rename_path, state_path, sync_parent_dir, write_base,
    AtRestRef,
};
use astream_wire::frame::decode_frame_header_bytes;
use astream_wire::{Frame, HEADER_SIZE, MAX_PAYLOAD_LEN};
use std::fs::{File, Permissions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
#[cfg(test)]
use std::sync::{mpsc, Mutex};

/// The copy's buffer: the most of the log it holds at once, beside the one frame it reads
/// whole for an identity.
pub(crate) const COMPACT_CHUNK: usize = 1 << 20;

/// The largest intent file an open reads: an intent is under a hundred bytes, sealed under
/// two hundred. Anything larger is no intent (an older build's copy of a log, left at this
/// name when it died mid-compaction, is the expected case).
const INTENT_FILE_CAP: u64 = 4096;

/// The intent's own format: magic and version.
const INTENT_MAGIC: &[u8; 5] = b"ASCI\x01";

/// Domain-separating AAD for sealing `<log>.compact` under the log's at-rest key.
#[cfg(feature = "at-rest")]
const INTENT_AAD: &[u8] = b"astream-compact-intent-v1";
#[cfg(feature = "at-rest")]
const INTENT_BOUND_PREFIX: &[u8; 25] = b"astream-compact-intent-v2";

#[cfg(feature = "at-rest")]
const fn intent_bound_aad(id: [u8; 16]) -> [u8; 41] {
    let p = INTENT_BOUND_PREFIX;
    [
        p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11], p[12], p[13],
        p[14], p[15], p[16], p[17], p[18], p[19], p[20], p[21], p[22], p[23], p[24], id[0], id[1],
        id[2], id[3], id[4], id[5], id[6], id[7], id[8], id[9], id[10], id[11], id[12], id[13],
        id[14], id[15],
    ]
}

/// A durable step of the compaction, in the order it takes them: where the seam can crash
/// it (see the module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Step {
    Held,
    Copy,
    State,
    Intent,
    Rename,
    StateInstalled,
    Base,
    Watermark,
    IntentRemoved,
}

/// `<log>` with `ext` appended to its name.
fn beside(log: &Path, ext: &str) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string().push(ext);
    p
}

/// The intent, `<log>.compact`.
pub(crate) fn intent_path(log: &Path) -> PathBuf {
    beside(log, ".compact")
}

/// The kept-suffix copy, `<log>.kept`.
pub(crate) fn kept_path(log: &Path) -> PathBuf {
    beside(log, ".kept")
}

/// The carried state staged for the new base, `<log>.state.next`.
pub(crate) fn staged_state_path(log: &Path) -> PathBuf {
    beside(log, ".state.next")
}

/// A stored frame's identity: its fingerprint over the bytes as stored, and the
/// anti-rollback id it gives a log it starts ([`log_identity`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FrameId {
    pub(crate) fp: [u8; 16],
    pub(crate) tag: [u8; 16],
}

impl FrameId {
    pub(crate) fn of(frame: &[u8]) -> FrameId {
        FrameId {
            fp: logid::frame_fingerprint(frame),
            tag: log_identity(frame),
        }
    }
}

/// What a compaction is about to do, durable before the rename (`<log>.compact`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Intent {
    /// The base before the compaction.
    pub(crate) old_base: u64,
    /// The base after it.
    pub(crate) new_base: u64,
    /// The log's first frame before it.
    pub(crate) old: FrameId,
    /// The kept suffix's first frame (`None` when the compaction keeps no record).
    pub(crate) new: Option<FrameId>,
    /// Whether a staged `<log>.state.next` belongs to this compaction.
    pub(crate) carries_state: bool,
}

/// The intent's encoded length: magic, two bases, the old identity, a flag and the new
/// identity, a flag.
const INTENT_LEN: usize = 5 + 8 + 8 + 32 + 1 + 32 + 1;

fn put_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn take<'a>(b: &'a [u8], pos: &mut usize, n: usize) -> Option<&'a [u8]> {
    let end = pos.checked_add(n)?;
    let s = b.get(*pos..end)?;
    *pos = end;
    Some(s)
}

fn take_u64(b: &[u8], pos: &mut usize) -> Option<u64> {
    let s = take(b, pos, 8)?;
    let (chunk, _) = s.split_first_chunk::<8>()?;
    Some(u64::from_le_bytes(*chunk))
}

fn take_16(b: &[u8], pos: &mut usize) -> Option<[u8; 16]> {
    let s = take(b, pos, 16)?;
    let (chunk, _) = s.split_first_chunk::<16>()?;
    Some(*chunk)
}

fn take_flag(b: &[u8], pos: &mut usize) -> Option<bool> {
    match take(b, pos, 1)? {
        [0] => Some(false),
        [1] => Some(true),
        _ => None,
    }
}

impl Intent {
    pub(crate) fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(INTENT_LEN);
        out.extend_from_slice(INTENT_MAGIC);
        put_u64(&mut out, self.old_base);
        put_u64(&mut out, self.new_base);
        out.extend_from_slice(&self.old.fp);
        out.extend_from_slice(&self.old.tag);
        let new = match self.new {
            Some(n) => n,
            None => FrameId {
                fp: [0; 16],
                tag: [0; 16],
            },
        };
        out.push(u8::from(self.new.is_some()));
        out.extend_from_slice(&new.fp);
        out.extend_from_slice(&new.tag);
        out.push(u8::from(self.carries_state));
        out
    }

    /// Decode an intent; `None` on anything that is not exactly one.
    pub(crate) fn decode(b: &[u8]) -> Option<Intent> {
        if b.len() != INTENT_LEN || b.get(..INTENT_MAGIC.len())? != INTENT_MAGIC {
            return None;
        }
        let mut pos = INTENT_MAGIC.len();
        let old_base = take_u64(b, &mut pos)?;
        let new_base = take_u64(b, &mut pos)?;
        let old = FrameId {
            fp: take_16(b, &mut pos)?,
            tag: take_16(b, &mut pos)?,
        };
        let has_new = take_flag(b, &mut pos)?;
        let new = FrameId {
            fp: take_16(b, &mut pos)?,
            tag: take_16(b, &mut pos)?,
        };
        let carries_state = take_flag(b, &mut pos)?;
        if new_base <= old_base {
            return None;
        }
        Some(Intent {
            old_base,
            new_base,
            old,
            new: if has_new { Some(new) } else { None },
            carries_state,
        })
    }
}

#[cfg(feature = "at-rest")]
fn seal(key: Option<AtRestRef<'_>>, payload: Vec<u8>) -> Vec<u8> {
    match key {
        Some(AtRestRef {
            key: k,
            seal_id: Some(id),
        }) => {
            let aad = intent_bound_aad(id);
            astream_aead::seal(k, &aad, &payload)
        }
        Some(AtRestRef {
            key: k,
            seal_id: None,
        }) => astream_aead::seal(k, INTENT_AAD, &payload),
        None => payload,
    }
}
#[cfg(not(feature = "at-rest"))]
fn seal(_key: Option<AtRestRef<'_>>, payload: Vec<u8>) -> Vec<u8> {
    payload
}

#[cfg(feature = "at-rest")]
fn unseal(key: Option<AtRestRef<'_>>, payload: Vec<u8>) -> Option<Vec<u8>> {
    match key {
        Some(AtRestRef {
            key: k,
            seal_id: Some(id),
        }) => {
            let aad = intent_bound_aad(id);
            match astream_aead::open(k, &aad, &payload) {
                Ok(p) => Some(p),
                Err(_) => None,
            }
        }
        Some(AtRestRef {
            key: k,
            seal_id: None,
        }) => match astream_aead::open(k, INTENT_AAD, &payload) {
            Ok(p) => Some(p),
            Err(_) => None,
        },
        None => Some(payload),
    }
}
#[cfg(not(feature = "at-rest"))]
fn unseal(_key: Option<AtRestRef<'_>>, payload: Vec<u8>) -> Option<Vec<u8>> {
    Some(payload)
}

/// Durably write `intent` at `<log>.compact`: tmp, full flush, rename, directory flush,
/// never following a link planted at either name. Sealed under the at-rest key when the
/// log has one, so no one without it can make an open re-identify the log's watermark. On
/// a plaintext log its identities are bytes of two records, so it is created with
/// `perms`, the log's own.
pub(crate) fn write_intent(
    log: &Path,
    key: Option<AtRestRef<'_>>,
    intent: &Intent,
    perms: &Permissions,
) -> io::Result<()> {
    let Ok(framed) = Frame::new(seal(key, intent.encode())).encode() else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "retention: compaction intent too large",
        ));
    };
    let path = intent_path(log);
    let tmp = beside(&path, ".tmp");
    {
        let mut f = create_like(&tmp, perms)?;
        f.write_all(&framed)?;
        flush_file(&f, &tmp)?;
    }
    rename_path(&tmp, &path)?;
    sync_parent_dir(&path)
}

/// What an open finds at `<log>.compact`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Found {
    /// No file.
    Absent,
    /// A file that is no intent this build wrote: not a regular file, too large, not one
    /// frame, failing to authenticate, or another format. Nothing acts on it.
    Unreadable(&'static str),
    /// An intent.
    Intent(Intent),
}

/// Read `<log>.compact` through a bounded, no-follow regular-file handle.
/// Absence is only the initial lookup; later admission and read failures refuse.
pub(crate) fn read_intent(log: &Path, key: Option<AtRestRef<'_>>) -> io::Result<Found> {
    let path = intent_path(log);
    let meta = match std::fs::symlink_metadata(&path) {
        Ok(m) => m,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Found::Absent),
        Err(e) => return Err(e),
    };
    if !meta.is_file() {
        return Ok(Found::Unreadable("not a regular file"));
    }
    if meta.len() > INTENT_FILE_CAP {
        return Ok(Found::Unreadable("larger than any intent"));
    }
    let file = open_regular_sidecar(&path, INTENT_FILE_CAP)?;
    let mut bytes = Vec::new();
    file.take(INTENT_FILE_CAP.saturating_add(1))
        .read_to_end(&mut bytes)?;
    Ok(decode_intent_file(&bytes, key))
}

/// Decode an intent file's bytes: exactly one frame, authenticated when keyed.
pub(crate) fn decode_intent_file(bytes: &[u8], key: Option<AtRestRef<'_>>) -> Found {
    let payload = match Frame::decode(bytes) {
        Ok(Some(d)) if d.consumed == bytes.len() => d.frame.payload,
        _ => return Found::Unreadable("not one frame"),
    };
    let Some(plain) = unseal(key, payload) else {
        return Found::Unreadable("does not authenticate");
    };
    match Intent::decode(&plain) {
        Some(intent) => Found::Intent(intent),
        None => Found::Unreadable("not an intent"),
    }
}

/// Remove `<log>.compact` and make the removal durable.
pub(crate) fn remove_intent(log: &Path) -> io::Result<()> {
    let path = intent_path(log);
    match remove_file_path(&path) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    sync_parent_dir(&path)
}

/// Remove what a compaction that never reached its intent can leave: the copy, the staged
/// state, and the tmp files the intent and the staged state are written through.
/// Best-effort: a file left here is replaced by the next compaction's own.
pub(crate) fn clear_leftovers(log: &Path) {
    let intent_tmp = beside(&intent_path(log), ".tmp");
    let staged_tmp = beside(&staged_state_path(log), ".tmp");
    for p in [
        kept_path(log),
        staged_state_path(log),
        intent_tmp,
        staged_tmp,
        crate::held::held_tmp_path(log),
    ] {
        let _ = remove_file_path(&p);
    }
}

/// A log this open CREATED carries none of a deleted predecessor's compaction, nor its
/// held store.
pub(crate) fn clear_created(log: &Path) {
    let _ = remove_file_path(&intent_path(log));
    let _ = remove_file_path(&crate::held::held_path(log));
    clear_leftovers(log);
}

/// How an open reads an intent against the log's first frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// The log starts with the kept suffix: the rename happened; finish the rest.
    Finish,
    /// The log starts with its old first frame: the rename did not happen; discard.
    Discard,
    /// The log starts with neither: refuse, touching nothing.
    Neither,
}

/// The pure judgement [`recover`] acts on. `first` is the log's first frame as the open
/// found it (`None` for an empty log).
pub(crate) fn judge(intent: &Intent, first: Option<FrameId>) -> Verdict {
    match (first, intent.new) {
        (None, None) => Verdict::Finish,
        (Some(f), Some(n)) if f == n => Verdict::Finish,
        (Some(f), _) if f == intent.old => Verdict::Discard,
        _ => Verdict::Neither,
    }
}

/// THE OPEN'S RECOVERY of a compaction a crash interrupted: run before the base and the
/// carried state are read, on `first`, the log's first stored frame as the open found it
/// ([`logid::first_frame`]; `None` when the log holds none). See the
/// module docs. `anti_rollback` says the open verifies the watermark. A finished compaction
/// re-identifies a watermark beside the log whenever the open holds the key, verified or
/// not ([`reidentify`]).
pub(crate) fn recover(
    log: &Path,
    first: Option<&[u8]>,
    key: Option<AtRestRef<'_>>,
    anti_rollback: bool,
) -> io::Result<()> {
    let intent = match read_intent(log, key)? {
        Found::Absent => {
            clear_leftovers(log);
            return Ok(());
        }
        Found::Unreadable(why) => {
            eprintln!(
                "astream-broker: {}: ignoring {}: {why}; the log is judged by its base as it \
                 stands",
                log.display(),
                intent_path(log).display()
            );
            return Ok(());
        }
        Found::Intent(intent) => intent,
    };
    let first = match first {
        Some(frame) => Some(FrameId::of(frame)),
        None => None,
    };
    match judge(&intent, first) {
        Verdict::Finish => finish(log, key, &intent, anti_rollback),
        Verdict::Discard => {
            remove_intent(log)?;
            clear_leftovers(log);
            eprintln!(
                "astream-broker: {}: discarded the compaction to base {} that a crash \
                 interrupted before it replaced the log; the log is as it was",
                log.display(),
                intent.new_base
            );
            Ok(())
        }
        Verdict::Neither => Err(neither(log, &intent)),
    }
}

/// WHAT [`recover`] WOULD DO, judged without doing it, for a check that writes nothing
/// (`BrokerLog::check_open`): `Some(new_base)` when it would finish a compaction whose rename
/// landed, `None` when there is none to finish (no intent, one it ignores as unreadable, or
/// one it discards, none of which changes the log, its base or its carried state), and the
/// refusal it would make: of a log that starts with neither frame its intent names, and the
/// finish's own ([`ready_to_finish`]), so the open's finish can fail only by a write.
pub(crate) fn pending(
    log: &Path,
    first: Option<&[u8]>,
    key: Option<AtRestRef<'_>>,
) -> io::Result<Option<u64>> {
    let Found::Intent(intent) = read_intent(log, key)? else {
        return Ok(None);
    };
    let first = match first {
        Some(frame) => Some(FrameId::of(frame)),
        None => None,
    };
    match judge(&intent, first) {
        Verdict::Finish => {
            ready_to_finish(log, key, &intent)?;
            Ok(Some(intent.new_base))
        }
        Verdict::Discard => Ok(None),
        Verdict::Neither => Err(neither(log, &intent)),
    }
}

/// The refusal of a log whose first frame is neither one `intent` names.
fn neither(log: &Path, intent: &Intent) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "{}: {} names a compaction from base {} to base {}, but the log's first frame is \
             neither the one it began with nor the one it kept; refusing to open, nothing \
             touched",
            log.display(),
            intent_path(log).display(),
            intent.old_base,
            intent.new_base
        ),
    )
}

/// What [`finish`] reads before it writes, and its refusals, which change nothing: the base
/// sidecar must read the compaction's old base or its new one, and a compaction that carried
/// state must find its staged state, or a state already at the new base. `Ok(true)` when the
/// staged state is there to install.
fn ready_to_finish(log: &Path, key: Option<AtRestRef<'_>>, intent: &Intent) -> io::Result<bool> {
    let base = read_base(log)?.0;
    if base != intent.old_base && base != intent.new_base {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{}: the base sidecar reads {base}, neither the {} nor the {} of the \
                 compaction {} names; refusing to open, nothing touched",
                log.display(),
                intent.old_base,
                intent.new_base,
                intent_path(log).display()
            ),
        ));
    }
    if !intent.carries_state {
        return Ok(false);
    }
    let staged = staged_state_path(log);
    match std::fs::symlink_metadata(&staged) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            if read_state_base(log, key)? != Some(intent.new_base) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{}: the compaction to base {} carried state, and neither {} nor a \
                         state at that base is here; refusing to open, nothing touched",
                        log.display(),
                        intent.new_base,
                        staged.display()
                    ),
                ));
            }
            Ok(false)
        }
        Err(e) => Err(e),
    }
}

/// Steps 5 to 8 for a compaction whose rename landed: each is idempotent, so a crash here
/// is recovered the same way by the next open.
fn finish(
    log: &Path,
    key: Option<AtRestRef<'_>>,
    intent: &Intent,
    anti_rollback: bool,
) -> io::Result<()> {
    if ready_to_finish(log, key, intent)? {
        let state = state_path(log);
        rename_path(&staged_state_path(log), &state)?;
        sync_parent_dir(&state)?;
    }
    write_base(log, intent.new_base)?;
    reidentify(log, key, intent, anti_rollback)?;
    remove_intent(log)?;
    clear_leftovers(log);
    eprintln!(
        "astream-broker: {}: finished the compaction to base {} that a crash interrupted",
        log.display(),
        intent.new_base
    );
    Ok(())
}

/// Step 7, at an open's recovery and at a compaction by a keyed handle that does not
/// verify: an authenticated watermark beside the log that names the log's old first frame
/// (or already its new one) is moved to the new first frame and base, its head kept; `true`
/// when it was written. One that names neither, or a base above the new one, is left for a
/// verified open's own check to refuse.
///
/// It needs the key, never the verified flag: a watermark is sealed under the log's at-rest
/// key, and so is the intent that asks for this, so no one without the key can make it
/// happen. Re-identified only under a verified open, a watermark would be left naming the
/// old first frame by a keyed open that does not verify (an operator's inspection, or a
/// broker opened by the unverified constructor) once it finished the compaction and removed
/// the intent, the one record of it, and every verified open after it would refuse the
/// log. `verified` says the open verifies the watermark: then a watermark that does not
/// authenticate refuses here; otherwise it is left for a verified open to refuse.
#[cfg(feature = "anti-rollback")]
pub(crate) fn reidentify(
    log: &Path,
    key: Option<AtRestRef<'_>>,
    intent: &Intent,
    verified: bool,
) -> io::Result<bool> {
    let Some(key) = key else {
        return Ok(false);
    };
    let hw = crate::store::watermark_path(log);
    let (id, base, head) = match crate::store::read_watermark(&hw, key) {
        Ok(Some(w)) => w,
        Ok(None) => return Ok(false),
        Err(e) if verified => return Err(e),
        Err(_) => return Ok(false),
    };
    let new_tag = match intent.new {
        Some(n) => n.tag,
        None => [0u8; 16],
    };
    let ours = id == intent.old.tag || id == new_tag;
    if ours && base <= intent.new_base && (id, base) != (new_tag, intent.new_base) {
        crate::store::write_watermark(&hw, key, &new_tag, intent.new_base, head)?;
        return Ok(true);
    }
    Ok(false)
}

#[cfg(not(feature = "anti-rollback"))]
pub(crate) fn reidentify(
    _log: &Path,
    _key: Option<AtRestRef<'_>>,
    _intent: &Intent,
    _verified: bool,
) -> io::Result<bool> {
    Ok(false)
}

/// THE COMPACTION'S I/O SEAM. Production arms nothing, and every method is then the call
/// it wraps or nothing. Under `cfg(test)` it CRASHES the compaction after a durable
/// [`Step`] (it stops dead there, cleaning nothing up, the log poisoned: what the files
/// hold is what the next open recovers), sets the copy's chunk, meters every read the
/// copy makes, and can hold the unlocked copy at its start or a durable step.
#[derive(Clone, Default)]
pub(crate) struct Seam {
    #[cfg(test)]
    pub(crate) crash_after: Option<Step>,
    #[cfg(test)]
    pub(crate) chunk: Option<usize>,
    #[cfg(test)]
    pub(crate) meter: Option<Arc<Meter>>,
    #[cfg(test)]
    pub(crate) gate: Option<Gate>,
    #[cfg(test)]
    pub(crate) step_gate: Option<(Step, Gate)>,
}

impl Seam {
    /// The injected crash after `step`, if armed there.
    #[cfg(test)]
    pub(crate) fn crash(&self, step: Step) -> io::Result<()> {
        if let Some((at, gate)) = &self.step_gate {
            if *at == step {
                gate.hold();
            }
        }
        if self.crash_after == Some(step) {
            return Err(io::Error::other(format!("injected crash after {step:?}")));
        }
        Ok(())
    }
    #[cfg(not(test))]
    pub(crate) const fn crash(&self, _step: Step) -> io::Result<()> {
        Ok(())
    }

    /// The copy's chunk (at least one byte).
    #[cfg(test)]
    fn chunk(&self) -> usize {
        match self.chunk {
            Some(c) => c.max(1),
            None => COMPACT_CHUNK,
        }
    }
    #[cfg(not(test))]
    const fn chunk(&self) -> usize {
        COMPACT_CHUNK
    }

    /// A read of `n` bytes into one buffer.
    #[cfg(test)]
    fn read(&self, n: usize) {
        if let Some(m) = &self.meter {
            m.peak.fetch_max(n, std::sync::atomic::Ordering::Relaxed);
            m.reads.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }
    #[cfg(not(test))]
    const fn read(&self, _n: usize) {}

    /// A flush of the copy that made `n` more of its bytes durable.
    #[cfg(test)]
    fn flushed(&self, n: u64) {
        if let Some(m) = &self.meter {
            m.flushes
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .push(n);
        }
    }
    #[cfg(not(test))]
    const fn flushed(&self, _n: u64) {}

    /// The unlocked copy is starting: a test's gate holds it here.
    #[cfg(test)]
    fn copy_starts(&self) {
        if let Some(g) = &self.gate {
            let _ = g.reached.send(());
            let resume = g
                .resume
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let _ = resume.recv();
        }
    }
    #[cfg(not(test))]
    const fn copy_starts(&self) {}
}

/// The seam's meter: the largest single read the copy made and how many there were, and
/// how many bytes each of its flushes made durable, in order.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct Meter {
    pub(crate) peak: std::sync::atomic::AtomicUsize,
    pub(crate) reads: std::sync::atomic::AtomicUsize,
    pub(crate) flushes: Mutex<Vec<u64>>,
}

/// The seam's hold on the unlocked copy ([`gate`]).
#[cfg(test)]
#[derive(Clone)]
pub(crate) struct Gate {
    reached: mpsc::Sender<()>,
    resume: Arc<Mutex<mpsc::Receiver<()>>>,
}

/// A test's end of a [`Gate`].
#[cfg(test)]
pub(crate) struct GateHandle {
    reached: mpsc::Receiver<()>,
    resume: mpsc::Sender<()>,
}

#[cfg(test)]
impl GateHandle {
    /// Wait for the copy to reach the gate: a one-minute HANG DETECTOR, never a budget.
    pub(crate) fn wait(&self) -> bool {
        self.reached
            .recv_timeout(std::time::Duration::from_secs(60))
            .is_ok()
    }

    /// Let the copy go on.
    pub(crate) fn resume(&self) {
        let _ = self.resume.send(());
    }
}

#[cfg(test)]
impl Gate {
    fn hold(&self) {
        let _ = self.reached.send(());
        let _ = self
            .resume
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .recv();
    }
}

/// A gate for the seam, and the test's handle on it.
#[cfg(test)]
pub(crate) fn gate() -> (Gate, GateHandle) {
    let (reached_tx, reached_rx) = mpsc::channel();
    let (resume_tx, resume_rx) = mpsc::channel();
    (
        Gate {
            reached: reached_tx,
            resume: Arc::new(Mutex::new(resume_rx)),
        },
        GateHandle {
            reached: reached_rx,
            resume: resume_tx,
        },
    )
}

fn cut_error() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "retention: could not locate the cut point in the durable log",
    )
}

/// THE KEPT-SUFFIX COPY: `<log>.kept`, filled in bounded chunks by POSITIONAL reads
/// through the log's own descriptor, shared (an `Arc`, as the flush handles share it),
/// never a second open of its path: on Windows the open's whole-file exclusive lock
/// (`LockFileEx` through that descriptor, `lock_exclusive`) denies reads through any other
/// handle of the file, this process's included, so a copy read through one would fail every
/// compaction there. It borrows nothing of the log, so the broker runs [`run`](Self::run)
/// with no lock held while the writer appends: every append is written by position at the
/// log's end (`storage::write_all_at`), so a read that moves the file cursor, as Windows'
/// `seek_read` does, moves nothing an append depends on.
pub(crate) struct KeptCopy {
    /// The log's own descriptor at the begin (the same inode: it is replaced only by a
    /// compaction, and this is the one).
    src: Arc<File>,
    /// `<log>.kept`.
    dst: File,
    kept: PathBuf,
    /// How many records the compaction drops: frames to skip from the file's start.
    drop_count: u64,
    /// The durable length when the compaction began: what [`run`](Self::run) copies to.
    begin_len: u64,
    /// The byte offset of the first kept frame, once the walk found it.
    cut: Option<u64>,
    /// How far the log is copied: `[cut, copied)` is in `<log>.kept`.
    copied: u64,
    /// How far the copy is flushed: `[cut, flushed)` is durable in `<log>.kept`.
    flushed: u64,
    /// The log's first frame (the first dropped).
    old: Option<FrameId>,
    /// The kept suffix's first frame, once copied.
    first: Option<FrameId>,
    buf: Vec<u8>,
    seam: Seam,
}

impl KeptCopy {
    /// Take `src`, the log's own descriptor, for the copy's reads (which [`run`](Self::run)
    /// and [`extend_to`](Self::extend_to) make; this reads nothing), and create
    /// `<log>.kept` beside the log at `log` with `perms`, the log's own (set exactly, past
    /// the umask, so the kept records are never readable more widely than the log they
    /// came from).
    pub(crate) fn begin(
        log: &Path,
        src: Arc<File>,
        perms: &Permissions,
        drop_count: u64,
        begin_len: u64,
        seam: Seam,
    ) -> io::Result<KeptCopy> {
        let kept = kept_path(log);
        let dst = create_like_read_write(&kept, perms)?;
        let chunk = seam.chunk();
        Ok(KeptCopy {
            src,
            dst,
            kept,
            drop_count,
            begin_len,
            cut: None,
            copied: 0,
            flushed: 0,
            old: None,
            first: None,
            buf: vec![0u8; chunk],
            seam,
        })
    }

    /// THE UNLOCKED COPY: find the cut, copy the log from it to the durable length the
    /// compaction began at, and flush the copy. Those bytes are durable, so nothing changes
    /// them meanwhile; flushed here, the locked finish flushes only the delta.
    pub(crate) fn run(&mut self) -> io::Result<()> {
        self.seam.copy_starts();
        self.walk()?;
        self.extend_to(self.begin_len)?;
        self.flush()
    }

    /// `buf.len()` bytes at `pos` into `buf`, by position, through the seam.
    fn read_at(&mut self, pos: u64, buf: &mut [u8]) -> io::Result<()> {
        read_exact_at(&self.src, buf, pos)?;
        self.seam.read(buf.len());
        Ok(())
    }

    /// The stored length (header and payload) of the frame at `pos`, which must end at or
    /// below `end`.
    fn frame_len_at(&mut self, pos: u64, end: u64) -> io::Result<u64> {
        let mut hdr = [0u8; HEADER_SIZE];
        self.read_at(pos, &mut hdr)?;
        let Ok((len, _crc)) = decode_frame_header_bytes(&hdr) else {
            return Err(cut_error());
        };
        let total = (HEADER_SIZE as u64).saturating_add(len as u64);
        match pos.checked_add(total) {
            Some(stop) if stop <= end => Ok(total),
            _ => Err(cut_error()),
        }
    }

    /// The whole frame at `pos` (one frame, at most the wire's payload cap and a header).
    fn read_frame(&mut self, pos: u64, end: u64) -> io::Result<Vec<u8>> {
        let total = self.frame_len_at(pos, end)?;
        // The header decode already refuses a payload over the cap; bounded here too, so
        // the one allocation sized by bytes on disk is visibly bounded where it is made.
        let n = match usize::try_from(total) {
            Ok(n) if n <= HEADER_SIZE.saturating_add(MAX_PAYLOAD_LEN) => n,
            _ => return Err(cut_error()),
        };
        let mut frame = vec![0u8; n];
        self.read_at(pos, &mut frame)?;
        Ok(frame)
    }

    /// Skip the dropped frames from the file's start, reading only their headers (and the
    /// first one whole, for its identity).
    fn walk(&mut self) -> io::Result<()> {
        if self.cut.is_some() {
            return Ok(());
        }
        let end = self.begin_len;
        let first = self.read_frame(0, end)?;
        self.old = Some(FrameId::of(&first));
        let mut pos = first.len() as u64;
        drop(first);
        let mut left = self.drop_count.saturating_sub(1);
        while left > 0 {
            let len = self.frame_len_at(pos, end)?;
            pos = pos.saturating_add(len);
            left = left.saturating_sub(1);
        }
        self.cut = Some(pos);
        self.copied = pos;
        self.flushed = pos;
        Ok(())
    }

    /// Copy the log from where the copy stands to `end`, in chunks. The broker's finish
    /// calls it under the lock with the durable length then: only the bytes appended
    /// since the begin are left to copy.
    pub(crate) fn extend_to(&mut self, end: u64) -> io::Result<()> {
        self.walk()?;
        if end < self.copied {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "retention: the durable log is shorter than the compaction already copied",
            ));
        }
        if self.first.is_none() && self.copied < end {
            let frame = self.read_frame(self.copied, end)?;
            self.dst.write_all(&frame)?;
            self.first = Some(FrameId::of(&frame));
            self.copied = self.copied.saturating_add(frame.len() as u64);
        }
        if self.copied >= end {
            return Ok(());
        }
        let KeptCopy {
            src,
            dst,
            buf,
            seam,
            copied,
            ..
        } = self;
        while *copied < end {
            let left = end.saturating_sub(*copied);
            let n = match usize::try_from(left) {
                Ok(l) => l.min(buf.len()),
                Err(_) => buf.len(),
            };
            let Some(chunk) = buf.get_mut(..n) else {
                return Err(cut_error());
            };
            if chunk.is_empty() {
                return Err(cut_error());
            }
            read_exact_at(src, chunk, *copied)?;
            seam.read(chunk.len());
            dst.write_all(chunk)?;
            *copied = copied.saturating_add(chunk.len() as u64);
        }
        Ok(())
    }

    /// Flush the copy in full: what was copied since the last flush becomes durable. The
    /// unlocked copy ends with one; the finish's, after the delta, is [`Step::Copy`].
    pub(crate) fn flush(&mut self) -> io::Result<()> {
        flush_file(&self.dst, &self.kept)?;
        self.seam.flushed(self.copied.saturating_sub(self.flushed));
        self.flushed = self.copied;
        Ok(())
    }

    /// The byte offset of the first kept frame (after [`run`](Self::run)).
    pub(crate) const fn cut(&self) -> Option<u64> {
        self.cut
    }

    /// The log's first frame (after [`run`](Self::run)).
    pub(crate) const fn old(&self) -> Option<FrameId> {
        self.old
    }

    /// The kept suffix's first frame, or `None` when it keeps none.
    pub(crate) const fn first(&self) -> Option<FrameId> {
        self.first
    }

    /// `<log>.kept`.
    pub(crate) fn kept(&self) -> &Path {
        &self.kept
    }

    /// The replacement descriptor, locked before its name becomes the live log.
    pub(crate) const fn destination(&self) -> &File {
        &self.dst
    }

    /// Transfer the exact locked descriptor; closing the source cannot unlock it.
    pub(crate) fn into_destination(self) -> File {
        self.dst
    }

    /// The compaction's seam, which the held store's append before the copy crashes at too.
    pub(crate) const fn seam(&self) -> &Seam {
        &self.seam
    }

    /// Give the compaction up before its switch: close and remove the copy.
    pub(crate) fn abandon(self) {
        let kept = self.kept;
        drop(self.src);
        let _ = self.dst.unlock();
        drop(self.dst);
        let _ = remove_file_path(&kept);
    }
}

#[cfg(test)]
#[path = "compact_tests.rs"]
mod tests;
