// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE HELD STORE, `<log>.held`: the records below the log's base that a hold rule still
//! wants, each at its ABSOLUTE offset, the floors the records given up raise, and the rules
//! they are held by (`retention.rs`; `REQUIREMENTS-fabric-operations` R4, "Design
//! (2026-10-19)").
//!
//! # The file
//!
//! A sequence of `astream_wire` frames, each payload sealed under the log's at-rest key when
//! it has one, with the AAD [`HELD_AAD`] and the frame's index in the file, so no frame can
//! be moved within the file. That is all the seal binds: a frame from another held store
//! sealed under the same key, or from this one before a rewrite, authenticates at the same
//! index, and a store cut back at a frame boundary reads as one with fewer frames (the
//! log's anti-rollback watermark does not cover the held store, which keeps none of its
//! own; the log's identity is no anchor either, since it is read from the log's first
//! frame, which every compaction changes). Four kinds of frame, each naming the CUT it was
//! written for (the base its compaction takes; the base at the job's begin for `S`):
//!
//! | kind | body |
//! |---|---|
//! | `R` | `cut, k u32, k × since u64, rules`: the rules the store holds by, and from where each of their `k` classes is whole |
//! | `S` | `cut, from u64, n u32, n × (head u64, ms u64)`: the retention tick's stamps (`retention::stamp`) from `from` on: the stamps read so far are cut back to `from` (`retention::clamp_stamps`), then these follow |
//! | `T` | `cut, n u32, n × at_ms u64`, then `n` frames, each a carried record's payload |
//! | `D` | `cut, n u32, n × offset u64, m u32, m × (len u32, subject, floor u64)`: held records given up, and the floors they raise |
//!
//! It starts with an `R` frame; a rules change appends another. Between compactions it is
//! only appended to: a compaction writes what it newly carries and what it gives up, never
//! what the store already holds, and every job first the stamps its tick took since the
//! last it wrote, so a record's age survives a restart (an `S` frame names the base the job
//! began at: a stamp is true whether or not the job's compaction lands). An open whose log
//! ends below the stamps read back (a crash lost records a tick had stamped, and their
//! offsets are taken again by records no tick saw yet) cuts them back to the log's head and
//! appends that cut as an `S` frame of no stamps before the log takes a record.
//!
//! # Crash safety
//!
//! A compaction appends its frames, and flushes them, before it copies the log and writes
//! its intent ([`Step::Held`](crate::compact::Step::Held)), so a compaction that lands
//! always finds its held records beside it. An open that reads a frame naming a cut ABOVE
//! the log's base knows that compaction never landed, and cuts the file there: every frame
//! after it is that compaction's own (compactions run one at a time, and one that fails in
//! process truncates its frames away before the next begins), and the records it carried
//! are still in the log. A file that ends inside a frame (a torn append), or in zeros, is
//! cut at that frame. Anything else that does not read refuses the open, naming the file.
//!
//! The cut is made once nothing refuses the open ([`HeldStore::make_owed_cut`]), never at the
//! read: only the log's scan can say the store was read under the right key. Read without its
//! key, a sealed frame is its nonce first, and about one sealed store in 256 reads as rules cut
//! above the base. A log with a `<log>.seal` beside it refuses a keyless open before this read
//! (`refuse_keyless_sealed`, in `store.rs`), but one whose `.seal` is gone reaches it, as a v1 log
//! does, and its scan refuses it only after: with the cut owed, that open changes nothing here.
//!
//! # Bounded
//!
//! The held records are bounded by their classes' `max_bytes` (`retention.rs`). The file is
//! REWRITTEN whole (tmp, flush, rename, directory flush) once it is more than twice what it
//! carries, so it stays within a small multiple of the rules' bytes. The per-subject floors
//! are at most [`FLOORS_MAX`] subjects and [`FLOOR_BYTES_MAX`] bytes of names: past either,
//! the lowest floors fold into one SPILL floor that every hold class's reads answer at least
//! (it tells more than it must, never less).
//!
//! # The ledger, in memory only
//!
//! Beside the floors the store keeps the LEDGER of every record the rules gave up, one by
//! one ([`retention::Ledger`], bounded as the floors are), from which a tail below the base
//! is told how many records of its filter it lost (R4's addendum, A9). It is not in the
//! file: an open starts it whole from the base it opens at, so the counts of what was given
//! up before a restart are not known after it, and the file's format is unchanged. What a
//! compaction no rules planned dropped unnamed is in the file all the same, as the spill
//! floor its own `D` frame raises ([`HeldStore::unplanned_job`]), so the range is still
//! told after a restart.

use crate::brecord::BrokerRecord;
use crate::retention::{self, Held, Retention, Stamps};
use crate::store::{
    create_like, flush_file, open_sidecar, rename_path, sync_parent_dir, AtRestKey, AtRestRef,
};
use astream_wire::{Filter, Frame, HEADER_SIZE};
use std::collections::{BTreeMap, HashMap};
use std::fs::{File, Permissions};
use std::io::{self, BufReader, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Domain-separating AAD for sealing `<log>.held` under the log's at-rest key (the frame's
/// index follows it).
#[cfg(feature = "at-rest")]
const HELD_AAD: &[u8; 15] = b"astream-held-v1";
#[cfg(feature = "at-rest")]
const HELD_BOUND_PREFIX: &[u8; 16] = b"astream-held-v2\0";

const KIND_RULES: u8 = b'R';
const KIND_STAMPS: u8 = b'S';
const KIND_GROUP: u8 = b'T';
const KIND_DECIDED: u8 = b'D';

/// The most records one `T` frame introduces.
const GROUP_MAX: usize = 65_536;

/// The most body bytes a `D` frame takes before the next one starts.
const DECIDED_CHUNK: usize = 1 << 20;

/// The most subjects the store keeps a floor for.
pub(crate) const FLOORS_MAX: usize = 65_536;

/// The most bytes of subject names the floors take.
pub(crate) const FLOOR_BYTES_MAX: usize = 8 << 20;

/// What the file may grow to past twice what it carries before it is rewritten.
const REWRITE_SLACK: u64 = 1 << 20;

/// `<log>` with `ext` appended to its name.
fn beside(log: &Path, ext: &str) -> PathBuf {
    let mut p = log.to_path_buf();
    p.as_mut_os_string().push(ext);
    p
}

/// The held store, `<log>.held`.
pub(crate) fn held_path(log: &Path) -> PathBuf {
    beside(log, ".held")
}

/// Where a rewrite of the held store is written before its rename.
pub(crate) fn held_tmp_path(log: &Path) -> PathBuf {
    beside(log, ".held.tmp")
}

/// A copy of the at-rest key and optional `<log>.seal` binding a job seals with outside
/// the log lock, zeroed on drop (`AtRestKey`).
pub(crate) struct KeyCopy(Option<AtRestKey>);

impl KeyCopy {
    pub(crate) const fn of(key: Option<AtRestRef<'_>>) -> KeyCopy {
        match key {
            Some(r) => KeyCopy(Some(AtRestKey {
                key: *r.key,
                seal_id: r.seal_id,
            })),
            None => KeyCopy(None),
        }
    }

    const fn get(&self) -> Option<AtRestRef<'_>> {
        match &self.0 {
            Some(k) => Some(k.as_ref()),
            None => None,
        }
    }
}

#[cfg(feature = "at-rest")]
const fn aad(index: u64) -> [u8; 23] {
    let p = HELD_AAD;
    let idx = index.to_le_bytes();
    [
        p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11], p[12], p[13],
        p[14], idx[0], idx[1], idx[2], idx[3], idx[4], idx[5], idx[6], idx[7],
    ]
}

#[cfg(feature = "at-rest")]
const fn held_bound_aad(id: [u8; 16], index: u64) -> [u8; 40] {
    let p = HELD_BOUND_PREFIX;
    let idx = index.to_le_bytes();
    [
        p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11], p[12], p[13],
        p[14], p[15], id[0], id[1], id[2], id[3], id[4], id[5], id[6], id[7], id[8], id[9], id[10],
        id[11], id[12], id[13], id[14], id[15], idx[0], idx[1], idx[2], idx[3], idx[4], idx[5],
        idx[6], idx[7],
    ]
}

#[cfg(feature = "at-rest")]
pub(crate) fn seal(key: Option<AtRestRef<'_>>, index: u64, plain: &[u8]) -> Vec<u8> {
    match key {
        Some(AtRestRef {
            key: k,
            seal_id: Some(id),
        }) => {
            let bound = held_bound_aad(id, index);
            astream_aead::seal(k, &bound, plain)
        }
        Some(AtRestRef {
            key: k,
            seal_id: None,
        }) => {
            let legacy = aad(index);
            astream_aead::seal(k, &legacy, plain)
        }
        None => plain.to_vec(),
    }
}
#[cfg(not(feature = "at-rest"))]
fn seal(_key: Option<AtRestRef<'_>>, _index: u64, plain: &[u8]) -> Vec<u8> {
    plain.to_vec()
}

#[cfg(feature = "at-rest")]
pub(crate) fn unseal(key: Option<AtRestRef<'_>>, index: u64, payload: Vec<u8>) -> Option<Vec<u8>> {
    match key {
        Some(AtRestRef {
            key: k,
            seal_id: Some(id),
        }) => {
            let bound = held_bound_aad(id, index);
            match astream_aead::open(k, &bound, &payload) {
                Ok(p) => Some(p),
                Err(_) => None,
            }
        }
        Some(AtRestRef {
            key: k,
            seal_id: None,
        }) => {
            let legacy = aad(index);
            match astream_aead::open(k, &legacy, &payload) {
                Ok(p) => Some(p),
                Err(_) => None,
            }
        }
        None => Some(payload),
    }
}
#[cfg(not(feature = "at-rest"))]
fn unseal(_key: Option<AtRestRef<'_>>, _index: u64, payload: Vec<u8>) -> Option<Vec<u8>> {
    Some(payload)
}

/// Frames being written: their bytes, how many, and the index the next one takes.
struct Out<'k> {
    key: Option<AtRestRef<'k>>,
    bytes: Vec<u8>,
    index: u64,
    frames: u64,
}

impl Out<'_> {
    fn frame(&mut self, plain: &[u8]) -> io::Result<()> {
        let sealed = seal(self.key, self.index, plain);
        let Ok(framed) = Frame::new(sealed).encode() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "retention: a held-store frame is too large",
            ));
        };
        self.bytes.extend_from_slice(&framed);
        self.index = self.index.saturating_add(1);
        self.frames = self.frames.saturating_add(1);
        Ok(())
    }

    fn rules(&mut self, cut: u64, since: &[u64], rules: Option<&Retention>) -> io::Result<()> {
        let mut p = vec![KIND_RULES];
        p.extend_from_slice(&cut.to_le_bytes());
        let k = u32::try_from(since.len()).unwrap_or(0);
        p.extend_from_slice(&k.to_le_bytes());
        for s in since.iter().take(usize::try_from(k).unwrap_or(0)) {
            p.extend_from_slice(&s.to_le_bytes());
        }
        if let Some(r) = rules {
            p.extend_from_slice(&r.encode());
        }
        self.frame(&p)
    }

    fn stamps(&mut self, cut: u64, from: u64, stamps: &[(u64, u64)]) -> io::Result<()> {
        let mut p = vec![KIND_STAMPS];
        p.extend_from_slice(&cut.to_le_bytes());
        p.extend_from_slice(&from.to_le_bytes());
        let n = u32::try_from(stamps.len()).unwrap_or(0);
        p.extend_from_slice(&n.to_le_bytes());
        for &(head, ms) in stamps.iter().take(usize::try_from(n).unwrap_or(0)) {
            p.extend_from_slice(&head.to_le_bytes());
            p.extend_from_slice(&ms.to_le_bytes());
        }
        self.frame(&p)
    }

    fn carried(&mut self, cut: u64, held: &[Held]) -> io::Result<()> {
        for group in held.chunks(GROUP_MAX) {
            let mut p = vec![KIND_GROUP];
            p.extend_from_slice(&cut.to_le_bytes());
            let n = u32::try_from(group.len()).unwrap_or(u32::MAX);
            p.extend_from_slice(&n.to_le_bytes());
            for h in group {
                p.extend_from_slice(&h.at_ms.to_le_bytes());
            }
            self.frame(&p)?;
            for h in group {
                let Ok(payload) = h
                    .rec
                    .encode_payload_marked_bt(crate::brecord::Mark::Unmarked, h.bt_ms)
                else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "retention: a held record does not encode",
                    ));
                };
                self.frame(&payload)?;
            }
        }
        Ok(())
    }

    fn decided(
        &mut self,
        cut: u64,
        removed: &[u64],
        floors: &BTreeMap<String, u64>,
    ) -> io::Result<()> {
        let mut offs = removed;
        let fl: Vec<(&String, &u64)> = floors.iter().collect();
        let mut fl_rest: &[(&String, &u64)] = &fl;
        while !offs.is_empty() || !fl_rest.is_empty() {
            let mut p = vec![KIND_DECIDED];
            p.extend_from_slice(&cut.to_le_bytes());
            let take = offs.len().min(DECIDED_CHUNK / 8);
            let Some((now, later)) = offs.split_at_checked(take) else {
                break;
            };
            p.extend_from_slice(&u32::try_from(now.len()).unwrap_or(0).to_le_bytes());
            for o in now {
                p.extend_from_slice(&o.to_le_bytes());
            }
            offs = later;
            let mut n = 0usize;
            let mut body = Vec::new();
            for (s, f) in fl_rest {
                if n > 0 && body.len().saturating_add(s.len()) > DECIDED_CHUNK {
                    break;
                }
                let len = u32::try_from(s.len()).unwrap_or(u32::MAX);
                body.extend_from_slice(&len.to_le_bytes());
                body.extend_from_slice(s.as_bytes());
                body.extend_from_slice(&f.to_le_bytes());
                n = n.saturating_add(1);
            }
            fl_rest = fl_rest.get(n..).unwrap_or(&[]);
            p.extend_from_slice(&u32::try_from(n).unwrap_or(0).to_le_bytes());
            p.extend_from_slice(&body);
            self.frame(&p)?;
        }
        Ok(())
    }
}

/// What a rewrite writes first: everything the store holds as the job began, at the base
/// it began at.
struct Snapshot {
    base: u64,
    since: Vec<u64>,
    stamps: Stamps,
    rules: Option<Retention>,
    entries: Vec<Held>,
    floors: BTreeMap<String, u64>,
}

/// What one retention planning changes in the held store: what it carries and gives up,
/// the floors that rise, and the frames that say so, appended (and flushed) with no lock
/// held before the compaction's copy ([`run`](Self::run)), and applied in memory at its
/// finish ([`HeldStore::finish`]). A store due a rewrite ([`HeldStore::rewrite_due`]) is
/// written whole instead, as it stood at the job's begin, before the job's own frames.
pub(crate) struct HeldJob {
    pub(crate) cut: u64,
    /// The base at the job's begin: the cut its `S` frame names.
    base: u64,
    /// The stamps the store's file does not hold yet, from `stamps_from` (its `S` frame;
    /// none when it is rewritten, whose snapshot holds them all), and the head of the last
    /// stamp the file holds once the job's frames are durable.
    stamps: Stamps,
    stamps_from: u64,
    stamped_to: u64,
    pub(crate) carry: Vec<Held>,
    pub(crate) remove: Vec<u64>,
    pub(crate) floors: BTreeMap<String, u64>,
    /// Unread records given up, by subject and why, and how many: the log lines.
    pub(crate) lost: BTreeMap<(String, retention::Why), u64>,
    /// Every record given up, one by one: what the store's ledger takes at the finish.
    given: retention::Ledger,
    file: Option<File>,
    path: PathBuf,
    tmp: PathBuf,
    perms: Permissions,
    key: KeyCopy,
    rewrite: Option<Snapshot>,
    /// The file's length and frame count before the job's own frames: where an abandon
    /// cuts it back to, and the index its first frame is sealed under. A rewrite sets them
    /// to the rewritten prefix's.
    len_before: u64,
    frames_before: u64,
    /// What [`run`](Self::run) wrote of the job's own frames, and whether it replaced the
    /// file.
    wrote: Option<(u64, u64)>,
    replaced: bool,
}

impl HeldJob {
    /// Whether the job writes nothing to the held store.
    pub(crate) fn writes_nothing(&self) -> bool {
        self.carry.is_empty()
            && self.stamps.is_empty()
            && self.remove.is_empty()
            && self.floors.is_empty()
            && self.rewrite.is_none()
    }

    /// APPEND the job's frames and flush them: the unlocked half, before the compaction's
    /// copy, so the frames are durable before its intent. A rewrite writes the store whole
    /// at a tmp name first, the job's frames after it, flushes, renames it over the store
    /// and flushes the directory.
    pub(crate) fn run(&mut self) -> io::Result<()> {
        if self.writes_nothing() {
            self.wrote = Some((0, 0));
            return Ok(());
        }
        if let Some(snap) = self.rewrite.take() {
            let mut out = Out {
                key: self.key.get(),
                bytes: Vec::new(),
                index: 0,
                frames: 0,
            };
            out.rules(snap.base, &snap.since, snap.rules.as_ref())?;
            if !snap.stamps.is_empty() {
                out.stamps(snap.base, 0, &snap.stamps)?;
            }
            out.carried(snap.base, &snap.entries)?;
            out.decided(snap.base, &[], &snap.floors)?;
            let (prefix_len, prefix_frames) = (out.bytes.len() as u64, out.frames);
            out.carried(self.cut, &self.carry)?;
            out.decided(self.cut, &self.remove, &self.floors)?;
            let mut f = create_like(&self.tmp, &self.perms)?;
            f.write_all(&out.bytes)?;
            flush_file(&f, &self.tmp)?;
            rename_path(&self.tmp, &self.path)?;
            self.file = Some(f);
            self.replaced = true;
            self.len_before = prefix_len;
            self.frames_before = prefix_frames;
            self.wrote = Some((
                (out.bytes.len() as u64).saturating_sub(prefix_len),
                out.frames.saturating_sub(prefix_frames),
            ));
            return sync_parent_dir(&self.path);
        }
        let mut out = Out {
            key: self.key.get(),
            bytes: Vec::new(),
            index: self.frames_before,
            frames: 0,
        };
        if !self.stamps.is_empty() {
            out.stamps(self.base, self.stamps_from, &self.stamps)?;
        }
        out.carried(self.cut, &self.carry)?;
        out.decided(self.cut, &self.remove, &self.floors)?;
        let Some(f) = self.file.as_mut() else {
            return Err(io::Error::other(
                "retention: the held store is not open; set the rules first",
            ));
        };
        f.seek(SeekFrom::Start(self.len_before))?;
        f.write_all(&out.bytes)?;
        flush_file(f, &self.path)?;
        self.wrote = Some((out.bytes.len() as u64, out.frames));
        Ok(())
    }

    /// Cut the file back to what it held before the job's own frames: a compaction that
    /// will not land. A failure here leaves frames an open would apply for a compaction that
    /// did not happen, so the caller poisons the log.
    fn cut_back(&mut self) -> io::Result<()> {
        let Some((n, _)) = self.wrote else {
            return Ok(());
        };
        if n == 0 {
            return Ok(());
        }
        let Some(f) = self.file.as_mut() else {
            return Ok(());
        };
        truncate(f, self.len_before)?;
        flush_file(f, &self.path)
    }
}

/// Truncate `f` to `len` bytes. Called through a function pointer, as `storage.rs` does, so
/// the verified lane reads `File::set_len` (a syscall) and not `Vec::set_len` (an unsafe
/// length write) by its name.
fn truncate(f: &File, len: u64) -> io::Result<()> {
    let op: fn(&File, u64) -> io::Result<()> = File::set_len;
    op(f, len)
}

/// THE HELD STORE in memory, beside its file (see the module docs).
#[derive(Default)]
pub(crate) struct HeldStore {
    /// The cut the open's read found and has not made: the file and where
    /// ([`Self::make_owed_cut`]).
    owed_cut: Option<(File, u64)>,
    /// The rules the store holds by: set this open, or the ones the file was last held
    /// under.
    pub(crate) rules: Option<Retention>,
    /// Whether this open set them ([`BrokerLog::set_retention`](crate::BrokerLog::set_retention)):
    /// only then does a compaction plan by them.
    pub(crate) active: bool,
    /// The held records, by offset (every one below the base).
    pub(crate) entries: BTreeMap<u64, Held>,
    /// How many of `entries` each subject has: what a forget asks of the store
    /// ([`holds_subject`](Self::holds_subject)). Kept with `entries`, by
    /// [`insert`](Self::insert) and [`remove_entry`](Self::remove_entry) alone.
    by_subject: HashMap<String, usize>,
    /// Each subject's floor: the offset after the newest record of it a hold rule gave up.
    pub(crate) floors: BTreeMap<String, u64>,
    floor_bytes: usize,
    /// The highest floor folded out of `floors` to keep it bounded.
    pub(crate) spill: u64,
    /// The highest of every floor, the spill included.
    pub(crate) floor_max: u64,
    /// From where the store is whole, class by class of `rules`: below a class's, no
    /// record of it its rule wants was ever carried (the base when that class took effect;
    /// [`retention::carried_since`] across a rules change).
    pub(crate) since: Vec<u64>,
    /// The tick's stamps (`retention::stamp`), and the head of the last one the file holds:
    /// read back at the open, the stamps below it are the file's, and the ones above it
    /// the next job writes ([`HeldJob::run`]).
    pub(crate) stamps: Stamps,
    stamped_to: u64,
    /// The bytes the held records take ([`retention::record_bytes`]).
    pub(crate) held_bytes: u64,
    /// What the last planning left each class before it is past its bytes
    /// (`Plan::room`), and the bytes of each class's records the log took since
    /// ([`note`](Self::note)): once a class has taken more than its room, the log is DUE a
    /// tick ([`BrokerLog::retention_due`](crate::BrokerLog::retention_due)). No room before
    /// this open's first planning: the first record makes it due.
    pub(crate) room: Vec<u64>,
    pub(crate) taken: Vec<u64>,
    pub(crate) due: bool,
    /// What the rules gave up, record by record, since the open (see the module docs).
    pub(crate) ledger: retention::Ledger,
    file: Option<File>,
    len: u64,
    frames: u64,
}

/// One frame read back from the file.
enum Read1 {
    Frame(Vec<u8>, u64),
    End,
    /// Cut the file at the frame's start: a torn append, or a zeroed tail.
    Torn,
}

fn bad(path: &Path, at: u64, why: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "{}: the held store does not read at byte {at}: {why}; refusing to open, nothing \
             touched",
            path.display()
        ),
    )
}

/// Whether the file holds nothing but zeros from `at`.
fn zeros_from(r: &mut BufReader<File>, at: u64) -> io::Result<bool> {
    r.seek(SeekFrom::Start(at))?;
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        let n = r.read(&mut buf)?;
        if n == 0 {
            return Ok(true);
        }
        let Some(read) = buf.get(..n) else {
            return Ok(false);
        };
        if read.iter().any(|&b| b != 0) {
            return Ok(false);
        }
    }
}

fn read_one(
    r: &mut BufReader<File>,
    key: Option<AtRestRef<'_>>,
    index: u64,
    at: u64,
    path: &Path,
) -> io::Result<Read1> {
    match crate::proto::read_frame(r) {
        Ok(None) => Ok(Read1::End),
        Ok(Some(payload)) => {
            let n = (HEADER_SIZE as u64).saturating_add(payload.len() as u64);
            match unseal(key, index, payload) {
                Some(p) => Ok(Read1::Frame(p, n)),
                None => Err(bad(
                    path,
                    at,
                    "a frame fails to authenticate (wrong at-rest key, or tampered)",
                )),
            }
        }
        Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => Ok(Read1::Torn),
        Err(e) if e.kind() == io::ErrorKind::InvalidData => {
            if zeros_from(r, at)? {
                Ok(Read1::Torn)
            } else {
                Err(bad(path, at, &e.to_string()))
            }
        }
        Err(e) => Err(e),
    }
}

fn u64_at(b: &[u8], pos: &mut usize) -> Option<u64> {
    let end = pos.checked_add(8)?;
    let (chunk, _) = b.get(*pos..end)?.split_first_chunk::<8>()?;
    *pos = end;
    Some(u64::from_le_bytes(*chunk))
}

fn u32_at(b: &[u8], pos: &mut usize) -> Option<usize> {
    let end = pos.checked_add(4)?;
    let (chunk, _) = b.get(*pos..end)?.split_first_chunk::<4>()?;
    *pos = end;
    usize::try_from(u32::from_le_bytes(*chunk)).ok()
}

/// A `D` frame's body: the offsets given up and the floors raised.
type Decided = (Vec<u64>, Vec<(String, u64)>);

fn decode_decided(b: &[u8], mut pos: usize) -> Option<Decided> {
    let n = u32_at(b, &mut pos)?;
    let mut offs = Vec::new();
    for _ in 0..n {
        offs.push(u64_at(b, &mut pos)?);
    }
    let m = u32_at(b, &mut pos)?;
    let mut floors = Vec::new();
    for _ in 0..m {
        let len = u32_at(b, &mut pos)?;
        let end = pos.checked_add(len)?;
        let s = std::str::from_utf8(b.get(pos..end)?).ok()?.to_string();
        pos = end;
        floors.push((s, u64_at(b, &mut pos)?));
    }
    if pos != b.len() {
        return None;
    }
    Some((offs, floors))
}

impl HeldStore {
    /// THE OPEN'S READ of `<log>.held` at the log's `base` (see the module docs): a log this
    /// open `created` carries none of a deleted predecessor's, and a rewrite that died
    /// before its rename leaves a tmp file that is removed.
    pub(crate) fn load(
        log: &Path,
        key: Option<AtRestRef<'_>>,
        base: u64,
        created: bool,
    ) -> io::Result<HeldStore> {
        let _ = crate::store::remove_file_path(&held_tmp_path(log));
        if created {
            let _ = crate::store::remove_file_path(&held_path(log));
            return Ok(HeldStore::default());
        }
        Self::read(log, key, base)
    }

    /// [`Self::load`]'s read of the store as it stands, which changes no file: the cut it
    /// finds is only owed ([`Self::make_owed_cut`]). The store is opened read-write, for the
    /// appends an open makes later, and nothing is written through it here: a check that
    /// writes nothing (`BrokerLog::check_open`) reads it so too, so a store the open could
    /// not append to is refused there as the open refuses it.
    pub(crate) fn read(log: &Path, key: Option<AtRestRef<'_>>, base: u64) -> io::Result<HeldStore> {
        let path = held_path(log);
        let Some(file) = open_sidecar(&path, u64::MAX, true, "held store")? else {
            return Ok(HeldStore::default());
        };
        let mut st = HeldStore::default();
        let mut r = BufReader::new(file);
        let mut pos: u64 = 0;
        let mut index: u64 = 0;
        // Where the file is cut, if it is: the byte and the frame count there.
        let mut cut_at: Option<(u64, u64)> = None;
        let mut first = true;
        'frames: loop {
            let start = pos;
            let start_index = index;
            let plain = match read_one(&mut r, key, index, start, &path)? {
                Read1::End => break,
                Read1::Torn => {
                    cut_at = Some((start, start_index));
                    break;
                }
                Read1::Frame(p, n) => {
                    pos = pos.saturating_add(n);
                    index = index.saturating_add(1);
                    p
                }
            };
            let Some((&kind, _)) = plain.split_first() else {
                return Err(bad(&path, start, "an empty frame"));
            };
            let mut at = 1usize;
            let Some(cut) = u64_at(&plain, &mut at) else {
                return Err(bad(&path, start, "a frame too short for its cut"));
            };
            if first && kind != KIND_RULES {
                return Err(bad(&path, start, "the store does not start with its rules"));
            }
            first = false;
            if cut > base {
                // A compaction that never landed: this frame and every one after it.
                cut_at = Some((start, start_index));
                break;
            }
            match kind {
                KIND_RULES => {
                    let Some(k) = u32_at(&plain, &mut at) else {
                        return Err(bad(&path, start, "a rules frame too short"));
                    };
                    let mut since = Vec::new();
                    for _ in 0..k {
                        let Some(s) = u64_at(&plain, &mut at) else {
                            return Err(bad(&path, start, "a rules frame too short"));
                        };
                        since.push(s);
                    }
                    let rest = plain.get(at..).unwrap_or(&[]);
                    st.rules = if rest.is_empty() {
                        None
                    } else {
                        match Retention::decode(rest) {
                            Some(r) if r.classes() == since.len() => Some(r),
                            Some(_) => {
                                return Err(bad(
                                    &path,
                                    start,
                                    "rules whose classes the frame does not name",
                                ))
                            }
                            None => return Err(bad(&path, start, "rules that do not read")),
                        }
                    };
                    st.since = since;
                }
                KIND_STAMPS => {
                    let (Some(from), Some(n)) = (u64_at(&plain, &mut at), u32_at(&plain, &mut at))
                    else {
                        return Err(bad(&path, start, "a stamps frame too short"));
                    };
                    retention::clamp_stamps(&mut st.stamps, from);
                    for _ in 0..n {
                        let (Some(head), Some(ms)) =
                            (u64_at(&plain, &mut at), u64_at(&plain, &mut at))
                        else {
                            return Err(bad(&path, start, "a stamps frame too short"));
                        };
                        retention::stamp(&mut st.stamps, head, ms);
                    }
                    if at != plain.len() {
                        return Err(bad(&path, start, "a stamps frame too long"));
                    }
                }
                KIND_GROUP => {
                    let Some(n) = u32_at(&plain, &mut at) else {
                        return Err(bad(&path, start, "a group frame too short"));
                    };
                    let mut ats = Vec::new();
                    for _ in 0..n {
                        let Some(ms) = u64_at(&plain, &mut at) else {
                            return Err(bad(&path, start, "a group frame too short"));
                        };
                        ats.push(ms);
                    }
                    let mut recs = Vec::new();
                    for ms in ats {
                        let rec_at = pos;
                        let payload = match read_one(&mut r, key, index, rec_at, &path)? {
                            Read1::Frame(p, n) => {
                                pos = pos.saturating_add(n);
                                index = index.saturating_add(1);
                                p
                            }
                            // The group's records were cut short: the whole group is torn.
                            Read1::End | Read1::Torn => {
                                cut_at = Some((start, start_index));
                                break 'frames;
                            }
                        };
                        let Some((rec, mark, bt_ms)) =
                            BrokerRecord::from_payload_marked_bt(&payload)
                        else {
                            return Err(bad(&path, rec_at, "a held record does not parse"));
                        };
                        if mark != crate::brecord::Mark::Unmarked {
                            return Err(bad(&path, rec_at, "a held record carries a batch mark"));
                        }
                        recs.push((rec, ms, bt_ms));
                    }
                    for (rec, at_ms, bt_ms) in recs {
                        if rec.seq.0 < base {
                            st.insert(Held {
                                rec: Arc::new(rec),
                                at_ms,
                                bt_ms,
                            });
                        }
                    }
                }
                KIND_DECIDED => {
                    let Some((offs, floors)) = decode_decided(&plain, at) else {
                        return Err(bad(&path, start, "a decision frame does not read"));
                    };
                    for o in offs {
                        st.remove_entry(o);
                    }
                    let mut map = BTreeMap::new();
                    for (s, f) in floors {
                        map.insert(s, f);
                    }
                    st.raise(&map);
                }
                _ => return Err(bad(&path, start, "a frame of no kind this build writes")),
            }
        }
        let mut file = r.into_inner();
        if let Some((at, frames)) = cut_at {
            pos = at;
            index = frames;
        }
        file.seek(SeekFrom::Start(pos))?;
        st.len = pos;
        st.frames = index;
        if st.len == 0 {
            // Nothing survived, not even the rules: as if there were no file.
            return Ok(HeldStore {
                owed_cut: cut_at.map(|(at, _)| (file, at)),
                ..HeldStore::default()
            });
        }
        st.stamped_to = match st.stamps.last() {
            Some(&(head, _)) => head,
            None => 0,
        };
        st.prune_stamps(base);
        st.owed_cut = match cut_at {
            Some((at, _)) => Some((file.try_clone()?, at)),
            None => None,
        };
        st.file = Some(file);
        Ok(st)
    }

    /// THE CUT [`Self::load`] FOUND (a compaction that never landed, a torn append), made once
    /// nothing refuses the open: an open that refuses, for a sealed store read without its key
    /// above all, leaves the file as it found it (see the module docs). A crash before this finds
    /// the same frames at the next open and owes the same cut.
    pub(crate) fn make_owed_cut(&mut self, log: &Path) -> io::Result<()> {
        if let Some((file, at)) = self.owed_cut.take() {
            truncate(&file, at)?;
            flush_file(&file, &held_path(log))?;
        }
        Ok(())
    }

    /// THE OPEN'S LOG HEAD `next`, its base `base` (the log at `log`): stamps read back past
    /// `next` named records a crash lost, whose offsets records no tick saw yet take again,
    /// so they are cut back to `next` (`retention::clamp_stamps`), and that cut is appended
    /// and flushed as an `S` frame of no stamps before the log takes a record: a later open
    /// reads it, whether or not a tick wrote stamps since. Nothing when no stamp is past it.
    pub(crate) fn opened_at(
        &mut self,
        log: &Path,
        key: Option<AtRestRef<'_>>,
        base: u64,
        next: u64,
    ) -> io::Result<()> {
        match self.stamps.last() {
            Some(&(head, _)) if head > next => {}
            _ => return Ok(()),
        }
        retention::clamp_stamps(&mut self.stamps, next);
        self.stamped_to = self.stamped_to.min(next);
        let Some(f) = self.file.as_mut() else {
            return Ok(());
        };
        let mut out = Out {
            key,
            bytes: Vec::new(),
            index: self.frames,
            frames: 0,
        };
        out.stamps(base, next, &[])?;
        let path = held_path(log);
        f.seek(SeekFrom::Start(self.len))?;
        f.write_all(&out.bytes)?;
        flush_file(f, &path)?;
        self.len = self.len.saturating_add(out.bytes.len() as u64);
        self.frames = self.frames.saturating_add(out.frames);
        Ok(())
    }

    /// Whether the tick took stamps the file does not hold yet.
    pub(crate) fn stamps_due(&self) -> bool {
        match self.stamps.last() {
            Some(&(head, _)) => head > self.stamped_to,
            None => false,
        }
    }

    /// Hold `h` at its offset, in place of what the store held there.
    pub(crate) fn insert(&mut self, h: Held) {
        let bytes = retention::record_bytes(&h.rec);
        let subject = h.rec.subject.clone();
        if let Some(old) = self.entries.insert(h.rec.seq.0, h) {
            self.forgo(&old);
        }
        self.held_bytes = self.held_bytes.saturating_add(bytes);
        let n = self.by_subject.entry(subject).or_insert(0);
        *n = n.saturating_add(1);
    }

    pub(crate) fn remove_entry(&mut self, off: u64) {
        if let Some(h) = self.entries.remove(&off) {
            self.forgo(&h);
        }
    }

    /// `h`'s bytes and its subject's count, taken back once it left `entries`.
    fn forgo(&mut self, h: &Held) {
        self.held_bytes = self
            .held_bytes
            .saturating_sub(retention::record_bytes(&h.rec));
        if let Some(n) = self.by_subject.get_mut(&h.rec.subject) {
            *n = n.saturating_sub(1);
            if *n == 0 {
                self.by_subject.remove(&h.rec.subject);
            }
        }
    }

    /// Whether the store holds any record of `subject`.
    pub(crate) fn holds_subject(&self, subject: &str) -> bool {
        self.by_subject.contains_key(subject)
    }

    /// Raise the floors `floors` names, keeping at most [`FLOORS_MAX`] subjects and
    /// [`FLOOR_BYTES_MAX`] bytes of names: the lowest floors fold into the spill. The
    /// empty name, which no subject is, is the spill's own (a rewrite writes it so).
    fn raise(&mut self, floors: &BTreeMap<String, u64>) {
        for (s, &f) in floors {
            self.floor_max = self.floor_max.max(f);
            if s.is_empty() {
                self.spill = self.spill.max(f);
                continue;
            }
            if f <= self.spill {
                continue;
            }
            match self.floors.get_mut(s) {
                Some(cur) => *cur = (*cur).max(f),
                None => {
                    self.floor_bytes = self.floor_bytes.saturating_add(s.len());
                    self.floors.insert(s.clone(), f);
                }
            }
        }
        if self.floors.len() <= FLOORS_MAX && self.floor_bytes <= FLOOR_BYTES_MAX {
            return;
        }
        let mut by_floor: Vec<(u64, String)> = Vec::new();
        for (s, &f) in &self.floors {
            by_floor.push((f, s.clone()));
        }
        by_floor.sort_unstable();
        let mut it = by_floor.into_iter();
        while self.floors.len() > FLOORS_MAX / 2 || self.floor_bytes > FLOOR_BYTES_MAX / 2 {
            let Some((f, s)) = it.next() else {
                break;
            };
            self.spill = self.spill.max(f);
            self.floor_bytes = self.floor_bytes.saturating_sub(s.len());
            self.floors.remove(&s);
        }
        let spill = self.spill;
        let mut gone = Vec::new();
        for (s, &f) in &self.floors {
            if f <= spill {
                gone.push(s.clone());
            }
        }
        for s in gone {
            self.floor_bytes = self.floor_bytes.saturating_sub(s.len());
            self.floors.remove(&s);
        }
    }

    /// The oldest offset of `filter`, at and above which it is complete: the greatest floor
    /// over what it matches ([`retention::oldest`]).
    pub(crate) fn oldest(&self, base: u64, filter: &Filter) -> u64 {
        retention::oldest(
            self.rules.as_ref(),
            base,
            &self.since,
            &self.floors,
            self.spill,
            self.floor_max,
            filter,
        )
    }

    /// How many records of `filter` at offsets in `from..to` the rules gave up that a tail
    /// told up to `told`, when the ledger stood at `seen`, was not counted
    /// ([`retention::Ledger::count`]), on a log at `base`: `None` unless the ledger names
    /// every one of them (whole from `from`, and [`retention::counted_from`]).
    pub(crate) fn gap_count(
        &self,
        base: u64,
        filter: &Filter,
        from: u64,
        to: u64,
        told: u64,
        seen: u64,
    ) -> Option<u64> {
        if self.ledger.whole() > from
            || !retention::counted_from(self.rules.as_ref(), &self.since, base, from, filter)
        {
            return None;
        }
        Some(self.ledger.count(filter, from, to, told, seen))
    }

    /// THE JOB OF A COMPACTION NO RULES PLANNED to `min`, on a log whose rules were read
    /// back and not set again (the writer's caps, a plain `retain_before`): it drops every
    /// record below `min` the store does not hold, of every class, naming none. So every
    /// hold class reads from at least `min` (the spill floor, which tells more than it must,
    /// never less), and the ledger is whole only from there. The spill is its `D` frame's
    /// one floor, the empty name's (as a rewrite keeps it), appended and flushed before the
    /// compaction's copy as a planned job's frames are: an open after the compaction landed
    /// reads it back, and one after a crash before it cuts the frame away (it names a cut
    /// above the base). The file's format is unchanged. `None` for a store that holds by no
    /// rules, where nothing reads a floor ([`cut_unplanned`](Self::cut_unplanned)).
    pub(crate) fn unplanned_job(
        &self,
        log: &Path,
        key: Option<AtRestRef<'_>>,
        perms: &Permissions,
        base: u64,
        min: u64,
    ) -> io::Result<Option<HeldJob>> {
        if self.rules.is_none() || self.file.is_none() {
            return Ok(None);
        }
        let mut plan = retention::Plan {
            cut: min,
            ..retention::Plan::default()
        };
        plan.floors.insert(String::new(), min);
        plan.given.whole_from(min);
        self.job(log, key, perms, base, plan).map(Some)
    }

    /// A COMPACTION NO RULES PLANNED landed at `min` with no job ([`unplanned_job`]): the
    /// ledger is whole only from `min`, and a store with rules but no file (none this build
    /// opens) reads every hold class from at least `min`, in memory.
    ///
    /// [`unplanned_job`]: Self::unplanned_job
    pub(crate) fn cut_unplanned(&mut self, min: u64) {
        if self.rules.is_some() {
            self.spill = self.spill.max(min);
            self.floor_max = self.floor_max.max(min);
        }
        self.ledger.whole_from(min);
    }

    /// The lowest offset a subscriber can still be delivered from: the oldest held record,
    /// or the base.
    pub(crate) fn read_floor(&self, base: u64) -> u64 {
        match self.entries.keys().next() {
            Some(&o) => o.min(base),
            None => base,
        }
    }

    /// The held records at offsets in `from..to`, in order.
    pub(crate) fn range(
        &self,
        from: u64,
        to: u64,
    ) -> std::collections::btree_map::Range<'_, u64, Held> {
        let to = to.max(from);
        self.entries.range(from..to)
    }

    /// SET THE RULES this open retains by (`log`'s permissions `perms`, its base `base`):
    /// the same rules the store already holds by keep it whole from where it was; other
    /// rules keep, class by class, where the old classes their subjects were in became
    /// whole, a class new to the rules (or one whose subjects the old rules did not keep
    /// below the base) starting at `base`, since below it no record of it was carried
    /// ([`retention::carried_since`]). Durable before it returns: the store is created, or
    /// its rules appended.
    pub(crate) fn set_rules(
        &mut self,
        log: &Path,
        key: Option<AtRestRef<'_>>,
        perms: &Permissions,
        base: u64,
        rules: Retention,
    ) -> io::Result<()> {
        let same = match (&self.rules, &self.file) {
            (Some(r), Some(_)) => r.encode() == rules.encode(),
            _ => false,
        };
        // Planned under no rules of this open: the first record asks for a tick.
        self.room = Vec::new();
        self.taken = Vec::new();
        self.due = true;
        if same {
            self.rules = Some(rules);
            self.active = true;
            return Ok(());
        }
        let since = retention::carried_since(self.rules.as_ref(), &self.since, &rules, base);
        let path = held_path(log);
        match self.file.as_mut() {
            Some(f) => {
                let mut out = Out {
                    key,
                    bytes: Vec::new(),
                    index: self.frames,
                    frames: 0,
                };
                out.rules(base, &since, Some(&rules))?;
                f.seek(SeekFrom::Start(self.len))?;
                f.write_all(&out.bytes)?;
                flush_file(f, &path)?;
                self.len = self.len.saturating_add(out.bytes.len() as u64);
                self.frames = self.frames.saturating_add(out.frames);
            }
            None => {
                let mut out = Out {
                    key,
                    bytes: Vec::new(),
                    index: 0,
                    frames: 0,
                };
                out.rules(base, &since, Some(&rules))?;
                let mut f = create_like(&path, perms)?;
                f.write_all(&out.bytes)?;
                flush_file(&f, &path)?;
                sync_parent_dir(&path)?;
                self.len = out.bytes.len() as u64;
                self.frames = out.frames;
                self.file = Some(f);
            }
        }
        self.since = since;
        self.rules = Some(rules);
        self.active = true;
        Ok(())
    }

    /// The job that writes `plan`'s held changes at its cut (see [`HeldJob`]), on the log at
    /// `log` with permissions `perms`, at its base `base`.
    pub(crate) fn job(
        &self,
        log: &Path,
        key: Option<AtRestRef<'_>>,
        perms: &Permissions,
        base: u64,
        plan: retention::Plan,
    ) -> io::Result<HeldJob> {
        let file = match &self.file {
            Some(f) => Some(f.try_clone()?),
            None => None,
        };
        let rewrite = if self.rewrite_due() {
            let mut floors = self.floors.clone();
            if self.spill > 0 {
                // The spill is no subject's: it is kept as the floor of the empty name, which
                // no subject is, and read back into the spill.
                floors.insert(String::new(), self.spill);
            }
            Some(Snapshot {
                base,
                since: self.since.clone(),
                stamps: self.stamps.clone(),
                rules: self.rules.clone(),
                entries: self.entries.values().cloned().collect(),
                floors,
            })
        } else {
            None
        };
        // What the file does not hold of the stamps yet: all of them in a rewrite's snapshot.
        let stamps = if rewrite.is_some() {
            Vec::new()
        } else {
            let from = self
                .stamps
                .partition_point(|&(head, _)| head <= self.stamped_to);
            self.stamps.get(from..).unwrap_or(&[]).to_vec()
        };
        let stamped_to = match self.stamps.last() {
            Some(&(head, _)) => head.max(self.stamped_to),
            None => self.stamped_to,
        };
        Ok(HeldJob {
            cut: plan.cut,
            base,
            stamps,
            stamps_from: self.stamped_to,
            stamped_to,
            carry: plan.carry,
            remove: plan.remove,
            floors: plan.floors,
            lost: plan.lost,
            given: plan.given,
            file,
            path: held_path(log),
            tmp: held_tmp_path(log),
            perms: perms.clone(),
            key: KeyCopy::of(key),
            rewrite,
            len_before: self.len,
            frames_before: self.frames,
            wrote: None,
            replaced: false,
        })
    }

    /// The job's file, if it replaced the store's: taken over whether the job lands or not.
    fn take_file(&mut self, job: &mut HeldJob) {
        if job.replaced {
            self.file = job.file.take();
            self.len = job.len_before;
            self.frames = job.frames_before;
        }
    }

    /// FINISH a job whose frames [`HeldJob::run`] made durable: in memory, the records it
    /// carried are held, the ones it gave up are gone, and the floors are raised.
    pub(crate) fn finish(&mut self, mut job: HeldJob) {
        self.take_file(&mut job);
        let (n, frames) = job.wrote.unwrap_or((0, 0));
        self.len = self.len.saturating_add(n);
        self.frames = self.frames.saturating_add(frames);
        self.stamped_to = self.stamped_to.max(job.stamped_to);
        self.ledger.take(std::mem::take(&mut job.given));
        for o in &job.remove {
            self.remove_entry(*o);
        }
        for h in job.carry {
            self.insert(h);
        }
        self.raise(&job.floors);
    }

    /// ABANDON a job whose compaction will not land: its frames are cut away, and a store
    /// it rewrote is the one held from here (it holds what the store did). `Err` when the
    /// cut failed: the caller poisons the log.
    pub(crate) fn abandon(&mut self, mut job: HeldJob) -> io::Result<()> {
        let cut = job.cut_back();
        self.take_file(&mut job);
        cut
    }

    /// Whether the file has grown past twice what it carries (and the slack), and is due
    /// a rewrite (the next [`job`](Self::job) writes it whole).
    pub(crate) fn rewrite_due(&self) -> bool {
        let live = self
            .held_bytes
            .saturating_add(self.floor_bytes as u64)
            .saturating_add((self.entries.len() as u64).saturating_mul(64))
            .saturating_add((self.stamps.len() as u64).saturating_mul(16));
        self.file.is_some() && self.len > live.saturating_mul(2).saturating_add(REWRITE_SLACK)
    }

    /// A record the log took, counted against its class's room: past it, the log is due a
    /// tick. Nothing for a log no rules this open set retain, or one already due.
    pub(crate) fn note(&mut self, rec: &BrokerRecord) {
        if !self.active || self.due {
            return;
        }
        let Some(rules) = self.rules.as_ref() else {
            return;
        };
        let c = rules.class_of(&rec.subject);
        match (self.taken.get_mut(c), self.room.get(c)) {
            (Some(t), Some(&room)) => {
                *t = t.saturating_add(retention::record_bytes(rec));
                if *t > room {
                    self.due = true;
                }
            }
            _ => self.due = true,
        }
    }

    /// A planning's `room` for each class, nothing taken against it yet: not due.
    pub(crate) fn planned(&mut self, room: Vec<u64>) {
        self.taken = match self.rules.as_ref() {
            Some(r) => r.per_class(0u64),
            None => Vec::new(),
        };
        self.room = room;
        self.due = false;
    }

    /// How many records the store holds.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Bytes on disk taken by `<log>.held` (`0` when no held sidecar is open).
    pub(crate) const fn file_bytes(&self) -> u64 {
        self.len
    }

    /// Whether `<log>.held` is currently open on disk.
    pub(crate) const fn has_file(&self) -> bool {
        self.file.is_some()
    }

    /// Drop the stamps no retained record needs any more.
    pub(crate) fn prune_stamps(&mut self, base: u64) {
        retention::prune_stamps(&mut self.stamps, base);
    }
}

#[cfg(test)]
#[path = "held_tests.rs"]
mod tests;
