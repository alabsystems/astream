// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE OPEN'S CHECKPOINT, `<log>.ckpt`: the open's fold stopped where a unit ended and
//! written down, so the next open takes the fold up there and reads only the frames after
//! it (aterm tracker LT-A7).
//!
//! An open folds every retained record into the indices (`IndexFold`: the exactly-once keys,
//! the last-value map, the bindings, the wills, the group commits and what a compaction
//! carried) and into the residency tier's pages ([`Opening`]), which costs the whole log
//! read and decoded however little of it is new. A checkpoint is that fold's state after the
//! log's first `count` records, with what binds it to them.
//!
//! ONLY A FOLD WRITES ONE. The state is never taken from a serving log's own maps: after a
//! cut those are not what an open would rebuild (a will's settled flag, a producer's last
//! broker time, who is charged for a subject after a cut that carried nothing), and the held
//! head keeps a group commit out of them. It is the state of the open's own fold
//! (`OpenFold`), or of that fold run again over the frames since the last checkpoint
//! ([`BrokerLog::checkpoint`]), so the state an open takes up from one is by construction
//! the state its full scan reaches at that record.
//!
//! WHAT A CHECKPOINT IS BOUND TO, each checked before a byte of its state is used
//! ([`load`]); anything else is the full scan:
//!
//! - the log's identity and generation as `<log>.id` records them (the generation moves
//!   whenever an offset may have come to name another record: a repair's cut, an older copy
//!   restored, a lossy stop), the retention base (a compaction moves every byte), and the
//!   first stored frame's tag;
//! - the byte it ends at, which the file must still reach, and the frame of its last record:
//!   read again where it was, it must be that record, whole, ending a unit, and byte for byte
//!   the frame fingerprinted then;
//! - its own bytes: every frame's CRC, a digest of the whole, and on a log sealed at rest the
//!   log's key, bound to its `.seal` and each frame's place.
//!
//! WHAT IT TRUSTS. A full scan checks every frame below the checkpoint; an open from one
//! does not read them, so damage there is found by the read that meets it, not by the open.
//! That is sound against a power loss because a checkpoint is written only of bytes a full
//! flush had already made durable: the open's own flush, or [`BrokerLog::sync_full`] before
//! the fold is run again. It is not a defence against a device that rots what it stored.
//!
//! Not used, by rule: on a replica (a leader's truncation rewrites below any point and the
//! identity it adopts moves no generation), under an explicit repair (which exists to read
//! every frame), on the simulated device (which keeps no sidecar but `.id`), and with no
//! residency budget (every record is then decoded for the window, which is the scan).

use std::io::Read;

use super::open_scan::{scan_on, unit_end_at, ReadAt, Reading, Resume, Sink};
use super::*;
use crate::logid::LogIdentity;
use crate::tier::{OpenRow, Opening};

/// What the checkpoint's stream starts with: its magic and format.
const MAGIC: &[u8; 5] = b"ASCK\x01";

/// The header's bytes: the magic, the base, the count, the two bytes, the identity and its
/// generation, the two fingerprints, and the length of the state after it.
const HEADER: usize = 5 + 8 + 8 + 8 + 8 + 16 + 8 + 16 + 16 + 8;

/// The digest's bytes, after the state.
const DIGEST: usize = 16;

/// The bytes of the stream a frame of the file holds at most (well under a frame's cap, a
/// sealed one's nonce and tag included).
const CHUNK: usize = 1 << 20;

/// What the digest of a checkpoint's stream is taken under.
const DIGEST_DOMAIN: &[u8] = b"astream-ckpt/1";

/// What the fingerprint of a checkpoint's last frame is taken under.
const FRAME_DOMAIN: &[u8] = b"astream-ckpt/frame/1";

/// Domain-separating AAD of a checkpoint's frames under the log's at-rest key: unbound (a
/// log with no `.seal`), and bound to the `.seal`'s id. The frame's place follows either.
#[cfg(feature = "at-rest")]
const AAD: &[u8; 15] = b"astream-ckpt-v1";
#[cfg(feature = "at-rest")]
const AAD_BOUND: &[u8; 15] = b"astream-ckpt-v2";

#[cfg(test)]
thread_local! {
    /// The opens on this thread that served from a checkpoint, and those that took one up,
    /// failed, and were judged again by the full scan (a test's count, `ckpt_tests.rs`).
    pub(crate) static OPENS: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
}

/// The header of the checkpoint beside the log at `path`, when it reads back whole.
#[cfg(test)]
pub(crate) fn header_of(path: &Path, key: Option<AtRestRef<'_>>) -> Option<Header> {
    read(path, key, u64::MAX).map(|(header, _)| header)
}

/// The checkpoint sidecar's path, `<log>.ckpt`.
pub(crate) fn checkpoint_path(path: &Path) -> PathBuf {
    let mut p = path.to_path_buf();
    p.as_mut_os_string().push(".ckpt");
    p
}

/// Where a checkpoint is staged before it takes its name.
fn staged_path(path: &Path) -> PathBuf {
    let mut p = checkpoint_path(path);
    p.as_mut_os_string().push(".tmp");
    p
}

/// Remove the log's checkpoint and a staged one a crash left: after anything that moves the
/// log's bytes (a compaction's switch, an offline seal), and beside a log just created. The
/// binding refuses a checkpoint of other bytes whether or not this ran; it runs so that
/// subjects and bodies a cut dropped do not outlive it here.
pub(crate) fn discard(path: &Path) {
    let _ = remove_file_path(&checkpoint_path(path));
    let _ = remove_file_path(&staged_path(path));
}

/// Where the checkpoint beside a log stands: the byte of the log it ends at, and the bytes
/// its own state takes (both 0 with none).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Standing {
    pub(crate) at: u64,
    pub(crate) size: u64,
}

/// Whether a checkpoint is due on a log `len` bytes long whose last one stands as `last`
/// says: `every` bytes were written since, and as many as that checkpoint's own state took
/// when that is more. Writing one costs the whole state, which grows with the log's records,
/// so a log whose state has outgrown `every` would otherwise write more checkpoint than log;
/// held to the state's size, the checkpoints never cost more bytes than the records they
/// follow, and the tail an open scans is `every` bytes or one state's worth (about 10 bytes
/// a record of 13 subjects by 8 producers; `ckpt_tests.rs` prints it).
pub(crate) fn due(every: u64, last: Standing, len: u64) -> bool {
    let since = len.saturating_sub(last.at);
    since > 0 && since >= every.max(last.size)
}

/// The most bytes the checkpoint of a log `len` bytes long may take as a file, which the
/// writer holds itself to and the reader refuses to read past (so a file planted at the name
/// cannot make an open read without bound). A state names each live subject three times (in
/// the last-value map, the charges and the rows' table) where the log may name it once, and
/// holds some 30 bytes a record of keys and rows where a frame of a header and a bare record
/// is over 40: four times the log holds both. The allowance holds what a compaction carried,
/// which is in `<log>.state` (one frame, at most 16 MiB) and not in the log at all.
fn cap(len: u64) -> u64 {
    len.saturating_mul(4).saturating_add(64 << 20)
}

/// The bytes a stream of `stream` bytes takes as a file at most: a frame's header a chunk,
/// and a sealed chunk's nonce and tag.
fn file_bytes(stream: u64) -> u64 {
    let chunks = (stream / CHUNK as u64).saturating_add(1);
    stream.saturating_add(chunks.saturating_mul(64))
}

/// What binds a checkpoint to the bytes it was taken of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Header {
    /// The retention base then.
    pub(crate) base: u64,
    /// The records folded: the checkpoint stands at offset `base + count`.
    pub(crate) count: u64,
    /// The byte record `base + count` starts at, where the last unit folded ends.
    pub(crate) len: u64,
    /// The byte the last record folded starts at.
    pub(crate) newest_at: u64,
    /// The log's identity then, as `<log>.id` recorded it.
    pub(crate) identity: LogIdentity,
    /// The first stored frame's tag ([`log_identity`]).
    pub(crate) first: [u8; 16],
    /// The fingerprint of the last record folded, as stored ([`frame_print`]).
    pub(crate) newest: [u8; 16],
}

/// A stored frame's fingerprint, as a checkpoint holds its last record's.
pub(crate) fn frame_print(frame: &[u8]) -> [u8; 16] {
    logid::fnv1a_128(&[FRAME_DOMAIN, frame])
}

impl Header {
    /// The header's bytes, the state after it `body` bytes long.
    fn encode(&self, body: u64) -> [u8; HEADER] {
        let mut out = [0u8; HEADER];
        let mut w = 0usize;
        let mut put = |bytes: &[u8]| {
            let end = w.saturating_add(bytes.len());
            if let Some(dst) = out.get_mut(w..end) {
                dst.copy_from_slice(bytes);
            }
            w = end;
        };
        put(MAGIC);
        put(&self.base.to_le_bytes());
        put(&self.count.to_le_bytes());
        put(&self.len.to_le_bytes());
        put(&self.newest_at.to_le_bytes());
        put(&self.identity.id);
        put(&self.identity.generation.to_le_bytes());
        put(&self.first);
        put(&self.newest);
        put(&body.to_le_bytes());
        out
    }

    /// The header `r` starts with, and the length of the state after it.
    fn decode(r: &mut Reader<'_>) -> Option<(Header, u64)> {
        if r.take(MAGIC.len())? != MAGIC {
            return None;
        }
        let base = r.u64()?;
        let count = r.u64()?;
        let len = r.u64()?;
        let newest_at = r.u64()?;
        let id = r.tag()?;
        let generation = r.u64()?;
        let first = r.tag()?;
        let newest = r.tag()?;
        let body = r.u64()?;
        Some((
            Header {
                base,
                count,
                len,
                newest_at,
                identity: LogIdentity { id, generation },
                first,
                newest,
            },
            body,
        ))
    }
}

// ---------------------------------------------------------------------------------------
// The stream's primitives.
// ---------------------------------------------------------------------------------------

/// `v` as a variable-length integer: seven bits a byte, the low ones first.
fn put_var(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push((v & 0x7f) as u8 | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

/// `to - from` as a variable-length integer that is short for a small step either way.
fn put_step(out: &mut Vec<u8>, from: u64, to: u64) {
    let d = to.wrapping_sub(from) as i64;
    put_var(out, ((d << 1) ^ (d >> 63)) as u64);
}

fn put_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_len(out: &mut Vec<u8>, n: usize) {
    put_var(out, n as u64);
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    put_len(out, b.len());
    out.extend_from_slice(b);
}

fn put_str(out: &mut Vec<u8>, s: &str) {
    put_bytes(out, s.as_bytes());
}

/// A map's entries in key order, so that equal states encode equally.
fn sorted<K: Ord, V>(m: &HashMap<K, V>) -> Vec<(&K, &V)> {
    let mut v: Vec<_> = m.iter().collect();
    v.sort_unstable_by(|a, b| a.0.cmp(b.0));
    v
}

/// The stream being read: every read is `None` past its end or for a value that is not
/// one, and a checkpoint that reads `None` anywhere is not used.
struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Reader<'a> {
        Reader { bytes, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        let taken = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(taken)
    }

    fn left(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    fn u8(&mut self) -> Option<u8> {
        self.take(1)?.first().copied()
    }

    fn flag(&mut self) -> Option<bool> {
        match self.u8()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }

    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }

    fn tag(&mut self) -> Option<[u8; 16]> {
        self.take(16)?.try_into().ok()
    }

    fn var(&mut self) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let b = self.u8()?;
            let low = u64::from(b & 0x7f);
            // The tenth byte holds the one bit left.
            if shift == 63 && low > 1 {
                return None;
            }
            v |= low.checked_shl(shift)?;
            if b & 0x80 == 0 {
                return Some(v);
            }
            shift = shift.checked_add(7)?;
            if shift > 63 {
                return None;
            }
        }
    }

    /// `from` moved by the step [`put_step`] wrote.
    fn step(&mut self, from: u64) -> Option<u64> {
        let z = self.var()?;
        let d = ((z >> 1) as i64) ^ -((z & 1) as i64);
        Some(from.wrapping_add(d as u64))
    }

    /// A count of entries, each at least `least` bytes: never more than the stream has left
    /// to hold, so a count that lies allocates nothing for it.
    fn count(&mut self, least: usize) -> Option<usize> {
        let n = usize::try_from(self.var()?).ok()?;
        if n > self.left() / least.max(1) {
            return None;
        }
        Some(n)
    }

    fn bytes(&mut self) -> Option<&'a [u8]> {
        let n = self.count(1)?;
        self.take(n)
    }

    fn str(&mut self) -> Option<&'a str> {
        core::str::from_utf8(self.bytes()?).ok()
    }

    fn string(&mut self) -> Option<String> {
        self.str().map(str::to_owned)
    }
}

// ---------------------------------------------------------------------------------------
// The state: the indices, then the tier's rows.
// ---------------------------------------------------------------------------------------

fn put_will(out: &mut Vec<u8>, w: &WillRecord) {
    put_u64(out, w.producer_id);
    put_u64(out, w.producer_seq);
    put_str(out, &w.subject);
    put_bytes(out, &w.body);
}

fn take_will(r: &mut Reader<'_>) -> Option<WillRecord> {
    Some(WillRecord {
        producer_id: r.u64()?,
        producer_seq: r.u64()?,
        subject: r.string()?,
        body: r.bytes()?.to_vec(),
    })
}

/// The exactly-once keys, a producer's together and each run of consecutive sequences as its
/// first sequence, its length and its offsets as steps: a producer that publishes `1, 2, 3`
/// at the head costs about a byte a key.
fn put_dedup(out: &mut Vec<u8>, dedup: &crate::dedup::DedupIndex) {
    let keys = dedup.sorted_keys();
    let mut runs = 0u64;
    let mut prev: Option<(u64, u64)> = None;
    for &(pid, seq, _) in &keys {
        if prev != Some((pid, seq.wrapping_sub(1))) || seq == 0 {
            runs = runs.saturating_add(1);
        }
        prev = Some((pid, seq));
    }
    put_var(out, runs);
    let mut i = 0usize;
    while let Some(&(pid, seq0, off0)) = keys.get(i) {
        let mut n = 1usize;
        while let Some(&(p, s, _)) = keys.get(i.saturating_add(n)) {
            if p != pid || Some(s) != seq0.checked_add(n as u64) {
                break;
            }
            n = n.saturating_add(1);
        }
        put_u64(out, pid);
        put_u64(out, seq0);
        put_len(out, n);
        put_var(out, off0);
        let mut last = off0;
        for &(_, _, off) in keys
            .get(i.saturating_add(1)..i.saturating_add(n))
            .unwrap_or(&[])
        {
            put_step(out, last, off);
            last = off;
        }
        i = i.saturating_add(n);
    }
}

fn take_dedup(r: &mut Reader<'_>) -> Option<crate::dedup::DedupIndex> {
    let mut dedup = crate::dedup::DedupIndex::new();
    for _ in 0..r.count(18)? {
        let pid = r.u64()?;
        let seq0 = r.u64()?;
        let n = r.count(1)?;
        if n == 0 {
            return None;
        }
        let mut off = r.var()?;
        dedup.insert(pid, seq0, Offset(off));
        for k in 1..n {
            off = r.step(off)?;
            dedup.insert(pid, seq0.checked_add(k as u64)?, Offset(off));
        }
    }
    dedup.shrink_to_fit();
    Some(dedup)
}

/// The indices as the fold holds them after its last record, every map in key order.
fn put_indices(out: &mut Vec<u8>, f: &IndexFold) -> Option<()> {
    put_dedup(out, &f.dedup);

    put_len(out, f.group_commits.len());
    for (group, &upto) in sorted(&f.group_commits) {
        put_str(out, group);
        put_var(out, upto);
    }

    put_len(out, f.last.len());
    for (subject, off) in &f.last {
        put_str(out, subject);
        put_var(out, off.0);
    }

    put_len(out, f.subject_charges.len());
    for (subject, &pid) in sorted(&f.subject_charges) {
        put_str(out, subject);
        put_u64(out, pid);
    }

    put_len(out, f.subjects_per_producer.len());
    for (&pid, &n) in sorted(&f.subjects_per_producer) {
        put_u64(out, pid);
        put_len(out, n);
    }

    put_len(out, f.durable_latest_wills.len());
    for (&pid, e) in sorted(&f.durable_latest_wills) {
        put_u64(out, pid);
        put_var(out, e.offset.0);
        out.push(u8::from(e.settled_above));
        put_will(out, &e.will);
    }

    put_len(out, f.durable_wills_by_subject.len());
    for (subject, pids) in sorted(&f.durable_wills_by_subject) {
        put_str(out, subject);
        let mut pids: Vec<u64> = pids.iter().copied().collect();
        pids.sort_unstable();
        put_len(out, pids.len());
        for pid in pids {
            put_u64(out, pid);
        }
    }

    put_len(out, f.bind.len());
    for (&pid, (principal, off)) in sorted(&f.bind) {
        put_u64(out, pid);
        put_str(out, principal);
        put_var(out, off.0);
    }

    put_len(out, f.high_water.len());
    for (&pid, &hw) in sorted(&f.high_water) {
        put_u64(out, pid);
        put_u64(out, hw);
    }

    put_len(out, f.carried_wills.len());
    for (&pid, (off, will)) in sorted(&f.carried_wills) {
        put_u64(out, pid);
        put_var(out, off.0);
        put_will(out, will);
    }

    put_len(out, f.carried_last.len());
    for (subject, rec) in &f.carried_last {
        put_str(out, subject);
        put_bytes(
            out,
            &rec.encode_payload_marked_bt(Mark::Unmarked, None).ok()?,
        );
    }

    put_len(out, f.carried_last_bt.len());
    for (subject, &bt) in &f.carried_last_bt {
        put_str(out, subject);
        put_u64(out, bt);
    }

    for charges in [&f.carried_charges, &f.pending_carried_charges] {
        put_len(out, charges.len());
        for (subject, &pid) in charges {
            put_str(out, subject);
            put_u64(out, pid);
        }
    }

    out.push(u8::from(f.uncarried_cut_tainted));
    f.relay_floors.encode(out)?;

    put_len(out, f.producer_last_bt.len());
    for (&pid, &bt) in sorted(&f.producer_last_bt) {
        put_u64(out, pid);
        put_u64(out, bt);
    }
    put_u64(out, f.max_bt);
    Some(())
}

fn take_indices(r: &mut Reader<'_>) -> Option<IndexFold> {
    let dedup = take_dedup(r)?;

    let mut group_commits = HashMap::new();
    for _ in 0..r.count(2)? {
        let group = r.string()?;
        group_commits.insert(group, r.var()?);
    }

    let mut last = BTreeMap::new();
    for _ in 0..r.count(2)? {
        let subject = r.string()?;
        last.insert(subject, Offset(r.var()?));
    }

    let mut subject_charges = HashMap::new();
    for _ in 0..r.count(9)? {
        let subject = r.string()?;
        subject_charges.insert(subject, r.u64()?);
    }

    let mut subjects_per_producer = HashMap::new();
    for _ in 0..r.count(9)? {
        let pid = r.u64()?;
        subjects_per_producer.insert(pid, usize::try_from(r.var()?).ok()?);
    }

    let mut durable_latest_wills = HashMap::new();
    for _ in 0..r.count(28)? {
        let pid = r.u64()?;
        let offset = Offset(r.var()?);
        let settled_above = r.flag()?;
        let will = take_will(r)?;
        durable_latest_wills.insert(
            pid,
            DurableWillEntry {
                offset,
                will,
                settled_above,
            },
        );
    }

    let mut durable_wills_by_subject = HashMap::new();
    for _ in 0..r.count(2)? {
        let subject = r.string()?;
        let mut pids = HashSet::new();
        for _ in 0..r.count(8)? {
            pids.insert(r.u64()?);
        }
        durable_wills_by_subject.insert(subject, pids);
    }

    let mut bind = HashMap::new();
    for _ in 0..r.count(10)? {
        let pid = r.u64()?;
        let principal = r.string()?;
        bind.insert(pid, (principal, Offset(r.var()?)));
    }

    let mut high_water = HashMap::new();
    for _ in 0..r.count(16)? {
        let pid = r.u64()?;
        high_water.insert(pid, r.u64()?);
    }

    let mut carried_wills = HashMap::new();
    for _ in 0..r.count(27)? {
        let pid = r.u64()?;
        let off = Offset(r.var()?);
        carried_wills.insert(pid, (off, take_will(r)?));
    }

    let mut carried_last = BTreeMap::new();
    for _ in 0..r.count(2)? {
        let subject = r.string()?;
        let (rec, mark, bt) = BrokerRecord::from_payload_marked_bt(r.bytes()?)?;
        if mark != Mark::Unmarked || bt.is_some() || rec.subject != subject {
            return None;
        }
        carried_last.insert(subject, Arc::new(rec));
    }

    let mut carried_last_bt = BTreeMap::new();
    for _ in 0..r.count(9)? {
        let subject = r.string()?;
        carried_last_bt.insert(subject, r.u64()?);
    }

    let mut charges = [BTreeMap::new(), BTreeMap::new()];
    for map in &mut charges {
        for _ in 0..r.count(9)? {
            let subject = r.string()?;
            map.insert(subject, r.u64()?);
        }
    }
    let [carried_charges, pending_carried_charges] = charges;

    let uncarried_cut_tainted = r.flag()?;
    let relay_floors = crate::relay_floor::RelayFloors::decode(r.bytes, &mut r.pos)?;

    let mut producer_last_bt = HashMap::new();
    for _ in 0..r.count(16)? {
        let pid = r.u64()?;
        producer_last_bt.insert(pid, r.u64()?);
    }
    let max_bt = r.u64()?;

    Some(IndexFold {
        dedup,
        group_commits,
        last,
        subject_charges,
        subjects_per_producer,
        durable_latest_wills,
        durable_wills_by_subject,
        bind,
        high_water,
        carried_wills,
        carried_last,
        carried_last_bt,
        carried_charges,
        uncarried_cut_tainted,
        relay_floors,
        pending_carried_charges,
        producer_last_bt,
        max_bt,
    })
}

/// The tier's rows: the subjects they name, each once, then a row a record, its subject by
/// its place among those, its `meta`, and its broker time, frame start and charge as steps
/// from the row before (the charge from its own frame bytes).
fn put_rows(out: &mut Vec<u8>, tier: &Opening) -> Option<()> {
    let mut names: Vec<&str> = Vec::new();
    let mut ids: HashMap<&str, u64> = HashMap::new();
    let mut rows = Vec::new();
    let (mut bt_then, mut at_then) = (0u64, 0u64);
    let mut n = 0u64;
    for row in tier.rows()? {
        let row = row?;
        let id = match ids.get(row.subject) {
            Some(&id) => id,
            None => {
                let id = names.len() as u64;
                names.push(row.subject);
                ids.insert(row.subject, id);
                id
            }
        };
        put_var(&mut rows, id);
        rows.extend_from_slice(&row.meta.to_le_bytes());
        if let Some(bt) = row.bt {
            put_step(&mut rows, bt_then, bt);
            bt_then = bt;
        }
        put_step(&mut rows, at_then, row.at);
        at_then = row.at;
        put_step(
            &mut rows,
            u64::from(OpenRow::meta_bytes(row.meta)),
            u64::from(row.cost),
        );
        n = n.saturating_add(1);
    }
    put_len(out, names.len());
    for name in names {
        put_str(out, name);
    }
    put_var(out, n);
    out.extend_from_slice(&rows);
    Some(())
}

/// The rows [`put_rows`] wrote, restored into `tier` as the fold pushed them, the first at
/// offset `header.base`: `header.count` of them, or `None`.
///
/// Each row's frame start is held to what a fold's is, the start of the next frame of one
/// file: the first at byte 0, each after it at least a frame header and at most a whole
/// frame past the one before, none past the checkpoint's last record. A read of a cold
/// record takes its length from two neighbours' starts, so starts no scan could have passed
/// must not reach the tier, whatever wrote them.
fn take_rows(r: &mut Reader<'_>, tier: &mut Opening, header: &Header) -> Option<()> {
    const LEAST: u64 = astream_wire::HEADER_SIZE as u64;
    const MOST: u64 = (astream_wire::HEADER_SIZE + astream_wire::MAX_PAYLOAD_LEN) as u64;
    let mut names: Vec<&str> = Vec::new();
    for _ in 0..r.count(1)? {
        names.push(r.str()?);
    }
    if r.count(7)? as u64 != header.count {
        return None;
    }
    let (mut bt_then, mut at_then) = (0u64, 0u64);
    for i in 0..header.count {
        let subject = names.get(usize::try_from(r.var()?).ok()?)?;
        let meta = r.u32()?;
        let bt = if OpenRow::meta_has_bt(meta) {
            bt_then = r.step(bt_then)?;
            Some(bt_then)
        } else {
            None
        };
        let at = r.step(at_then)?;
        let in_order = match at.checked_sub(at_then) {
            Some(0) => i == 0,
            Some(gap) => i > 0 && (LEAST..=MOST).contains(&gap),
            None => false,
        };
        if !in_order || at > header.newest_at {
            return None;
        }
        at_then = at;
        let cost = u32::try_from(r.step(u64::from(OpenRow::meta_bytes(meta)))?).ok()?;
        tier.restore(
            header.base.checked_add(i)?,
            OpenRow {
                subject,
                meta,
                bt,
                at,
                cost,
            },
        );
    }
    Some(())
}

/// The fold's state after its last record as a checkpoint's stream holds it, room for the
/// header left before it: `None` when the fold did not keep its records' charges, or holds
/// what does not encode.
pub(super) fn encode_state(indices: &IndexFold, tier: &Opening) -> Option<Vec<u8>> {
    let mut out = vec![0u8; HEADER];
    put_indices(&mut out, indices)?;
    put_rows(&mut out, tier)?;
    Some(out)
}

// ---------------------------------------------------------------------------------------
// The file.
// ---------------------------------------------------------------------------------------

/// The AAD of the checkpoint's frame `index` under the log's key.
#[cfg(feature = "at-rest")]
fn frame_aad(seal_id: Option<[u8; 16]>, index: u64) -> Vec<u8> {
    let mut aad = Vec::with_capacity(AAD.len() + 16 + 8);
    match seal_id {
        Some(id) => {
            aad.extend_from_slice(AAD_BOUND);
            aad.extend_from_slice(&id);
        }
        None => aad.extend_from_slice(AAD),
    }
    aad.extend_from_slice(&index.to_le_bytes());
    aad
}

/// Frame `index`'s payload as the file holds it: sealed under the log's key when it has one.
#[cfg(feature = "at-rest")]
fn seal_chunk(key: Option<AtRestRef<'_>>, index: u64, chunk: &[u8]) -> Vec<u8> {
    match key {
        Some(k) => astream_aead::seal(k.key, &frame_aad(k.seal_id, index), chunk),
        None => chunk.to_vec(),
    }
}
#[cfg(not(feature = "at-rest"))]
fn seal_chunk(_key: Option<AtRestRef<'_>>, _index: u64, chunk: &[u8]) -> Vec<u8> {
    chunk.to_vec()
}

/// The bytes of the stream frame `index`'s payload holds, or `None` when it does not open.
#[cfg(feature = "at-rest")]
fn open_chunk(key: Option<AtRestRef<'_>>, index: u64, payload: Vec<u8>) -> Option<Vec<u8>> {
    match key {
        Some(k) => astream_aead::open(k.key, &frame_aad(k.seal_id, index), &payload).ok(),
        None => Some(payload),
    }
}
#[cfg(not(feature = "at-rest"))]
fn open_chunk(_key: Option<AtRestRef<'_>>, _index: u64, payload: Vec<u8>) -> Option<Vec<u8>> {
    Some(payload)
}

/// The digest of a checkpoint's stream: its header and its state.
fn digest(stream: &[u8]) -> [u8; 16] {
    logid::fnv1a_128(&[DIGEST_DOMAIN, stream])
}

/// Write the checkpoint `header` binds, its state `stream` ([`encode_state`]), beside the
/// log at `path`: staged with the log's own permissions (it holds subjects, and the bodies
/// of wills and of what a compaction carried), flushed, and renamed over the last one. The
/// caller has flushed the log in full through `header.len` already. The bytes of the stream
/// written ([`Standing::size`]).
pub(super) fn write(
    path: &Path,
    key: Option<AtRestRef<'_>>,
    header: &Header,
    mut stream: Vec<u8>,
) -> io::Result<u64> {
    let too_large = || io::Error::new(io::ErrorKind::InvalidData, "checkpoint: state too large");
    let body = stream.len().checked_sub(HEADER).ok_or_else(too_large)?;
    let head = header.encode(body as u64);
    match stream.get_mut(..HEADER) {
        Some(dst) => dst.copy_from_slice(&head),
        None => return Err(too_large()),
    }
    let sum = digest(&stream);
    stream.extend_from_slice(&sum);
    let size = stream.len() as u64;
    let perms = std::fs::metadata(path)?.permissions();
    let tmp = staged_path(path);
    let written = (|| {
        let mut f = create_like(&tmp, &perms)?;
        for (index, chunk) in stream.chunks(CHUNK).enumerate() {
            let payload = seal_chunk(key, index as u64, chunk);
            let framed = Frame::new(payload).encode().map_err(|_| too_large())?;
            f.write_all(&framed)?;
        }
        flush_file(&f, &tmp)
    })();
    if let Err(e) = written {
        let _ = remove_file_path(&tmp);
        return Err(e);
    }
    let to = checkpoint_path(path);
    rename_path(&tmp, &to)?;
    sync_parent_dir(&to)?;
    Ok(size)
}

/// The checkpoint beside the log at `path`, whole: its header, and its stream (the state is
/// the bytes after the header's and before the digest's). `None` when there is none, when it
/// is not a regular file of at most `cap` bytes, and when any frame, the key, the digest or
/// the header says it is not one this build wrote whole.
fn read(path: &Path, key: Option<AtRestRef<'_>>, cap: u64) -> Option<(Header, Vec<u8>)> {
    let mut file = open_sidecar(&checkpoint_path(path), cap, false, "checkpoint").ok()??;
    let mut stream = Vec::new();
    let mut index = 0u64;
    while let Some(payload) = crate::proto::read_frame(&mut file).ok()? {
        let chunk = open_chunk(key, index, payload)?;
        // Every frame but the last is a whole chunk: a frame taken out or put in elsewhere
        // moves the rest, which the digest then refuses.
        if chunk.is_empty() || chunk.len() > CHUNK {
            return None;
        }
        stream.extend_from_slice(&chunk);
        index = index.checked_add(1)?;
    }
    let mut extra = [0u8; 1];
    if file.read(&mut extra).ok()? != 0 {
        return None;
    }
    let body_end = stream.len().checked_sub(DIGEST)?;
    let (covered, sum) = stream.split_at_checked(body_end)?;
    if digest(covered) != sum {
        return None;
    }
    let (header, body) = Header::decode(&mut Reader::new(covered))?;
    if usize::try_from(body).ok()? != body_end.checked_sub(HEADER)? {
        return None;
    }
    stream.truncate(body_end);
    Some((header, stream))
}

/// What a log must still be for a checkpoint of it to be taken up ([`load`]).
pub(super) struct Bound<'a> {
    /// The retention base, as `<log>.base` gives it.
    pub(super) base: u64,
    /// The identity `<log>.id` records.
    pub(super) identity: LogIdentity,
    /// The first stored frame's tag ([`log_identity`]).
    pub(super) first: [u8; 16],
    /// The bytes the log holds that a checkpoint may cover: the file's length at an open,
    /// the committed length of a log that serves.
    pub(super) len: u64,
    pub(super) key: Option<AtRestRef<'a>>,
    pub(super) mutation: Mutation,
    /// The negative control (`ReadOpen::unbound_checkpoint`): the identity, the first frame
    /// and the last record's bytes go unchecked.
    #[cfg(test)]
    pub(super) unbound: bool,
}

/// A checkpoint taken up: what bound it, the bytes its state took, and the fold as it stood
/// there.
pub(super) struct Seed {
    pub(super) header: Header,
    pub(super) size: u64,
    pub(super) indices: IndexFold,
    pub(super) tier: Opening,
}

impl Seed {
    /// Where the scan takes the log up after it, for a log whose durable floor is `floor`.
    /// `None` when the floor's record is among those folded and the rows do not say where it
    /// starts.
    pub(super) fn resume(&self, floor: Option<u64>) -> Option<Resume> {
        let count = usize::try_from(self.header.count).ok()?;
        let pos = usize::try_from(self.header.len).ok()?;
        let floor_at = match floor.and_then(|f| f.checked_sub(self.header.base)) {
            Some(i) if i < self.header.count => {
                let at = self.tier.at(usize::try_from(i).ok()?)?;
                Some(usize::try_from(at).ok()?)
            }
            _ => None,
        };
        Some(Resume {
            count,
            pos,
            floor_at,
        })
    }
}

/// THE CHECKPOINT TAKEN UP: the one beside the log at `path`, when it is bound to the log
/// `src` holds as `bound` says (the module's head has the list), its state restored into the
/// fold it was taken of, the tier's rows into `tier()`. `None` for anything else, which is
/// the full scan: a checkpoint is never a reason to refuse an open.
pub(super) fn load(
    src: &(impl ReadAt + ?Sized),
    path: &Path,
    bound: &Bound<'_>,
    tier: impl FnOnce(usize) -> Opening,
) -> Option<Seed> {
    let (header, stream) = read(path, bound.key, cap(bound.len))?;
    #[cfg(test)]
    let unbound = bound.unbound;
    #[cfg(not(test))]
    let unbound = false;
    let same_log = header.identity == bound.identity && header.first == bound.first;
    // No more records than the bytes it covers hold in frames of a header each: the count
    // is what the tier's columns are then reserved for.
    let most = header.len / astream_wire::HEADER_SIZE as u64;
    if header.base != bound.base
        || !(same_log || unbound)
        || header.count == 0
        || header.count > most
        || header.len > bound.len
        || header.newest_at >= header.len
    {
        return None;
    }
    // The last record folded, where it was: still that record, whole, ending a unit, and the
    // bytes fingerprinted then.
    let newest = header.base.checked_add(header.count)?.checked_sub(1)?;
    let frame = unit_end_at(src, bound.key, bound.mutation, header.newest_at, newest).ok()??;
    if header.newest_at.checked_add(frame.len() as u64)? != header.len
        || !(frame_print(&frame) == header.newest || unbound)
    {
        return None;
    }
    let count = usize::try_from(header.count).ok()?;
    let mut r = Reader::new(stream.get(HEADER..)?);
    let indices = take_indices(&mut r)?;
    let mut tier = tier(count);
    take_rows(&mut r, &mut tier, &header)?;
    if r.left() != 0 || tier.len() != count || tier.newest_at() != Some(header.newest_at) {
        return None;
    }
    Some(Seed {
        header,
        size: (stream.len() as u64).saturating_add(DIGEST as u64),
        indices,
        tier,
    })
}

// ---------------------------------------------------------------------------------------
// The fold run again, for a log that serves.
// ---------------------------------------------------------------------------------------

/// The fold of a checkpoint a serving log writes: the indices and the rows alone, up to the
/// record it stops at.
struct Advance {
    indices: IndexFold,
    tier: Opening,
    /// The records still to fold.
    left: usize,
}

impl Sink for Advance {
    fn record(&mut self, rec: BrokerRecord, bt: Option<u64>, at: u64, _: &[u8], _: bool) -> bool {
        if self.left == 0 {
            return false;
        }
        self.indices.fold(&rec, bt);
        self.tier.push(rec, bt, at);
        self.left = self.left.saturating_sub(1);
        self.left > 0
    }
}

impl BrokerLog {
    /// WRITE A CHECKPOINT of this log at its head (`<log>.ckpt`), so that the next open with
    /// a [`resident_budget`](OpenOptions::resident_budget) reads only the frames after it:
    /// `Ok(true)` when one was written, `Ok(false)` when this log takes none now (it is
    /// empty, a replica, on a simulated device, holds its head for a flush that has not
    /// succeeded, its newest record does not end a unit, or its state is larger than an open
    /// would read back: over four times the log and 64 MiB).
    ///
    /// The state it writes is the open's own fold, run over the frames since the last
    /// checkpoint (or, with none that still binds, over the whole log), never this log's
    /// serving maps: so it costs the read and decode of those frames and the write of the
    /// whole state, on the caller's thread, and holds that fold's indices and rows beside the
    /// log's own while it runs. The log is flushed in full first
    /// ([`sync_full`](Self::sync_full)) when a full flush does not already cover its head: a
    /// checkpoint covers only bytes a power loss cannot take.
    ///
    /// [`OpenOptions::checkpoint_every`] has a log used directly call this from the append
    /// that made one due.
    ///
    /// # Errors
    ///
    /// The flush's (which poisons the log as any failed full flush does), a read's or a
    /// write's, `InvalidInput` with a batch staged, and `InvalidData` when the frames below
    /// the head no longer fold to it. None of them leaves a checkpoint that an open would
    /// take up for other bytes: the last one stands, or none.
    pub fn checkpoint(&mut self) -> io::Result<bool> {
        self.check_poisoned()?;
        if !self.dir.is_os() || self.replica || self.closed || self.released {
            return Ok(false);
        }
        if !self.staged.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "checkpoint: a batch is staged; commit or abort it first",
            ));
        }
        let Some(count) = self.next.0.checked_sub(self.base.0).filter(|&n| n > 0) else {
            return Ok(false);
        };
        let Ok(records) = usize::try_from(count) else {
            return Ok(false);
        };
        if self.durable_head < self.next.0 {
            self.sync_full()?;
        }
        if self.durable_head < self.next.0 || self.held_from.is_some() {
            return Ok(false);
        }
        let len = self.durable_len;
        let empty = |n: usize| {
            let expect = crate::tier::Expect {
                records: n.max(records),
                exact: true,
                end: len,
            };
            crate::tier::Tier::opening(0, expect).keeping_costs()
        };
        let seed = load(
            &self.file,
            &self.path,
            &Bound {
                base: self.base.0,
                identity: self.identity.identity,
                first: self.log_id,
                len,
                key: self.at_rest_ref(),
                mutation: Mutation::Off,
                #[cfg(test)]
                unbound: false,
            },
            empty,
        );
        let (mut fold, from) = match seed.and_then(|seed| Some((seed.resume(None)?, seed))) {
            Some((from, seed)) => (
                Advance {
                    indices: seed.indices,
                    tier: seed.tier,
                    left: records.saturating_sub(from.count),
                },
                from,
            ),
            None => (
                Advance {
                    indices: IndexFold::new(read_state(
                        &self.path,
                        self.at_rest_ref(),
                        self.base.0,
                    )?),
                    tier: empty(records),
                    left: records,
                },
                Resume::default(),
            ),
        };
        if fold.left > 0 {
            let scanned = scan_on(
                &self.file,
                Reading::shipped(),
                self.at_rest_ref(),
                self.base.0,
                None,
                Mutation::Off,
                from,
                &mut fold,
            )?;
            if fold.left > 0 || scanned.scan.valid_len as u64 != len {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{}: checkpoint: the log's frames fold to record {} at byte {}, not \
                         to its head {} at byte {len}",
                        self.path.display(),
                        self.base.0.saturating_add(scanned.scan.count as u64),
                        scanned.scan.valid_len,
                        self.next.0,
                    ),
                ));
            }
        }
        let state = encode_state(&fold.indices, &fold.tier).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "checkpoint: the fold's state does not encode",
            )
        })?;
        drop(fold);
        self.write_checkpoint(state)
    }

    /// Write `state`, the fold's after every record this log holds ([`encode_state`]), as the
    /// log's checkpoint: `Ok(false)`, and nothing written, when the newest record is not the
    /// whole frame the log ends with, or does not end a unit (a checkpoint stands only where
    /// one did: the scan that takes it up starts a unit there), or the state is larger than
    /// an open reads back ([`cap`]).
    fn write_checkpoint(&mut self, state: Vec<u8>) -> io::Result<bool> {
        let (Some(count), Some(newest_at)) = (self.next.0.checked_sub(self.base.0), self.newest_at)
        else {
            return Ok(false);
        };
        let Some(newest) = self.next.0.checked_sub(1).filter(|_| count > 0) else {
            return Ok(false);
        };
        let len = self.durable_len;
        let key = self.at_rest_ref();
        let Some(frame) = unit_end_at(&self.file, key, Mutation::Off, newest_at, newest)? else {
            return Ok(false);
        };
        if newest_at.checked_add(frame.len() as u64) != Some(len) {
            return Ok(false);
        }
        // No more than an open would read back ([`cap`]). The state's size stands as the
        // last one's would, so the next is due only once the log has grown by as much.
        let stream = (state.len() as u64).saturating_add(DIGEST as u64);
        if file_bytes(stream) > cap(len) {
            self.checkpoint = Standing {
                at: len,
                size: stream,
            };
            return Ok(false);
        }
        let size = write(
            &self.path,
            key,
            &Header {
                base: self.base.0,
                count,
                len,
                newest_at,
                identity: self.identity.identity,
                first: self.log_id,
                newest: frame_print(&frame),
            },
            state,
        )?;
        self.checkpoint = Standing { at: len, size };
        Ok(true)
    }

    /// At the end of an open, everything it kept flushed in full and its identity settled:
    /// write the checkpoint the open's fold left `state` for, when
    /// [`OpenOptions::checkpoint_every`] asks for one and the one the open took up
    /// (`standing`) no longer binds or is that far behind; else keep `standing` while it
    /// binds, and remove a checkpoint this open could not take up (`looked`) or left behind
    /// (its generation moved, or the log is a replica). A checkpoint is a cache: none of this
    /// fails an open.
    pub(super) fn checkpoint_opened(
        &mut self,
        state: Option<Vec<u8>>,
        standing: Option<(Header, u64)>,
        looked: bool,
    ) {
        let standing =
            standing.filter(|(h, _)| h.identity == self.identity.identity && !self.replica);
        self.checkpoint =
            standing.map_or_else(Standing::default, |(h, size)| Standing { at: h.len, size });
        if let (Some(every), Some(state)) = (self.checkpoint_every, state) {
            if (standing.is_none() || due(every, self.checkpoint, self.durable_len))
                && matches!(self.write_checkpoint(state), Ok(true))
            {
                return;
            }
        }
        if standing.is_none() && (looked || self.replica) {
            discard(&self.path);
        }
    }

    /// After an append: write the checkpoint [`OpenOptions::checkpoint_every`] makes due. A
    /// checkpoint is a cache, so a failure of its own (a read, the write, a state too large)
    /// fails no append, and the next is tried an interval on: a log that cannot write one
    /// does not fold its tail again at every append. The full flush before it is the log's
    /// own ([`sync_full`](Self::sync_full)), and its failure is the log's as any failed full
    /// flush is.
    pub(super) fn checkpoint_if_due(&mut self) {
        let Some(every) = self.checkpoint_every else {
            return;
        };
        if !due(every, self.checkpoint, self.durable_len) {
            return;
        }
        if !matches!(self.checkpoint(), Ok(true)) {
            self.checkpoint.at = self.durable_len;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(seq: u64) -> BrokerRecord {
        BrokerRecord {
            seq: Offset(seq),
            producer_id: 1,
            producer_seq: seq + 1,
            subject: format!("/f/rows/{}", seq % 3),
            body: vec![4u8; 20],
            commit: None,
        }
    }

    fn opening() -> Opening {
        let expect = crate::tier::Expect {
            records: 0,
            exact: false,
            end: 0,
        };
        crate::tier::Tier::opening(0, expect).keeping_costs()
    }

    /// The rows of a fold that pushed five records at `starts`, read back as a checkpoint of
    /// base 7 whose last record starts where the last of them does.
    fn read_back(starts: [u64; 5]) -> Option<Vec<Option<u64>>> {
        let mut pushed = opening();
        for (i, at) in starts.into_iter().enumerate() {
            pushed.push(record(7 + i as u64), Some(1_000 + i as u64), at);
        }
        let mut bytes = Vec::new();
        put_rows(&mut bytes, &pushed)?;
        let header = Header {
            base: 7,
            count: 5,
            len: starts[4] + 60,
            newest_at: starts[4],
            identity: LogIdentity {
                id: [1; 16],
                generation: 0,
            },
            first: [2; 16],
            newest: [3; 16],
        };
        let mut restored = opening();
        let mut r = Reader::new(&bytes);
        take_rows(&mut r, &mut restored, &header)?;
        assert_eq!(r.left(), 0, "the rows' bytes left unread");
        Some((0..5).map(|i| restored.at(i)).collect())
    }

    /// Rows are taken up only as a fold's frame starts are: the first at byte 0, each a
    /// frame's worth past the one before, none past the checkpoint's last. Starts no scan
    /// passes (one before its neighbour, one more than a whole frame on, a first record off
    /// byte 0, two nearer than a header) are refused, whatever wrote them.
    #[test]
    fn rows_are_taken_up_only_at_frame_starts_in_order() {
        let frames = [0u64, 60, 120, 180, 240];
        assert_eq!(
            read_back(frames),
            Some(frames.map(Some).to_vec()),
            "a fold's own rows"
        );
        let most = (astream_wire::HEADER_SIZE + astream_wire::MAX_PAYLOAD_LEN) as u64;
        assert!(read_back([0, most, most + 60, most + 120, most + 180]).is_some());
        let far = 1u64 << 62;
        for (what, starts) in [
            ("a start before its neighbour", [0u64, 120, 60, 180, 240]),
            (
                "a start past a whole frame",
                [0, most + 1, most + 60, most + 120, most + 180],
            ),
            (
                "a start far past its neighbour",
                [0, 60, far, far + 60, far + 120],
            ),
            ("a first record off byte 0", [12, 60, 120, 180, 240]),
            ("two starts nearer than a header", [0, 60, 71, 180, 240]),
            ("two records at one start", [0, 60, 60, 180, 240]),
        ] {
            assert_eq!(read_back(starts), None, "{what} was taken up");
        }
    }

    /// A step either way round trips, at the ends of the range too.
    #[test]
    fn a_step_round_trips_over_the_whole_range() {
        for (from, to) in [
            (0u64, 0u64),
            (0, 1),
            (1, 0),
            (0, u64::MAX),
            (u64::MAX, 0),
            (1 << 63, (1 << 63) - 1),
            (5, 1 << 40),
        ] {
            let mut bytes = Vec::new();
            put_step(&mut bytes, from, to);
            let mut r = Reader::new(&bytes);
            assert_eq!(r.step(from), Some(to), "the step from {from} to {to}");
            assert_eq!(r.left(), 0, "the step's bytes from {from} to {to}");
        }
    }
}
