//! `BrokerLog` — the broker's durable message log: a TIERED (Strict / Relaxed)
//! group-commit log with exactly-once ingest and durable consumer-group commits.
//!
//! Ports the atomic-append rollback and recover-on-open discipline from
//! `astream_engine::store`/`durable` (longest intact in-order prefix) and tightens
//! it: only a TORN TAIL — an incomplete trailing frame, or a zero-filled tail, the
//! signatures of an interrupted write — is truncated on open. A complete-but-corrupt
//! frame, a record-format (`BREC_VERSION`) mismatch, or an offset gap FOLLOWED BY MORE
//! BYTES is corruption, and [`BrokerLog::open_with`] refuses to open rather than
//! silently truncating what may be acked data ([`BrokerLog::open_repair`] is the
//! explicit, data-losing repair). Adds exactly-once **ingest**: a `(producer_id,
//! producer_seq)` idempotency key maps to the original `Offset`, so a re-sent publish
//! is NOT re-appended and returns the offset it first got — the precise pair, NOT the
//! engine's monotonic high-water (which would wrongly reject a producer legitimately
//! re-sending an old seq after a crash). The dedup map and the offset spine are
//! rebuilt from the stored bytes on open, so exactly-once survives a broker restart.
//!
//! The broker's hot path is GROUP COMMIT (`stage_*` + `BrokerLog::commit_batch`):
//! a batch of records is written, then ONE fsync (Strict) or none (Relaxed) covers
//! it. The per-record `publish` / `commit` / `process_and_produce` methods are the
//! un-batched equivalents with the same tier semantics. An open log holds an
//! EXCLUSIVE advisory lock on its file, so two brokers can never serve one log.

use crate::brecord::{BrokerRecord, GroupCommit};
use astream_wire::{Filter, Frame, FrameError, Offset};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::ops::Bound;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Reserved subject for pure (no-output) consumer-group commit records. A wildcard
/// data filter (e.g. `/a/>` or `/a/*`) WOULD match it, so the broker's delivery
/// paths skip this subject explicitly (filter-independently): commit records consume
/// offsets but are never delivered to data subscribers. It is broker-INTERNAL: a
/// publish / process_and_produce / fork replacement on this subject is refused
/// (`StageErr::Reserved`), so the only records that carry it are commit records.
pub const COMMIT_SUBJECT: &str = "/a/commit";

/// Reserved subject for a connection's registered LAST WILL (the record the broker
/// appends on that connection's behalf when it ends). Hidden exactly like
/// [`COMMIT_SUBJECT`]: excluded from dedup, from the [`BrokerLog::last_matching`]
/// index, and from every delivery path, and refused to a client publish by name.
pub const WILL_SUBJECT: &str = "/a/will";

/// Reserved subject for the producer-id BINDING table (`producer id -> principal`,
/// appended when a bound capability first attaches). Hidden exactly like
/// [`COMMIT_SUBJECT`].
pub const BIND_SUBJECT: &str = "/a/bind";

/// Every broker-INTERNAL subject, in one place: a record on one of these consumes an
/// offset but is never delivered, never enters the dedup map, the per-producer
/// high-water map or the last-value index, and is refused to a client publish by
/// name. Kept as one predicate so a new hidden kind cannot be added to the store and
/// forgotten on a delivery path (e.g. commit records reaching a wildcard subscriber).
#[must_use]
pub fn is_hidden_subject(subject: &str) -> bool {
    matches!(subject, COMMIT_SUBJECT | WILL_SUBJECT | BIND_SUBJECT)
}

/// The top half of the producer sequence space, RESERVED for acks.
///
/// An ack derives its `producer_seq` from the OFFSET it acknowledges, which is what
/// makes a retry idempotent, and that derivation has to live somewhere both faces of
/// this crate agree on: the library helper [`crate::ack`] and the `asb ack` CLI verb
/// produce records for the same logical operation, and a bridge will use BOTH. If the
/// two derived different keys for one `(producer_id, offset)`, the broker's dedup would
/// not recognise a retry that crossed faces and the ack would append twice. So the
/// derivation is `ACK_SEQ_BASE | offset` and it is a WIRE CONTRACT, read from this one
/// constant by both.
///
/// It is defined HERE, in the log, and re-exported by the client, because the
/// reservation is a property of the LOG and not a convention of a client: an ack's
/// sequence is derived from an offset, so it is NOT an incarnation, and the last-will
/// fence must not read it as one. `ACK_SEQ_BASE | offset` is above every
/// incarnation-derived sequence a producer will ever publish, so folding acks into the
/// fence's high water would put the fence above every will that producer could register
/// and suppress its goodbye for good. The log keeps the halves apart in both
/// directions: acks never enter [`BrokerLog::producer_high_water`], and a will offered
/// a sequence in this half is REFUSED at registration (`stage_will_register`) rather
/// than accepted and left permanently unfenceable.
pub const ACK_SEQ_BASE: u64 = 1 << 63;

/// A connection's registered LAST WILL: the record the broker appends on that
/// connection's behalf when it ends.
///
/// Persisted as a hidden [`WILL_SUBJECT`] record whose producer fields carry the
/// will's own `(producer_id, producer_seq)` — which is exactly why hidden subjects
/// stay OUT of the dedup map: a will record that entered it would dedup away the very
/// publish it exists to make.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WillRecord {
    /// The producer key the will publishes under (and is deduped by).
    pub producer_id: u64,
    /// The sequence the will publishes under, and the value the FENCE compares
    /// against: a later record from the same producer suppresses it.
    pub producer_seq: u64,
    /// The subject the will publishes to.
    pub subject: String,
    /// The body the will publishes.
    pub body: Vec<u8>,
}

impl WillRecord {
    /// The stored body of a `/a/will` record: `u32 LE subject length ‖ subject ‖ body`.
    /// The producer key rides in the record's own producer fields.
    fn encode_body(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 + self.subject.len() + self.body.len());
        out.extend_from_slice(&(self.subject.len() as u32).to_le_bytes());
        out.extend_from_slice(self.subject.as_bytes());
        out.extend_from_slice(&self.body);
        out
    }

    /// Decode a stored `/a/will` record; `None` on anything malformed (a will the
    /// broker cannot read is one it does not fire).
    fn from_record(rec: &BrokerRecord) -> Option<WillRecord> {
        let len = u32::from_le_bytes(rec.body.get(..4)?.try_into().ok()?) as usize;
        let end = len.checked_add(4)?; // a u32 length can overflow a 32-bit usize
        let subject = String::from_utf8(rec.body.get(4..end)?.to_vec()).ok()?;
        Some(WillRecord {
            producer_id: rec.producer_id,
            producer_seq: rec.producer_seq,
            subject,
            body: rec.body.get(end..)?.to_vec(),
        })
    }
}

/// Cap on how many DISTINCT subjects one producer may create, counted in the
/// last-value index. Distinct subjects grow with history (one presence row per
/// session ever spawned, one ack per member per barrier), and each costs a permanent
/// index entry; a publish that would exceed this is refused. Per PRODUCER because a
/// guarded broker binds a producer id to a capability's principal.
///
/// Enforced on EVERY append path — the staged (group-commit) one the broker's writer
/// uses, and the un-batched [`BrokerLog::publish`] /
/// [`BrokerLog::process_and_produce`] an embedder of the re-exported type calls —
/// from the one predicate, so the two cannot disagree.
pub const MAX_SUBJECTS_PER_PRODUCER: usize = 4096;

/// The longest literal prefix every subject a filter can match must start with: the
/// filter's leading literal segments, terminated by `/`, up to (not including) its
/// first `*` or `>`. `/f/F/pub/*/*/presence` -> `/f/F/pub/`; `/x/>` -> `/x/`; `/>` ->
/// `/`. A wildcard-free filter yields the filter itself — a longer subject that
/// starts with it is still rejected by `Filter::matches`, so the prefix is only ever
/// a range BOUND, never the match.
fn literal_prefix(filter: &Filter) -> String {
    let mut out = String::new();
    for seg in filter.as_str().split('/').skip(1) {
        if seg == "*" || seg == ">" {
            out.push('/');
            return out;
        }
        out.push('/');
        out.push_str(seg);
    }
    out
}

/// A durable, single-writer message log with exactly-once ingest and durable
/// consumer-group commit offsets.
pub struct BrokerLog {
    file: File,
    /// The DURABLE bytes only (recovered prefix + everything a successful batch fsync
    /// has committed). Staged bytes live in `staged_bytes` until `commit_batch`
    /// writes them; a failed write or fsync truncates the file back to here.
    mirror: Vec<u8>,
    /// Committed records, each behind an `Arc` so the egress catch-up (`read_from`)
    /// hands subscribers cheap shared handles instead of deep-copying subject+body.
    records: Vec<Arc<BrokerRecord>>,
    /// The lowest offset still retained (records below it were pruned by retention).
    /// `0` for a never-retained log; recovered from the `<log>.base` sidecar. Kept
    /// records keep their ABSOLUTE offsets — record `i` in `records` has seq
    /// `base + i` — so a consumer's offsets stay meaningful across retention.
    base: Offset,
    next: Offset,
    dedup: HashMap<(u64, u64), Offset>,
    /// LAST-VALUE index: subject -> the offset of that subject's most recent durable
    /// record. Ordered, so a query seeks to a filter's literal prefix in `O(log n)` and
    /// then scans forward under a bound the caller supplies, rather than walking the
    /// whole log — or, for a filter whose matches are sparse inside that prefix, the
    /// whole index. Hidden subjects are excluded, so a retained-state query can never
    /// surface one.
    last: BTreeMap<String, Offset>,
    /// How many distinct subjects each producer has created in `last` (the bound
    /// [`MAX_SUBJECTS_PER_PRODUCER`] is checked against this).
    subjects_per_producer: HashMap<u64, usize>,
    /// Subjects RESERVED by registered wills that have not landed yet, per producer:
    /// a will's TARGET subject, held from the moment its `/a/will` record commits
    /// until a record on that subject lands under the same producer. Counted against
    /// [`MAX_SUBJECTS_PER_PRODUCER`] beside `subjects_per_producer`, because a will
    /// FIRING is exempt from the bound. Without the reservation the check at
    /// registration reads the same count for every live connection, so N connections
    /// registering wills for N DISTINCT new subjects all pass it, and the firings then
    /// take the producer one subject past the cap per connection.
    ///
    /// Rebuilt on open from the log's own `/a/will` records (see
    /// [`pending_wills`](Self::pending_wills)), so a reservation survives a restart.
    ///
    /// DELIBERATELY CONSERVATIVE, always in the direction that keeps the cap. A
    /// reservation is released when a record on that subject lands under that
    /// producer, and NOT when the will is superseded by a replacement for a different
    /// subject, fenced by a later record, or beaten to the subject by another
    /// producer; and while a publish to a reserved subject is STAGED it is counted
    /// both as the batch's pending new subject and as the reservation, until the batch
    /// commits. Each of those holds one extra unit of one producer's budget — never
    /// more than the budget itself, since a registration that would exceed it is
    /// refused — and the next open rebuilds the set from the wills that would actually
    /// fire, at most one per producer. The cost: a producer that registers wills on
    /// many connections for many subjects reaches its cap sooner than its landed
    /// subjects alone would say. The alternative, releasing a reservation a live
    /// connection's will could still use, would let the firings overshoot the cap.
    will_reserved: HashMap<u64, HashSet<String>>,
    /// Per-producer HIGH WATER: the largest `producer_seq` that producer has landed,
    /// over the visible (non-hidden) records. A will FIRES only if nothing above its
    /// own sequence has since landed from the same producer — so a reconnected
    /// producer that publishes at a higher sequence suppresses its previous
    /// incarnation's will structurally, with no reader-side fold.
    high_water: HashMap<u64, u64>,
    /// The path this log was opened from: the log's own name, the stem the replica
    /// marker beside it is derived from, and what the retention compaction rewrites
    /// (with its base sidecar).
    path: PathBuf,
    /// THIS LOG IS A REPLICA: it took a leader's record while it was still empty, or an
    /// operator declared it one. Durable, in the `<log>.replica` marker beside the
    /// file, because the property must survive the restart it exists to make safe. A
    /// replica's log is the leader's spine and NOTHING may be appended to it on this
    /// broker's own initiative — in particular no will may FIRE here (see
    /// [`stage_will_fire`](Self::stage_will_fire)); its wills fire on the leader and
    /// arrive by replication like every other record.
    replica: bool,
    /// The producer-id BINDING table: `producer id -> (principal, the offset of the
    /// /a/bind record that bound it)`. Rebuilt on open from those records, so a
    /// binding survives a broker restart. It is belt-and-braces on top of the 64-bit
    /// second-preimage cost of `producer_id_of`: two DIFFERENT principals that derive
    /// one id cannot both attach.
    bind: HashMap<u64, (String, Offset)>,
    /// Per-group last fully-processed offset (resume is `upto + 1`). Rebuilt from
    /// the records' `commit` annotations on open, so it survives a broker restart.
    group_commits: HashMap<String, u64>,
    /// Records staged into the in-flight batch, with their encoded frames
    /// (`staged_bytes`) and an in-batch dedup view. They reach the file and become
    /// durable (promoted into `records`/`dedup`/`group_commits`/`mirror`, advancing
    /// `next`) only when [`commit_batch`](Self::commit_batch) writes and fsyncs them —
    /// this is group commit: one write and one fsync amortized over a whole batch,
    /// with the SAME Strict durability contract (ack ⟹ fsync'd).
    staged: Vec<BrokerRecord>,
    staged_bytes: Vec<u8>,
    staged_dedup: HashMap<(u64, u64), Offset>,
    /// Subjects the in-flight batch would ADD to `last`, per producer — so the
    /// distinct-subject bound counts a batch's own new subjects too and one batch
    /// cannot overshoot it.
    staged_new_subjects: HashMap<u64, HashSet<String>>,
    /// Bindings the in-flight batch would add, so two `Attach`es inside one batch
    /// see each other's binding instead of both appending.
    staged_bind: HashMap<u64, (String, Offset)>,
    /// What an `ack` promises (see [`Durability`]). Strict fsyncs each batch; Relaxed
    /// skips the fsync (ack on page-cache write).
    durability: Durability,
    /// `Some(reason)` once the file or its sidecars no longer provably match this
    /// state: a failed batch could not be rolled back (the truncate itself failed), a
    /// retention rewrite failed half-way, or the anti-rollback watermark could not be
    /// advanced over promoted records. Every further mutation is refused until the log
    /// is reopened (the recovery scan re-establishes the prefix). Without this, after
    /// a failed rollback the next batch would append records with the SAME seqs after
    /// the orphaned suffix, and recovery would resurrect the rolled-back records and
    /// drop the acked ones.
    poisoned: Option<String>,
    /// The documented fault-injection seam ([`inject_faults`](Self::inject_faults)).
    faults: InjectedFaults,
    /// Encrypt-at-rest key. `Some` seals every record's payload on disk under
    /// XChaCha20-Poly1305 (bound to its log index as AAD); `None` writes plaintext
    /// frames. Set only by the `open_encrypted*` constructors. The key is never
    /// written to the log.
    at_rest_key: Option<[u8; 32]>,
    /// Anti-rollback: when `Some(path)`, an authenticated monotonic head watermark is
    /// maintained in the sidecar at `path` after every durable commit, and checked on
    /// open — so a write-capable attacker cannot silently truncate the log to an
    /// earlier state (per-record sealing alone leaves each surviving record valid).
    /// Requires an at-rest key.
    #[cfg_attr(not(feature = "anti-rollback"), allow(dead_code))]
    head_watermark: Option<PathBuf>,
}

/// How `open_inner` treats the anti-rollback head watermark.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AntiRollbackMode {
    /// No watermark maintained or checked (the default, and every non-encrypted path).
    Off,
    /// Require + verify the watermark: refuse if the log head is below it (rollback)
    /// or the sidecar is missing on a non-empty log (deleted).
    #[cfg(feature = "anti-rollback")]
    Verify,
    /// Establish/bootstrap the watermark at the current head (first adoption) without
    /// requiring a prior sidecar.
    #[cfg(feature = "anti-rollback")]
    Init,
}

/// AAD binding the head-watermark sidecar to its purpose (domain separation from the
/// record-sealing AAD, which is a bare u64 index).
#[cfg(feature = "anti-rollback")]
const HW_AAD: &[u8] = b"astream-anti-rollback-v1";

/// The sidecar path for a log at `path`.
#[cfg(feature = "anti-rollback")]
fn watermark_path(path: &Path) -> PathBuf {
    let mut s = path.as_os_str().to_os_string();
    s.push(".hw");
    PathBuf::from(s)
}

/// The retention base-offset sidecar path for a log at `path`.
#[cfg(feature = "retention")]
fn base_path(path: &Path) -> PathBuf {
    let mut s = path.as_os_str().to_os_string();
    s.push(".base");
    PathBuf::from(s)
}

/// Read the persisted retention base offset (`0` / `Offset::ZERO` if none). A base
/// that does not match the recovered records is caught by scan's `seq == base + i`
/// check (a mismatch is a Corrupt tail), so a tampered base cannot silently reindex.
fn read_base(path: &Path) -> io::Result<Offset> {
    #[cfg(feature = "retention")]
    {
        match std::fs::read(base_path(path)) {
            Ok(b) => {
                let arr: [u8; 8] = b.as_slice().try_into().map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "retention: malformed base offset",
                    )
                })?;
                Ok(Offset(u64::from_le_bytes(arr)))
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(Offset::ZERO),
            Err(e) => Err(e),
        }
    }
    #[cfg(not(feature = "retention"))]
    {
        let _ = path;
        Ok(Offset::ZERO)
    }
}

/// Create `path` as a NEW file, first removing whatever entry holds the name. The
/// log's sidecars are written at fixed names beside it, and `create_new` (O_EXCL)
/// never follows a symlink: a link planted at one of those names by someone who can
/// write the log directory cannot redirect the write onto another file.
fn create_fresh(path: &Path, opts: &mut OpenOptions) -> io::Result<File> {
    match std::fs::remove_file(path) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    opts.write(true).create_new(true).open(path)
}

/// Durably persist the retention base offset via tmp-file rename.
#[cfg(feature = "retention")]
fn write_base(path: &Path, base: u64) -> io::Result<()> {
    let bp = base_path(path);
    let mut tmp = bp.as_os_str().to_os_string();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    {
        let mut f = create_fresh(&tmp, &mut OpenOptions::new())?;
        f.write_all(&base.to_le_bytes())?;
        f.sync_all()?;
    }
    std::fs::rename(&tmp, &bp)?;
    sync_parent_dir(&bp)?;
    Ok(())
}

/// A per-log identity derived from the log's own sealed content: the authentication
/// tag of the FIRST record's sealed frame. It is unique per log (the first record's
/// nonce is random), survives truncation (record 0 always remains), and cannot be
/// produced for a given log without the key. Binding it into the watermark stops a
/// key-less attacker from splicing a DIFFERENT same-key log's watermark onto this one
/// (a watermark from log B carries log B's identity). `[0; 16]` for an empty log.
#[cfg(feature = "anti-rollback")]
fn log_identity(durable_frames: &[u8]) -> [u8; 16] {
    if let Ok(Some(d)) = Frame::decode(durable_frames) {
        let p = &d.frame.payload;
        if p.len() >= 16 {
            let mut id = [0u8; 16];
            id.copy_from_slice(&p[p.len() - 16..]);
            return id;
        }
    }
    [0u8; 16]
}

/// Read + authenticate the persisted watermark, returning `(log_identity, base, head)`.
/// `Ok(None)` if the sidecar does not exist; `Err` if it exists but fails to
/// authenticate (tampered or wrong key).
#[cfg(feature = "anti-rollback")]
fn read_watermark(path: &Path, key: &[u8; 32]) -> io::Result<Option<([u8; 16], u64, u64)>> {
    match std::fs::read(path) {
        Ok(bytes) => {
            let pt = astream_aead::open(key, HW_AAD, &bytes).map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "anti-rollback: the head-watermark sidecar failed to authenticate (tampered or wrong key)",
                )
            })?;
            if pt.len() != 32 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "anti-rollback: malformed watermark",
                ));
            }
            let mut id = [0u8; 16];
            id.copy_from_slice(&pt[..16]);
            let base = u64::from_le_bytes(pt[16..24].try_into().unwrap());
            let head = u64::from_le_bytes(pt[24..32].try_into().unwrap());
            Ok(Some((id, base, head)))
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Durably (re)write the authenticated watermark to `(log_id, base, head)` via a
/// tmp-file rename, so a crash never leaves a torn watermark. Binding `base` too
/// keeps the (unauthenticated) retention base sidecar from being tampered under an
/// anti-rollback log. Monotone by construction (the caller only advances head).
#[cfg(feature = "anti-rollback")]
fn write_watermark(
    path: &Path,
    key: &[u8; 32],
    log_id: &[u8; 16],
    base: u64,
    head: u64,
) -> io::Result<()> {
    let mut pt = [0u8; 32];
    pt[..16].copy_from_slice(log_id);
    pt[16..24].copy_from_slice(&base.to_le_bytes());
    pt[24..].copy_from_slice(&head.to_le_bytes());
    let sealed = astream_aead::seal(key, HW_AAD, &pt);
    let mut tmp = path.as_os_str().to_os_string();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    {
        let mut f = create_fresh(&tmp, &mut OpenOptions::new())?;
        f.write_all(&sealed)?;
        f.sync_all()?;
    }
    std::fs::rename(&tmp, path)?;
    sync_parent_dir(path)?;
    Ok(())
}

/// Seal a record's payload for disk under the at-rest key (bound to its log index
/// as AAD so a record cannot be moved/duplicated within the log), or pass it
/// through when no key is set.
#[cfg(feature = "at-rest")]
fn seal_disk_payload(key: Option<&[u8; 32]>, index: u64, payload: Vec<u8>) -> Vec<u8> {
    match key {
        Some(k) => astream_aead::seal(k, &index.to_le_bytes(), &payload),
        None => payload,
    }
}
#[cfg(not(feature = "at-rest"))]
fn seal_disk_payload(_key: Option<&[u8; 32]>, _index: u64, payload: Vec<u8>) -> Vec<u8> {
    payload
}

/// Open a disk record's payload: `Some(plaintext)` on success, `None` if a key is
/// set and the payload fails to authenticate (wrong key or a tampered record).
#[cfg(feature = "at-rest")]
fn open_disk_payload(
    key: Option<&[u8; 32]>,
    index: u64,
    frame_payload: Vec<u8>,
) -> Option<Vec<u8>> {
    match key {
        Some(k) => astream_aead::open(k, &index.to_le_bytes(), &frame_payload).ok(),
        None => Some(frame_payload),
    }
}
#[cfg(not(feature = "at-rest"))]
fn open_disk_payload(
    _key: Option<&[u8; 32]>,
    _index: u64,
    frame_payload: Vec<u8>,
) -> Option<Vec<u8>> {
    Some(frame_payload)
}

/// A point on the durability dial — what an `ack` promises. Orthogonal to the
/// determinism dial; every setting is benchmarkable and its guarantee is stated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Durability {
    /// `ack` ⟹ the batch is `fsync`'d to disk. Survives single-node power loss. The
    /// default and the strictest tier (stricter than the usual-suspects' defaults).
    Strict,
    /// `ack` ⟹ the batch is written to the OS page cache (NO `fsync`). Survives a
    /// process crash (`kill -9` — the bytes are already in the kernel) but NOT a power
    /// loss. Crash-CONSISTENT regardless: recovery still keeps the longest intact
    /// in-order prefix, so a torn tail is dropped, never corrupted. Lowest latency /
    /// highest throughput (no fsync on the hot path), comparable to Redis
    /// `appendfsync=no` / Kafka `acks=1`. The honest move is surfacing this choice, not
    /// hiding a durability difference inside a benchmark.
    Relaxed,
}

/// A DOCUMENTED fault-injection seam: make the log's fsync and/or its rollback
/// truncate fail, so the failed-fsync rollback and the failed-rollback POISON paths
/// can be witnessed by the claim tests without a real disk fault. Integration tests
/// link the library without `cfg(test)`, so this is always compiled; it is inert
/// unless armed, and nothing in the broker arms it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct InjectedFaults {
    /// Every `fsync` of the log fails (the batch is rolled back, nothing acked).
    pub sync: bool,
    /// Every rollback truncate fails (the log poisons itself).
    pub truncate: bool,
}

/// Why staging a record into the current batch failed.
#[derive(Debug)]
pub(crate) enum StageErr {
    /// The encoded record exceeds the frame limit — an op-level error; the file is
    /// untouched, so the batch can still commit its other records.
    TooLarge,
    /// The subject is one of the broker-internal hidden subjects — an op-level error;
    /// a client cannot append a record there (it would bypass dedup and never be
    /// delivered). Carries the subject so the refusal names it.
    Reserved(String),
    /// This producer already owns [`MAX_SUBJECTS_PER_PRODUCER`] distinct subjects and
    /// the record would create one more — an op-level error; the file is untouched.
    SubjectBound(String),
    /// A will did not fire: a record with a HIGHER `producer_seq` from the same
    /// producer has landed since it was registered. Not a failure — the intended
    /// outcome of the fence.
    Fenced(String),
    /// A producer id is already bound to a DIFFERENT principal — an op-level error;
    /// the file is untouched and the attach is refused.
    Collision(String),
    /// A replicated record does not extend this log's spine (a gap, or a different
    /// record already held at that offset) — an op-level error naming the offset.
    Diverged(String),
    /// A will was offered a `producer_seq` in the reserved ack half
    /// ([`ACK_SEQ_BASE`]) — an op-level error refused at REGISTRATION, where the
    /// client is still listening; the file is untouched.
    SeqReserved(String),
    /// A replicated HIDDEN record (`/a/will`, `/a/bind`) was offered to a log this
    /// broker OWNS — an op-level error; the file is untouched. Decided in the writer,
    /// under the lock that appends, because "whose log is this" is only settled there:
    /// carries the whole message, which is the same wording the connection thread's
    /// early refusal uses.
    ReservedReplica(String),
    /// The log is a REPLICA and the op would have appended a record of this broker's
    /// OWN making (a will firing at open). Not a failure — the intended outcome of
    /// the leader/replica split; the file is untouched.
    Replica(String),
    /// An I/O error while staging (the replica marker could not be written) — the
    /// batch is poisoned and must be aborted. Also raised for every mutation once the
    /// log is [poisoned](BrokerLog#poison).
    Io(io::Error),
}

/// The one wording every path uses to refuse a hidden subject, so the CLI, the
/// library and the wire all say the same thing.
pub(crate) fn reserved_msg(subject: &str) -> String {
    format!("reserved subject {subject}: broker-internal (consumer-group commits, wills and producer bindings are the broker's own records)")
}

/// The PURE COMMIT shape: a leader's own `/a/commit` record, which carries a group
/// commit and nothing else (no producer key, no body). The one hidden record shape a
/// client-reachable `Replicate` may carry onto any log — it appends no publish and
/// grants nothing `Request::Commit` does not already grant.
fn is_pure_commit(rec: &BrokerRecord) -> bool {
    rec.subject == COMMIT_SUBJECT
        && rec.producer_id == 0
        && rec.producer_seq == 0
        && rec.body.is_empty()
        && rec.commit.is_some()
}

/// The one wording for a replicated HIDDEN record offered to a log this broker owns,
/// used by the connection thread's early refusal and by the writer's own check under
/// the lock, so the two cannot say different things about the same frame.
pub(crate) fn replicated_reserved_msg(subject: &str) -> String {
    format!(
        "reserved subject {subject}: this broker OWNS its log, and only a replication \
         target takes a replicated {subject} record (a follower seeded from a copied log \
         is declared with Broker::open_replica)"
    )
}

fn reserved_err(subject: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, reserved_msg(subject))
}

/// The one wording for the distinct-subject bound.
pub(crate) fn subject_bound_msg(producer_id: u64) -> String {
    format!(
        "producer {producer_id} already holds {MAX_SUBJECTS_PER_PRODUCER} distinct subjects \
         (MAX_SUBJECTS_PER_PRODUCER): a new subject would grow the last-value index without bound"
    )
}

/// Take the exclusive advisory lock on the log file, failing `AlreadyExists` if
/// another open `BrokerLog` (in this or any process) holds it. A filesystem without
/// advisory locks is tolerated (the lock is a guard, not the durability mechanism).
/// The OS releases the lock when the process dies, so a crashed broker never leaves a
/// stale lock behind (unlike a lock FILE would).
// `File::try_lock` / `unlock` are std-stable since 1.89; the toolchain is pinned at
// 1.95 by rust-toolchain.toml, only the workspace's declared `rust-version` (1.85) lags.
fn lock_exclusive(file: &File, path: &Path) -> io::Result<()> {
    match file.try_lock() {
        Ok(()) => Ok(()),
        Err(std::fs::TryLockError::WouldBlock) => Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "log {} is locked by another open BrokerLog (a broker already serves it)",
                path.display()
            ),
        )),
        Err(std::fs::TryLockError::Error(e)) if e.kind() == io::ErrorKind::Unsupported => Ok(()),
        Err(std::fs::TryLockError::Error(e)) => Err(e),
    }
}

/// What the replica marker file holds — prose for an operator who finds it, since
/// only its EXISTENCE is load-bearing.
const REPLICA_MARKER_NOTE: &[u8] = b"astream-broker: this log is a REPLICATION TARGET.\n\
    Its records are a leader's spine; this broker appends nothing of its own to it\n\
    (in particular it does not fire the wills the log holds when it opens).\n";

/// The REPLICA MARKER beside a log: `<log>.replica`, an empty-but-for-a-comment file
/// whose mere EXISTENCE records that this log is a replication TARGET — that it took
/// its first replicated record through [`stage_replica`](BrokerLog::stage_replica)
/// while it was still empty, or that an operator declared it one.
///
/// It cannot live IN the log: every byte of the log is the leader's spine, so a
/// marker record would be exactly the divergence the marker exists to prevent.
///
/// THE UNDO IS THE FILE. There is no verb that un-declares a replica, because the
/// declaration is the file: delete `<log>.replica` and the next open reads a log this
/// broker owns again, which fires the wills it holds. That is the whole of the repair
/// for a follower declared by mistake, and it is what the stderr line
/// [`mark_replica`](BrokerLog::mark_replica) prints on the first write points at.
fn replica_marker_path(path: &Path) -> std::path::PathBuf {
    let mut p = path.as_os_str().to_os_string();
    p.push(".replica");
    std::path::PathBuf::from(p)
}

/// fsync the directory that names `path` (a just-created log, or a sidecar just
/// created or renamed into place), so the directory entry — not only the file's data
/// — survives a power loss. `sync_data` on the file alone never persists the entry
/// that names it.
#[cfg(unix)]
fn sync_parent_dir(path: &Path) -> io::Result<()> {
    let parent = match path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    match File::open(parent).and_then(|d| d.sync_all()) {
        Ok(()) => Ok(()),
        // The directory entry simply cannot be fsync'd here, through no fault of the
        // log: a filesystem that refuses to fsync a directory handle (Unsupported /
        // InvalidInput), or a directory this process may write but not OPEN — a
        // write-only 0300 log directory, where opening the log itself is allowed.
        // The file's own bytes are still fsync'd; there is nothing more we can do
        // about the entry, and FAILING here would refuse a log that opens fine.
        Err(e)
            if matches!(
                e.kind(),
                io::ErrorKind::Unsupported
                    | io::ErrorKind::InvalidInput
                    | io::ErrorKind::PermissionDenied
                    | io::ErrorKind::NotFound
            ) =>
        {
            Ok(())
        }
        Err(e) => Err(e),
    }
}
#[cfg(not(unix))]
fn sync_parent_dir(_path: &Path) -> io::Result<()> {
    Ok(())
}

/// Open (creating if absent) and exclusively lock the log file, then fsync its
/// directory, returning whether this call created the file. `sync_dir` is
/// [`sync_parent_dir`], injectable so a test can see it.
fn open_log_file(path: &Path, sync_dir: fn(&Path) -> io::Result<()>) -> io::Result<(File, bool)> {
    let (file, created) = match OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(f) => (f, true),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            (OpenOptions::new().read(true).write(true).open(path)?, false)
        }
        Err(e) => return Err(e),
    };
    lock_exclusive(&file, path)?;
    // On EVERY open, not only the one that creates the file: that open may have died
    // (or failed) before its directory fsync, and a record acked into a file whose
    // entry is not durable can vanish with it on a power loss.
    sync_dir(path)?;
    Ok((file, created))
}

impl BrokerLog {
    /// Open (creating if absent) the log at `path` with Strict durability.
    pub fn open(path: impl AsRef<Path>) -> io::Result<BrokerLog> {
        Self::open_with(path, Durability::Strict)
    }

    /// Open (creating if absent) the log at `path` at the given [`Durability`],
    /// recovering the longest intact, in-order prefix and rebuilding the offset spine +
    /// dedup map from it. (Recovery is identical for both tiers — both keep a clean
    /// prefix; the tier only changes whether an `ack` waits for `fsync`.)
    ///
    /// Recovery distinguishes a TORN TAIL from CORRUPTION: an incomplete trailing
    /// frame or a zero-filled tail (an interrupted write) is truncated, durably. A
    /// complete frame that does not decode (bad CRC/magic/version), a record whose
    /// payload does not parse (a `BREC_VERSION` mismatch — e.g. an older-format log —
    /// or a foreign file), or an offset gap, when MORE BYTES FOLLOW or the frame is
    /// itself complete, is corruption: this returns `InvalidData` naming the offset
    /// and byte, and leaves the file UNTOUCHED. Use [`open_repair`](Self::open_repair)
    /// to truncate at that point explicitly.
    ///
    /// Takes an exclusive advisory lock on the file: a second open of the same log
    /// (this or another process) fails `AlreadyExists` until the first is closed. On a
    /// fresh file the parent directory is fsync'd, so the entry naming the log survives
    /// a power loss along with the data later fsync'd into it.
    pub fn open_with(path: impl AsRef<Path>, durability: Durability) -> io::Result<BrokerLog> {
        Self::open_inner(
            path.as_ref(),
            durability,
            false,
            None,
            AntiRollbackMode::Off,
        )
        .map(|(log, _)| log)
    }

    /// Open (creating if absent) an ENCRYPT-AT-REST log: every record's payload is
    /// sealed on disk under `key` (XChaCha20-Poly1305, random nonce, log-index AAD),
    /// so a reader of the file recovers nothing without it. A wrong key or a tampered
    /// record is a corrupt-tail error (refuse to open), never a silent truncation —
    /// encrypted data is never discarded. Strict durability.
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted(path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<BrokerLog> {
        Self::open_inner(
            path.as_ref(),
            Durability::Strict,
            false,
            Some(key),
            AntiRollbackMode::Off,
        )
        .map(|(log, _)| log)
    }

    /// [`open_encrypted`](Self::open_encrypted) at a chosen [`Durability`].
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted_with(
        path: impl AsRef<Path>,
        durability: Durability,
        key: [u8; 32],
    ) -> io::Result<BrokerLog> {
        Self::open_inner(
            path.as_ref(),
            durability,
            false,
            Some(key),
            AntiRollbackMode::Off,
        )
        .map(|(log, _)| log)
    }

    /// Like [`open_with`](Self::open_with) but TRUNCATES at a corruption point instead
    /// of refusing to open, returning the log and the number of bytes discarded (the
    /// corrupt record and everything after it — possibly acked data; this is the
    /// explicit, operator-invoked repair, never the default). A clean log or a merely
    /// torn tail opens exactly as `open_with` would.
    pub fn open_repair(
        path: impl AsRef<Path>,
        durability: Durability,
    ) -> io::Result<(BrokerLog, u64)> {
        Self::open_inner(path.as_ref(), durability, true, None, AntiRollbackMode::Off)
    }

    /// Open an ENCRYPT-AT-REST log with ANTI-ROLLBACK: an authenticated monotonic head
    /// watermark (a `<log>.hw` sidecar) is maintained after every durable commit and
    /// verified on open. A log truncated/rolled back below the watermark — or a
    /// watermark sidecar missing (deleted) on a non-empty log — is REFUSED, so a
    /// write-capable attacker cannot silently revert the log to an earlier state
    /// without the key. Use [`open_encrypted_verified_init`](Self::open_encrypted_verified_init)
    /// ONCE to establish the watermark the first time anti-rollback is enabled.
    #[cfg(feature = "anti-rollback")]
    pub fn open_encrypted_verified(path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<BrokerLog> {
        Self::open_inner(
            path.as_ref(),
            Durability::Strict,
            false,
            Some(key),
            AntiRollbackMode::Verify,
        )
        .map(|(log, _)| log)
    }

    /// Bootstrap [`open_encrypted_verified`](Self::open_encrypted_verified): establish
    /// the head watermark at the current head without requiring a prior sidecar (first
    /// adoption). This one open cannot detect a rollback that predates the watermark.
    #[cfg(feature = "anti-rollback")]
    pub fn open_encrypted_verified_init(
        path: impl AsRef<Path>,
        key: [u8; 32],
    ) -> io::Result<BrokerLog> {
        Self::open_inner(
            path.as_ref(),
            Durability::Strict,
            false,
            Some(key),
            AntiRollbackMode::Init,
        )
        .map(|(log, _)| log)
    }

    /// Verify (or establish) the anti-rollback head watermark on open, returning the
    /// sidecar path to maintain (or `None` when anti-rollback is off).
    #[cfg(feature = "anti-rollback")]
    fn open_watermark(
        mode: AntiRollbackMode,
        path: &Path,
        key: Option<&[u8; 32]>,
        durable: &[u8],
        base: u64,
        head: u64,
    ) -> io::Result<Option<PathBuf>> {
        if mode == AntiRollbackMode::Off {
            return Ok(None);
        }
        let key = key.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "anti-rollback requires an at-rest key",
            )
        })?;
        let hw = watermark_path(path);
        let log_id = log_identity(durable);
        match read_watermark(&hw, key)? {
            Some((persisted_id, persisted_base, persisted_head)) => {
                if head < persisted_head {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "anti-rollback: log head {head} is BELOW the persisted watermark \
                             {persisted_head} — the log was truncated or rolled back"
                        ),
                    ));
                }
                // Bind to THIS log. A non-empty log's watermark always carries this
                // log's identity — the first commit binds it before writing a byte
                // (`prebind_watermark`) — so a watermark spliced from a DIFFERENT
                // same-key log (its own identity), or an unbound zero one, is refused:
                // a key-less attacker cannot mint a matching one. A log AHEAD of its own
                // bound watermark is only the crash lag advanced below.
                //
                // An EMPTY log has no identity. It may sit under an unbound watermark,
                // or under a pre-bind whose records never landed — at exactly this base
                // and head. A bound watermark any other empty log sits under is a log
                // truncated away with its base sidecar moved up to hide it.
                let bound = if head > base {
                    persisted_id == log_id
                } else {
                    persisted_id == [0u8; 16] || (persisted_base, persisted_head) == (base, head)
                };
                if !bound {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "anti-rollback: the watermark does not belong to this log \
                         (foreign or stale watermark / cross-log splice)",
                    ));
                }
                // The authenticated watermark also pins the retention base, so a
                // tampered (unauthenticated) base sidecar cannot silently reindex the
                // log under anti-rollback. A base BELOW the watermark's is a rollback;
                // ahead is only the benign crash-lag advanced below.
                if base < persisted_base {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "anti-rollback: retention base {base} is BELOW the persisted \
                             base {persisted_base} — the base sidecar was rolled back or tampered"
                        ),
                    ));
                }
                // The log committed/compacted past the last watermark write (a crash
                // between the record/base durability and the watermark update): advance.
                if head > persisted_head || base > persisted_base {
                    write_watermark(&hw, key, &log_id, base, head)?;
                }
            }
            None => {
                if mode == AntiRollbackMode::Verify && head > 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "anti-rollback: the head-watermark sidecar is missing on a non-empty log \
                         (deleted?) — re-establish it with open_encrypted_verified_init",
                    ));
                }
                write_watermark(&hw, key, &log_id, base, head)?;
            }
        }
        Ok(Some(hw))
    }

    #[cfg(not(feature = "anti-rollback"))]
    fn open_watermark(
        _mode: AntiRollbackMode,
        _path: &Path,
        _key: Option<&[u8; 32]>,
        _durable: &[u8],
        _base: u64,
        _head: u64,
    ) -> io::Result<Option<PathBuf>> {
        Ok(None)
    }

    /// Advance the anti-rollback head watermark to the current head after a durable
    /// commit. FAIL-CLOSED: the write is propagated, so a batch is not acked unless its
    /// head is durably covered by the watermark — the invariant `persisted >= every
    /// acked head` is what makes a below-watermark head on open a sound rollback signal.
    /// (A no-op when anti-rollback is off.)
    #[cfg(feature = "anti-rollback")]
    fn advance_watermark(&self) -> io::Result<()> {
        if let (Some(hw), Some(key)) = (&self.head_watermark, self.at_rest_key.as_ref()) {
            let log_id = log_identity(&self.mirror);
            write_watermark(hw, key, &log_id, self.base.0, self.next.0)?;
        }
        Ok(())
    }

    #[cfg(not(feature = "anti-rollback"))]
    fn advance_watermark(&self) -> io::Result<()> {
        Ok(())
    }

    /// Before the first record of an EMPTY log is written, bind the watermark to the
    /// identity that record will give the log (at the unchanged head). Otherwise a
    /// crash between that record's fsync and the watermark update after it leaves a
    /// non-empty log under an unbound watermark, which a verified open must refuse
    /// (it is also what a watermark spliced from a fresh log looks like) — where
    /// this way it is only a log ahead of its own watermark, the ordinary crash lag.
    /// `first_frames` are the frames about to be written. A no-op on a non-empty log,
    /// whose identity is fixed, or when anti-rollback is off.
    #[cfg(feature = "anti-rollback")]
    fn prebind_watermark(&self, first_frames: &[u8]) -> io::Result<()> {
        if let (true, Some(hw), Some(key)) = (
            self.mirror.is_empty(),
            &self.head_watermark,
            self.at_rest_key.as_ref(),
        ) {
            let log_id = log_identity(first_frames);
            write_watermark(hw, key, &log_id, self.base.0, self.next.0)?;
        }
        Ok(())
    }

    #[cfg(not(feature = "anti-rollback"))]
    fn prebind_watermark(&self, _first_frames: &[u8]) -> io::Result<()> {
        Ok(())
    }

    /// [`advance_watermark`](Self::advance_watermark) over records that were just
    /// promoted. They are already durable and visible, so a failure cannot be undone
    /// by a rollback: it POISONS the log instead. Otherwise a retry of the same key
    /// would be acked as a dedup hit the watermark does not cover — or, on the
    /// un-batched path, which records the key in dedup only after this returns, be
    /// appended a second time. A reopen re-establishes the watermark.
    fn cover_head(&mut self) -> io::Result<()> {
        self.advance_watermark().inspect_err(|e| {
            self.poisoned = Some(format!("anti-rollback watermark update failed: {e}"));
        })
    }

    fn open_inner(
        path: &Path,
        durability: Durability,
        repair: bool,
        at_rest_key: Option<[u8; 32]>,
        anti_rollback: AntiRollbackMode,
    ) -> io::Result<(BrokerLog, u64)> {
        let (mut file, created) = open_log_file(path, sync_parent_dir)?;
        // A log that ever took a replicated record is a replica FOREVER, across every
        // constructor: the marker beside it is read before a single record is decoded.
        // A log WE just created carries none of that history, so a marker left beside
        // the name by a deleted predecessor is stale and is cleared rather than
        // inherited.
        let marker = replica_marker_path(path);
        if created {
            let _ = std::fs::remove_file(&marker);
        }
        let replica = marker.exists();
        let mut existing = Vec::new();
        file.read_to_end(&mut existing)?;
        let base = read_base(path)?;
        let scanned = scan(&existing, at_rest_key.as_ref(), base.0);
        if let Tail::Corrupt {
            offset,
            at_byte,
            reason,
        } = &scanned.tail
        {
            if !repair {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "corrupt record at offset {offset} (byte {at_byte} of {}): {reason}; \
                         refusing to open — the {} bytes from there may be acked data \
                         (`asb repair <log>`, or BrokerLog::open_repair, truncates them explicitly)",
                        existing.len(),
                        existing.len() - at_byte
                    ),
                ));
            }
        }
        let valid_len = scanned.valid_len;
        let dropped = (existing.len() - valid_len) as u64;
        if dropped > 0 {
            file.set_len(valid_len as u64)?;
        }
        // fsync even when nothing was cut: a writer that died between a batch's write
        // and its fsync leaves complete records it never acked, only in the page
        // cache. Recovery accepts them, so they must be durable before this process
        // serves them or acks a retry as their dedup hit. When something was cut, the
        // same fsync keeps a power loss from resurrecting it.
        file.sync_all()?;
        file.seek(SeekFrom::End(0))?;
        existing.truncate(valid_len);
        let mirror = existing;
        let records = scanned.records;
        let mut dedup = HashMap::new();
        let mut group_commits: HashMap<String, u64> = HashMap::new();
        let mut last: BTreeMap<String, Offset> = BTreeMap::new();
        let mut subjects_per_producer: HashMap<u64, usize> = HashMap::new();
        let mut bind: HashMap<u64, (String, Offset)> = HashMap::new();
        let mut high_water: HashMap<u64, u64> = HashMap::new();
        for r in &records {
            if r.subject == BIND_SUBJECT {
                if let Ok(principal) = std::str::from_utf8(&r.body) {
                    bind.entry(r.producer_id)
                        .or_insert_with(|| (principal.to_string(), r.seq));
                }
            }
            // The broker's own hidden records (commits, wills, producer bindings) are
            // not produces: they never enter the dedup map and never enter the
            // last-value index. Rebuilding both here is what makes exactly-once ingest
            // AND retained state survive a restart.
            if !is_hidden_subject(&r.subject) {
                dedup.insert((r.producer_id, r.producer_seq), r.seq);
                if last.insert(r.subject.clone(), r.seq).is_none() {
                    *subjects_per_producer.entry(r.producer_id).or_insert(0) += 1;
                }
                // The reserved ack half never enters the fence's high water — the
                // same rule `index_last` applies, applied here, so the fence a
                // restart rebuilds is the fence the log had before it.
                if r.producer_seq < ACK_SEQ_BASE {
                    let hw = high_water.entry(r.producer_id).or_insert(r.producer_seq);
                    *hw = (*hw).max(r.producer_seq);
                }
            }
            if let Some(c) = &r.commit {
                let e = group_commits.entry(c.group.clone()).or_insert(0);
                *e = (*e).max(c.upto);
            }
        }
        let next = Offset(base.0 + records.len() as u64);
        // Anti-rollback: verify (or establish) the authenticated head watermark against
        // the recovered head, refusing a log that was truncated below it.
        let head_watermark = Self::open_watermark(
            anti_rollback,
            path,
            at_rest_key.as_ref(),
            &mirror,
            base.0,
            next.0,
        )?;
        // Wrap the recovered records in Arc for the shared egress read path (the dedup +
        // group_commits above were already rebuilt from the borrowed records).
        let records: Vec<Arc<BrokerRecord>> = records.into_iter().map(Arc::new).collect();
        let mut log = BrokerLog {
            file,
            path: path.to_path_buf(),
            replica,
            mirror,
            records,
            base,
            next,
            dedup,
            last,
            subjects_per_producer,
            will_reserved: HashMap::new(),
            high_water,
            bind,
            group_commits,
            staged: Vec::new(),
            staged_bytes: Vec::new(),
            staged_dedup: HashMap::new(),
            staged_new_subjects: HashMap::new(),
            staged_bind: HashMap::new(),
            durability,
            poisoned: None,
            faults: InjectedFaults::default(),
            at_rest_key,
            head_watermark,
        };
        // The recovery scan rebuilt the landed subjects; this rebuilds the ones the
        // log's still-pending wills have SPOKEN FOR. Both halves of the bound are
        // recovered from the bytes, so a broker restart cannot hand a producer back a
        // budget its registered wills already hold.
        log.reserve_pending_will_subjects();
        Ok((log, dropped))
    }

    /// Re-establish the will-subject reservations after a recovery scan: every will the
    /// log still holds ([`pending_wills`](Self::pending_wills) — at most one per
    /// producer, the one a broker open would actually fire) holds its target subject
    /// unless that subject is already an index entry.
    fn reserve_pending_will_subjects(&mut self) {
        for will in self.pending_wills() {
            self.reserve_will_subject(&will);
        }
    }

    /// Hold `will`'s TARGET subject against its producer's distinct-subject budget,
    /// unless that subject is already in the last-value index (where it is counted
    /// already, and where a firing adds no entry). Idempotent.
    fn reserve_will_subject(&mut self, will: &WillRecord) {
        if is_hidden_subject(&will.subject) || self.last.contains_key(&will.subject) {
            return;
        }
        self.will_reserved
            .entry(will.producer_id)
            .or_default()
            .insert(will.subject.clone());
    }

    /// Release the exclusive file lock early (the broker calls this at shutdown, once
    /// its writer has exited, so a successor can open the log while connection threads
    /// that still hold the old log's `Arc` are being reaped). Dropping the log also
    /// releases it.
    pub(crate) fn unlock(&self) {
        let _ = self.file.unlock();
    }

    /// Arm (or clear) the [`InjectedFaults`] seam. See its docs — a test hook, inert
    /// by default.
    pub fn inject_faults(&mut self, faults: InjectedFaults) {
        self.faults = faults;
    }

    /// `Some(reason)` once the log has refused further mutation because a failed batch
    /// could not be rolled back on disk (see the `poisoned` field). Reopen to recover.
    pub fn poisoned(&self) -> Option<&str> {
        self.poisoned.as_deref()
    }

    /// Whether this log is a REPLICA — a replication TARGET whose contents are a
    /// leader's spine rather than this broker's own. True from the moment an EMPTY log
    /// accepts its first replicated record (or [`declare_replica`](Self::declare_replica)
    /// is called), and durable from then on: the `<log>.replica` marker beside the file
    /// is read on every open, and removing that file is the only undo.
    ///
    /// The broker asks this before doing anything on its OWN initiative to the log —
    /// re-firing the wills it holds at open, above all. A replica that fired the
    /// leader's wills locally would append a record the leader does not have, which
    /// permanently diverges it and fences its link.
    pub fn is_replica(&self) -> bool {
        self.replica
    }

    /// Declare this log a REPLICA — for an operator standing a follower up on a log
    /// seeded by other means (a copy of the leader's). Writes the durable
    /// `<log>.replica` marker; idempotent, and says so on stderr the first time.
    ///
    /// A log that takes its first replicated record while it is still EMPTY declares
    /// itself, so a follower brought up on a fresh log never needs this. A log that
    /// already holds records does NOT: taking a replicated record beside them says
    /// nothing about whose log it is, so a seeded follower has to be declared, and this
    /// (or [`Broker::open_replica`](crate::Broker::open_replica)) is how.
    ///
    /// There is no undeclare. The declaration IS the `<log>.replica` file: remove it
    /// and the next open reads a log this broker owns again.
    pub fn declare_replica(&mut self) -> io::Result<()> {
        self.mark_replica()
    }

    /// Write the durable replica marker (once). Any I/O error is the caller's to
    /// handle: a replicated record whose marker could not be written is REFUSED,
    /// because accepting it would leave a log that is a replica in fact and not in
    /// evidence — the exact state whose next restart forges a `gone`.
    ///
    /// The first write says so on stderr. This is a one-way, durable change to what the
    /// broker will do with the log — no will ever fires here again — so it is not a
    /// thing to happen silently; the line names the marker file, which is also how an
    /// operator undoes a declaration made in error (`rm <log>.replica`).
    fn mark_replica(&mut self) -> io::Result<()> {
        if self.replica {
            return Ok(());
        }
        let marker = replica_marker_path(&self.path);
        let mut f = create_fresh(&marker, &mut OpenOptions::new())?;
        f.write_all(REPLICA_MARKER_NOTE)?;
        f.sync_all()?;
        sync_parent_dir(&marker)?;
        self.replica = true;
        eprintln!(
            "astream-broker: log {} is now a REPLICATION TARGET. Its records are a \
             leader's spine; this broker appends nothing of its own to it and fires \
             NONE of the wills it holds, on this open or any later one. Marked by {}; \
             remove that file to undo a declaration made in error.",
            self.path.display(),
            marker.display()
        );
        Ok(())
    }

    /// The next offset to be assigned (== current head == record count).
    pub fn head(&self) -> Offset {
        self.next
    }

    /// The tier this log was opened at.
    pub fn durability(&self) -> Durability {
        self.durability
    }

    /// Publish a message with exactly-once ingest (the un-batched path: one append,
    /// one fsync at Strict, none at Relaxed). If `(producer_id, producer_seq)` was
    /// already appended, returns `(original_offset, true)` and appends nothing;
    /// otherwise appends at the tier's guarantee and returns `(new_offset, false)`. A
    /// hidden subject is refused (`InvalidInput`), and so is a record that would take
    /// this producer past [`MAX_SUBJECTS_PER_PRODUCER`] distinct subjects — the same
    /// bound the staged path applies, decided in the same place, so the invariant holds
    /// for the TYPE and not only for the wire.
    pub fn publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    ) -> io::Result<(Offset, bool)> {
        self.check_poisoned()?;
        if is_hidden_subject(&subject) {
            return Err(reserved_err(&subject));
        }
        if let Some(off) = self.dedup.get(&(producer_id, producer_seq)) {
            return Ok((*off, true));
        }
        let seq = self.next;
        let rec = BrokerRecord {
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit: None,
        };
        if self.subject_bound_exceeded(&rec, 0) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                subject_bound_msg(producer_id),
            ));
        }
        self.append_record(rec)?; // Strict: on disk when this returns Ok; Relaxed: page cache
        self.dedup.insert((producer_id, producer_seq), seq);
        Ok((seq, false))
    }

    /// The offset a consumer group resumes from: `committed_upto + 1`, or
    /// `Offset::ZERO` if the group has never committed.
    pub fn group_start(&self, group: &str) -> Offset {
        match self.group_commits.get(group) {
            Some(&upto) => Offset(upto.saturating_add(1)),
            None => Offset::ZERO,
        }
    }

    /// Advance a consumer group's committed offset (a pure, no-output commit) at the
    /// tier's guarantee. Idempotent + monotone: re-committing an old offset never
    /// regresses the cursor. Appends a commit record on the reserved subject.
    pub fn commit(&mut self, group: String, upto: u64) -> io::Result<Offset> {
        self.check_poisoned()?;
        let seq = self.next;
        let rec = BrokerRecord {
            seq,
            producer_id: 0,
            producer_seq: 0,
            subject: COMMIT_SUBJECT.to_string(),
            body: Vec::new(),
            commit: Some(GroupCommit { group, upto }),
        };
        self.append_record(rec)?;
        Ok(seq)
    }

    /// The read-process-write TRANSACTION: append `out_body` to `out_subject` AND
    /// commit `group` to `upto` in ONE record (one append, one fsync at Strict) —
    /// exactly-once processing. Deduped by `(producer_id, producer_seq)`: a retried
    /// transaction (e.g. after a crash before the ack) is NOT re-appended and the
    /// commit is not re-applied; it returns the original offset. So the output appears
    /// exactly once and the offset is committed exactly once, even across a crash
    /// mid-transaction. A hidden subject is refused as an output, and so is one that
    /// would take this producer past [`MAX_SUBJECTS_PER_PRODUCER`] distinct subjects.
    pub fn process_and_produce(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        out_subject: String,
        out_body: Vec<u8>,
        group: String,
        upto: u64,
    ) -> io::Result<(Offset, bool)> {
        self.check_poisoned()?;
        if is_hidden_subject(&out_subject) {
            return Err(reserved_err(&out_subject));
        }
        if let Some(off) = self.dedup.get(&(producer_id, producer_seq)) {
            return Ok((*off, true)); // the commit was already applied at first append
        }
        let seq = self.next;
        let rec = BrokerRecord {
            seq,
            producer_id,
            producer_seq,
            subject: out_subject,
            body: out_body,
            commit: Some(GroupCommit { group, upto }),
        };
        if self.subject_bound_exceeded(&rec, 0) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                subject_bound_msg(producer_id),
            ));
        }
        self.append_record(rec)?;
        self.dedup.insert((producer_id, producer_seq), seq);
        Ok((seq, false))
    }

    // ---- group commit: stage many records, then ONE fsync covers the batch ----
    //
    // The writer thread stages each queued op (encoding its bytes into the batch
    // buffer), then calls `commit_batch` once to write and fsync them all. Durability is unchanged: a staged
    // record is NOT acked, NOT in `dedup`, and NOT visible to subscribers (head does
    // not advance) until the batch fsync makes it durable. So `ack ⟹ fsync'd` still
    // holds — the fsync is merely amortized over the batch instead of per message.

    fn check_poisoned(&self) -> io::Result<()> {
        match &self.poisoned {
            Some(reason) => Err(io::Error::other(format!(
                "log poisoned ({reason}); reopen it to recover"
            ))),
            None => Ok(()),
        }
    }

    fn check_poisoned_stage(&self) -> Result<(), StageErr> {
        self.check_poisoned().map_err(StageErr::Io)
    }

    /// The offset the next staged record would take (`next + staged.len()`), or `None`
    /// on offset overflow.
    fn next_staged_seq(&self) -> Option<Offset> {
        self.next
            .0
            .checked_add(self.staged.len() as u64)
            .map(Offset)
    }

    /// The offset a staged-or-durable duplicate of `(producer_id, producer_seq)` maps
    /// to, checking both the durable dedup map and the in-flight batch. (A key is
    /// never in both: staging consults both first, and a commit clears the staged view.)
    fn staged_or_durable_dup(&self, key: (u64, u64)) -> Option<Offset> {
        self.dedup
            .get(&key)
            .or_else(|| self.staged_dedup.get(&key))
            .copied()
    }

    /// Whether `rec` would create a NEW distinct subject for its producer beyond
    /// [`MAX_SUBJECTS_PER_PRODUCER`], counting the durable index, the subjects that
    /// producer's registered wills have RESERVED (`will_reserved`), and `pending` (the
    /// in-flight batch's own not-yet-promoted new subjects for that producer). The ONE
    /// place the bound is decided, so the staged path and the un-batched
    /// [`publish`](Self::publish) / [`process_and_produce`](Self::process_and_produce)
    /// cannot disagree about it.
    fn subject_bound_exceeded(&self, rec: &BrokerRecord, pending: usize) -> bool {
        if is_hidden_subject(&rec.subject) || self.last.contains_key(&rec.subject) {
            return false;
        }
        // A record on a subject this producer has ALREADY reserved consumes that
        // reservation rather than adding an entry beside it, so it is not counted
        // against itself: a producer at the cap can still publish (and still fire a
        // will) on a subject its own will spoke for.
        let reserved = self.will_reserved.get(&rec.producer_id);
        let held = reserved.map_or(0, HashSet::len)
            - usize::from(reserved.is_some_and(|held| held.contains(&rec.subject)));
        let already = pending
            + held
            + self
                .subjects_per_producer
                .get(&rec.producer_id)
                .copied()
                .unwrap_or(0);
        already >= MAX_SUBJECTS_PER_PRODUCER
    }

    /// Stage a publish into the current batch (exactly-once ingest). Mirrors
    /// [`publish`](Self::publish) but defers the fsync to [`commit_batch`].
    pub(crate) fn stage_publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    ) -> Result<(Offset, bool), StageErr> {
        self.stage_publish_bounded(producer_id, producer_seq, subject, body, true)
    }

    /// [`stage_publish`](Self::stage_publish) with the distinct-subject bound made
    /// explicit. `enforce_bound: false` is for the ONE record whose subject was already
    /// checked, and answered for, at an earlier verb: a will FIRING (see
    /// [`stage_will_fire`](Self::stage_will_fire)).
    fn stage_publish_bounded(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
        enforce_bound: bool,
    ) -> Result<(Offset, bool), StageErr> {
        self.check_poisoned_stage()?;
        if is_hidden_subject(&subject) {
            return Err(StageErr::Reserved(subject));
        }
        if let Some(off) = self.staged_or_durable_dup((producer_id, producer_seq)) {
            return Ok((off, true));
        }
        let seq = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        self.stage_record_bounded(
            BrokerRecord {
                seq,
                producer_id,
                producer_seq,
                subject,
                body,
                commit: None,
            },
            enforce_bound,
        )?;
        Ok((seq, false))
    }

    /// Stage a pure consumer-group commit into the current batch (mirrors
    /// [`commit`](Self::commit) but deferred to [`commit_batch`]).
    pub(crate) fn stage_commit(&mut self, group: String, upto: u64) -> Result<Offset, StageErr> {
        self.check_poisoned_stage()?;
        let seq = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        self.stage_record(BrokerRecord {
            seq,
            producer_id: 0,
            producer_seq: 0,
            subject: COMMIT_SUBJECT.to_string(),
            body: Vec::new(),
            commit: Some(GroupCommit { group, upto }),
        })?;
        Ok(seq)
    }

    /// Stage an atomic read-process-write transaction into the current batch (mirrors
    /// [`process_and_produce`](Self::process_and_produce) but deferred).
    pub(crate) fn stage_process_and_produce(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        out_subject: String,
        out_body: Vec<u8>,
        group: String,
        upto: u64,
    ) -> Result<(Offset, bool), StageErr> {
        self.check_poisoned_stage()?;
        if is_hidden_subject(&out_subject) {
            return Err(StageErr::Reserved(out_subject));
        }
        if let Some(off) = self.staged_or_durable_dup((producer_id, producer_seq)) {
            return Ok((off, true));
        }
        let seq = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        self.stage_record(BrokerRecord {
            seq,
            producer_id,
            producer_seq,
            subject: out_subject,
            body: out_body,
            commit: Some(GroupCommit { group, upto }),
        })?;
        Ok((seq, false))
    }

    /// Stage a record REPLICATED from a leader, at the leader's offset: the follower's
    /// log must be an identical prefix of the leader's, so the record either extends
    /// this spine exactly (`rec.seq == next staged seq` → staged, `(seq, false)`), or
    /// is already held here byte-for-byte (`seq` below the head → nothing staged,
    /// `(seq, true)` — idempotent re-shipping), or is refused with
    /// [`StageErr::Diverged`] naming the offset (a gap, or a DIFFERENT record already at
    /// that offset — never silently overwritten or skipped).
    pub(crate) fn stage_replica(&mut self, rec: BrokerRecord) -> Result<(Offset, bool), StageErr> {
        self.check_poisoned_stage()?;
        // WHOSE LOG IS THIS — decided here, in the writer, in the same critical section
        // that appends the record, because that is the only place the answer cannot
        // change under the decision. The connection thread asks the same question
        // before it queues the op, but it reads the PROMOTED head and then drops the
        // lock: between that read and this staging, this connection's own pipelined
        // records are staged but not promoted, so `head()` still says 0 on a log that
        // is about to hold records of its own. A hidden record admitted on the strength
        // of "still empty" and staged onto an OWNED log is the injection this rule
        // exists to refuse — the broker itself fires that `/a/will` at its next open,
        // as an arbitrary publish to an arbitrary subject under an arbitrary producer
        // id, outside the capability matrix; an `/a/bind` locks a victim principal out
        // of attaching for good.
        //
        // The admission test and the marking are ONE predicate (`declares`),
        // evaluated once, here: a hidden record lands only on a log that is already a
        // replica or is still empty at STAGE time — which is exactly the log that this
        // record declares a replica.
        //
        // A PURE COMMIT is exempt, as it is on the connection thread: it is a leader's
        // own `/a/commit` record, it carries no producer key and no body, and a client
        // that can reach this verb can advance a group cursor with `Commit` anyway.
        let declares = self.next.0 == 0 && self.staged.is_empty();
        if is_hidden_subject(&rec.subject) && !is_pure_commit(&rec) && !(self.replica || declares) {
            return Err(StageErr::ReservedReplica(replicated_reserved_msg(
                &rec.subject,
            )));
        }
        let next = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        if rec.seq.0 < next.0 {
            // Records sit at absolute offsets base..next, indexed base-relative. A
            // record below the retained base was pruned here — we can neither compare
            // nor accept it.
            if rec.seq.0 < self.base.0 {
                return Err(StageErr::Diverged(format!(
                    "replica offset {} predates the retained base {}",
                    rec.seq.0, self.base.0
                )));
            }
            let held: &BrokerRecord = if rec.seq.0 < self.next.0 {
                &self.records[(rec.seq.0 - self.base.0) as usize]
            } else {
                &self.staged[(rec.seq.0 - self.next.0) as usize]
            };
            if *held == rec {
                // Already held, byte for byte: idempotent re-shipping, and NOTHING is
                // appended. It is also nothing to infer ownership from — this branch
                // is reachable for any record already on the log, so a reader that
                // fetches record 0 and echoes it back reaches it too; marking here
                // would let one such echo, appending not a single byte, disable
                // will-firing for every producer on the broker for good.
                return Ok((rec.seq, true));
            }
            return Err(StageErr::Diverged(format!(
                "replica diverged at offset {}: a different record is already held there",
                rec.seq.0
            )));
        }
        if rec.seq.0 > next.0 {
            return Err(StageErr::Diverged(format!(
                "replica gap: this log's next offset is {}, the record is {}",
                next.0, rec.seq.0
            )));
        }
        // A log that takes its first replicated record while it is STILL EMPTY is a
        // replica, durably and from here on: it has nothing of its own, so the whole of
        // what it holds is the leader's spine, and this broker appends nothing of its
        // own to it ever again. A marker that cannot be written REFUSES the record — a
        // log that is a replica in fact but not in evidence is exactly the one whose
        // next restart forges its leader's wills.
        //
        // A log that already holds records is NOT converted here. Accepting a record at
        // this log's own next offset says nothing about whose log it is, and the
        // conversion is not a small thing: it disables will-firing for every producer
        // on this broker, for good, with the `<log>.replica` file as the only trace. It
        // may not be inferred from a frame any reader can construct — an ordinary
        // Publish-shaped `Replicate` at the head, or a byte-identical echo of a record
        // already held, which appends nothing at all. A follower seeded from a COPY of
        // the leader's log is DECLARED by its operator
        // ([`declare_replica`](Self::declare_replica), `Broker::open_replica`); that is
        // what the declaration is for, and it is the only thing that can tell a seeded
        // follower from a broker that owns its log.
        //
        // STAGED FIRST, MARKED SECOND. `mark_replica` is one-way, durable and fsynced,
        // and it disables will-firing for every producer on this broker for good, so it
        // may not be written for a record the log does not take: staging can still
        // refuse this record (`TooLarge` — a request frame is accepted at a size whose
        // record payload is not), and a refused record is not one the log "takes". The
        // invariant that a marker which cannot be WRITTEN refuses the record still
        // holds the other way round: a marker I/O error is `StageErr::Io`, which
        // poisons the batch, and `process_batch` then aborts it — this record and every
        // byte of it roll back with it.
        //
        // EXEMPT from the distinct-subject bound: that is the leader's admission
        // policy, already applied to this record, and a follower's own count can
        // differ from the leader's (will reservations are rebuilt only when a log
        // reopens). Refusing here would stall the follower on a committed record.
        let seq = rec.seq;
        self.stage_record_bounded(rec, false)?;
        if declares {
            self.mark_replica().map_err(StageErr::Io)?;
        }
        Ok((seq, false))
    }

    /// REGISTER a last will: append the hidden `/a/will` record that makes it durable.
    /// The stored record is strictly LARGER than the record the will would publish, so
    /// a registration that fits guarantees the firing will fit too.
    ///
    /// The DISTINCT-SUBJECT BOUND is checked here, against the subject the will would
    /// publish to — not against `/a/will`, which is hidden and outside the bound
    /// entirely. A registration is a promise that the goodbye will be delivered, and a
    /// will whose subject would be its producer's 4097th distinct one cannot be: the
    /// firing is fire-and-forget, so its refusal reaches nobody, and the `/a/will`
    /// record stays on the log for every later open to re-attempt and re-fail. Refusing
    /// at REGISTRATION is the only point where a client is still listening.
    ///
    /// A registration that passes also RESERVES that subject against the producer's
    /// budget (`will_reserved`, promoted when the batch commits and rebuilt on open),
    /// so the next registration sees it — the firings are exempt from the bound, and
    /// the reservation is what keeps them from overshooting it.
    pub(crate) fn stage_will_register(&mut self, will: &WillRecord) -> Result<Offset, StageErr> {
        self.check_poisoned_stage()?;
        // THE FENCE IS WHAT MAKES A STALE GOODBYE HARMLESS, and it does not reach into
        // the reserved ack half ([`ACK_SEQ_BASE`]): a sequence there is derived from an
        // offset, not from an incarnation, so it never enters the high water. A will
        // registered in that half could therefore never be fenced — the producer could
        // come back, republish `state=live`, and the old goodbye would still fire over
        // it. Refused HERE, at registration, which is the only point where the client
        // is listening (a firing's refusal reaches nobody), so the half being reserved
        // is a fact the log enforces rather than a convention it assumes.
        if will.producer_seq >= ACK_SEQ_BASE {
            return Err(StageErr::SeqReserved(format!(
                "will for producer {} at seq {}: sequences at or above {ACK_SEQ_BASE} are \
                 reserved for acks and lie outside the will fence, so a will registered \
                 there could never be fenced by a later record — register it below",
                will.producer_id, will.producer_seq
            )));
        }
        let seq = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        let probe = BrokerRecord {
            seq,
            producer_id: will.producer_id,
            producer_seq: will.producer_seq,
            subject: will.subject.clone(),
            body: Vec::new(),
            commit: None,
        };
        let pending = self.staged_new_subjects.get(&will.producer_id);
        let already_queued = pending.is_some_and(|p| p.contains(&will.subject));
        if !already_queued && self.subject_bound_exceeded(&probe, pending.map_or(0, HashSet::len)) {
            return Err(StageErr::SubjectBound(subject_bound_msg(will.producer_id)));
        }
        self.stage_record(BrokerRecord {
            seq,
            producer_id: will.producer_id,
            producer_seq: will.producer_seq,
            subject: WILL_SUBJECT.to_string(),
            body: will.encode_body(),
            commit: None,
        })?;
        // Reserve inside this batch too, so a second registration (or a publish) staged
        // before the commit sees the budget already spent. The batch's own queue is the
        // right place for it: an aborted batch drops the `/a/will` record and this
        // reservation together, and `commit_batch` promotes it into `will_reserved`.
        // Nothing is queued for a subject already indexed or already held — it costs no
        // second index entry, and double-counting it would refuse a legitimate publish.
        let held = self
            .will_reserved
            .get(&will.producer_id)
            .is_some_and(|held| held.contains(&will.subject));
        if !already_queued && !held && !self.last.contains_key(&will.subject) {
            self.staged_new_subjects
                .entry(will.producer_id)
                .or_default()
                .insert(will.subject.clone());
        }
        Ok(seq)
    }

    /// FIRE a will as an ordinary publish, FENCED: nothing is appended if a record
    /// with a HIGHER `producer_seq` from the same producer has already landed
    /// ([`StageErr::Fenced`]) — a record below [`ACK_SEQ_BASE`], since the fence reads
    /// [`producer_high_water`](Self::producer_high_water) and an ack in the reserved
    /// half is not an incarnation. Otherwise it is a plain [`stage_publish`](Self::stage_publish),
    /// so a will whose key is already on the log dedups to a no-op — an exactly-once
    /// goodbye whether the producer said it itself or the broker said it for them.
    ///
    /// EXEMPT from the distinct-subject bound, because
    /// [`stage_will_register`](Self::stage_will_register) already applied it to this
    /// exact subject and answered the client with it. `Fenced` and `Replica` are
    /// intended outcomes of a will — nothing is owed to anyone when they refuse it —
    /// but `SubjectBound` is not: the firing's ack goes nowhere, so a bound applied
    /// here loses the goodbye silently and forever, re-attempted and re-refused at
    /// every later open. The exemption costs no overshoot: registration RESERVED this
    /// subject against the producer's budget (`will_reserved`) and holds it until this
    /// record lands, so what the firing indexes was already paid for.
    pub(crate) fn stage_will_fire(&mut self, will: WillRecord) -> Result<(Offset, bool), StageErr> {
        self.check_poisoned_stage()?;
        // NEVER on a replica. The log is the leader's spine: the wills it holds are the
        // leader's, they fire THERE, and firing one here would append a record the
        // leader does not have — a forged death notice for a live node, a log that is
        // no longer a prefix of the leader's, and a link fenced for good.
        if self.replica {
            return Err(StageErr::Replica(format!(
                "will for producer {} is not fired here: this log is a replication \
                 target, so its wills fire on the leader that owns them",
                will.producer_id
            )));
        }
        if let Some(hw) = self.producer_high_water(will.producer_id) {
            if hw > will.producer_seq {
                return Err(StageErr::Fenced(format!(
                    "will for producer {} at seq {} is fenced: seq {hw} has landed since",
                    will.producer_id, will.producer_seq
                )));
            }
        }
        self.stage_publish_bounded(
            will.producer_id,
            will.producer_seq,
            will.subject,
            will.body,
            false,
        )
    }

    /// The largest `producer_seq` BELOW [`ACK_SEQ_BASE`] this producer has landed on a
    /// visible subject, durable or staged — the value the will fence compares against.
    ///
    /// The reserved ack half is excluded on purpose: an ack's sequence is derived from
    /// an offset, not from an incarnation, so it says nothing about whether the
    /// producer has been heard from since it registered its will — and being above
    /// every incarnation-derived sequence, one ack would fence every will that producer
    /// could ever register. See [`ACK_SEQ_BASE`].
    pub fn producer_high_water(&self, producer_id: u64) -> Option<u64> {
        let durable = self.high_water.get(&producer_id).copied();
        let staged = self
            .staged
            .iter()
            .filter(|r| {
                r.producer_id == producer_id
                    && !is_hidden_subject(&r.subject)
                    && r.producer_seq < ACK_SEQ_BASE
            })
            .map(|r| r.producer_seq)
            .max();
        match (durable, staged) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        }
    }

    /// Every will the log still holds, at most one per producer — the LAST one that
    /// producer registered, which is what "one per connection, a second replaces"
    /// means once the connection itself is gone — in ascending offset order.
    ///
    /// The set is keyed by PRODUCER, not by connection, and nothing tombstones a
    /// superseded `/a/will` record: replacement is durable exactly because a connection
    /// may hold wills under ONE producer id only (a second under a different id is
    /// refused at the verb), so "the connection's latest" and "that producer's latest"
    /// are the same will.
    ///
    /// HONEST BOUNDARY: a producer that registered wills on TWO live connections at
    /// once has only its most recent one re-fired across a broker restart. Wills that
    /// already fired, and wills a later record fenced, are still returned here: they
    /// append nothing when fired, by dedup and by the fence respectively, which is
    /// what makes re-firing every one of them on open idempotent. On a REPLICA the
    /// caller must not fire any of them at all — see [`is_replica`](Self::is_replica).
    pub fn pending_wills(&self) -> Vec<WillRecord> {
        self.latest_wills().into_iter().map(|(_, w)| w).collect()
    }

    /// [`pending_wills`](Self::pending_wills), each with the offset of its `/a/will`
    /// record.
    fn latest_wills(&self) -> Vec<(Offset, WillRecord)> {
        let mut latest: HashMap<u64, (Offset, WillRecord)> = HashMap::new();
        for rec in &self.records {
            if rec.subject != WILL_SUBJECT {
                continue;
            }
            if let Some(will) = WillRecord::from_record(rec) {
                latest.insert(rec.producer_id, (rec.seq, will));
            }
        }
        let mut out: Vec<(Offset, WillRecord)> = latest.into_values().collect();
        out.sort_by_key(|(off, _)| off.0);
        out
    }

    /// The lowest record below `min` that retention must not drop, with what it
    /// holds. Bindings and wills live ONLY in their records — an open rebuilds both
    /// from the log — so compacting one away loses it at the next open: a bound
    /// producer id free for any principal to attach under, or a goodbye never said.
    /// A will that can no longer append anything is not held: one already fired or
    /// otherwise on the log (its key dedups), fenced by a later record of its producer,
    /// or superseded by a later registration.
    #[cfg(feature = "retention")]
    fn retention_blocker(&self, min: u64) -> Option<(u64, String)> {
        let bindings =
            self.bind
                .iter()
                .filter(|(_, (_, off))| off.0 < min)
                .map(|(id, (principal, off))| {
                    let what = format!("producer {id}'s binding to principal {principal:?}");
                    (off.0, what)
                });
        let wills = self
            .latest_wills()
            .into_iter()
            .filter(|(off, w)| {
                off.0 < min
                    && !self.dedup.contains_key(&(w.producer_id, w.producer_seq))
                    && self
                        .high_water
                        .get(&w.producer_id)
                        .is_none_or(|&hw| hw <= w.producer_seq)
            })
            .map(|(off, w)| {
                let what = format!("producer {}'s pending last will", w.producer_id);
                (off.0, what)
            });
        bindings.chain(wills).min_by_key(|(off, _)| *off)
    }

    /// The principal a producer id is bound to (durable or in the in-flight batch),
    /// with the offset of the `/a/bind` record that bound it.
    pub fn binding(&self, producer_id: u64) -> Option<(&str, Offset)> {
        self.staged_bind
            .get(&producer_id)
            .or_else(|| self.bind.get(&producer_id))
            .map(|(p, off)| (p.as_str(), *off))
    }

    /// BIND a producer id to a principal, appending the hidden `/a/bind` record that
    /// makes the binding durable. Idempotent: re-binding the same principal appends
    /// nothing and returns the original offset with `deduped = true`. A DIFFERENT
    /// principal for an id already bound is [`StageErr::Collision`] — the belt-and-
    /// braces refusal behind `producer_id_of`'s 64-bit second-preimage cost.
    ///
    /// The check and the append happen together under the writer's lock, so two
    /// connections racing to bind colliding ids can never both succeed.
    pub(crate) fn stage_bind(
        &mut self,
        producer_id: u64,
        principal: String,
    ) -> Result<(Offset, bool), StageErr> {
        self.check_poisoned_stage()?;
        if let Some((held, off)) = self.binding(producer_id) {
            if held == principal {
                return Ok((off, true));
            }
            return Err(StageErr::Collision(format!(
                "producer id collision: {producer_id} is already bound to principal {held:?}, \
                 not {principal:?}"
            )));
        }
        let seq = self.next_staged_seq().ok_or(StageErr::TooLarge)?;
        self.stage_record(BrokerRecord {
            seq,
            producer_id,
            producer_seq: 0,
            subject: BIND_SUBJECT.to_string(),
            body: principal.clone().into_bytes(),
            commit: None,
        })?;
        self.staged_bind.insert(producer_id, (principal, seq));
        Ok((seq, false))
    }

    /// Frame a record for disk, sealing its payload under the at-rest key (bound to
    /// its log index) when one is set. The plaintext path is byte-for-byte
    /// `BrokerRecord::encode`.
    fn encode_for_disk(&self, rec: &BrokerRecord) -> Result<Vec<u8>, FrameError> {
        let payload =
            seal_disk_payload(self.at_rest_key.as_ref(), rec.seq.0, rec.encode_payload()?);
        Frame::new(payload).encode()
    }

    /// Encode `rec` into the in-flight batch (and the in-batch dedup view). Nothing
    /// reaches the file until `commit_batch` writes the batch in one call.
    fn stage_record(&mut self, rec: BrokerRecord) -> Result<(), StageErr> {
        self.stage_record_bounded(rec, true)
    }

    /// [`stage_record`](Self::stage_record), with the distinct-subject bound made
    /// explicit — see [`stage_publish_bounded`](Self::stage_publish_bounded). An
    /// exempt record still COUNTS toward the bound once it is indexed; it is only the
    /// refusal that is skipped.
    fn stage_record_bounded(
        &mut self,
        rec: BrokerRecord,
        enforce_bound: bool,
    ) -> Result<(), StageErr> {
        // The distinct-subject bound is checked BEFORE the record is staged, counting
        // the durable index and this batch's own not-yet-promoted new subjects, so a
        // refusal leaves the batch untouched and one batch cannot overshoot the cap.
        // An EXEMPT record is still counted — it really does add an index entry — but
        // it is never refused. It is queued only once staged: a record refused for
        // size spends none of the budget.
        let queued = self.staged_new_subjects.get(&rec.producer_id);
        let new_subject = !is_hidden_subject(&rec.subject)
            && !self.last.contains_key(&rec.subject)
            && !queued.is_some_and(|p| p.contains(&rec.subject));
        if new_subject
            && enforce_bound
            && self.subject_bound_exceeded(&rec, queued.map_or(0, HashSet::len))
        {
            return Err(StageErr::SubjectBound(subject_bound_msg(rec.producer_id)));
        }
        let frame = self.encode_for_disk(&rec).map_err(|_| StageErr::TooLarge)?;
        self.staged_bytes.extend_from_slice(&frame);
        if new_subject {
            self.staged_new_subjects
                .entry(rec.producer_id)
                .or_default()
                .insert(rec.subject.clone());
        }
        if !is_hidden_subject(&rec.subject) {
            self.staged_dedup
                .insert((rec.producer_id, rec.producer_seq), rec.seq);
        }
        self.staged.push(rec);
        Ok(())
    }

    /// Record `rec` in the last-value index (and the per-producer distinct-subject
    /// count) as it becomes durable. Hidden subjects are excluded, so no query and no
    /// bound ever sees one.
    fn index_last(&mut self, rec: &BrokerRecord) {
        if is_hidden_subject(&rec.subject) {
            return;
        }
        // The last-will FENCE asks "has this producer been heard from SINCE it
        // registered?", and a will's sequence is its incarnation's reserved top. An
        // ack's sequence is not an incarnation at all — it is `ACK_SEQ_BASE | offset`,
        // above every incarnation-derived sequence there is — so one ack folded in
        // here would fence every will that producer could ever register, permanently
        // and with nothing logged (the firing is fire-and-forget). The reserved half is
        // excluded, here and in the rebuild on open; a will is refused that half at
        // registration, so nothing the fence has to protect lives there.
        if rec.producer_seq < ACK_SEQ_BASE {
            let hw = self
                .high_water
                .entry(rec.producer_id)
                .or_insert(rec.producer_seq);
            *hw = (*hw).max(rec.producer_seq);
        }
        match self.last.get_mut(&rec.subject) {
            Some(slot) => *slot = rec.seq,
            None => {
                self.last.insert(rec.subject.clone(), rec.seq);
                *self
                    .subjects_per_producer
                    .entry(rec.producer_id)
                    .or_insert(0) += 1;
            }
        }
        // The subject has landed: any will reservation this producer held for it is
        // discharged — either it is counted in `subjects_per_producer` now, or it was
        // already an index entry. Holding it too would charge the budget twice. This is
        // the will's own firing on the ordinary path, and a producer that publishes the
        // subject itself before it dies on the other.
        if let Some(held) = self.will_reserved.get_mut(&rec.producer_id) {
            if held.remove(&rec.subject) && held.is_empty() {
                self.will_reserved.remove(&rec.producer_id);
            }
        }
    }

    /// Write the whole staged batch in ONE call and fsync it ONCE, then promote every
    /// staged record to the durable state (dedup, group commits, offset spine, mirror)
    /// — making them ack-able and visible to subscribers. An empty batch is a no-op
    /// (no write, no fsync). On a write or fsync error nothing is promoted and the
    /// written suffix is rolled back, so the
    /// on-disk log + mirror stay a clean durable prefix (the atomic-append contract,
    /// at batch granularity); if that rollback itself fails the log POISONS itself
    /// (every later mutation errors until reopen) rather than build on an unknown
    /// on-disk suffix.
    pub(crate) fn commit_batch(&mut self) -> io::Result<()> {
        self.check_poisoned()?;
        if self.staged.is_empty() {
            return Ok(());
        }
        // All-or-nothing: validate the final offset BEFORE the fsync / any promotion, so
        // an offset-overflow can never leave a half-promoted batch that process_batch
        // then reports as wholly failed. (Staging already advances offsets via
        // next_staged_seq, so this is a belt-and-suspenders check at u64 saturation.)
        if self.next.0.checked_add(self.staged.len() as u64).is_none() {
            self.abort_batch();
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "offset overflow",
            ));
        }
        // Strict: write + fsync the whole batch before promoting (ack ⟹ on disk).
        // Relaxed: skip the fsync — the write puts the bytes in the page cache, so the
        // ack means page-cache-durable (survives a process crash, not power loss).
        let strict = self.durability == Durability::Strict;
        let res = self.prebind_watermark(&self.staged_bytes);
        let res = res.and_then(|()| self.file.write_all(&self.staged_bytes));
        let res = res.and_then(|()| if strict { self.sync_data() } else { Ok(()) });
        if let Err(e) = res {
            self.abort_batch();
            return Err(e);
        }
        self.mirror.extend_from_slice(&self.staged_bytes);
        self.staged_bytes.clear();
        self.staged_dedup.clear();
        self.staged_new_subjects.clear();
        self.staged_bind.clear();
        for rec in std::mem::take(&mut self.staged) {
            // A committed `/a/will` record holds its target subject from here on: the
            // staged reservation went out with `staged_new_subjects` above, and this is
            // what an open rebuilds from these same records.
            if rec.subject == WILL_SUBJECT {
                if let Some(will) = WillRecord::from_record(&rec) {
                    self.reserve_will_subject(&will);
                }
            }
            if rec.subject == BIND_SUBJECT {
                if let Ok(principal) = std::str::from_utf8(&rec.body) {
                    self.bind
                        .entry(rec.producer_id)
                        .or_insert_with(|| (principal.to_string(), rec.seq));
                }
            }
            if !is_hidden_subject(&rec.subject) {
                self.dedup
                    .insert((rec.producer_id, rec.producer_seq), rec.seq);
            }
            self.index_last(&rec);
            if let Some(c) = &rec.commit {
                let e = self.group_commits.entry(c.group.clone()).or_insert(0);
                *e = (*e).max(c.upto);
            }
            // Validated above, so this never errors mid-loop (no partial promotion).
            self.next = rec
                .seq
                .checked_next()
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "offset overflow"))?;
            self.records.push(Arc::new(rec));
        }
        // The batch is durable; advance the anti-rollback watermark to the new head.
        self.cover_head()
    }

    /// Discard the staged (unsynced) batch, truncating the file back to the durable
    /// mirror length so disk + mirror remain a clean prefix. Used when staging hit an
    /// I/O error, or the batch's write or fsync failed. If the truncate (or the
    /// seek back to the end) fails, the on-disk suffix is unknown: the log is POISONED
    /// and refuses every further mutation until reopened.
    pub(crate) fn abort_batch(&mut self) {
        self.rollback_to(self.mirror.len() as u64);
        self.staged.clear();
        self.staged_bytes.clear();
        self.staged_dedup.clear();
        self.staged_new_subjects.clear();
        self.staged_bind.clear();
    }

    /// Truncate the file back to `len` durable bytes and reposition at its end;
    /// poison the log if that cannot be done.
    fn rollback_to(&mut self, len: u64) {
        let res = self
            .truncate_to(len)
            .and_then(|()| self.file.seek(SeekFrom::End(0)).map(|_| ()));
        if let Err(e) = res {
            self.poisoned = Some(format!(
                "could not roll the staged suffix back to {len} bytes: {e}"
            ));
        }
    }

    fn sync_data(&self) -> io::Result<()> {
        if self.faults.sync {
            return Err(io::Error::other("injected fsync fault"));
        }
        self.file.sync_data()
    }

    fn truncate_to(&self, len: u64) -> io::Result<()> {
        if self.faults.truncate {
            return Err(io::Error::other("injected truncate fault"));
        }
        self.file.set_len(len)
    }

    /// Encode + atomically append a record, then advance the offset spine and apply
    /// any carried group commit. (Shared by publish/commit/process_and_produce.)
    fn append_record(&mut self, rec: BrokerRecord) -> io::Result<()> {
        // Checked BEFORE any byte is written: a record with no successor offset must
        // never reach the disk.
        let next = rec
            .seq
            .checked_next()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "offset overflow"))?;
        let frame = self
            .encode_for_disk(&rec)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "message too large"))?;
        self.prebind_watermark(&frame)?; // before a byte is written
        self.append_frame(&frame)?; // Strict: on disk when this returns Ok
        self.index_last(&rec);
        if let Some(c) = &rec.commit {
            let e = self.group_commits.entry(c.group.clone()).or_insert(0);
            *e = (*e).max(c.upto);
        }
        self.next = next;
        self.records.push(Arc::new(rec));
        self.cover_head()
    }

    /// LAST-VALUE query (retained state): the most recent record of every subject
    /// matching `filter` whose subject sorts strictly AFTER `after` (`""` for the
    /// first page), in ascending SUBJECT order, at most `max` of them, and only
    /// records BELOW `visible`. Returns the page and its RESUME CURSOR.
    ///
    /// BOUNDED WORK, like [`fetch`](Self::fetch): the scan of the ordered index starts
    /// at the filter's literal prefix (`O(log n)` to find) and then visits at most
    /// `scan_max` entries — matched or not. Without that bound the cost is
    /// `O(entries under the literal prefix)`, not `O(page)`: a filter whose matches are
    /// SPARSE within its prefix (`/f/F/pub/*/*/ack/<B>` over an index holding one
    /// `ack` subject per member per barrier ever issued) pays a `Subject::new` +
    /// `Filter::matches` for every entry it skips, and the caller holds the log lock
    /// for all of it — the whole-index walk a read-only holder could loop to stall the
    /// writer.
    ///
    /// The cursor is what keeps that bound honest. `Some(subject)` is the `after` to
    /// pass for the next page — the last entry VISITED, matched or not, so a page that
    /// matched nothing still advances (the same reason `fetch`'s `next` counts scanned
    /// records rather than delivered ones). `None` means the scan reached the end of
    /// the filter's prefix range: this was the last page. A caller that ignores it sees
    /// a page silently truncated at `scan_max`.
    ///
    /// The page hands out the same cheap `Arc` handles as
    /// [`read_from`](Self::read_from), so the caller writes them to a socket with the
    /// log lock released.
    ///
    /// `visible` is the SUBSCRIBER-VISIBLE head, which the caller must read under the
    /// same lock as this call. In the Strict/Relaxed tiers it is the durable head; in
    /// the Replicated tier it LAGS it, and a subject whose newest record is at or
    /// above it is OMITTED from the page rather than answered with a record the tail
    /// path would refuse to deliver — the same fail-closed direction as `tail_loop`.
    ///
    /// Hidden subjects are not in the index at all, so no filter can reach one.
    pub fn last_matching(
        &self,
        filter: &Filter,
        after: &str,
        max: usize,
        scan_max: usize,
        visible: u64,
    ) -> (Vec<Arc<BrokerRecord>>, Option<String>) {
        let mut out = Vec::new();
        if max == 0 {
            // The head query: nothing is scanned and nothing is delivered, and there is
            // no page to continue — the only answer is the caller's `Mark`.
            return (out, None);
        }
        let prefix = literal_prefix(filter);
        // `>=`, not `>`: a WILDCARD-FREE filter's literal prefix IS the only subject it
        // can match, so a resume cursor equal to the prefix must EXCLUDE it (with `>`
        // the range would restart at `Included(prefix)` and return that row forever).
        // The empty first-page cursor still takes the `Included` branch ("" < "/").
        let lower: Bound<String> = if after >= prefix.as_str() && !after.is_empty() {
            Bound::Excluded(after.to_string())
        } else {
            Bound::Included(prefix.clone())
        };
        let mut visited = 0usize;
        for (subject, off) in self.last.range((lower, Bound::Unbounded)) {
            if !subject.starts_with(&prefix) {
                break; // past the filter's literal prefix: nothing later can match
            }
            visited += 1;
            let matched = off.0 < visible && filter.matches_str(subject);
            if matched {
                if let Some(rec) = self.record_at(off.0) {
                    out.push(rec.clone());
                }
            }
            if out.len() >= max || visited >= scan_max {
                // The resume cursor is the last entry VISITED, matched or not.
                return (out, Some(subject.clone()));
            }
        }
        // The range ran out: the answer is complete, so there is nothing to resume.
        (out, None)
    }

    /// BOUNDED READ: at most `max` records matching `filter` with offset >= `from`,
    /// scanning at most `scan_max` records and never at or above `visible`. Returns
    /// the page (cheap `Arc` handles, as [`read_from`](Self::read_from)) and the
    /// offset AFTER the last record SCANNED.
    ///
    /// The scan bound is what makes this a *bounded* read: one request costs
    /// `O(scan_max)` whatever the filter matches, so a sparse filter over a long log
    /// pages instead of holding the log lock for a whole-history walk. Because `next`
    /// counts SCANNED records rather than delivered ones, a page that matched nothing
    /// still advances the cursor — otherwise a sparse reader would loop forever.
    ///
    /// `max == 0` scans nothing and returns `(empty, from)`: the head query, whose
    /// only answer is the `Mark`. Hidden subjects are skipped exactly as on the tail
    /// path, and they are still SCANNED (they consume offsets, so `next` counts them).
    pub fn fetch(
        &self,
        from: u64,
        filter: &Filter,
        max: usize,
        scan_max: usize,
        visible: u64,
    ) -> (Vec<Arc<BrokerRecord>>, u64) {
        let mut out = Vec::new();
        if max == 0 {
            return (out, from);
        }
        // Nothing below the retained base exists to scan: start at the earliest
        // retained record, as `read_from` does, so a pruned range costs no budget.
        let start = from.max(self.base.0);
        let limit = start.saturating_add(scan_max as u64).min(visible);
        let mut next = start;
        let mut off = start;
        while off < limit {
            next = off.saturating_add(1);
            if let Some(rec) = self.record_at(off) {
                if !is_hidden_subject(&rec.subject) && filter.matches_str(&rec.subject) {
                    out.push(rec.clone());
                    if out.len() >= max {
                        break;
                    }
                }
            }
            off = next;
        }
        (out, next)
    }

    /// The retained record at ABSOLUTE offset `off` (records are held base-relative),
    /// or `None` if it was pruned or is not committed.
    fn record_at(&self, off: u64) -> Option<&Arc<BrokerRecord>> {
        let i = usize::try_from(off.checked_sub(self.base.0)?).ok()?;
        self.records.get(i)
    }

    /// How many DISTINCT subjects `producer_id` has created in the last-value index.
    /// [`MAX_SUBJECTS_PER_PRODUCER`] bounds this PLUS
    /// [`will_reserved_subjects`](Self::will_reserved_subjects), not this alone.
    pub fn subjects_per_producer(&self, producer_id: u64) -> usize {
        self.subjects_per_producer
            .get(&producer_id)
            .copied()
            .unwrap_or(0)
    }

    /// How many subjects `producer_id`'s registered-but-unlanded wills have RESERVED
    /// against its budget — the other half of what [`MAX_SUBJECTS_PER_PRODUCER`]
    /// bounds. Durable: rebuilt from the log's `/a/will` records on open.
    pub fn will_reserved_subjects(&self, producer_id: u64) -> usize {
        self.will_reserved.get(&producer_id).map_or(0, HashSet::len)
    }

    /// The lowest offset still retained (records below it were pruned by retention).
    pub fn base(&self) -> Offset {
        self.base
    }

    /// Compact the log by dropping records with offset `< min_offset` (retention). Kept
    /// records keep their ABSOLUTE offsets, so a consumer at a surviving offset is
    /// unaffected; one below the new base catches up from the earliest retained.
    /// Returns the number of records dropped.
    ///
    /// REFUSED (`InvalidInput`, naming the offset — the highest floor it can take)
    /// when the dropped prefix holds a producer binding or a will that could still
    /// fire: those live only in their own records, so compaction would lose them at
    /// the next open. Group commits are not held back: after a reopen, a group whose
    /// last commit record was dropped resumes from the base (the earliest retained
    /// record), and may re-read records it had already committed.
    ///
    /// Cold + explicit: no batch may be staged. The kept suffix is rewritten
    /// atomically (tmp + rename); then the base floor (and, under anti-rollback, the
    /// re-identified watermark) is advanced. An in-process failure after the rewrite
    /// POISONS the log. A CRASH in the small window between the log rewrite and the
    /// base/watermark update leaves them disagreeing, which the next open REFUSES
    /// (fail-safe — no acked data is silently dropped); recover by restoring the log
    /// file from a backup (NOT `open_repair`, which is keyless and would truncate an
    /// encrypted log). Do retention on a broker you can restart, off the ack path.
    #[cfg(feature = "retention")]
    pub fn retain_before(&mut self, min_offset: Offset) -> io::Result<u64> {
        self.check_poisoned()?;
        if !self.staged.is_empty() {
            return Err(io::Error::other(
                "retention: a batch is staged; compact when idle",
            ));
        }
        let min = min_offset.0.clamp(self.base.0, self.next.0);
        if min <= self.base.0 {
            return Ok(0);
        }
        if let Some((off, what)) = self.retention_blocker(min) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "retention: the record at offset {off}, below the floor {min}, holds \
                     {what}, which only that record keeps across a restart; the highest \
                     floor retention can take now is {off}"
                ),
            ));
        }
        let drop_count = min - self.base.0;
        // Byte offset of the first KEPT record in the durable mirror.
        let mut cut = 0usize;
        for _ in 0..drop_count {
            match Frame::decode(&self.mirror[cut..]) {
                Ok(Some(d)) if d.consumed > 0 => cut += d.consumed,
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "retention: could not locate the cut point in the durable log",
                    ))
                }
            }
        }
        let kept: Vec<u8> = self.mirror[cut..].to_vec();

        // 1) Rewrite the log to the kept suffix, atomically (tmp + rename), then reopen
        //    and re-lock the new file (the old inode is now unlinked).
        let mut tmp = self.path.as_os_str().to_os_string();
        tmp.push(".compact");
        let tmp = PathBuf::from(tmp);
        // The copy REPLACES the log, so it carries the log's permissions — and is
        // created with them (then set exactly, past the umask), so the kept records
        // are never readable more widely than the log they came from, even briefly.
        let perms = self.file.metadata()?.permissions();
        {
            let mut opts = OpenOptions::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
                opts.mode(perms.mode());
            }
            let mut f = create_fresh(&tmp, &mut opts)?;
            f.set_permissions(perms)?;
            f.write_all(&kept)?;
            f.sync_all()?;
        }
        std::fs::rename(&tmp, &self.path)?;

        // From here the on-disk log is ALREADY compacted, so any failure leaves the
        // in-memory state and the base/watermark sidecars possibly disagreeing with it.
        // Do the remaining durable I/O FIRST, and POISON on any failure — the log then
        // refuses every further op until it is reopened (whereupon a base/log mismatch
        // is a fail-safe REFUSE, never silent loss). `next`/head is unchanged (front prune).
        if let Err(e) = self.finish_retention(min) {
            self.poisoned = Some(format!("retention compaction failed after rewrite: {e}"));
            return Err(e);
        }

        // In-memory state (infallible): re-base + drop pruned records and their
        // still-theirs dedup keys, then re-write the anti-rollback watermark to the NEW
        // first-record identity (also fail-closed -> poison).
        for rec in self.records.drain(..drop_count as usize) {
            if rec.subject != COMMIT_SUBJECT
                && self.dedup.get(&(rec.producer_id, rec.producer_seq)) == Some(&rec.seq)
            {
                self.dedup.remove(&(rec.producer_id, rec.producer_seq));
            }
        }
        self.mirror = kept;
        self.base = Offset(min);
        if let Err(e) = self.advance_watermark() {
            self.poisoned = Some(format!("retention: watermark update failed: {e}"));
            return Err(e);
        }
        Ok(drop_count)
    }

    /// Reopen + re-lock the freshly-compacted log and durably record the new base
    /// floor. Split out so a failure here is caught and poisons the log.
    #[cfg(feature = "retention")]
    fn finish_retention(&mut self, min: u64) -> io::Result<()> {
        // Make the rename durable, reopen + re-lock the new inode (the old is now
        // unlinked), and record the new base — all inside the caller's poison guard, so
        // an in-process failure at ANY step (including this directory fsync) poisons the
        // log rather than leaving it serving on the dead inode.
        sync_parent_dir(&self.path)?;
        let newf = OpenOptions::new().read(true).write(true).open(&self.path)?;
        lock_exclusive(&newf, &self.path)?;
        self.file = newf;
        self.file.seek(SeekFrom::End(0))?;
        write_base(&self.path, min)
    }

    /// Hand out every committed record with `seq >= start` (from the earliest retained
    /// one if `start` was pruned), in order, as cheap `Arc` clones — the egress read
    /// path does NO deep copy of subject/body, so the lock is released (the caller
    /// writes outside it) without paying for the payload bytes.
    pub fn read_from(&self, start: Offset) -> Vec<Arc<BrokerRecord>> {
        self.read_range(start, usize::MAX)
    }

    /// [`read_from`](Self::read_from), BOUNDED: at most `max` records from `start`
    /// (from the earliest retained one if `start` was pruned), in order, as cheap `Arc`
    /// clones. Copying the handles is the whole cost of a read made under the log lock,
    /// and it grows with the suffix: a reader that holds the lock while it copies — a
    /// subscriber catching up, a fork's snapshot — takes a long suffix this way in
    /// pieces, releasing the lock between them.
    pub fn read_range(&self, start: Offset, max: usize) -> Vec<Arc<BrokerRecord>> {
        // Records sit at absolute offsets base..next; map `start` to an index (clamp a
        // below-base request for pruned records to the earliest retained). Clamp in u64
        // space then narrow — a lossy `as usize` would wrap a >2^32 offset on 32-bit.
        let len = self.records.len();
        let from = start.0.saturating_sub(self.base.0).min(len as u64) as usize;
        let to = from.saturating_add(max).min(len);
        self.records[from..to].to_vec()
    }

    /// How many retained records a handle OUTSIDE the log still shares: copies a
    /// reader took and has not yet delivered and dropped. For tests of how much a
    /// reader copies out of the log at once.
    #[cfg(test)]
    pub(crate) fn shared_records(&self) -> usize {
        self.records
            .iter()
            .filter(|r| Arc::strong_count(r) > 1)
            .count()
    }

    /// A COUNTERFACTUAL snapshot as SHARED handles: the committed records with the one
    /// at `fork_at` replaced by `replacement` (its `seq` forced to `fork_at`). Only the
    /// `Arc` pointers are cloned (plus the one replacement record), so taking this under
    /// the log lock costs O(records) pointer copies, never O(payload bytes) — the same
    /// zero-copy discipline as [`read_from`](Self::read_from). The live log is
    /// unchanged. An out-of-range `fork_at` returns the records as-is.
    pub fn fork_shared(
        &self,
        fork_at: Offset,
        replacement: BrokerRecord,
    ) -> Vec<Arc<BrokerRecord>> {
        let mut out = self.records.clone();
        // `fork_at` is an ABSOLUTE offset; records are stored base-relative, so a fork
        // at or above the retained base maps to index `fork_at - base` (a fork below
        // the base targets a pruned record and is a no-op).
        if let Some(i) = fork_at
            .0
            .checked_sub(self.base.0)
            .and_then(|rel| usize::try_from(rel).ok())
        {
            if i < out.len() {
                let mut r = replacement;
                r.seq = fork_at;
                out[i] = Arc::new(r);
            }
        }
        out
    }

    /// [`fork_shared`](Self::fork_shared) materialized as OWNED records (a deep copy
    /// of every payload). Kept for callers that want owned data; the broker's
    /// fork-delivery path reads the log in bounded pieces
    /// ([`read_range`](Self::read_range)) and copies no payload at all.
    pub fn fork(&self, fork_at: Offset, replacement: BrokerRecord) -> Vec<BrokerRecord> {
        self.fork_shared(fork_at, replacement)
            .into_iter()
            .map(|a| (*a).clone())
            .collect()
    }

    /// The durable bytes (recovered prefix + everything appended since).
    pub fn bytes(&self) -> &[u8] {
        &self.mirror
    }

    /// Atomic append at the tier's guarantee: rolls a partial frame back on a
    /// write/fsync error so the on-disk log stays a clean prefix equal to the mirror
    /// (poisoning the log if the rollback itself fails).
    fn append_frame(&mut self, frame_bytes: &[u8]) -> io::Result<()> {
        let committed = self.mirror.len() as u64;
        // Strict fsyncs; Relaxed writes to the page cache only (see [`Durability`]).
        let strict = self.durability == Durability::Strict;
        let res = self.file.write_all(frame_bytes).and_then(|()| {
            if strict {
                self.sync_data()
            } else {
                Ok(())
            }
        });
        if let Err(e) = res {
            self.rollback_to(committed);
            return Err(e);
        }
        self.mirror.extend_from_slice(frame_bytes);
        Ok(())
    }
}

/// How a stored log ends, as seen by [`scan`].
#[derive(Debug, PartialEq, Eq)]
enum Tail {
    /// Every byte is an intact, in-order record.
    Clean,
    /// The intact prefix is followed by an INCOMPLETE frame with nothing decodable
    /// behind it, or by an all-zero tail — the signatures of a write interrupted by a
    /// crash/power loss. Safe to truncate: no complete frame was ever written there, so
    /// nothing in it was ever acked. (Residual, by construction undetectable: a rotted
    /// length field on the very LAST record also looks like an incomplete frame.)
    Torn,
    /// The intact prefix is followed by bytes that are present but WRONG: a complete
    /// frame with a bad CRC/magic/version, a record payload that does not parse (a
    /// `BREC_VERSION` mismatch, a foreign file), or an offset gap. Truncating here
    /// would destroy every record after it — possibly acked data — so the default open
    /// refuses instead.
    Corrupt {
        offset: u64,
        at_byte: usize,
        reason: String,
    },
}

struct Scan {
    records: Vec<BrokerRecord>,
    /// Byte length of the intact prefix.
    valid_len: usize,
    tail: Tail,
}

/// Whether a complete, parsable record starts ANYWHERE after the first byte of
/// `rest` — the bytes that `Frame::decode` said are an incomplete frame. A write
/// interrupted by a crash leaves nothing decodable behind its partial frame; a frame
/// that is in fact complete but whose LENGTH field rotted (so it "extends past EOF")
/// leaves the later records intact and decodable behind it. Only positions whose
/// magic bytes match are decoded, so this is cheap even over a long tail.
fn later_record_exists(rest: &[u8], key: Option<&[u8; 32]>) -> bool {
    use astream_wire::frame::MAGIC;
    use astream_wire::HEADER_SIZE;
    let mut q = 1usize;
    while q + HEADER_SIZE <= rest.len() {
        if rest[q] == MAGIC[0] && rest[q + 1] == MAGIC[1] {
            if let Ok(Some(d)) = Frame::decode(&rest[q..]) {
                // A complete, CRC-valid frame follows the "past-EOF" one. Plaintext: it
                // must also parse as a record. Encrypted: its payload is ciphertext we
                // cannot parse (and whose index we do not know here), but a 32-bit-CRC
                // -valid frame is strong evidence of a real sealed record, so treat its
                // presence as a rotted length field (corruption), not a torn tail.
                let real = match key {
                    Some(_) => true,
                    None => BrokerRecord::from_payload(&d.frame.payload).is_some(),
                };
                if real {
                    return true;
                }
            }
        }
        q += 1;
    }
    false
}

/// Scan stored bytes into the longest intact, in-order (`seq == expected`) prefix
/// of records, its byte length, and HOW the bytes end (clean / torn / corrupt — the
/// distinction that decides whether recovery may truncate). Pure and panic-free.
fn scan(bytes: &[u8], key: Option<&[u8; 32]>, base: u64) -> Scan {
    let mut out: Vec<BrokerRecord> = Vec::new();
    let mut pos = 0usize;
    loop {
        let rest = &bytes[pos..];
        if rest.is_empty() {
            return Scan {
                records: out,
                valid_len: pos,
                tail: Tail::Clean,
            };
        }
        let expected = base + out.len() as u64;
        let corrupt = |out: Vec<BrokerRecord>, reason: String| Scan {
            records: out,
            valid_len: pos,
            tail: Tail::Corrupt {
                offset: expected,
                at_byte: pos,
                reason,
            },
        };
        let torn = |out: Vec<BrokerRecord>| Scan {
            records: out,
            valid_len: pos,
            tail: Tail::Torn,
        };
        match Frame::decode(rest) {
            Ok(Some(d)) => {
                // Decrypt the sealed payload (identity when no key is set); a COMPLETE
                // frame that fails to authenticate is a wrong key or a tampered record
                // — a corrupt tail, never silently discarded.
                let payload = match open_disk_payload(key, expected, d.frame.payload) {
                    Some(p) => p,
                    None => {
                        return corrupt(
                            out,
                            "record failed to authenticate (wrong at-rest key or a tampered record)"
                                .to_string(),
                        );
                    }
                };
                match BrokerRecord::from_payload(&payload) {
                    // No offset follows u64::MAX, so the log never writes a record
                    // there; refusing one also keeps `base + records` from overflowing.
                    Some(r) if r.seq.0 == u64::MAX => {
                        return corrupt(
                            out,
                            "record at offset u64::MAX, which the log never assigns".to_string(),
                        );
                    }
                    Some(r) if r.seq.0 == expected => {
                        out.push(r);
                        // A decoded frame always consumes >= its header; guard anyway so
                        // a zero-progress decode can never spin.
                        if d.consumed == 0 {
                            return corrupt(out, "zero-length frame".to_string());
                        }
                        pos += d.consumed;
                    }
                    // A CRC-valid frame that is not the next record was WRITTEN that way:
                    // never an interrupted write.
                    Some(r) => {
                        return corrupt(
                            out,
                            format!("offset gap: expected seq {expected}, found {}", r.seq.0),
                        );
                    }
                    None => {
                        return corrupt(
                            out,
                            "record payload does not parse (BREC_VERSION mismatch or malformed)"
                                .to_string(),
                        );
                    }
                }
            }
            // An incomplete trailing frame is the classic torn write — unless intact
            // records follow it, which means its LENGTH field is what is wrong (a
            // complete frame whose header rotted), i.e. corruption mid-log.
            Ok(None) => {
                return if later_record_exists(rest, key) {
                    corrupt(
                        out,
                        "frame claims to extend past the end of the log but intact records \
                         follow it (a corrupt length field, not a torn write)"
                            .to_string(),
                    )
                } else {
                    torn(out)
                }
            }
            // Bytes that are present but wrong. An ALL-ZERO tail is the one exception:
            // the file was extended before the data landed (a power loss under delayed
            // allocation) — no frame was ever written there (a frame starts with a
            // non-zero magic), so nothing acked can be in it: torn.
            Err(e) => {
                return if rest.iter().all(|&b| b == 0) {
                    torn(out)
                } else {
                    corrupt(out, format!("frame does not decode: {e}"))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::brecord::BREC_VERSION;

    /// Removes its paths when dropped, each with every `<path>.*` sidecar beside it
    /// (`.hw`, `.base`, `.replica`, a `.hw.tmp` planted as a directory, …), so a test
    /// leaves nothing behind whether it passes or panics. Bound before the log that
    /// uses the paths, so it drops after it.
    struct Cleanup(Vec<PathBuf>);

    impl Cleanup {
        fn new<P: AsRef<Path>>(paths: &[P]) -> Cleanup {
            Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
        }
    }

    impl Drop for Cleanup {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
                let _ = std::fs::remove_dir_all(path);
                let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
                    continue;
                };
                let prefix = format!("{}.", name.to_string_lossy());
                for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                    if entry.file_name().to_string_lossy().starts_with(&prefix) {
                        let _ = std::fs::remove_file(entry.path());
                        let _ = std::fs::remove_dir_all(entry.path());
                    }
                }
            }
        }
    }

    /// A log path unique to this process and `tag`, and the guard that removes it.
    fn tmp(tag: &str) -> (Cleanup, std::path::PathBuf) {
        let path = std::env::temp_dir().join(format!(
            "astream_brokerlog_{}_{tag}.log",
            std::process::id()
        ));
        (Cleanup::new(&[&path]), path)
    }

    fn rec(seq: u64, pid: u64, pseq: u64) -> BrokerRecord {
        BrokerRecord {
            seq: Offset(seq),
            producer_id: pid,
            producer_seq: pseq,
            subject: "/a/s/x".to_string(),
            body: format!("b{seq}").into_bytes(),
            commit: None,
        }
    }

    /// A log of `n` publishes (producer 1, seqs 1..=n), closed cleanly.
    fn write_log(path: &Path, n: u64) -> u64 {
        let mut log = BrokerLog::open(path).unwrap();
        for i in 1..=n {
            log.publish(1, i, "/a/s/x".into(), format!("b{i}").into_bytes())
                .unwrap();
        }
        log.bytes().len() as u64
    }

    /// Creating a log in a directory this process may write but not READ must still
    /// open: `sync_parent_dir` cannot fsync the entry there, which is not a reason
    /// to refuse a log whose own bytes are fsync'd (and the file has already been
    /// created by then, so failing leaves a zero-length log behind).
    #[test]
    #[cfg(unix)]
    fn a_write_only_log_directory_still_opens() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!(
            "astream_brokerlog_{}_wronly_dir",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let _tmp = Cleanup::new(&[&dir]);
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o300)).unwrap();
        // Running as root (or on a filesystem that ignores the mode) defeats the
        // scenario entirely: the directory is still openable, so there is nothing
        // to assert. Probe rather than guess.
        let unreadable = File::open(&dir).is_err();
        let path = dir.join("x.log");
        let opened = BrokerLog::open(&path);
        let _ = std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700));
        let _ = std::fs::remove_dir_all(&dir);
        if unreadable {
            let mut log = opened.expect("a write-only log directory must not refuse the log");
            assert_eq!(
                log.publish(1, 1, "/a/s/x".into(), b"a".to_vec()).unwrap(),
                (Offset(0), false)
            );
        }
    }

    /// An open that finds the log already present still fsyncs its directory: the
    /// open that created it may have died (or failed) before its own directory
    /// fsync, and records acked into a file whose entry is not durable can vanish
    /// with it on a power loss.
    #[test]
    fn opening_an_existing_log_still_fsyncs_its_directory() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static SYNCS: AtomicUsize = AtomicUsize::new(0);
        fn counting(_: &Path) -> io::Result<()> {
            SYNCS.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }
        fn failing(_: &Path) -> io::Result<()> {
            Err(io::Error::other("injected directory fsync failure"))
        }
        let (_tmp, path) = tmp("dirsync");
        let _ = std::fs::remove_file(&path);
        // The first open creates the file, but its directory fsync fails.
        assert!(open_log_file(&path, failing).is_err());
        assert!(path.exists(), "the file was created");
        // The next open finds the file there and must still fsync the directory.
        let (_file, created) = open_log_file(&path, counting).unwrap();
        assert!(!created);
        assert_eq!(SYNCS.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn publish_dedup_and_recover() {
        let (_tmp, path) = tmp("dedup");
        let _ = std::fs::remove_file(&path);
        {
            let mut log = BrokerLog::open(&path).unwrap();
            assert_eq!(
                log.publish(1, 1, "/a/s/x".into(), b"a".to_vec()).unwrap(),
                (Offset(0), false)
            );
            assert_eq!(
                log.publish(1, 2, "/a/s/x".into(), b"b".to_vec()).unwrap(),
                (Offset(1), false)
            );
            // re-send (1,1): original offset, deduped, not re-appended.
            assert_eq!(
                log.publish(1, 1, "/a/s/x".into(), b"a".to_vec()).unwrap(),
                (Offset(0), true)
            );
            assert_eq!(log.head(), Offset(2));
            assert_eq!(log.read_from(Offset(0)).len(), 2);
        }
        // Reopen: records + dedup recovered from disk.
        let mut log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.head(), Offset(2), "recovered the offset spine");
        assert_eq!(log.read_from(Offset(0)).len(), 2);
        assert_eq!(
            log.publish(1, 1, "/a/s/x".into(), b"a".to_vec()).unwrap(),
            (Offset(0), true),
            "dedup survived restart"
        );
    }

    /// A torn tail — a trailing frame cut mid-payload — is truncated on open, durably,
    /// and the intact prefix is recovered whole.
    #[test]
    fn torn_tail_is_truncated_and_prefix_recovered() {
        let (_tmp, path) = tmp("torn");
        let _ = std::fs::remove_file(&path);
        let clean_len = write_log(&path, 5);
        // Append the first 20 bytes of what would be record 5 (a torn write).
        let partial = rec(5, 1, 6).encode().unwrap();
        {
            let mut f = OpenOptions::new().append(true).open(&path).unwrap();
            f.write_all(&partial[..20]).unwrap();
        }
        assert_eq!(std::fs::metadata(&path).unwrap().len(), clean_len + 20);
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.head(), Offset(5), "the 5 intact records recovered");
        assert_eq!(log.bytes().len() as u64, clean_len);
        assert_eq!(
            std::fs::metadata(&path).unwrap().len(),
            clean_len,
            "the torn bytes were truncated off the file"
        );
        drop(log);

        // A zero-filled tail (the file was extended but the data never landed) is
        // torn too.
        {
            let mut f = OpenOptions::new().append(true).open(&path).unwrap();
            f.write_all(&[0u8; 64]).unwrap();
        }
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.head(), Offset(5));
        assert_eq!(std::fs::metadata(&path).unwrap().len(), clean_len);
        drop(log);
    }

    /// A complete-but-corrupt frame in the MIDDLE of the log (a flipped byte in record
    /// 2 of 5) is NOT a torn tail: open refuses (naming the offset) and leaves the file
    /// untouched; only the explicit `open_repair` truncates, reporting what it dropped.
    #[test]
    fn mid_log_corruption_refuses_to_open_and_repair_is_explicit() {
        let (_tmp, path) = tmp("midcorrupt");
        let _ = std::fs::remove_file(&path);
        let clean_len = write_log(&path, 5);
        let one = rec(0, 1, 1).encode().unwrap().len() as u64; // every record here is the same size
                                                               // Flip a payload byte inside record 2.
        {
            let mut f = OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
                .unwrap();
            let at = 2 * one + 20;
            f.seek(SeekFrom::Start(at)).unwrap();
            let mut b = [0u8; 1];
            f.read_exact(&mut b).unwrap();
            f.seek(SeekFrom::Start(at)).unwrap();
            f.write_all(&[b[0] ^ 0xFF]).unwrap();
        }
        let err = BrokerLog::open(&path).err().expect("must refuse to open");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        let msg = err.to_string();
        assert!(
            msg.contains("offset 2") && msg.contains("open_repair"),
            "names the offset and the repair path: {msg}"
        );
        assert_eq!(
            std::fs::metadata(&path).unwrap().len(),
            clean_len,
            "refusing to open must not touch the file"
        );
        // Explicit repair: truncates at record 2, reports the 3 records' bytes dropped.
        let (log, dropped) = BrokerLog::open_repair(&path, Durability::Strict).unwrap();
        assert_eq!(dropped, 3 * one);
        assert_eq!(log.head(), Offset(2));
        assert_eq!(std::fs::metadata(&path).unwrap().len(), 2 * one);
        drop(log);
        let _ = std::fs::remove_file(&path);

        // A rotted LENGTH field mid-log makes record 2 "extend past EOF" — the shape
        // of a torn tail — but records 3 and 4 are intact behind it, so it is refused
        // as corruption too (a torn write leaves nothing decodable behind it).
        let clean_len = write_log(&path, 5);
        {
            let mut f = OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
                .unwrap();
            f.seek(SeekFrom::Start(2 * one + 6)).unwrap(); // high bytes of record 2's len
            f.write_all(&[0x10, 0x00]).unwrap(); // +1 MiB: past EOF, under the cap
        }
        let err = BrokerLog::open(&path).err().expect("must refuse to open");
        assert!(
            err.to_string().contains("offset 2") && err.to_string().contains("length"),
            "{err}"
        );
        assert_eq!(std::fs::metadata(&path).unwrap().len(), clean_len);
        let (log, dropped) = BrokerLog::open_repair(&path, Durability::Strict).unwrap();
        assert_eq!((dropped, log.head()), (3 * one, Offset(2)));
        drop(log);
    }

    /// A record-format mismatch (an older/newer BREC_VERSION) mid-log, an offset gap
    /// followed by more records, and a complete-but-invalid LAST frame are all
    /// corruption (refused), not torn tails — none of them is the shape of an
    /// interrupted write.
    #[test]
    fn version_mismatch_gap_and_bad_last_frame_are_corruption_not_torn() {
        let one = rec(0, 1, 1).encode().unwrap();
        let mut good = Vec::new();
        for i in 0..3 {
            good.extend_from_slice(&rec(i, 1, i + 1).encode().unwrap());
        }
        // (a) a record whose payload carries BREC_VERSION+1, followed by a good one.
        let mut alien_payload = rec(3, 1, 4).encode().unwrap()[12..].to_vec();
        alien_payload[0] = BREC_VERSION + 1;
        let alien = Frame::new(alien_payload).encode().unwrap();
        let mut a = good.clone();
        a.extend_from_slice(&alien);
        a.extend_from_slice(&rec(4, 1, 5).encode().unwrap());
        // (b) an offset gap (seq 5 where 3 is expected) followed by more bytes.
        let mut b = good.clone();
        b.extend_from_slice(&rec(5, 1, 6).encode().unwrap());
        b.extend_from_slice(&rec(6, 1, 7).encode().unwrap());
        // (c) a complete last frame with a corrupt CRC (no bytes after it).
        let mut c = good.clone();
        let mut bad = rec(3, 1, 4).encode().unwrap();
        bad[20] ^= 0x55;
        c.extend_from_slice(&bad);
        for (tag, bytes, want_offset) in [("alien", a, 3u64), ("gap", b, 3), ("badlast", c, 3)] {
            let (_tmp, path) = tmp(&format!("corrupt_{tag}"));
            let _ = std::fs::remove_file(&path);
            std::fs::write(&path, &bytes).unwrap();
            let err = BrokerLog::open(&path).err().expect("must refuse to open");
            assert_eq!(err.kind(), io::ErrorKind::InvalidData, "{tag}");
            assert!(
                err.to_string().contains(&format!("offset {want_offset}")),
                "{tag}: {err}"
            );
            assert_eq!(
                std::fs::metadata(&path).unwrap().len(),
                bytes.len() as u64,
                "{tag}: file untouched"
            );
            let (log, dropped) = BrokerLog::open_repair(&path, Durability::Strict).unwrap();
            assert_eq!(
                log.head(),
                Offset(3),
                "{tag}: repair keeps the intact prefix"
            );
            assert_eq!(dropped as usize, bytes.len() - 3 * one.len(), "{tag}");
            drop(log);
        }
    }

    /// The log file is exclusively locked while open: a second open (the shape of two
    /// brokers serving one log) fails AlreadyExists until the first is closed.
    #[test]
    fn open_log_is_exclusively_locked() {
        let (_tmp, path) = tmp("lock");
        let _ = std::fs::remove_file(&path);
        let first = BrokerLog::open(&path).unwrap();
        let err = BrokerLog::open(&path).err().expect("must refuse to open");
        assert_eq!(err.kind(), io::ErrorKind::AlreadyExists, "{err}");
        drop(first);
        let again = BrokerLog::open(&path).unwrap();
        // An explicit unlock (what the broker does at shutdown) releases it early too.
        again.unlock();
        let third = BrokerLog::open(&path).unwrap();
        drop(third);
        drop(again);
    }

    /// A failed batch fsync rolls the staged suffix back: nothing promoted (head,
    /// dedup, records unchanged), the file truncated back to the durable prefix, and a
    /// reopen recovers exactly that prefix.
    #[test]
    fn failed_fsync_rolls_the_staged_batch_back() {
        let (_tmp, path) = tmp("fsyncfault");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(1, 1, "/a/s/x".into(), b"durable".to_vec())
            .unwrap();
        let durable_len = log.bytes().len() as u64;
        log.inject_faults(InjectedFaults {
            sync: true,
            truncate: false,
        });
        assert_eq!(
            log.stage_publish(1, 2, "/a/s/x".into(), b"lost".to_vec())
                .unwrap(),
            (Offset(1), false)
        );
        log.stage_commit("g".into(), 0).unwrap();
        assert_eq!(
            std::fs::metadata(&path).unwrap().len(),
            durable_len,
            "staging only buffers the batch: commit_batch writes it in one call"
        );
        let err = log.commit_batch().unwrap_err();
        assert!(err.to_string().contains("injected fsync fault"), "{err}");
        assert_eq!(log.head(), Offset(1), "nothing promoted");
        assert_eq!(
            log.group_start("g"),
            Offset(0),
            "the commit was not applied"
        );
        assert_eq!(
            std::fs::metadata(&path).unwrap().len(),
            durable_len,
            "the staged suffix was truncated off the file"
        );
        assert_eq!(log.bytes().len() as u64, durable_len);
        assert!(log.poisoned().is_none());
        // The rolled-back key is NOT in dedup: re-staging it appends anew at offset 1.
        log.inject_faults(InjectedFaults::default());
        assert_eq!(
            log.stage_publish(1, 2, "/a/s/x".into(), b"retry".to_vec())
                .unwrap(),
            (Offset(1), false),
            "the failed batch left no phantom dedup entry"
        );
        log.commit_batch().unwrap();
        drop(log);
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.head(), Offset(2));
        assert_eq!(log.read_from(Offset(1))[0].body, b"retry");
        drop(log);
    }

    /// If the rollback truncate itself fails the log POISONS: every later mutation is
    /// refused (nothing can be appended after an orphaned on-disk suffix), and a reopen
    /// re-establishes the prefix from the bytes actually on disk.
    #[test]
    fn failed_rollback_poisons_the_log_until_reopen() {
        let (_tmp, path) = tmp("poison");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(1, 1, "/a/s/x".into(), b"durable".to_vec())
            .unwrap();
        log.inject_faults(InjectedFaults {
            sync: true,
            truncate: true,
        });
        log.stage_publish(1, 2, "/a/s/x".into(), b"orphan".to_vec())
            .unwrap();
        assert!(log.commit_batch().is_err());
        let reason = log.poisoned().expect("poisoned").to_string();
        assert!(reason.contains("injected truncate fault"), "{reason}");
        log.inject_faults(InjectedFaults::default());
        // Poisoned: batched and un-batched mutations are all refused, nothing appended.
        assert!(matches!(
            log.stage_publish(1, 3, "/a/s/x".into(), b"x".to_vec()),
            Err(StageErr::Io(_))
        ));
        assert!(matches!(
            log.stage_commit("g".into(), 0),
            Err(StageErr::Io(_))
        ));
        assert!(log.publish(1, 3, "/a/s/x".into(), b"x".to_vec()).is_err());
        assert!(log.commit("g".into(), 0).is_err());
        assert!(log.commit_batch().is_err());
        assert_eq!(log.head(), Offset(1));
        drop(log);
        // Reopen: the orphaned (complete, in-order) frame is on disk, so it is
        // recovered as record 1 — an un-acked write that landed, which its producer's
        // idempotent retry dedups against; never a seq collision.
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.head(), Offset(2));
        assert_eq!(log.read_from(Offset(1))[0].body, b"orphan");
        assert!(log.poisoned().is_none());
        drop(log);
    }

    /// A batch whose anti-rollback watermark write fails after its fsync is durable
    /// but not covered, so nothing may be acknowledged on the strength of it: the log
    /// poisons, and a retried key is refused rather than acked as a dedup hit.
    /// A crash between the first commit's fsync and its watermark update leaves the
    /// log ahead of the watermark the commit bound to it BEFORE writing a byte
    /// (identity of its first record, the old head). That is the ordinary lagging
    /// case: a verified open accepts it and advances the watermark. The same state
    /// with an unbound (zero-identity) watermark stays refused.
    #[cfg(feature = "anti-rollback")]
    #[test]
    fn a_log_ahead_of_its_own_bound_watermark_opens_verified() {
        const KEY: [u8; 32] = [0x24; 32];
        let (_tmp, path) = tmp("hwlag");
        let hw = watermark_path(&path);
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(&hw);
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        log.stage_publish(1, 1, "/a/s/x".into(), b"one".to_vec())
            .unwrap();
        log.commit_batch().unwrap();
        let id = log_identity(log.bytes());
        drop(log);
        // Roll the watermark back to what the first commit bound before its write.
        write_watermark(&hw, &KEY, &id, 0, 0).unwrap();
        let log = BrokerLog::open_encrypted_verified(&path, KEY)
            .expect("a log ahead of its own bound watermark was refused");
        assert_eq!(log.head(), Offset(1));
        drop(log);
        assert_eq!(read_watermark(&hw, &KEY).unwrap(), Some((id, 0, 1)));
        // An unbound watermark (no identity) under the same log is still refused.
        write_watermark(&hw, &KEY, &[0u8; 16], 0, 0).unwrap();
        assert!(BrokerLog::open_encrypted_verified(&path, KEY).is_err());
    }

    /// An EMPTY log under a bound watermark is accepted only as a pre-bind whose
    /// records never landed (at exactly the watermark's base and head) — never as a
    /// log truncated to nothing with its base sidecar moved up to the watermark's
    /// head, which is what a key-less rollback of a whole log would look like.
    #[cfg(all(feature = "anti-rollback", feature = "retention"))]
    #[test]
    fn an_empty_log_is_accepted_only_under_its_own_pre_bind() {
        const KEY: [u8; 32] = [0x25; 32];
        let (_tmp, path) = retained_path("hwempty");
        let hw = watermark_path(&path);
        let _ = std::fs::remove_file(&hw);
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        for i in 0..3u64 {
            log.publish(1, i, "/a/s/x".into(), b"x".to_vec()).unwrap();
        }
        drop(log);
        // The attack: every record gone, the base moved up to the head.
        OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(0)
            .unwrap();
        write_base(&path, 3).unwrap();
        assert!(
            BrokerLog::open_encrypted_verified(&path, KEY).is_err(),
            "a log truncated to nothing was accepted"
        );
        // The crash: retention emptied the log, and the next first commit bound the
        // watermark but its records never landed.
        write_watermark(&hw, &KEY, &[7u8; 16], 3, 3).unwrap();
        let log = BrokerLog::open_encrypted_verified(&path, KEY)
            .expect("an empty log under its own pre-bind was refused");
        assert_eq!((log.base(), log.head()), (Offset(3), Offset(3)));
        drop(log);
    }

    #[cfg(feature = "anti-rollback")]
    #[test]
    fn a_failed_watermark_write_poisons_the_batched_path() {
        let (_tmp, path) = tmp("hwbatch");
        let hw_tmp = {
            let mut s = watermark_path(&path).into_os_string();
            s.push(".tmp");
            PathBuf::from(s)
        };
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(watermark_path(&path));
        let _ = std::fs::remove_dir(&hw_tmp);
        let mut log = BrokerLog::open_encrypted_verified_init(&path, [0x42; 32]).unwrap();
        log.stage_publish(1, 1, "/a/s/x".into(), b"one".to_vec())
            .unwrap();
        log.commit_batch().unwrap();
        std::fs::create_dir(&hw_tmp).unwrap();
        log.stage_publish(1, 2, "/a/s/x".into(), b"two".to_vec())
            .unwrap();
        assert!(log.commit_batch().is_err());
        std::fs::remove_dir(&hw_tmp).unwrap();
        assert!(log.poisoned().is_some());
        assert!(
            matches!(
                log.stage_publish(1, 2, "/a/s/x".into(), b"two".to_vec()),
                Err(StageErr::Io(_))
            ),
            "a retry was acknowledged past a watermark that does not cover it"
        );
        drop(log);
        let log = BrokerLog::open_encrypted_verified(&path, [0x42; 32]).unwrap();
        assert_eq!(log.head(), Offset(2));
        drop(log);
    }

    #[cfg(feature = "retention")]
    fn retained_path(tag: &str) -> (Cleanup, PathBuf) {
        let (guard, path) = tmp(tag);
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(base_path(&path));
        (guard, path)
    }

    /// A producer binding lives only in its `/a/bind` record, so retention refuses
    /// a floor above it (the next open would rebuild the table without it, freeing
    /// the id for any principal) and the log is untouched; a floor at or below it
    /// compacts as usual, and the binding survives a reopen.
    #[cfg(feature = "retention")]
    #[test]
    fn retention_refuses_to_drop_a_producer_binding() {
        let (_tmp, path) = retained_path("retbind");
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(1, 1, "/a/s/x".into(), b"a".to_vec()).unwrap(); // 0
        log.publish(1, 2, "/a/s/x".into(), b"b".to_vec()).unwrap(); // 1
        assert_eq!(
            log.stage_bind(7, "alice".into()).unwrap(),
            (Offset(2), false)
        );
        log.commit_batch().unwrap();
        log.publish(1, 3, "/a/s/x".into(), b"c".to_vec()).unwrap(); // 3
        let bytes = log.bytes().len();
        let err = log.retain_before(Offset(3)).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput, "{err}");
        let msg = err.to_string();
        assert!(
            msg.contains("offset 2") && msg.contains("binding") && msg.contains("alice"),
            "{msg}"
        );
        assert_eq!((log.base(), log.bytes().len()), (Offset(0), bytes));
        assert!(log.poisoned().is_none());
        assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
        drop(log);
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.base(), Offset(2));
        assert_eq!(log.binding(7), Some(("alice", Offset(2))));
        drop(log);
    }

    /// A will that would still fire lives only in its `/a/will` record, so
    /// retention refuses a floor above it. A will that can no longer append anything
    /// — already fired (its key is on the log), fenced by a later record of its
    /// producer, or superseded by a later registration — does not hold the floor.
    #[cfg(feature = "retention")]
    #[test]
    fn retention_refuses_to_drop_a_pending_will_only() {
        let will = |producer_id, producer_seq, subject: &str| WillRecord {
            producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: b"gone".to_vec(),
        };
        let (_tmp, path) = retained_path("retwill");
        let mut log = BrokerLog::open(&path).unwrap();
        log.stage_will_register(&will(9, 4, "/f/x/gone")).unwrap(); // 0: pending
        log.stage_will_register(&will(8, 4, "/f/y/gone")).unwrap(); // 1: will be fired
        log.stage_will_register(&will(6, 4, "/f/z/gone")).unwrap(); // 2: will be fenced
        log.stage_will_register(&will(5, 4, "/f/w/old")).unwrap(); // 3: superseded
        log.stage_will_register(&will(5, 4, "/f/w/new")).unwrap(); // 4: pending
        log.commit_batch().unwrap();
        log.stage_will_fire(will(8, 4, "/f/y/gone")).unwrap(); // 5
        log.stage_publish(6, 5, "/f/z/live".into(), b"live".to_vec())
            .unwrap(); // 6
        log.commit_batch().unwrap();

        // Producer 9's will at offset 0 is pending: nothing above offset 0 may go.
        let err = log.retain_before(Offset(1)).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput, "{err}");
        assert!(
            err.to_string().contains("offset 0") && err.to_string().contains("will"),
            "{err}"
        );
        assert_eq!(log.base(), Offset(0));
        assert!(log.poisoned().is_none());
        // Fire it; then the fired, fenced and superseded ones go, and the pending
        // will at offset 4 holds the floor there.
        log.stage_will_fire(will(9, 4, "/f/x/gone")).unwrap(); // 7
        log.commit_batch().unwrap();
        let err = log.retain_before(Offset(6)).unwrap_err();
        assert!(err.to_string().contains("offset 4"), "{err}");
        assert_eq!(log.retain_before(Offset(4)).unwrap(), 4);
        drop(log);
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.pending_wills(), vec![will(5, 4, "/f/w/new")]);
        drop(log);
    }

    /// A bind the log refuses (too large to store) leaves no binding behind, not
    /// even for the rest of its batch: the same producer can still bind for real.
    #[test]
    fn a_refused_bind_leaves_no_phantom_binding() {
        let (_tmp, path) = tmp("bindphantom");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        let huge = "p".repeat(crate::MAX_RECORD_PAYLOAD);
        assert!(matches!(log.stage_bind(7, huge), Err(StageErr::TooLarge)));
        assert!(log.binding(7).is_none(), "a refused bind left a binding");
        assert_eq!(
            log.stage_bind(7, "alice".into()).unwrap(),
            (Offset(0), false)
        );
        log.commit_batch().unwrap();
        assert_eq!(log.binding(7), Some(("alice", Offset(0))));
        drop(log);
    }

    /// A record refused for size spends none of its producer's distinct-subject
    /// budget, so the next new subject in the same batch still fits under the cap.
    #[test]
    fn a_record_refused_for_size_spends_no_subject_budget() {
        let (_tmp, path) = tmp("budgetphantom");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
        for i in 0..MAX_SUBJECTS_PER_PRODUCER as u64 - 1 {
            log.stage_publish(1, i, format!("/a/s/{i}"), Vec::new())
                .unwrap();
        }
        log.commit_batch().unwrap();
        assert_eq!(log.subjects_per_producer(1), MAX_SUBJECTS_PER_PRODUCER - 1);
        let too_big = vec![0u8; crate::MAX_RECORD_PAYLOAD];
        assert!(matches!(
            log.stage_publish(1, 1 << 40, "/a/big".into(), too_big),
            Err(StageErr::TooLarge)
        ));
        assert!(
            log.stage_publish(1, (1 << 40) + 1, "/a/last".into(), b"x".to_vec())
                .is_ok(),
            "the refused record spent the producer's last subject"
        );
        log.commit_batch().unwrap();
        assert_eq!(log.subjects_per_producer(1), MAX_SUBJECTS_PER_PRODUCER);
        drop(log);
    }

    /// Replica staging keeps the follower's log an identical prefix of the leader's:
    /// in-order records extend it, a re-shipped record already held is idempotent, a
    /// gap or a different record at a held offset is refused by offset.
    #[test]
    fn stage_replica_extends_dedups_or_refuses_by_offset() {
        let (_tmp, path) = tmp("replica");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.stage_replica(rec(0, 7, 1)).unwrap(), (Offset(0), false));
        assert_eq!(log.stage_replica(rec(1, 7, 2)).unwrap(), (Offset(1), false));
        // Already held (still staged): idempotent, nothing appended.
        assert_eq!(log.stage_replica(rec(0, 7, 1)).unwrap(), (Offset(0), true));
        log.commit_batch().unwrap();
        // Already held (durable): idempotent.
        assert_eq!(log.stage_replica(rec(1, 7, 2)).unwrap(), (Offset(1), true));
        // A gap is refused, naming the offsets; nothing staged.
        match log.stage_replica(rec(5, 7, 6)) {
            Err(StageErr::Diverged(m)) => assert!(m.contains("gap") && m.contains('5'), "{m}"),
            other => panic!("expected a gap error, got {other:?}"),
        }
        // A DIFFERENT record at a held offset is refused, never overwritten.
        match log.stage_replica(rec(1, 9, 9)) {
            Err(StageErr::Diverged(m)) => assert!(m.contains("offset 1"), "{m}"),
            other => panic!("expected a divergence error, got {other:?}"),
        }
        assert_eq!(log.head(), Offset(2));
        // A replicated commit record applies its group commit on the follower.
        let mut c = rec(2, 0, 0);
        c.subject = COMMIT_SUBJECT.to_string();
        c.body.clear();
        c.commit = Some(GroupCommit {
            group: "g".into(),
            upto: 1,
        });
        assert_eq!(log.stage_replica(c).unwrap(), (Offset(2), false));
        log.commit_batch().unwrap();
        assert_eq!(log.group_start("g"), Offset(2));
        // The replicated dedup map matches the leader's: (7,1) dedups to 0.
        assert_eq!(
            log.stage_publish(7, 1, "/a/s/x".into(), b"dup".to_vec())
                .unwrap(),
            (Offset(0), true)
        );
        drop(log);
    }

    /// The reserved commit subject cannot be published to (batched or not, as a
    /// publish or a transaction output): it would bypass dedup and never be delivered.
    #[test]
    fn reserved_commit_subject_is_refused_for_publishes() {
        let (_tmp, path) = tmp("reserved");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        assert!(matches!(
            log.stage_publish(5, 1, COMMIT_SUBJECT.into(), b"x".to_vec()),
            Err(StageErr::Reserved(_))
        ));
        assert!(matches!(
            log.stage_process_and_produce(5, 1, COMMIT_SUBJECT.into(), vec![], "g".into(), 0),
            Err(StageErr::Reserved(_))
        ));
        let e = log
            .publish(5, 1, COMMIT_SUBJECT.into(), b"x".to_vec())
            .unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidInput);
        assert!(log
            .process_and_produce(5, 1, COMMIT_SUBJECT.into(), vec![], "g".into(), 0)
            .is_err());
        assert_eq!(log.head(), Offset(0), "nothing appended");
        assert!(log.staged.is_empty());
        // A real commit still lands on the reserved subject (and stays out of dedup).
        assert_eq!(log.commit("g".into(), 3).unwrap(), Offset(0));
        assert!(log.dedup.is_empty());
        drop(log);
    }

    /// `fork_shared` swaps exactly one record and SHARES every other one (no payload
    /// copy under the lock).
    #[test]
    fn fork_shared_swaps_one_and_shares_the_rest() {
        let (_tmp, path) = tmp("fork");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        for i in 1..=3 {
            log.publish(1, i, "/a/s/x".into(), format!("m{i}").into_bytes())
                .unwrap();
        }
        let live = log.read_from(Offset(0));
        let alt = log.fork_shared(Offset(1), rec(99, 0, 0));
        assert_eq!(alt.len(), 3);
        assert!(Arc::ptr_eq(&alt[0], &live[0]) && Arc::ptr_eq(&alt[2], &live[2]));
        assert_eq!(
            alt[1].seq,
            Offset(1),
            "the replacement takes the fork offset"
        );
        assert_eq!(alt[1].body, b"b99");
        assert_eq!(live[1].body, b"m2", "the live log is untouched");
        // Out of range: the records as-is.
        assert_eq!(log.fork_shared(Offset(9), rec(0, 0, 0)).len(), 3);
        drop(log);
    }

    // -----------------------------------------------------------------------
    // Replica admission, the will fence and the reserved ack half.
    // -----------------------------------------------------------------------

    /// The `/a/will` body a forged registration would carry.
    fn will_body(subject: &str, body: &[u8]) -> Vec<u8> {
        WillRecord {
            producer_id: 0,
            producer_seq: 0,
            subject: subject.to_string(),
            body: body.to_vec(),
        }
        .encode_body()
    }

    fn replicated(seq: u64, subject: &str, body: Vec<u8>) -> BrokerRecord {
        BrokerRecord {
            seq: Offset(seq),
            producer_id: 4242,
            producer_seq: 7,
            subject: subject.to_string(),
            body,
            commit: None,
        }
    }

    /// A hidden replicated record is refused once THIS BATCH has staged a record,
    /// even though the PROMOTED head — the only thing the connection thread can read
    /// before it queues the op — is still 0.
    ///
    /// This is the whole of the injection: a `/a/will` admitted on the strength of
    /// "the log is still empty" and staged onto a log the broker OWNS, which then
    /// fires it at the next open as an arbitrary publish outside the capability
    /// matrix. The admission test lives where the append does.
    #[test]
    fn a_hidden_replicate_is_refused_once_this_batch_has_staged_a_record() {
        let (_tmp, path) = tmp("injectstaged");
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(replica_marker_path(&path));
        let mut log = BrokerLog::open(&path).unwrap();
        assert_eq!(
            log.stage_publish(1, 1, "/f/x/one".into(), b"seed".to_vec())
                .unwrap(),
            (Offset(0), false)
        );
        assert_eq!(
            log.head(),
            Offset(0),
            "the promoted head is still 0: this is exactly what the guard on the \
             connection thread reads while the batch is in flight"
        );
        let rec = replicated(1, WILL_SUBJECT, will_body("/f/pwned/gone", b"owned"));
        match log.stage_replica(rec) {
            Err(StageErr::ReservedReplica(msg)) => {
                assert!(msg.contains("reserved subject /a/will"), "{msg}")
            }
            other => panic!("the /a/will was not refused: {other:?}"),
        }
        // The same for /a/bind, which locks a principal out of attaching for good.
        let rec = replicated(1, BIND_SUBJECT, b"victim".to_vec());
        assert!(matches!(
            log.stage_replica(rec),
            Err(StageErr::ReservedReplica(_))
        ));
        log.commit_batch().unwrap();
        assert_eq!(log.head(), Offset(1), "only the publish landed");
        assert!(log.pending_wills().is_empty(), "a will was injected");
        assert!(!log.is_replica());
        assert!(!replica_marker_path(&path).exists());
        drop(log);
    }

    /// Writing the replica marker never follows a symlink planted at its name: the
    /// file the link points to stays untouched, and the marker is a file of its own.
    #[test]
    #[cfg(unix)]
    fn the_replica_marker_does_not_follow_a_planted_symlink() {
        let (_tmp, path) = tmp("markerlink");
        let marker = replica_marker_path(&path);
        let victim = path.with_extension("victim");
        let _victim = Cleanup::new(&[&victim]);
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(&marker);
        std::fs::write(&victim, b"precious").unwrap();
        let mut log = BrokerLog::open(&path).unwrap();
        std::os::unix::fs::symlink(&victim, &marker).unwrap();
        log.declare_replica().unwrap();
        assert_eq!(std::fs::read(&victim).unwrap(), b"precious");
        assert!(!std::fs::symlink_metadata(&marker).unwrap().is_symlink());
        drop(log);
    }

    /// A replicated record REFUSED FOR SIZE does not declare the log a replica. The
    /// marker is one-way, durable and fsynced, and it stops this broker firing any
    /// will ever again; a record the log does not take must not write it. A request
    /// frame is accepted at sizes whose record payload is not, so the attacker picks
    /// the body length — no capability, not one byte appended.
    #[test]
    fn a_replicate_refused_for_size_does_not_declare_the_log_a_replica() {
        let (_tmp, path) = tmp("injectsize");
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(replica_marker_path(&path));
        let mut log = BrokerLog::open(&path).unwrap();
        let too_big = replicated(0, "/f/x/one", vec![7u8; crate::MAX_RECORD_PAYLOAD]);
        assert!(matches!(
            log.stage_replica(too_big),
            Err(StageErr::TooLarge)
        ));
        assert_eq!(log.head(), Offset(0), "nothing appended");
        assert!(
            !log.is_replica(),
            "a record the log refused declared it a replica"
        );
        assert!(!replica_marker_path(&path).exists());
        // ...and the log is still an ordinary one: a will registered on it fires.
        let will = WillRecord {
            producer_id: 9,
            producer_seq: 4,
            subject: "/f/x/gone".to_string(),
            body: b"gone".to_vec(),
        };
        log.stage_will_register(&will).unwrap();
        log.commit_batch().unwrap();
        assert_eq!(log.stage_will_fire(will).unwrap(), (Offset(1), false));
        log.commit_batch().unwrap();
        drop(log);
    }

    /// The follower bring-up the rule exists to allow is unchanged: an EMPTY log
    /// takes a leader's first shipped record, is declared a replica by it, and the
    /// rest of that same batch — hidden records included, which is what a guarded
    /// leader's own first records are — lands beside it.
    #[test]
    fn a_leaders_first_batch_still_declares_an_empty_log_and_carries_its_hidden_records() {
        let (_tmp, path) = tmp("bringup");
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(replica_marker_path(&path));
        let mut log = BrokerLog::open(&path).unwrap();
        assert_eq!(
            log.stage_replica(replicated(0, "/f/x/one", b"first".to_vec()))
                .unwrap(),
            (Offset(0), false)
        );
        assert!(log.is_replica(), "the first shipped record declares it");
        assert!(replica_marker_path(&path).exists());
        assert_eq!(
            log.stage_replica(replicated(1, BIND_SUBJECT, b"leader-principal".to_vec()))
                .unwrap(),
            (Offset(1), false),
            "a hidden record later in the SAME batch still ships: the log is a replica"
        );
        assert_eq!(
            log.stage_replica(replicated(2, WILL_SUBJECT, will_body("/f/x/gone", b"gone")))
                .unwrap(),
            (Offset(2), false)
        );
        log.commit_batch().unwrap();
        assert_eq!(log.head(), Offset(3));
        drop(log);
    }

    /// A replica takes every record its leader committed: the distinct-subject bound
    /// is the LEADER's admission policy, and a follower's view of it can differ (its
    /// will reservations are rebuilt only when IT reopens). Here the follower still
    /// holds the reservations of every will the leader shipped, while the leader —
    /// reopened, holding only the latest — accepted a publish on a new subject.
    #[test]
    fn a_replica_takes_a_record_its_own_subject_budget_would_refuse() {
        let (_tmp, path) = tmp("replicabound");
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(replica_marker_path(&path));
        let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
        let n = MAX_SUBJECTS_PER_PRODUCER as u64;
        for i in 0..n {
            let will = will_body(&format!("/f/x/gone{i}"), b"gone");
            log.stage_replica(replicated(i, WILL_SUBJECT, will))
                .unwrap();
        }
        log.commit_batch().unwrap();
        assert_eq!(log.will_reserved_subjects(4242), MAX_SUBJECTS_PER_PRODUCER);
        assert_eq!(
            log.stage_replica(replicated(n, "/f/x/new", b"hello".to_vec()))
                .unwrap(),
            (Offset(n), false),
            "the follower refused a record its leader committed"
        );
        log.commit_batch().unwrap();
        drop(log);
    }

    /// AN ACK IS NOT AN INCARNATION. `ack` keys its record `ACK_SEQ_BASE | offset`,
    /// which is above every sequence a will can hold, so folding acks into the fence's
    /// high water would fence that producer's will permanently — the goodbye would
    /// never land, on the connection's end or on any later open, and the refusal would
    /// reach nobody. The reserved half is excluded on all three paths the fence reads:
    /// the durable fold, the in-flight batch, and the rebuild on open.
    #[test]
    fn an_ack_does_not_raise_the_will_fence() {
        let (_tmp, path) = tmp("ackfence");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(7, 5, "/f/x/live".into(), b"state=live".to_vec())
            .unwrap();
        log.publish(7, ACK_SEQ_BASE | 3, "/f/x/answers".into(), b"a".to_vec())
            .unwrap();
        assert_eq!(
            log.producer_high_water(7),
            Some(5),
            "the durable fold took the ack for an incarnation"
        );
        log.stage_publish(7, ACK_SEQ_BASE | 9, "/f/x/answers".into(), b"b".to_vec())
            .unwrap();
        assert_eq!(
            log.producer_high_water(7),
            Some(5),
            "the in-flight batch took the ack for an incarnation"
        );
        log.commit_batch().unwrap();
        drop(log);
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(
            log.producer_high_water(7),
            Some(5),
            "the rebuild on open took the ack for an incarnation"
        );
        drop(log);
    }

    /// A will may not be registered in the reserved half. The fence does not reach
    /// there, so such a will could never be fenced by a later record — a goodbye its
    /// producer had already outlived would fire over a live node's `state=live`.
    /// Refused at REGISTRATION, the only point where the client is listening.
    #[test]
    fn a_will_in_the_reserved_ack_half_is_refused_at_registration() {
        let (_tmp, path) = tmp("willreserved");
        let _ = std::fs::remove_file(&path);
        let mut log = BrokerLog::open(&path).unwrap();
        let will = WillRecord {
            producer_id: 7,
            producer_seq: ACK_SEQ_BASE | 4,
            subject: "/f/x/gone".to_string(),
            body: b"gone".to_vec(),
        };
        match log.stage_will_register(&will) {
            Err(StageErr::SeqReserved(msg)) => assert!(msg.contains("reserved for acks"), "{msg}"),
            other => panic!("the will was accepted in the ack half: {other:?}"),
        }
        assert_eq!(log.head(), Offset(0), "nothing was appended");
        // One sequence below the reservation is an ordinary will.
        let ok = WillRecord {
            producer_seq: ACK_SEQ_BASE - 1,
            ..will
        };
        log.stage_will_register(&ok).unwrap();
        log.commit_batch().unwrap();
        assert_eq!(log.pending_wills(), vec![ok]);
        drop(log);
    }
}

/// Model-based verification: run random sequences of staged operations through BOTH the
/// real file-backed `BrokerLog` (the group-commit `stage_*` + `commit_batch` path) AND
/// an in-memory reference model of the log's observable semantics (the SPEC), and
/// assert they agree — at every flush, and after recovery from a simulated crash.
///
/// The model is a deliberately-trivial spec (a `Vec` + two `HashMap`s); the real log
/// adds encoding, fsync, the recovery scan, and rollback. Agreement over many seeded
/// random sequences cross-checks offset assignment, exactly-once dedup (the durable AND
/// the in-batch dedup maps are compared directly, so the commit-subject-skips-dedup
/// rule is load-bearing: producer 0 publishes are in the mix and a commit record's
/// (0,0) key must NOT shadow them), the group-commit `.max()` monotonicity, the
/// reserved-subject refusal, and CRASH RECOVERY: a random step drops the log with an
/// unsynced staged batch and cuts the file mid-frame (or zero-fills the tail), and the
/// reopened log must equal the model's rule "the staged records wholly on disk landed;
/// the torn one and everything after it did not". The model shares the impl's staging
/// vocabulary (it is a spec of the same interface, not a foreign oracle); what it
/// independently pins down is the observable state after every flush and crash.
/// Std-only (a seeded xorshift PRNG): reproducible, and no third-party dev-dependency.
#[cfg(test)]
mod model_tests {
    use super::*;
    use std::collections::HashMap;

    /// Removes a seed's log when dropped, so a failing seed leaves nothing behind.
    struct Cleanup(PathBuf);

    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    /// xorshift64* — a tiny deterministic PRNG (std-only, reproducible per seed).
    struct Rng(u64);
    impl Rng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n
        }
    }

    /// The reference SPEC of the log's observable semantics. `durable` mirrors
    /// `read_from(0)` (offset, subject, body) for EVERY record (commit records too, on
    /// the unified axis); `pending` is the not-yet-fsync'd batch.
    #[derive(Default)]
    struct Model {
        durable: Vec<(u64, String, Vec<u8>)>,
        dedup: HashMap<(u64, u64), u64>,
        gc: HashMap<String, u64>,
        next: u64,
        pending: Vec<Rec>,
        pdedup: HashMap<(u64, u64), u64>,
    }
    struct Rec {
        off: u64,
        dedup_key: Option<(u64, u64)>, // Some iff subject != COMMIT_SUBJECT
        pid: u64,
        pseq: u64,
        subject: String,
        body: Vec<u8>,
        commit: Option<(String, u64)>,
    }
    impl Model {
        fn dup_offset(&self, key: (u64, u64)) -> Option<u64> {
            self.dedup
                .get(&key)
                .or_else(|| self.pdedup.get(&key))
                .copied()
        }
        fn stage_publish(
            &mut self,
            pid: u64,
            pseq: u64,
            subject: String,
            body: Vec<u8>,
        ) -> (u64, bool) {
            if let Some(o) = self.dup_offset((pid, pseq)) {
                return (o, true);
            }
            let off = self.next + self.pending.len() as u64;
            self.pdedup.insert((pid, pseq), off);
            self.pending.push(Rec {
                off,
                dedup_key: Some((pid, pseq)),
                pid,
                pseq,
                subject,
                body,
                commit: None,
            });
            (off, false)
        }
        fn stage_commit(&mut self, group: String, upto: u64) -> u64 {
            let off = self.next + self.pending.len() as u64;
            self.pending.push(Rec {
                off,
                dedup_key: None,
                pid: 0,
                pseq: 0,
                subject: COMMIT_SUBJECT.to_string(),
                body: Vec::new(),
                commit: Some((group, upto)),
            });
            off
        }
        #[allow(clippy::too_many_arguments)]
        fn stage_rpw(
            &mut self,
            pid: u64,
            pseq: u64,
            subject: String,
            body: Vec<u8>,
            group: String,
            upto: u64,
        ) -> (u64, bool) {
            if let Some(o) = self.dup_offset((pid, pseq)) {
                return (o, true);
            }
            let off = self.next + self.pending.len() as u64;
            self.pdedup.insert((pid, pseq), off);
            self.pending.push(Rec {
                off,
                dedup_key: Some((pid, pseq)),
                pid,
                pseq,
                subject,
                body,
                commit: Some((group, upto)),
            });
            (off, false)
        }
        fn promote(&mut self, r: Rec) {
            if let Some(k) = r.dedup_key {
                self.dedup.insert(k, r.off);
            }
            if let Some((g, u)) = &r.commit {
                let e = self.gc.entry(g.clone()).or_insert(0);
                *e = (*e).max(*u);
            }
            self.next += 1;
            self.durable.push((r.off, r.subject, r.body));
        }
        fn commit_batch(&mut self) {
            for r in std::mem::take(&mut self.pending) {
                self.promote(r);
            }
            self.pdedup.clear();
        }
        /// The crash rule: the first `landed` staged records were wholly on disk and
        /// are recovered as durable (an un-acked write that landed); the rest are gone.
        fn crash(&mut self, landed: usize) {
            let pending = std::mem::take(&mut self.pending);
            for (i, r) in pending.into_iter().enumerate() {
                if i < landed {
                    self.promote(r);
                }
            }
            self.pdedup.clear();
        }
        fn group_start(&self, g: &str) -> u64 {
            self.gc.get(g).map(|u| u.saturating_add(1)).unwrap_or(0)
        }
        /// The on-disk frame length of each pending record, from the SAME encoder the
        /// log uses (the cut points must fall on real frame boundaries).
        fn pending_frame_lens(&self) -> Vec<usize> {
            self.pending
                .iter()
                .map(|r| {
                    BrokerRecord {
                        seq: Offset(r.off),
                        producer_id: r.pid,
                        producer_seq: r.pseq,
                        subject: r.subject.clone(),
                        body: r.body.clone(),
                        commit: r.commit.as_ref().map(|(g, u)| GroupCommit {
                            group: g.clone(),
                            upto: *u,
                        }),
                    }
                    .encode()
                    .unwrap()
                    .len()
                })
                .collect()
        }
    }

    fn stage_pub(log: &mut BrokerLog, pid: u64, pseq: u64, s: String, b: Vec<u8>) -> (u64, bool) {
        let (o, d) = log
            .stage_publish(pid, pseq, s, b)
            .expect("tiny op never errors");
        (o.0, d)
    }

    fn sorted_map(m: &HashMap<(u64, u64), Offset>) -> Vec<((u64, u64), u64)> {
        let mut v: Vec<_> = m.iter().map(|(k, o)| (*k, o.0)).collect();
        v.sort_unstable();
        v
    }
    fn sorted_model_map(m: &HashMap<(u64, u64), u64>) -> Vec<((u64, u64), u64)> {
        let mut v: Vec<_> = m.iter().map(|(k, o)| (*k, *o)).collect();
        v.sort_unstable();
        v
    }

    /// The in-flight (staged) view must match after every stage op.
    fn compare_staged(log: &BrokerLog, model: &Model, ctx: &str) {
        assert_eq!(
            sorted_map(&log.staged_dedup),
            sorted_model_map(&model.pdedup),
            "{ctx}: in-batch dedup map"
        );
        assert_eq!(log.staged.len(), model.pending.len(), "{ctx}: staged count");
    }

    fn compare(log: &BrokerLog, model: &Model, ctx: &str) {
        assert_eq!(log.head().0, model.next, "{ctx}: head");
        let recs: Vec<(u64, String, Vec<u8>)> = log
            .read_from(Offset(0))
            .into_iter()
            .map(|r| (r.seq.0, r.subject.clone(), r.body.clone()))
            .collect();
        assert_eq!(recs, model.durable, "{ctx}: durable records");
        // The dedup map itself, not just its effect on a few probes: commit records
        // must be absent from it and every publish/rpw key present at its offset.
        assert_eq!(
            sorted_map(&log.dedup),
            sorted_model_map(&model.dedup),
            "{ctx}: durable dedup map"
        );
        for g in ["g0", "g1", "g2"] {
            assert_eq!(
                log.group_start(g).0,
                model.group_start(g),
                "{ctx}: group_start {g}"
            );
        }
        compare_staged(log, model, ctx);
    }

    #[test]
    fn staged_log_matches_reference_model_over_random_sequences() {
        const SEEDS: u64 = 120;
        let pid_proc = std::process::id();
        for seed in 0..SEEDS {
            let path = std::env::temp_dir().join(format!("astream_model_{pid_proc}_{seed}.log"));
            let _ = std::fs::remove_file(&path);
            let _tmp = Cleanup(path.clone());

            let mut model = Model::default();
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
            {
                let mut log = BrokerLog::open(&path).unwrap();
                let steps = 6 + rng.below(26);
                for _ in 0..steps {
                    match rng.below(6) {
                        0 => {
                            // producer 0 is in the mix: its keys must never be shadowed
                            // by a commit record's (0,0) identity.
                            let pid = rng.below(5);
                            let pseq = rng.below(7);
                            let subj = format!("/a/s/{}", rng.below(3));
                            let body = vec![rng.below(256) as u8];
                            let r = stage_pub(&mut log, pid, pseq, subj.clone(), body.clone());
                            let m = model.stage_publish(pid, pseq, subj, body);
                            assert_eq!(r, m, "seed {seed}: stage_publish");
                            compare_staged(&log, &model, &format!("seed {seed} after publish"));
                        }
                        1 => {
                            let group = format!("g{}", rng.below(3));
                            let upto = rng.below(50);
                            let r = log.stage_commit(group.clone(), upto).unwrap().0;
                            let m = model.stage_commit(group, upto);
                            assert_eq!(r, m, "seed {seed}: stage_commit");
                            compare_staged(&log, &model, &format!("seed {seed} after commit"));
                        }
                        2 => {
                            let pid = rng.below(5);
                            let pseq = rng.below(7);
                            let subj = format!("/a/out/{}", rng.below(3));
                            let body = vec![rng.below(256) as u8];
                            let group = format!("g{}", rng.below(3));
                            let upto = rng.below(50);
                            let (o, d) = log
                                .stage_process_and_produce(
                                    pid,
                                    pseq,
                                    subj.clone(),
                                    body.clone(),
                                    group.clone(),
                                    upto,
                                )
                                .expect("tiny op never errors");
                            let m = model.stage_rpw(pid, pseq, subj, body, group, upto);
                            assert_eq!((o.0, d), m, "seed {seed}: stage_rpw");
                            compare_staged(&log, &model, &format!("seed {seed} after rpw"));
                        }
                        3 => {
                            // The reserved subject is refused and changes nothing.
                            let pid = rng.below(5);
                            let pseq = rng.below(7);
                            assert!(matches!(
                                log.stage_publish(pid, pseq, COMMIT_SUBJECT.into(), vec![1]),
                                Err(StageErr::Reserved(_))
                            ));
                            compare_staged(&log, &model, &format!("seed {seed} after reserved"));
                        }
                        4 => {
                            // CRASH with an unsynced staged batch on disk: the process
                            // dies and the tail is cut mid-frame (a torn write) or
                            // zero-filled. Recovery must equal the model's crash rule.
                            let lens = model.pending_frame_lens();
                            let durable_len = log.bytes().len();
                            let landed = rng.below(lens.len() as u64 + 1) as usize;
                            let mut keep = durable_len + lens[..landed].iter().sum::<usize>();
                            // Zero-fill (the file extended, the data blocks never
                            // landed) starts at a frame boundary; a prefix cut (the
                            // write stopped mid-frame) can fall anywhere in the frame.
                            let zero_fill = landed < lens.len() && rng.below(3) == 0;
                            if landed < lens.len() && !zero_fill {
                                keep += rng.below(lens[landed] as u64) as usize;
                            }
                            // The process dies inside `commit_batch`, between the
                            // batch's write and its fsync: the staged bytes reached the
                            // file, and the crash keeps only a prefix of them.
                            let staged = log.staged_bytes.clone();
                            assert_eq!(staged.len(), lens.iter().sum::<usize>());
                            drop(log);
                            OpenOptions::new()
                                .append(true)
                                .open(&path)
                                .unwrap()
                                .write_all(&staged)
                                .unwrap();
                            {
                                let f = OpenOptions::new().write(true).open(&path).unwrap();
                                if zero_fill {
                                    let total = f.metadata().unwrap().len() as usize;
                                    let mut f = f;
                                    f.seek(SeekFrom::Start(keep as u64)).unwrap();
                                    f.write_all(&vec![0u8; total - keep]).unwrap();
                                } else {
                                    f.set_len(keep as u64).unwrap();
                                }
                            }
                            log = BrokerLog::open(&path).unwrap();
                            model.crash(landed);
                            assert_eq!(
                                log.bytes().len(),
                                durable_len + lens[..landed].iter().sum::<usize>(),
                                "seed {seed}: the torn/zero tail was truncated off"
                            );
                            compare(&log, &model, &format!("seed {seed} after crash"));
                        }
                        _ => {
                            log.commit_batch().unwrap();
                            model.commit_batch();
                            compare(&log, &model, &format!("seed {seed} mid-flush"));
                        }
                    }
                }
                log.commit_batch().unwrap();
                model.commit_batch();
                compare(&log, &model, &format!("seed {seed} final-flush"));
            }

            // RECOVERY: reopen from disk; the recovered state must equal the model.
            let mut log2 = BrokerLog::open(&path).unwrap();
            compare(&log2, &model, &format!("seed {seed} after-reopen"));
            // dedup survived the restart: every known key re-stages as a deduped hit to
            // its original offset (and appends nothing).
            for (&(pid, pseq), &off) in model.dedup.iter() {
                let (o, d) = stage_pub(&mut log2, pid, pseq, "/a/s/0".into(), vec![0]);
                assert_eq!(
                    (o, d),
                    (off, true),
                    "seed {seed}: dedup recovered for ({pid},{pseq})"
                );
            }
            log2.abort_batch(); // discard the throwaway dedup probes (none staged)
        }
    }
}
