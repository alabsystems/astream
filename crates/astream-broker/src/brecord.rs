//! The broker's durable record skin: a versioned, CRC-framed message carrying its
//! subject and the producer idempotency key. Disjoint from the engine
//! `ENV_VERSION`, the cognition `COG_VERSION`, and the durable-exec `STEP_VERSION`
//! — the broker reuses the `astream_wire::Frame` codec (CRC + 16 MiB cap), not the
//! engine `Envelope` (which carries no `Subject` and no publish key).
//!
//! ONE `encode`/`from_payload` pair is used by BOTH append and recover, so a
//! restart reconstructs records and the dedup map byte-for-byte (round-trip test).

use astream_wire::{CausalEdge, Frame, FrameError, Offset, MAX_PAYLOAD_LEN};

#[cfg(clean_islands)]
#[path = "brecord_island.rs"]
mod brecord_island;
#[cfg(not(clean_islands))]
pub use crate::twins::brecord_clamp_body_len;
#[cfg(clean_islands)]
pub use brecord_island::brecord_clamp_body_len;

contract_fn! {
    /// Verified check that a broker record version byte matches the current format
    /// (`ver == 2`), linked via `clean-kernel-defeq` to `brecord_version_current_isl`.
    #[must_use]
    pub const fn brecord_version_current(ver: u8) -> bool
    clauses [ensures result == (ver == 2)]
    {
        ver == 2
    }
}

/// Broker record format version (2 adds the optional atomic `commit` annotation).
///
/// Every stored record's payload starts with this byte, and a log is read record by
/// record, so a log holds whatever versions wrote it. EVERY version keeps the same
/// first nine bytes — this byte, then the record's own offset as a little-endian
/// `u64` — because that prefix is how an older build tells a newer record from
/// damage.
///
/// A FORMAT CHANGE — bumping this, or changing what an existing version's stored
/// bytes mean (a hidden record's body, a durable key's derivation, a sidecar beside
/// the log) — ships, in the same change:
///
/// - a READ-THROUGH: [`BrokerRecord::from_payload`] decodes every version an astream
///   release has written up to the new one (fields the old one lacks take their
///   defaults), so every existing log still opens, while appends write the newest;
/// - a FIXTURE of the previous format: a small log written by the last release,
///   committed as bytes and never regenerated, and a test that this build opens it
///   and reads its records back as that release wrote them.
///
/// The other direction is already handled and needs nothing new: a build that meets
/// a record above its own version refuses the log by name — written by a newer
/// astream, `ErrorKind::Unsupported` — on `open` and `open_repair` alike, never as
/// corruption and never truncated. (v1 is not read: 2b84f85 dropped it with no
/// read-through, before this rule was written down.)
///
/// # The batch marks, in every version from 2 on
///
/// Every record the log writes carries a MARK after its last field. The LAST record of
/// a batch carries a 5-byte SEAL: [`SEAL_TAG`] (`0xB5`), then the batch's record count
/// as a little-endian `u32` (at least 1); the batch is the records
/// `seq - count + 1 ..= seq`. Every OTHER record of the batch carries the one byte
/// [`CONTINUES_TAG`] (`0xB4`): the batch goes on past it. A record with NOTHING after
/// its last field was written by a build that predates the marks. A stored record's
/// payload therefore ends in exactly one of three ways — at its last field, or there
/// plus one well-formed mark — and anything else after the last field is not a record
/// this build reads ([`from_payload`](BrokerRecord::from_payload) answers `None`).
///
/// The seal is how recovery finds a batch's start after a power loss: a torn batch is
/// cut at its start, so the log is always a prefix of whole batches, and a sealed batch
/// found intact BEHIND damage proves the damage is not a torn write (see the store's
/// recovery). The continues mark is how recovery tells a torn batch of a sealing build
/// from records an OLDER build appended: a revert to a build that predates the marks
/// (one that predates log identity, too, never rewrites `<log>.id`, so the durable floor
/// a sealing build recorded there still stands), or a copy such a build wrote restored
/// alone, leaves unmarked records above that floor — each written and acked whole, on
/// its own, as a unit no later seal closes. Without the mark the two are the same
/// bytes: records a batch's lost seal never closed, which recovery cuts. With it, an
/// unmarked record ends a unit exactly as a seal does, and only records that SAY their
/// batch goes on can be a torn batch's.
///
/// The marks claim NO version: they are defined as "the bytes after the record's last
/// field, in every record version from 2 on", so a future version (a writer-staged
/// retire's marker, say) keeps them after its own last field. A different suffix is a
/// version bump under the rule above. They cost one byte per record that is not a
/// batch's last, and five per batch.
///
/// Why inside the record and not a frame of its own: every v2 parser since `2b84f85`
/// returns at the commit field without looking at what follows, so an OLDER build
/// decodes a sealed record as the same record and reads a sealed log unchanged — a
/// revert costs no outage and tempts no repair — and every stored frame is still
/// exactly one record, so no walker of stored frames (the identity fingerprint, the
/// retention cut, the torn-tail probe) changes. The fixtures under
/// `crates/astream-broker/tests/fixtures/` hold both directions: an unsealed log the
/// last release wrote, read here, and a sealed log read through a frozen copy of the
/// release's parser.
pub const BREC_VERSION: u8 = 2;
/// The first byte of a batch seal: see [`BREC_VERSION`].
pub const SEAL_TAG: u8 = 0xB5;
/// Bytes a batch seal takes: the tag and a `u32` count.
pub const SEAL_LEN: usize = 5;
/// The one byte every record of a batch but its last carries after its last field:
/// the batch continues past it. See [`BREC_VERSION`].
pub const CONTINUES_TAG: u8 = 0xB4;
/// Tag byte introducing the optional 9-byte broker-stamped monotone wall-clock
/// trailer (`[BT_TAG, bt_ms_le_8]`) written immediately before the batch `Mark`
/// (`REQUIREMENTS` R3). Pre-R3 builds omit this trailer (`bt = None`).
pub const BT_TAG: u8 = 0xB6;
/// Tag of the origin trailer on a wire `Delivery` that asked for it
/// (`[ORIGIN_TAG, producer_id_le_8, producer_seq_le_8]`, after any `bt=` trailer): who published
/// the record, and under which sequence. Never written to a log.
pub const ORIGIN_TAG: u8 = 0xB7;
/// Byte length of a broker-stamped wall-clock trailer: `BT_TAG` (1) + `u64` LE (8).
pub const BT_LEN: usize = 9;
/// The commit-tag byte on a writer-staged `/a/retire` record (`DESIGN-aterm-fabric`
/// §5.2): an older build's `from_payload_marked` knows only `0` (none) and `1` (group
/// commit) and refuses `2` as malformed (`_ => return None`), failing closed rather than
/// silently reading a retired subject as live.
pub const COMMIT_TAG_RETIRE: u8 = 2;
/// Sentinel `producer_seq` carried by a writer-staged `/a/retire` record (`u64::MAX`):
/// outside the incarnation-derived range `< ACK_SEQ_BASE` (`1 << 63`) that ordinary
/// publishes use, so an unmarked `/a/retire` record written by an older client before
/// `/a/retire` was reserved is distinguished from a marked retire record.
pub const RETIRE_PRODUCER_SEQ: u64 = u64::MAX;

/// What a stored record carries after its last field (see [`BREC_VERSION`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mark {
    /// Nothing: written by a build that predates the batch marks, as a unit of its own.
    Unmarked,
    /// [`CONTINUES_TAG`]: a record of a batch whose last record is still to come.
    Continues,
    /// A [`SEAL_TAG`] seal: the last record of a batch of `count` records.
    Seal(u32),
}

impl Mark {
    /// Whether a unit of the log ENDS at this record — a batch's seal, or a record a
    /// build that predates the marks wrote whole — so the next record starts a new one.
    pub(crate) const fn ends_a_unit(self) -> bool {
        !matches!(self, Mark::Continues)
    }
}

/// Fixed header: version(1) + seq(8) + producer_id(8) + producer_seq(8).
const HEADER: usize = 25;
/// The bytes every unmarked record payload takes beside its subject, its body and its
/// commit's group and offset: the header, the two length prefixes and the commit tag
/// (`retention::record_bytes`).
pub(crate) const RECORD_FIXED_LEN: usize = HEADER + 9;
/// The largest record payload the log accepts: the frame cap minus a margin, so a
/// stored record ALWAYS also fits the frame wherever it is re-framed — inside a
/// `Replicate` request (whose envelope, with the leader's log-identity trailer, is 25
/// bytes larger than the record's own), and sealed at rest on an encrypted log (a
/// 24-byte nonce and a 16-byte tag). A record at the cap could otherwise be committed
/// on a leader yet never be shippable to, or storable on, a follower.
pub const MAX_RECORD_PAYLOAD: usize = MAX_PAYLOAD_LEN - RECORD_MARGIN;
/// The larger of the two re-framing overheads above — the at-rest seal's 40 bytes —
/// plus room for the broker timestamp trailer ([`BT_LEN`], 9 bytes) and the largest
/// batch mark, the seal ([`SEAL_LEN`], 5 bytes), rounded up to 56: a record carries its
/// timestamp and mark INSIDE the payload the at-rest layer seals, so a record at the cap
/// must still fit the frame with all three (`40 + 9 + 5 = 54 <= 56`).
const RECORD_MARGIN: usize = 56;
#[cfg(any(feature = "aead", feature = "at-rest"))]
const _: () = assert!(RECORD_MARGIN >= astream_aead::OVERHEAD + SEAL_LEN + BT_LEN);

/// One durable message on the broker log.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrokerRecord {
    /// This record's own offset (dense from `Offset::ZERO`).
    pub seq: Offset,
    /// The producer's stable id (idempotency key, first half).
    pub producer_id: u64,
    /// The producer's monotone-per-message sequence (idempotency key, second half).
    pub producer_seq: u64,
    /// The validated subject string this message was published to.
    pub subject: String,
    /// The opaque message body.
    pub body: Vec<u8>,
    /// An optional consumer-group commit carried ATOMICALLY by this record. A normal
    /// publish is `None`; a transactional read-process-write (or a pure commit)
    /// stamps `Some(GroupCommit)`, so the produced output and the offset commit land
    /// in ONE durable append (one fsync) — exactly-once processing.
    pub commit: Option<GroupCommit>,
}

/// A consumer group advancing its committed offset to `upto` (the last offset it has
/// fully processed). Carried on a [`BrokerRecord`] so produce+commit is atomic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupCommit {
    /// The consumer group id.
    pub group: String,
    /// The last offset the group has fully processed (resume is `upto + 1`).
    pub upto: u64,
}

/// The bytes a [`BrokerRecord`] takes in a plaintext [`Frame`] (without batch marks,
/// `bt=` trailer, or at-rest AEAD overhead): shared by retention byte accounting
/// (`retention::record_bytes`), wire `Stats` per-face accounting, and `Tier` summaries.
#[must_use]
pub(crate) fn plaintext_frame_bytes(rec: &BrokerRecord) -> u64 {
    let commit = match &rec.commit {
        Some(c) => c.group.len().saturating_add(12),
        None => 0,
    };
    let n = astream_wire::HEADER_SIZE
        .saturating_add(RECORD_FIXED_LEN)
        .saturating_add(rec.subject.len())
        .saturating_add(rec.body.len())
        .saturating_add(commit);
    n as u64
}

const fn encode_u32_le_bytes(v: u32) -> [u8; 4] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]
}

const fn encode_u64_le_bytes(v: u64) -> [u8; 8] {
    [
        v as u8,
        (v >> 8) as u8,
        (v >> 16) as u8,
        (v >> 24) as u8,
        (v >> 32) as u8,
        (v >> 40) as u8,
        (v >> 48) as u8,
        (v >> 56) as u8,
    ]
}

const fn encode_record_header(seq: u64, producer_id: u64, producer_seq: u64) -> [u8; HEADER] {
    [
        BREC_VERSION,
        seq as u8,
        (seq >> 8) as u8,
        (seq >> 16) as u8,
        (seq >> 24) as u8,
        (seq >> 32) as u8,
        (seq >> 40) as u8,
        (seq >> 48) as u8,
        (seq >> 56) as u8,
        producer_id as u8,
        (producer_id >> 8) as u8,
        (producer_id >> 16) as u8,
        (producer_id >> 24) as u8,
        (producer_id >> 32) as u8,
        (producer_id >> 40) as u8,
        (producer_id >> 48) as u8,
        (producer_id >> 56) as u8,
        producer_seq as u8,
        (producer_seq >> 8) as u8,
        (producer_seq >> 16) as u8,
        (producer_seq >> 24) as u8,
        (producer_seq >> 32) as u8,
        (producer_seq >> 40) as u8,
        (producer_seq >> 48) as u8,
        (producer_seq >> 56) as u8,
    ]
}

/// The fixed record fields, subject length, and unconsumed payload.
type RecordHeader<'a> = (u8, Offset, u64, u64, usize, &'a [u8]);

const fn decode_u32_le_bytes(b: &[u8; 4]) -> u32 {
    (b[0] as u32) | ((b[1] as u32) << 8) | ((b[2] as u32) << 16) | ((b[3] as u32) << 24)
}

const fn decode_u64_le_bytes(b: &[u8; 8]) -> u64 {
    (b[0] as u64)
        | ((b[1] as u64) << 8)
        | ((b[2] as u64) << 16)
        | ((b[3] as u64) << 24)
        | ((b[4] as u64) << 32)
        | ((b[5] as u64) << 40)
        | ((b[6] as u64) << 48)
        | ((b[7] as u64) << 56)
}

const fn decode_record_header_bytes(raw: &[u8; 29]) -> (u8, Offset, u64, u64, usize) {
    let version = raw[0];
    let seq = (raw[1] as u64)
        | ((raw[2] as u64) << 8)
        | ((raw[3] as u64) << 16)
        | ((raw[4] as u64) << 24)
        | ((raw[5] as u64) << 32)
        | ((raw[6] as u64) << 40)
        | ((raw[7] as u64) << 48)
        | ((raw[8] as u64) << 56);
    let producer_id = (raw[9] as u64)
        | ((raw[10] as u64) << 8)
        | ((raw[11] as u64) << 16)
        | ((raw[12] as u64) << 24)
        | ((raw[13] as u64) << 32)
        | ((raw[14] as u64) << 40)
        | ((raw[15] as u64) << 48)
        | ((raw[16] as u64) << 56);
    let producer_seq = (raw[17] as u64)
        | ((raw[18] as u64) << 8)
        | ((raw[19] as u64) << 16)
        | ((raw[20] as u64) << 24)
        | ((raw[21] as u64) << 32)
        | ((raw[22] as u64) << 40)
        | ((raw[23] as u64) << 48)
        | ((raw[24] as u64) << 56);
    let sl = ((raw[25] as u32)
        | ((raw[26] as u32) << 8)
        | ((raw[27] as u32) << 16)
        | ((raw[28] as u32) << 24)) as usize;
    (version, Offset(seq), producer_id, producer_seq, sl)
}

const fn decode_record_header_and_sl(p: &[u8]) -> Option<RecordHeader<'_>> {
    let &[version, s0, s1, s2, s3, s4, s5, s6, s7, pid0, pid1, pid2, pid3, pid4, pid5, pid6, pid7, pseq0, pseq1, pseq2, pseq3, pseq4, pseq5, pseq6, pseq7, sl0, sl1, sl2, sl3, ref rest @ ..] =
        p
    else {
        return None;
    };
    let (v, seq, producer_id, producer_seq, sl) = decode_record_header_bytes(&[
        version, s0, s1, s2, s3, s4, s5, s6, s7, pid0, pid1, pid2, pid3, pid4, pid5, pid6, pid7,
        pseq0, pseq1, pseq2, pseq3, pseq4, pseq5, pseq6, pseq7, sl0, sl1, sl2, sl3,
    ]);
    Some((v, seq, producer_id, producer_seq, sl, rest))
}

const fn take_u8(s: &[u8]) -> Option<(u8, &[u8])> {
    let &[b0, ref rest @ ..] = s else {
        return None;
    };
    Some((b0, rest))
}

const fn take_u32_le(s: &[u8]) -> Option<(u32, &[u8])> {
    let &[b0, b1, b2, b3, ref rest @ ..] = s else {
        return None;
    };
    Some((decode_u32_le_bytes(&[b0, b1, b2, b3]), rest))
}

const fn take_u64_le(s: &[u8]) -> Option<(u64, &[u8])> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = s else {
        return None;
    };
    Some((decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7]), rest))
}

const fn decode_mark(rest: &[u8]) -> Option<Mark> {
    match rest {
        [] => Some(Mark::Unmarked),
        [CONTINUES_TAG] => Some(Mark::Continues),
        &[SEAL_TAG, c0, c1, c2, c3] => {
            let count = decode_u32_le_bytes(&[c0, c1, c2, c3]);
            if count == 0 {
                None
            } else {
                Some(Mark::Seal(count))
            }
        }
        _ => None,
    }
}

const fn decode_mark_and_bt(rest: &[u8]) -> Option<(Mark, Option<u64>)> {
    let (bt_ms, after_bt) = match rest {
        &[BT_TAG, b0, b1, b2, b3, b4, b5, b6, b7, ref tail @ ..] => (
            Some(decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7])),
            tail,
        ),
        _ => (None, rest),
    };
    let Some(mark) = decode_mark(after_bt) else {
        return None;
    };
    Some((mark, bt_ms))
}

const fn encode_seal(count: u32) -> [u8; SEAL_LEN] {
    [
        SEAL_TAG,
        count as u8,
        (count >> 8) as u8,
        (count >> 16) as u8,
        (count >> 24) as u8,
    ]
}

const fn decode_newer_format_bytes(raw: &[u8; 9], offset: Option<u64>) -> Option<u8> {
    let version = raw[0];
    let seq = (raw[1] as u64)
        | ((raw[2] as u64) << 8)
        | ((raw[3] as u64) << 16)
        | ((raw[4] as u64) << 24)
        | ((raw[5] as u64) << 32)
        | ((raw[6] as u64) << 40)
        | ((raw[7] as u64) << 48)
        | ((raw[8] as u64) << 56);
    let offset_matches = match offset {
        None => true,
        Some(o) => o == seq,
    };
    if version > BREC_VERSION && offset_matches {
        Some(version)
    } else {
        None
    }
}

/// The record format a stored payload names, when it is NEWER than this build reads,
/// judged by the prefix every version keeps (see [`BREC_VERSION`]): a version byte
/// above this build's, then — when `offset` is known — the record's own offset. Asked
/// only of a payload that passed the frame CRC, so such a record was written by a
/// newer astream, not damaged; the offset check is what keeps a payload this build
/// cannot read for another reason (an encrypted log opened without its key, whose
/// first byte is a random nonce byte) from passing as one. `None` otherwise.
pub(crate) const fn newer_format(p: &[u8], offset: Option<u64>) -> Option<u8> {
    let &[version, b1, b2, b3, b4, b5, b6, b7, b8, ref _rest @ ..] = p else {
        return None;
    };
    decode_newer_format_bytes(&[version, b1, b2, b3, b4, b5, b6, b7, b8], offset)
}

impl BrokerRecord {
    /// Construct a marked `/a/retire` record (`DESIGN-aterm-fabric` §5.2) for
    /// `target_subject` charged to `producer_id` at offset `seq`.
    #[must_use]
    pub fn marked_retire(seq: Offset, producer_id: u64, target_subject: &str) -> Self {
        Self {
            seq,
            producer_id,
            producer_seq: RETIRE_PRODUCER_SEQ,
            subject: crate::store::RETIRE_SUBJECT.to_string(),
            body: target_subject.as_bytes().to_vec(),
            commit: None,
        }
    }

    /// Whether this record is a writer-staged marked `/a/retire` record (`DESIGN-aterm-fabric` §5.2).
    /// This identifies the explicit wire marker only. The store separately recognizes
    /// the previous retirement writer's seq-zero, no-commit header; other unmarked
    /// `/a/retire` records remain ordinary visible legacy data.
    #[must_use]
    pub fn is_marked_retire(&self) -> bool {
        self.subject == crate::store::RETIRE_SUBJECT
            && self.producer_seq == RETIRE_PRODUCER_SEQ
            && self.commit.is_none()
    }

    /// Serialize to a CRC [`Frame`]'s bytes. A field exceeding `u32`, or a payload
    /// over [`MAX_RECORD_PAYLOAD`], is [`FrameError::TooLarge`] (never panics).
    pub fn encode(&self) -> Result<Vec<u8>, FrameError> {
        Frame::new(self.encode_payload()?).encode()
    }

    /// The record's serialized bytes WITHOUT the outer CRC frame — the unit the
    /// at-rest layer seals before framing (so the frame carries ciphertext). The
    /// [`MAX_RECORD_PAYLOAD`] cap is enforced here so it holds for both the plaintext
    /// and the sealed path. Unmarked, as a build that predates the batch marks wrote
    /// it: see [`encode_payload_marked`](Self::encode_payload_marked).
    pub(crate) fn encode_payload(&self) -> Result<Vec<u8>, FrameError> {
        self.encode_payload_marked(Mark::Unmarked)
    }

    /// [`encode_payload`](Self::encode_payload), ending in `mark` (see
    /// [`BREC_VERSION`]). The cap is checked on the record's own fields, before the
    /// mark: [`MAX_RECORD_PAYLOAD`]'s margin keeps room for the largest, so whether a
    /// record fits never depends on where it lands in a batch. A seal's count of 0 is
    /// no batch and is refused (`TooLarge`, the one error this path has).
    pub(crate) fn encode_payload_marked(&self, mark: Mark) -> Result<Vec<u8>, FrameError> {
        self.encode_payload_marked_bt(mark, None)
    }

    /// [`encode_payload_marked`](Self::encode_payload_marked), optionally stamping the
    /// 9-byte monotone broker wall-clock trailer (`[BT_TAG, bt_le_8]`, `REQUIREMENTS` R3)
    /// immediately before `mark`.
    pub(crate) fn encode_payload_marked_bt(
        &self,
        mark: Mark,
        bt_ms: Option<u64>,
    ) -> Result<Vec<u8>, FrameError> {
        // Sized check on the record's own fields before optional bt + mark trailers.
        let commit_len = match &self.commit {
            None => 0usize,
            Some(c) => {
                let Some(n) = c.group.len().checked_add(12) else {
                    return Err(FrameError::TooLarge);
                };
                n
            }
        };
        let Some(n1) = HEADER.saturating_add(9).checked_add(self.subject.len()) else {
            return Err(FrameError::TooLarge);
        };
        let Some(n2) = n1.checked_add(self.body.len()) else {
            return Err(FrameError::TooLarge);
        };
        let Some(unmark_len) = n2.checked_add(commit_len) else {
            return Err(FrameError::TooLarge);
        };
        if unmark_len > MAX_RECORD_PAYLOAD {
            return Err(FrameError::TooLarge);
        }
        let mut p = Vec::new();
        p.extend_from_slice(&encode_record_header(
            self.seq.0,
            self.producer_id,
            self.producer_seq,
        ));
        let Ok(sl) = u32::try_from(self.subject.len()) else {
            return Err(FrameError::TooLarge);
        };
        p.extend_from_slice(&encode_u32_le_bytes(sl));
        p.extend_from_slice(self.subject.as_bytes());
        let Ok(bl) = u32::try_from(self.body.len()) else {
            return Err(FrameError::TooLarge);
        };
        p.extend_from_slice(&encode_u32_le_bytes(bl));
        p.extend_from_slice(&self.body);
        match &self.commit {
            None if self.is_marked_retire() => p.push(COMMIT_TAG_RETIRE),
            None => p.push(0),
            Some(c) => {
                p.push(1);
                let Ok(gl) = u32::try_from(c.group.len()) else {
                    return Err(FrameError::TooLarge);
                };
                p.extend_from_slice(&encode_u32_le_bytes(gl));
                p.extend_from_slice(c.group.as_bytes());
                p.extend_from_slice(&encode_u64_le_bytes(c.upto));
            }
        }
        if p.len() > MAX_RECORD_PAYLOAD {
            return Err(FrameError::TooLarge);
        }
        if let Some(bt) = bt_ms {
            p.push(BT_TAG);
            p.extend_from_slice(&encode_u64_le_bytes(bt));
        }
        match mark {
            Mark::Unmarked => {}
            Mark::Continues => p.push(CONTINUES_TAG),
            Mark::Seal(0) => return Err(FrameError::TooLarge),
            Mark::Seal(count) => p.extend_from_slice(&encode_seal(count)),
        }
        p.shrink_to_fit();
        Ok(p)
    }

    /// Parse from a decoded frame's payload — a record this build reads, marked or not
    /// (see [`BREC_VERSION`]); the mark itself is the store's business. Every read is
    /// bounds-checked, so hostile bytes yield `None`, never a panic.
    pub fn from_payload(p: &[u8]) -> Option<BrokerRecord> {
        let Some((rec, _, _)) = Self::from_payload_marked_bt(p) else {
            return None;
        };
        Some(rec)
    }

    /// [`from_payload`](Self::from_payload), with the batch [`Mark`] the record
    /// carries (ignoring any optional broker timestamp trailer).
    pub(crate) fn from_payload_marked(p: &[u8]) -> Option<(BrokerRecord, Mark)> {
        let Some((rec, mark, _bt)) = Self::from_payload_marked_bt(p) else {
            return None;
        };
        Some((rec, mark))
    }

    /// [`from_payload_marked`](Self::from_payload_marked), also returning the optional
    /// broker-stamped monotone wall-clock time (`bt_ms`, `REQUIREMENTS` R3).
    pub(crate) fn from_payload_marked_bt(p: &[u8]) -> Option<(BrokerRecord, Mark, Option<u64>)> {
        let (version, seq, producer_id, producer_seq, sl, rest) = decode_record_header_and_sl(p)?;
        if !brecord_version_current(version) {
            return None;
        }
        let Some(subj_bytes) = rest.get(..sl) else {
            return None;
        };
        let Some(rest) = rest.get(sl..) else {
            return None;
        };
        let Ok(subject_str) = core::str::from_utf8(subj_bytes) else {
            return None;
        };
        let subject = subject_str.to_owned();
        let (bl_u32, rest) = take_u32_le(rest)?;
        let bl = bl_u32 as usize;
        let Some(body_bytes) = rest.get(..bl) else {
            return None;
        };
        let Some(rest) = rest.get(bl..) else {
            return None;
        };
        let body = body_bytes.to_vec();
        let (commit_tag, mut rest) = take_u8(rest)?;
        let commit = match commit_tag {
            0 => {
                if subject == crate::store::RETIRE_SUBJECT && producer_seq == RETIRE_PRODUCER_SEQ {
                    return None;
                }
                None
            }
            1 => {
                let (gl_u32, after_gl) = take_u32_le(rest)?;
                let gl = gl_u32 as usize;
                let Some(grp_bytes) = after_gl.get(..gl) else {
                    return None;
                };
                let Some(after_grp) = after_gl.get(gl..) else {
                    return None;
                };
                let Ok(group_str) = core::str::from_utf8(grp_bytes) else {
                    return None;
                };
                let group = group_str.to_owned();
                let (upto, after_upto) = take_u64_le(after_grp)?;
                rest = after_upto;
                Some(GroupCommit { group, upto })
            }
            COMMIT_TAG_RETIRE => {
                if subject != crate::store::RETIRE_SUBJECT || producer_seq != RETIRE_PRODUCER_SEQ {
                    return None;
                }
                None
            }
            _ => return None,
        };
        let (mark, bt_ms) = decode_mark_and_bt(rest)?;
        let rec = BrokerRecord {
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit,
        };
        Some((rec, mark, bt_ms))
    }

    /// Project this broker record as a [`CausalEdge<String>`] for [`astream_wire::CausalCut`]
    /// consistency verification, linking `cause_subject` at `cause_offset` to this
    /// record's `(self.subject, self.seq)`.
    #[must_use]
    pub fn causal_edge_from(
        &self,
        cause_subject: &str,
        cause_offset: Offset,
    ) -> CausalEdge<String> {
        CausalEdge {
            cause: (cause_subject.to_owned(), cause_offset),
            effect: (self.subject.clone(), self.seq),
        }
    }

    /// When this record carries an atomic consumer-group commit (`ProcessAndProduce` /
    /// `asb ack`), project the transaction's causal dependency (`(commit.group, commit.upto) -> (self.subject, self.seq)`)
    /// as a [`CausalEdge<String>`].
    #[must_use]
    pub fn commit_causal_edge(&self) -> Option<CausalEdge<String>> {
        match &self.commit {
            Some(c) => Some(CausalEdge {
                cause: (c.group.clone(), Offset(c.upto)),
                effect: (self.subject.clone(), self.seq),
            }),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_through_a_frame() {
        let r = BrokerRecord {
            seq: Offset(7),
            producer_id: 42,
            producer_seq: 3,
            subject: "/a/stream/x".to_string(),
            body: b"hello".to_vec(),
            commit: None,
        };
        let bytes = r.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(BrokerRecord::from_payload(&decoded.frame.payload), Some(r));
    }

    #[test]
    fn round_trips_with_an_atomic_commit() {
        let r = BrokerRecord {
            seq: Offset(3),
            producer_id: 1,
            producer_seq: 1,
            subject: "/a/out/y".to_string(),
            body: b"processed".to_vec(),
            commit: Some(GroupCommit {
                group: "g1".to_string(),
                upto: 9,
            }),
        };
        let bytes = r.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(BrokerRecord::from_payload(&decoded.frame.payload), Some(r));
    }

    /// A record at the record cap encodes; one byte over is `TooLarge` — and the cap
    /// leaves room for the larger `Replicate` envelope around the same record.
    #[test]
    fn record_cap_leaves_room_for_the_replicate_envelope() {
        let fixed = 1 + 8 + 8 + 8 + 4 + 4 + 1; // version, seq, ids, two lengths, commit tag
        let at_cap = BrokerRecord {
            seq: Offset(1),
            producer_id: 1,
            producer_seq: 1,
            subject: String::new(),
            body: vec![7u8; MAX_RECORD_PAYLOAD - fixed],
            commit: None,
        };
        let bytes = at_cap.encode().expect("at the record cap encodes");
        assert_eq!(bytes.len(), 12 + MAX_RECORD_PAYLOAD);
        // The largest envelope: the leader's log-identity trailer included.
        let leader = crate::LogIdentity {
            id: [1; 16],
            generation: 1,
        };
        let req = crate::proto::encode_replicate(1, 1, 1, "", &at_cap.body, None, Some(&leader));
        assert!(
            Frame::new(req).encode().is_ok(),
            "the same record inside a Replicate request still fits the frame cap"
        );
        let over = BrokerRecord {
            body: vec![7u8; MAX_RECORD_PAYLOAD - fixed + 1],
            ..at_cap
        };
        assert_eq!(over.encode(), Err(FrameError::TooLarge));
    }

    /// The payload buffer is sized exactly, with or without a commit, so encoding
    /// never grows (reallocates and copies) it.
    #[test]
    fn encode_payload_sizes_its_buffer_exactly() {
        for commit in [
            None,
            Some(GroupCommit {
                group: "g1".to_string(),
                upto: 9,
            }),
        ] {
            let r = BrokerRecord {
                seq: Offset(1),
                producer_id: 1,
                producer_seq: 1,
                subject: "/a/x".to_string(),
                body: vec![7u8; 1000],
                commit,
            };
            let p = r.encode_payload().unwrap();
            assert_eq!(p.capacity(), p.len());
        }
    }

    #[test]
    fn rejects_truncated_payload_without_panicking() {
        assert_eq!(BrokerRecord::from_payload(&[BREC_VERSION, 1, 2]), None);
        // Claims a 1000-byte subject with none present.
        let mut p = vec![BREC_VERSION];
        p.extend_from_slice(&[0u8; 24]); // seq + ids
        p.extend_from_slice(&1000u32.to_le_bytes());
        assert_eq!(BrokerRecord::from_payload(&p), None);
    }

    /// A sealed record decodes as the same record, with its count; a continuing one
    /// with the continues mark; an unmarked one as a build before the marks wrote it.
    /// With and without a commit, since the mark follows whichever field is last.
    #[test]
    fn a_mark_follows_the_last_field_and_round_trips() {
        for commit in [
            None,
            Some(GroupCommit {
                group: "g".to_string(),
                upto: 4,
            }),
        ] {
            let r = BrokerRecord {
                seq: Offset(9),
                producer_id: 3,
                producer_seq: 1,
                subject: "/a/x".to_string(),
                body: b"body".to_vec(),
                commit,
            };
            let plain = r.encode_payload().unwrap();
            let sealed = r.encode_payload_marked(Mark::Seal(3)).unwrap();
            let continues = r.encode_payload_marked(Mark::Continues).unwrap();
            assert_eq!(sealed.len(), plain.len() + SEAL_LEN);
            assert_eq!(&sealed[..plain.len()], &plain[..], "the seal only appends");
            assert_eq!(&sealed[plain.len()..], &[SEAL_TAG, 3, 0, 0, 0]);
            assert_eq!(
                &continues[..plain.len()],
                &plain[..],
                "the mark only appends"
            );
            assert_eq!(&continues[plain.len()..], &[CONTINUES_TAG]);
            assert_eq!(
                BrokerRecord::from_payload_marked(&sealed),
                Some((r.clone(), Mark::Seal(3)))
            );
            assert_eq!(
                BrokerRecord::from_payload_marked(&continues),
                Some((r.clone(), Mark::Continues))
            );
            assert_eq!(BrokerRecord::from_payload(&sealed), Some(r.clone()));
            assert_eq!(BrokerRecord::from_payload(&continues), Some(r.clone()));
            assert_eq!(
                BrokerRecord::from_payload_marked(&plain),
                Some((r.clone(), Mark::Unmarked))
            );
            for p in [&sealed, &continues] {
                assert_eq!(p.capacity(), p.len(), "sized exactly, mark included");
            }
        }
        assert!(Mark::Seal(1).ends_a_unit() && Mark::Unmarked.ends_a_unit());
        assert!(!Mark::Continues.ends_a_unit());
    }

    /// After the last field there is nothing, the continues byte, or exactly one
    /// well-formed seal: a seal cut short, one with more behind it, a zero count, a
    /// continues byte with anything behind it, another tag or a stray byte is not a
    /// record this build reads. And a count of 0 is never written.
    #[test]
    fn anything_but_one_mark_after_the_last_field_is_not_a_record() {
        let r = BrokerRecord {
            seq: Offset(1),
            producer_id: 1,
            producer_seq: 1,
            subject: "/a/x".to_string(),
            body: Vec::new(),
            commit: None,
        };
        let plain = r.encode_payload().unwrap();
        let with = |tail: &[u8]| [&plain[..], tail].concat();
        for tail in [
            &[SEAL_TAG, 1, 0, 0][..],
            &[SEAL_TAG, 1, 0, 0, 0, 0],
            &[SEAL_TAG, 0, 0, 0, 0],
            &[CONTINUES_TAG, 0],
            &[CONTINUES_TAG, CONTINUES_TAG],
            &[CONTINUES_TAG, SEAL_TAG, 1, 0, 0, 0],
            &[0xB6, 1, 0, 0, 0],
            &[0],
        ] {
            assert_eq!(
                BrokerRecord::from_payload_marked(&with(tail)),
                None,
                "{tail:?}"
            );
        }
        assert_eq!(
            r.encode_payload_marked(Mark::Seal(0)),
            Err(FrameError::TooLarge)
        );
    }

    /// A record at the cap still takes its seal, and the sealed payload still fits the
    /// frame with the at-rest overhead on top: the margin leaves room for both.
    #[test]
    fn a_record_at_the_cap_takes_its_seal_and_still_fits_sealed_at_rest() {
        let fixed = 1 + 8 + 8 + 8 + 4 + 4 + 1;
        let at_cap = BrokerRecord {
            seq: Offset(1),
            producer_id: 1,
            producer_seq: 1,
            subject: String::new(),
            body: vec![7u8; MAX_RECORD_PAYLOAD - fixed],
            commit: None,
        };
        let sealed = at_cap.encode_payload_marked(Mark::Seal(u32::MAX)).unwrap();
        assert_eq!(sealed.len(), MAX_RECORD_PAYLOAD + SEAL_LEN);
        // The at-rest layer's nonce and tag: 40 bytes.
        assert!(sealed.len() + 40 <= MAX_PAYLOAD_LEN);
        assert!(Frame::new(vec![0u8; sealed.len() + 40]).encode().is_ok());
    }

    #[test]
    fn broker_record_causal_edges_project_into_causal_cut() {
        let rec = BrokerRecord {
            seq: Offset(12),
            producer_id: 9,
            producer_seq: 4,
            subject: "/f/F/ack/s-1".to_string(),
            body: b"handled".to_vec(),
            commit: Some(GroupCommit {
                group: "/f/F/in/s-1".to_string(),
                upto: 7,
            }),
        };
        let edge1 = rec.causal_edge_from("/f/F/in/s-1", Offset(7));
        let edge2 = rec.commit_causal_edge().unwrap();
        assert_eq!(edge1, edge2);

        let mut cut = crate::CausalCut::new();
        cut.set("/f/F/ack/s-1".to_string(), Offset(12));
        cut.set("/f/F/in/s-1".to_string(), Offset(6));
        assert!(!cut.is_consistent(std::slice::from_ref(&edge1)));
        assert_eq!(cut.heal(&[edge1]), 1);
        assert!(cut.includes(&"/f/F/in/s-1".to_string(), Offset(7)));
    }
}
