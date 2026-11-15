//! The record envelope: the versioned on-wire skin over an [`astream_term::Record`].
//!
//! `astream_wire::Frame` carries an opaque payload and an unused `flags` byte
//! (hardcoded 0), so record-type dispatch is a **1-byte tag at the head of the
//! payload**, never a frame flag. The envelope is what makes the log
//! self-describing — its own offset and the logical clock travel with it:
//!
//! ```text
//! payload =
//!   | ENV_VERSION: u8 = 3 |   unknown => Err(BadVersion); bumped by any new field
//!   | tag: u8           |   1=In 2=Out 3=Resize 4=Exit; 0 reserved => Err(BadTag)
//!   | seq: u64 LE       |   = Offset.0, this record's own offset
//!   | ts_logical: u64 LE|   from the seam Clock at append time (a recorded input)
//!   | cause_present: u8 |   0 => uncaused; 1 => a cause block follows
//!   |   [cause_offset: u64 LE     ]  the causing record's offset
//!   |   [cause_part_present: u8   ]  0 => same-log self-cause; 1 => a partition follows
//!   |     [cause_partition: u64 LE]  the causing record's partition (cross-log)
//!   | body ...          |   per-tag
//! ```
//!
//! `caused_by` is the **durable** causal pointer: an injected `In` can name the
//! orchestrator `Out` (in another partition) that produced it, so the fleet's
//! cross-edges survive crash/reconnect ON THE LOG rather than only in memory. Every
//! variable read in the cause block is bounds-checked, like the body.
//!
//! Per-tag body: `In` = `client_id,client_seq: u64 LE | len: u32 LE | bytes`;
//! `Out` = `len: u32 LE | bytes`; `Resize` = `cols,rows: u16 LE`; `Exit` =
//! `code: i32 LE`. Decoding is panic-free on hostile input — every fixed read and
//! every `u32` length is bounds-checked before slicing, the same discipline as
//! `Frame::decode`.

use astream_term::Record;
use astream_wire::{Frame, FrameError, Offset};

#[cfg(test)]
#[path = "envelope_legacy_tests.rs"]
pub(crate) mod legacy;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "envelope_island.rs"]
mod envelope_island;
#[cfg(not(clean_islands))]
pub use crate::twins::envelope_clamp_cause_len;
#[cfg(clean_islands)]
pub use envelope_island::envelope_clamp_cause_len;

contract_fn! {
    /// Kernel-certified check that an envelope's version byte equals [`ENV_VERSION`] (`3`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `envelope_version_valid_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn envelope_version_valid(version: u8) -> bool
    clauses [ensures result == (version == 3)]
    {
        version == 3
    }
}

/// Current envelope format version.
pub const ENV_VERSION: u8 = 3;
/// Tag for [`Record::In`].
pub const TAG_IN: u8 = 1;
/// Tag for [`Record::Out`].
pub const TAG_OUT: u8 = 2;
/// Tag for [`Record::Resize`].
pub const TAG_RESIZE: u8 = 3;
/// Tag for [`Record::Exit`].
pub const TAG_EXIT: u8 = 4;

/// Fixed header bytes: version(1) + tag(1) + seq(8) + ts_logical(8).
const HEADER_LEN: usize = 18;

/// A durable causal pointer: the record that produced this one. `partition` is
/// `None` for a same-log self-cause (an echo `Out` naming the `In` it answers) and
/// `Some(p)` for a cross-log cause (an injected `In` naming the orchestrator `Out`
/// in partition `p`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CausedBy {
    /// The causing record's partition, or `None` if it is in this same log.
    pub partition: Option<u64>,
    /// The causing record's offset.
    pub offset: u64,
}

/// One log record plus the header the engine stamps onto it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Envelope {
    /// This record's own offset.
    pub seq: Offset,
    /// The logical clock value read through the seam at append time.
    pub ts_logical: u64,
    /// The record that caused this one, if any (durable causality).
    pub caused_by: Option<CausedBy>,
    /// The session record itself ([`astream_term::Record`]).
    pub record: Record,
}

/// Fully validated envelope metadata. Body bytes are checked through the same
/// decoder as owned records, but header-only consumers never materialize them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EnvelopeMetadata {
    pub(crate) seq: Offset,
    pub(crate) ts_logical: u64,
    pub(crate) caused_by: Option<CausedBy>,
    input_key: Option<(u64, u64)>,
}

impl EnvelopeMetadata {
    pub(crate) fn from_payload(payload: &[u8]) -> Result<Self, EnvelopeError> {
        let (tag, seq, ts_logical, caused_by, body) = Envelope::decode_envelope_prefix(payload)?;
        let MetadataRecord(input_key) = Envelope::decode_record::<MetadataRecord>(tag, body)?;
        Ok(Self {
            seq,
            ts_logical,
            caused_by,
            input_key,
        })
    }

    pub(crate) const fn input_key(&self) -> Option<(u64, u64)> {
        self.input_key
    }
}

// Constructors receive validated borrowed fields. Static dispatch retains the
// original owned-return path without building and rematching a borrowed enum.
trait RecordBuilder: Sized {
    fn input(bytes: &[u8], client_id: u64, client_seq: u64) -> Self;
    fn output(bytes: &[u8]) -> Self;
    fn resize(cols: u16, rows: u16) -> Self;
    fn exit(code: i32) -> Self;
}

impl RecordBuilder for Record {
    #[inline]
    fn input(bytes: &[u8], client_id: u64, client_seq: u64) -> Self {
        #[cfg(test)]
        owned_decode_work::record(bytes.len());
        Self::In {
            bytes: bytes.to_vec(),
            client_id,
            client_seq,
        }
    }
    #[inline]
    fn output(bytes: &[u8]) -> Self {
        #[cfg(test)]
        owned_decode_work::record(bytes.len());
        Self::Out(bytes.to_vec())
    }
    #[inline]
    fn resize(cols: u16, rows: u16) -> Self {
        Self::Resize { cols, rows }
    }
    #[inline]
    fn exit(code: i32) -> Self {
        Self::Exit { code }
    }
}

struct MetadataRecord(Option<(u64, u64)>);
impl RecordBuilder for MetadataRecord {
    #[inline]
    fn input(_: &[u8], client_id: u64, client_seq: u64) -> Self {
        Self(Some((client_id, client_seq)))
    }
    #[inline]
    fn output(_: &[u8]) -> Self {
        Self(None)
    }
    #[inline]
    fn resize(_: u16, _: u16) -> Self {
        Self(None)
    }
    #[inline]
    fn exit(_: i32) -> Self {
        Self(None)
    }
}

#[cfg(test)]
pub(crate) mod owned_decode_work {
    use std::cell::Cell;
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) struct Work {
        pub(crate) materializations: usize,
        pub(crate) nonempty: usize,
        pub(crate) bytes: usize,
    }
    thread_local! {
        static WORK: Cell<Work> = const { Cell::new(Work { materializations: 0, nonempty: 0, bytes: 0 }) };
    }
    pub(crate) fn record(len: usize) {
        WORK.with(|work| {
            let mut value = work.get();
            value.materializations = value.materializations.saturating_add(1);
            value.nonempty = value.nonempty.saturating_add(usize::from(len > 0));
            value.bytes = value.bytes.saturating_add(len);
            work.set(value);
        });
    }
    pub(crate) fn capture<T>(f: impl FnOnce() -> T) -> (T, Work) {
        WORK.with(|work| work.set(Work::default()));
        let value = f();
        let work = WORK.with(|work| work.replace(Work::default()));
        (value, work)
    }
}

/// Why a buffer is not a valid envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnvelopeError {
    /// The buffer ended before a fixed-size read could complete.
    Short,
    /// The version byte is not one we understand.
    BadVersion(u8),
    /// The tag byte is reserved or unknown.
    BadTag(u8),
    /// A declared body length runs past the buffer (or exceeds `u32` on encode).
    BadBodyLen,
    /// The outer frame failed to encode/decode.
    Frame(FrameError),
}

impl std::fmt::Display for EnvelopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvelopeError::Short => write!(f, "record envelope buffer too short"),
            EnvelopeError::BadVersion(v) => write!(f, "unsupported envelope version {v}"),
            EnvelopeError::BadTag(t) => write!(f, "unknown record tag {t}"),
            EnvelopeError::BadBodyLen => write!(f, "record body length runs past the buffer"),
            EnvelopeError::Frame(e) => write!(f, "frame error: {e}"),
        }
    }
}

impl std::error::Error for EnvelopeError {}

const fn tag_of(record: &Record) -> u8 {
    match record {
        Record::In { .. } => TAG_IN,
        Record::Out(_) => TAG_OUT,
        Record::Resize { .. } => TAG_RESIZE,
        Record::Exit { .. } => TAG_EXIT,
    }
}

/// The decoded envelope header fields, optional cause, and unconsumed payload.
type EnvelopePrefix<'a> = (u8, Offset, u64, Option<CausedBy>, &'a [u8]);

impl Envelope {
    #[inline]
    const fn encode_envelope_header(tag: u8, seq: Offset, ts_logical: u64) -> [u8; HEADER_LEN] {
        let mut out = [0u8; HEADER_LEN];
        out[0] = ENV_VERSION;
        out[1] = tag;
        let s = [
            (seq.0 & 0xff) as u8,
            ((seq.0 >> 8) & 0xff) as u8,
            ((seq.0 >> 16) & 0xff) as u8,
            ((seq.0 >> 24) & 0xff) as u8,
            ((seq.0 >> 32) & 0xff) as u8,
            ((seq.0 >> 40) & 0xff) as u8,
            ((seq.0 >> 48) & 0xff) as u8,
            ((seq.0 >> 56) & 0xff) as u8,
        ];
        out[2] = s[0];
        out[3] = s[1];
        out[4] = s[2];
        out[5] = s[3];
        out[6] = s[4];
        out[7] = s[5];
        out[8] = s[6];
        out[9] = s[7];
        let t = [
            (ts_logical & 0xff) as u8,
            ((ts_logical >> 8) & 0xff) as u8,
            ((ts_logical >> 16) & 0xff) as u8,
            ((ts_logical >> 24) & 0xff) as u8,
            ((ts_logical >> 32) & 0xff) as u8,
            ((ts_logical >> 40) & 0xff) as u8,
            ((ts_logical >> 48) & 0xff) as u8,
            ((ts_logical >> 56) & 0xff) as u8,
        ];
        out[10] = t[0];
        out[11] = t[1];
        out[12] = t[2];
        out[13] = t[3];
        out[14] = t[4];
        out[15] = t[5];
        out[16] = t[6];
        out[17] = t[7];
        out
    }

    #[inline]
    const fn decode_envelope_header(hdr: &[u8; HEADER_LEN]) -> (u8, u8, Offset, u64) {
        let version = hdr[0];
        let tag = hdr[1];
        let seq = Offset(
            (hdr[2] as u64)
                | ((hdr[3] as u64) << 8)
                | ((hdr[4] as u64) << 16)
                | ((hdr[5] as u64) << 24)
                | ((hdr[6] as u64) << 32)
                | ((hdr[7] as u64) << 40)
                | ((hdr[8] as u64) << 48)
                | ((hdr[9] as u64) << 56),
        );
        let ts_logical = (hdr[10] as u64)
            | ((hdr[11] as u64) << 8)
            | ((hdr[12] as u64) << 16)
            | ((hdr[13] as u64) << 24)
            | ((hdr[14] as u64) << 32)
            | ((hdr[15] as u64) << 40)
            | ((hdr[16] as u64) << 48)
            | ((hdr[17] as u64) << 56);
        (version, tag, seq, ts_logical)
    }

    #[inline]
    const fn encode_cause_self(offset: u64) -> [u8; 10] {
        let mut out = [0u8; 10];
        out[0] = 1;
        let o = [
            (offset & 0xff) as u8,
            ((offset >> 8) & 0xff) as u8,
            ((offset >> 16) & 0xff) as u8,
            ((offset >> 24) & 0xff) as u8,
            ((offset >> 32) & 0xff) as u8,
            ((offset >> 40) & 0xff) as u8,
            ((offset >> 48) & 0xff) as u8,
            ((offset >> 56) & 0xff) as u8,
        ];
        out[1] = o[0];
        out[2] = o[1];
        out[3] = o[2];
        out[4] = o[3];
        out[5] = o[4];
        out[6] = o[5];
        out[7] = o[6];
        out[8] = o[7];
        out[9] = 0;
        out
    }

    #[inline]
    const fn encode_cause_cross(offset: u64, partition: u64) -> [u8; 18] {
        let mut out = [0u8; 18];
        out[0] = 1;
        let o = [
            (offset & 0xff) as u8,
            ((offset >> 8) & 0xff) as u8,
            ((offset >> 16) & 0xff) as u8,
            ((offset >> 24) & 0xff) as u8,
            ((offset >> 32) & 0xff) as u8,
            ((offset >> 40) & 0xff) as u8,
            ((offset >> 48) & 0xff) as u8,
            ((offset >> 56) & 0xff) as u8,
        ];
        out[1] = o[0];
        out[2] = o[1];
        out[3] = o[2];
        out[4] = o[3];
        out[5] = o[4];
        out[6] = o[5];
        out[7] = o[6];
        out[8] = o[7];
        out[9] = 1;
        let p = [
            (partition & 0xff) as u8,
            ((partition >> 8) & 0xff) as u8,
            ((partition >> 16) & 0xff) as u8,
            ((partition >> 24) & 0xff) as u8,
            ((partition >> 32) & 0xff) as u8,
            ((partition >> 40) & 0xff) as u8,
            ((partition >> 48) & 0xff) as u8,
            ((partition >> 56) & 0xff) as u8,
        ];
        out[10] = p[0];
        out[11] = p[1];
        out[12] = p[2];
        out[13] = p[3];
        out[14] = p[4];
        out[15] = p[5];
        out[16] = p[6];
        out[17] = p[7];
        out
    }

    #[inline]
    const fn decode_u64_le(bytes: &[u8; 8]) -> u64 {
        (bytes[0] as u64)
            | ((bytes[1] as u64) << 8)
            | ((bytes[2] as u64) << 16)
            | ((bytes[3] as u64) << 24)
            | ((bytes[4] as u64) << 32)
            | ((bytes[5] as u64) << 40)
            | ((bytes[6] as u64) << 48)
            | ((bytes[7] as u64) << 56)
    }

    #[inline]
    const fn encode_in_prefix(client_id: u64, client_seq: u64, len: u32) -> [u8; 20] {
        let mut out = [0u8; 20];
        let cid = [
            (client_id & 0xff) as u8,
            ((client_id >> 8) & 0xff) as u8,
            ((client_id >> 16) & 0xff) as u8,
            ((client_id >> 24) & 0xff) as u8,
            ((client_id >> 32) & 0xff) as u8,
            ((client_id >> 40) & 0xff) as u8,
            ((client_id >> 48) & 0xff) as u8,
            ((client_id >> 56) & 0xff) as u8,
        ];
        out[0] = cid[0];
        out[1] = cid[1];
        out[2] = cid[2];
        out[3] = cid[3];
        out[4] = cid[4];
        out[5] = cid[5];
        out[6] = cid[6];
        out[7] = cid[7];
        let cseq = [
            (client_seq & 0xff) as u8,
            ((client_seq >> 8) & 0xff) as u8,
            ((client_seq >> 16) & 0xff) as u8,
            ((client_seq >> 24) & 0xff) as u8,
            ((client_seq >> 32) & 0xff) as u8,
            ((client_seq >> 40) & 0xff) as u8,
            ((client_seq >> 48) & 0xff) as u8,
            ((client_seq >> 56) & 0xff) as u8,
        ];
        out[8] = cseq[0];
        out[9] = cseq[1];
        out[10] = cseq[2];
        out[11] = cseq[3];
        out[12] = cseq[4];
        out[13] = cseq[5];
        out[14] = cseq[6];
        out[15] = cseq[7];
        let l = [
            (len & 0xff) as u8,
            ((len >> 8) & 0xff) as u8,
            ((len >> 16) & 0xff) as u8,
            ((len >> 24) & 0xff) as u8,
        ];
        out[16] = l[0];
        out[17] = l[1];
        out[18] = l[2];
        out[19] = l[3];
        out
    }

    #[inline]
    const fn decode_in_prefix(hdr: &[u8; 20]) -> (u64, u64, usize) {
        let client_id = (hdr[0] as u64)
            | ((hdr[1] as u64) << 8)
            | ((hdr[2] as u64) << 16)
            | ((hdr[3] as u64) << 24)
            | ((hdr[4] as u64) << 32)
            | ((hdr[5] as u64) << 40)
            | ((hdr[6] as u64) << 48)
            | ((hdr[7] as u64) << 56);
        let client_seq = (hdr[8] as u64)
            | ((hdr[9] as u64) << 8)
            | ((hdr[10] as u64) << 16)
            | ((hdr[11] as u64) << 24)
            | ((hdr[12] as u64) << 32)
            | ((hdr[13] as u64) << 40)
            | ((hdr[14] as u64) << 48)
            | ((hdr[15] as u64) << 56);
        let len = ((hdr[16] as u32)
            | ((hdr[17] as u32) << 8)
            | ((hdr[18] as u32) << 16)
            | ((hdr[19] as u32) << 24)) as usize;
        (client_id, client_seq, len)
    }

    #[inline]
    const fn decode_out_len(hdr: &[u8; 4]) -> usize {
        ((hdr[0] as u32)
            | ((hdr[1] as u32) << 8)
            | ((hdr[2] as u32) << 16)
            | ((hdr[3] as u32) << 24)) as usize
    }

    #[inline]
    const fn encode_resize_body(cols: u16, rows: u16) -> [u8; 4] {
        let mut out = [0u8; 4];
        let c = [(cols & 0xff) as u8, ((cols >> 8) & 0xff) as u8];
        out[0] = c[0];
        out[1] = c[1];
        let r = [(rows & 0xff) as u8, ((rows >> 8) & 0xff) as u8];
        out[2] = r[0];
        out[3] = r[1];
        out
    }

    #[inline]
    const fn decode_resize_body(hdr: &[u8; 4]) -> (u16, u16) {
        let cols = (hdr[0] as u16) | ((hdr[1] as u16) << 8);
        let rows = (hdr[2] as u16) | ((hdr[3] as u16) << 8);
        (cols, rows)
    }

    #[inline]
    const fn decode_exit_body(hdr: &[u8; 4]) -> i32 {
        ((hdr[0] as u32)
            | ((hdr[1] as u32) << 8)
            | ((hdr[2] as u32) << 16)
            | ((hdr[3] as u32) << 24)) as i32
    }

    /// The payload length [`encode`](Self::encode) would produce for `record` +
    /// `caused_by`, computed arithmetically without allocating. Returns
    /// [`EnvelopeError::BadBodyLen`] exactly when `encode` would (a body that does
    /// not fit the `u32` length field).
    pub const fn payload_len(
        record: &Record,
        caused_by: Option<CausedBy>,
    ) -> Result<usize, EnvelopeError> {
        let cause = Self::cause_len(caused_by);
        let body = match record {
            Record::In { bytes, .. } => match Self::in_body_len(bytes.len()) {
                Ok(n) => n,
                Err(e) => return Err(e),
            },
            Record::Out(bytes) => {
                if bytes.len() > u32::MAX as usize {
                    return Err(EnvelopeError::BadBodyLen);
                }
                let Some(n) = 4usize.checked_add(bytes.len()) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                n
            }
            Record::Resize { .. } | Record::Exit { .. } => 4,
        };
        let Some(after_cause) = HEADER_LEN.checked_add(cause) else {
            return Err(EnvelopeError::BadBodyLen);
        };
        let Some(total) = after_cause.checked_add(body) else {
            return Err(EnvelopeError::BadBodyLen);
        };
        Ok(total)
    }

    /// The encoded body length of an `In` carrying `body_len` bytes.
    const fn in_body_len(body_len: usize) -> Result<usize, EnvelopeError> {
        if body_len > u32::MAX as usize {
            return Err(EnvelopeError::BadBodyLen);
        }
        match (8usize + 8 + 4).checked_add(body_len) {
            Some(n) => Ok(n),
            None => Err(EnvelopeError::BadBodyLen),
        }
    }

    /// The encoded cause-block length for `caused_by`.
    const fn cause_len(caused_by: Option<CausedBy>) -> usize {
        match caused_by {
            None => 1,
            Some(CausedBy {
                partition: None, ..
            }) => 10,
            Some(CausedBy {
                partition: Some(_), ..
            }) => 18,
        }
    }

    /// Whether `record` + `caused_by` can be encoded at all: the body fits `u32`
    /// and the payload fits the frame's `MAX_PAYLOAD_LEN` policy cap. Pure and
    /// allocation-free, so a writer can check *before* it commits anything.
    /// These are the exact conditions under which [`encode`](Self::encode) fails,
    /// and the only ones.
    pub const fn check_encodable(
        record: &Record,
        caused_by: Option<CausedBy>,
    ) -> Result<(), EnvelopeError> {
        let len = match Self::payload_len(record, caused_by) {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        Self::check_payload_len(len)
    }

    /// [`check_encodable`](Self::check_encodable) for an `In` of `body_len` bytes,
    /// without materializing the record — so an ingest can decide whether a
    /// keystroke *would* commit before it delivers the keystroke anywhere.
    pub const fn check_in_encodable(
        body_len: usize,
        caused_by: Option<CausedBy>,
    ) -> Result<(), EnvelopeError> {
        let in_len = match Self::in_body_len(body_len) {
            Ok(n) => n,
            Err(e) => return Err(e),
        };
        let Some(after_cause) = HEADER_LEN.checked_add(Self::cause_len(caused_by)) else {
            return Err(EnvelopeError::BadBodyLen);
        };
        let Some(len) = after_cause.checked_add(in_len) else {
            return Err(EnvelopeError::BadBodyLen);
        };
        Self::check_payload_len(len)
    }

    const fn check_payload_len(len: usize) -> Result<(), EnvelopeError> {
        if len > u32::MAX as usize || len > astream_wire::MAX_PAYLOAD_LEN {
            return Err(EnvelopeError::Frame(FrameError::TooLarge));
        }
        Ok(())
    }

    /// Serialize the header and body, then wrap them in a CRC [`Frame`] and
    /// encode to bytes. A body larger than `u32` returns [`EnvelopeError::BadBodyLen`]
    /// (it never panics — the same discipline as `Frame::encode`).
    pub fn encode(&self) -> Result<Vec<u8>, EnvelopeError> {
        // Sized exactly, and refused before anything is built.
        let len = Self::payload_len(&self.record, self.caused_by)?;
        Self::check_payload_len(len)?;
        if len > astream_wire::MAX_PAYLOAD_LEN {
            return Err(EnvelopeError::Frame(FrameError::TooLarge));
        }
        let mut payload = Vec::with_capacity(len);
        let hdr = Self::encode_envelope_header(tag_of(&self.record), self.seq, self.ts_logical);
        payload.extend_from_slice(&hdr);
        match self.caused_by {
            None => payload.push(0),
            Some(cb) => match cb.partition {
                None => {
                    let cause = Self::encode_cause_self(cb.offset);
                    payload.extend_from_slice(&cause);
                }
                Some(p) => {
                    let cause = Self::encode_cause_cross(cb.offset, p);
                    payload.extend_from_slice(&cause);
                }
            },
        }
        match &self.record {
            Record::In {
                bytes,
                client_id,
                client_seq,
            } => {
                let Ok(len) = u32::try_from(bytes.len()) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                let prefix = Self::encode_in_prefix(*client_id, *client_seq, len);
                payload.extend_from_slice(&prefix);
                payload.extend_from_slice(bytes);
            }
            Record::Out(bytes) => {
                let Ok(len) = u32::try_from(bytes.len()) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                payload.extend_from_slice(&len.to_le_bytes());
                payload.extend_from_slice(bytes);
            }
            Record::Resize { cols, rows } => {
                let body = Self::encode_resize_body(*cols, *rows);
                payload.extend_from_slice(&body);
            }
            Record::Exit { code } => {
                payload.extend_from_slice(&code.to_le_bytes());
            }
        }
        Frame::new(payload).encode().map_err(EnvelopeError::Frame)
    }

    const fn decode_envelope_prefix(payload: &[u8]) -> Result<EnvelopePrefix<'_>, EnvelopeError> {
        let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, ref after_header @ ..] =
            payload
        else {
            return Err(EnvelopeError::Short);
        };
        let (version, tag, seq, ts_logical) = Self::decode_envelope_header(&[
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        ]);
        if !envelope_version_valid(version) {
            return Err(EnvelopeError::BadVersion(version));
        }
        let &[cause_present, ref after_cause_flag @ ..] = after_header else {
            return Err(EnvelopeError::Short);
        };
        let (caused_by, body) = if cause_present == 0 {
            (None, after_cause_flag)
        } else {
            let &[o0, o1, o2, o3, o4, o5, o6, o7, part_present, ref after_part_flag @ ..] =
                after_cause_flag
            else {
                return Err(EnvelopeError::Short);
            };
            let offset = Self::decode_u64_le(&[o0, o1, o2, o3, o4, o5, o6, o7]);
            if part_present == 0 {
                (
                    Some(CausedBy {
                        partition: None,
                        offset,
                    }),
                    after_part_flag,
                )
            } else {
                let &[p0, p1, p2, p3, p4, p5, p6, p7, ref after_part @ ..] = after_part_flag else {
                    return Err(EnvelopeError::Short);
                };
                let partition = Some(Self::decode_u64_le(&[p0, p1, p2, p3, p4, p5, p6, p7]));
                (Some(CausedBy { partition, offset }), after_part)
            }
        };
        Ok((tag, seq, ts_logical, caused_by, body))
    }

    const fn decode_in_header(body: &[u8]) -> Result<(u64, u64, usize, &[u8]), EnvelopeError> {
        let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, ref rest @ ..] =
            body
        else {
            return Err(EnvelopeError::Short);
        };
        let (client_id, client_seq, len) = Self::decode_in_prefix(&[
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
            b19,
        ]);
        if rest.len() < len {
            return Err(EnvelopeError::BadBodyLen);
        }
        Ok((client_id, client_seq, len, rest))
    }

    const fn decode_out_header(body: &[u8]) -> Result<(usize, &[u8]), EnvelopeError> {
        let &[b0, b1, b2, b3, ref rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        let len = Self::decode_out_len(&[b0, b1, b2, b3]);
        if rest.len() < len {
            return Err(EnvelopeError::BadBodyLen);
        }
        Ok((len, rest))
    }

    const fn decode_resize_slice(body: &[u8]) -> Result<(u16, u16), EnvelopeError> {
        let &[b0, b1, b2, b3, ref _rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        Ok(Self::decode_resize_body(&[b0, b1, b2, b3]))
    }

    const fn decode_exit_slice(body: &[u8]) -> Result<i32, EnvelopeError> {
        let &[b0, b1, b2, b3, ref _rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        Ok(Self::decode_exit_body(&[b0, b1, b2, b3]))
    }

    // One format validator serves both output representations. In particular,
    // ignored metadata bodies still check every fixed field and declared length.
    #[inline(always)]
    fn decode_record<R: RecordBuilder>(tag: u8, body: &[u8]) -> Result<R, EnvelopeError> {
        match tag {
            TAG_IN => {
                let (client_id, client_seq, len, rest) = Self::decode_in_header(body)?;
                let Some(bytes) = rest.get(..len) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                Ok(R::input(bytes, client_id, client_seq))
            }
            TAG_OUT => {
                let (len, rest) = Self::decode_out_header(body)?;
                let Some(bytes) = rest.get(..len) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                Ok(R::output(bytes))
            }
            TAG_RESIZE => {
                let (cols, rows) = Self::decode_resize_slice(body)?;
                Ok(R::resize(cols, rows))
            }
            TAG_EXIT => Ok(R::exit(Self::decode_exit_slice(body)?)),
            other => Err(EnvelopeError::BadTag(other)),
        }
    }

    /// Parse one envelope out of a decoded frame's payload. Bounds-checks every
    /// read before it happens, so hostile bytes yield `Err`, never a panic.
    pub fn from_payload(payload: &[u8]) -> Result<Envelope, EnvelopeError> {
        let (tag, seq, ts_logical, caused_by, body) = Self::decode_envelope_prefix(payload)?;
        let record = Self::decode_record::<Record>(tag, body)?;
        Ok(Envelope {
            seq,
            ts_logical,
            caused_by,
            record,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Encode an envelope, decode the outer frame, and parse the payload back.
    fn roundtrip(record: Record) -> Envelope {
        roundtrip_caused(record, None)
    }

    fn roundtrip_caused(record: Record, caused_by: Option<CausedBy>) -> Envelope {
        let env = Envelope {
            seq: Offset(7),
            ts_logical: 42,
            caused_by,
            record,
        };
        let bytes = env.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        Envelope::from_payload(&decoded.frame.payload).unwrap()
    }

    #[test]
    fn roundtrips_caused_by_self_and_cross_log() {
        // self-cause (partition None)
        let e = roundtrip_caused(
            Record::Out(b"echo".to_vec()),
            Some(CausedBy {
                partition: None,
                offset: 5,
            }),
        );
        assert_eq!(
            e.caused_by,
            Some(CausedBy {
                partition: None,
                offset: 5
            })
        );
        // cross-log cause (partition Some)
        let e = roundtrip_caused(
            Record::In {
                bytes: b"x".to_vec(),
                client_id: 1,
                client_seq: 1,
            },
            Some(CausedBy {
                partition: Some(2),
                offset: 9,
            }),
        );
        assert_eq!(
            e.caused_by,
            Some(CausedBy {
                partition: Some(2),
                offset: 9
            })
        );
        // uncaused
        assert_eq!(roundtrip(Record::Out(b"x".to_vec())).caused_by, None);
    }

    #[test]
    fn rejects_truncation_inside_the_cause_block_without_panicking() {
        // cause_present = 1 but no offset bytes follow -> Short, never panic.
        let mut p = vec![ENV_VERSION, TAG_EXIT];
        p.extend_from_slice(&[0u8; 16]); // seq + ts
        p.push(1); // cause_present, then truncated
        assert_eq!(Envelope::from_payload(&p), Err(EnvelopeError::Short));
        // cause_present=1, offset present, cause_part_present=1 but no partition.
        let mut p = vec![ENV_VERSION, TAG_EXIT];
        p.extend_from_slice(&[0u8; 16]);
        p.push(1);
        p.extend_from_slice(&7u64.to_le_bytes());
        p.push(1); // part present, then truncated
        assert_eq!(Envelope::from_payload(&p), Err(EnvelopeError::Short));
    }

    #[test]
    fn roundtrips_each_variant_and_header() {
        let in_rec = Record::In {
            bytes: b"ls -la\n".to_vec(),
            client_id: 9,
            client_seq: 3,
        };
        assert_eq!(roundtrip(in_rec.clone()).record, in_rec);
        assert_eq!(
            roundtrip(Record::Out(b"\x1b[2J".to_vec())).record,
            Record::Out(b"\x1b[2J".to_vec())
        );
        assert_eq!(
            roundtrip(Record::Resize { cols: 80, rows: 24 }).record,
            Record::Resize { cols: 80, rows: 24 }
        );
        assert_eq!(
            roundtrip(Record::Exit { code: -1 }).record,
            Record::Exit { code: -1 }
        );
        let e = roundtrip(Record::Out(b"x".to_vec()));
        assert_eq!(e.seq, Offset(7));
        assert_eq!(e.ts_logical, 42);
    }

    #[test]
    fn rejects_short_bad_version_and_bad_tag() {
        assert_eq!(
            Envelope::from_payload(&[1, 2, 3]),
            Err(EnvelopeError::Short)
        );

        let mut p = vec![ENV_VERSION, TAG_EXIT];
        p.extend_from_slice(&[0u8; 16]); // seq + ts
        p.push(0); // cause_present = 0
        p.extend_from_slice(&0i32.to_le_bytes());
        assert!(Envelope::from_payload(&p).is_ok());

        p[0] = 2; // the previous (now unsupported) version
        assert_eq!(
            Envelope::from_payload(&p),
            Err(EnvelopeError::BadVersion(2))
        );
        // A complete header names its version even without a cause flag;
        // fewer than HEADER_LEN bytes cannot establish that header yet.
        assert_eq!(
            Envelope::from_payload(&p[..HEADER_LEN - 1]),
            Err(EnvelopeError::Short)
        );
        assert_eq!(
            Envelope::from_payload(&p[..HEADER_LEN + 1]),
            Err(EnvelopeError::BadVersion(2))
        );
        assert_eq!(
            Envelope::from_payload(&p[..HEADER_LEN]),
            Err(EnvelopeError::BadVersion(2)),
            "A_COMPLETE_HEADER_NAMES_ITS_VERSION_BEFORE_THE_CAUSE_FLAG"
        );
        p[0] = ENV_VERSION;
        assert_eq!(
            Envelope::from_payload(&p[..HEADER_LEN]),
            Err(EnvelopeError::Short)
        );
        assert_eq!(
            Envelope::from_payload(&p[..HEADER_LEN + 1]),
            Err(EnvelopeError::Short)
        );
        p[1] = 0;
        assert_eq!(Envelope::from_payload(&p), Err(EnvelopeError::BadTag(0)));
    }

    #[test]
    fn payload_len_and_check_encodable_agree_with_encode() {
        use astream_wire::{HEADER_SIZE, MAX_PAYLOAD_LEN};
        let cases: Vec<(Record, Option<CausedBy>)> = vec![
            (Record::Out(b"hello".to_vec()), None),
            (
                Record::In {
                    bytes: b"ls\n".to_vec(),
                    client_id: 1,
                    client_seq: 2,
                },
                Some(CausedBy {
                    partition: Some(4),
                    offset: 9,
                }),
            ),
            (
                Record::Resize { cols: 1, rows: 2 },
                Some(CausedBy {
                    partition: None,
                    offset: 0,
                }),
            ),
            (Record::Exit { code: 3 }, None),
        ];
        for (record, caused_by) in cases {
            let env = Envelope {
                seq: Offset(1),
                ts_logical: 2,
                caused_by,
                record: record.clone(),
            };
            let bytes = env.encode().unwrap();
            assert_eq!(
                Envelope::payload_len(&record, caused_by).unwrap(),
                bytes.len() - HEADER_SIZE,
                "arithmetic payload length equals the encoded payload length"
            );
            assert!(Envelope::check_encodable(&record, caused_by).is_ok());
        }
        // The In precheck agrees with the record-based check at the boundary.
        let max_in = MAX_PAYLOAD_LEN - HEADER_LEN - 1 - 20;
        assert!(Envelope::check_in_encodable(max_in, None).is_ok());
        assert_eq!(
            Envelope::check_in_encodable(max_in + 1, None),
            Err(EnvelopeError::Frame(FrameError::TooLarge))
        );
        let in_rec = Record::In {
            bytes: vec![0u8; max_in + 1],
            client_id: 1,
            client_seq: 1,
        };
        assert_eq!(
            Envelope::check_encodable(&in_rec, None),
            Err(EnvelopeError::Frame(FrameError::TooLarge))
        );
        // A same-log cause block is 10 bytes instead of the 1-byte "no cause"
        // marker, so the In boundary moves down by 9.
        let cb = Some(CausedBy {
            partition: None,
            offset: 0,
        });
        assert!(Envelope::check_in_encodable(max_in - 9, cb).is_ok());
        assert!(Envelope::check_in_encodable(max_in - 8, cb).is_err());

        // The largest Out that fits and the first that does not: both agree with encode.
        let max_body = MAX_PAYLOAD_LEN - HEADER_LEN - 1 - 4;
        assert!(Envelope::check_encodable(&Record::Out(vec![0u8; max_body]), None).is_ok());
        let too_big = Record::Out(vec![0u8; max_body + 1]);
        assert_eq!(
            Envelope::check_encodable(&too_big, None),
            Err(EnvelopeError::Frame(FrameError::TooLarge))
        );
        let env = Envelope {
            seq: Offset(0),
            ts_logical: 0,
            caused_by: None,
            record: too_big,
        };
        assert_eq!(
            env.encode(),
            Err(EnvelopeError::Frame(FrameError::TooLarge))
        );
    }

    #[test]
    fn rejects_body_len_running_past_buffer() {
        let mut p = vec![ENV_VERSION, TAG_OUT];
        p.extend_from_slice(&0u64.to_le_bytes()); // seq
        p.extend_from_slice(&0u64.to_le_bytes()); // ts
        p.push(0); // cause_present = 0
        p.extend_from_slice(&100u32.to_le_bytes()); // claims 100 body bytes, supplies none
        assert_eq!(Envelope::from_payload(&p), Err(EnvelopeError::BadBodyLen));
    }
}
