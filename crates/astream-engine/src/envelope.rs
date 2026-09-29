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

fn tag_of(record: &Record) -> u8 {
    match record {
        Record::In { .. } => TAG_IN,
        Record::Out(_) => TAG_OUT,
        Record::Resize { .. } => TAG_RESIZE,
        Record::Exit { .. } => TAG_EXIT,
    }
}

impl Envelope {
    /// The payload length [`encode`](Self::encode) would produce for `record` +
    /// `caused_by`, computed arithmetically without allocating. Returns
    /// [`EnvelopeError::BadBodyLen`] exactly when `encode` would (a body that does
    /// not fit the `u32` length field).
    pub fn payload_len(
        record: &Record,
        caused_by: Option<CausedBy>,
    ) -> Result<usize, EnvelopeError> {
        let cause = Self::cause_len(caused_by);
        let body = match record {
            Record::In { bytes, .. } => Self::in_body_len(bytes.len())?,
            Record::Out(bytes) => {
                u32::try_from(bytes.len()).map_err(|_| EnvelopeError::BadBodyLen)?;
                4 + bytes.len()
            }
            Record::Resize { .. } | Record::Exit { .. } => 4,
        };
        Ok(HEADER_LEN + cause + body)
    }

    /// The encoded body length of an `In` carrying `body_len` bytes.
    fn in_body_len(body_len: usize) -> Result<usize, EnvelopeError> {
        u32::try_from(body_len).map_err(|_| EnvelopeError::BadBodyLen)?;
        Ok(8 + 8 + 4 + body_len)
    }

    /// The encoded cause-block length for `caused_by`.
    fn cause_len(caused_by: Option<CausedBy>) -> usize {
        match caused_by {
            None => 1,
            Some(CausedBy {
                partition: None, ..
            }) => 1 + 8 + 1,
            Some(CausedBy {
                partition: Some(_), ..
            }) => 1 + 8 + 1 + 8,
        }
    }

    /// Whether `record` + `caused_by` can be encoded at all: the body fits `u32`
    /// and the payload fits the frame's `MAX_PAYLOAD_LEN` policy cap. Pure and
    /// allocation-free, so a writer can check *before* it commits anything.
    /// These are the exact conditions under which [`encode`](Self::encode) fails,
    /// and the only ones.
    pub fn check_encodable(
        record: &Record,
        caused_by: Option<CausedBy>,
    ) -> Result<(), EnvelopeError> {
        Self::check_payload_len(Self::payload_len(record, caused_by)?)
    }

    /// [`check_encodable`](Self::check_encodable) for an `In` of `body_len` bytes,
    /// without materializing the record — so an ingest can decide whether a
    /// keystroke *would* commit before it delivers the keystroke anywhere.
    pub fn check_in_encodable(
        body_len: usize,
        caused_by: Option<CausedBy>,
    ) -> Result<(), EnvelopeError> {
        let len = HEADER_LEN + Self::cause_len(caused_by) + Self::in_body_len(body_len)?;
        Self::check_payload_len(len)
    }

    fn check_payload_len(len: usize) -> Result<(), EnvelopeError> {
        if u32::try_from(len).is_err() || len > astream_wire::MAX_PAYLOAD_LEN {
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
        let mut payload = Vec::with_capacity(len);
        payload.push(ENV_VERSION);
        payload.push(tag_of(&self.record));
        payload.extend_from_slice(&self.seq.0.to_le_bytes());
        payload.extend_from_slice(&self.ts_logical.to_le_bytes());
        match self.caused_by {
            None => payload.push(0),
            Some(cb) => {
                payload.push(1);
                payload.extend_from_slice(&cb.offset.to_le_bytes());
                match cb.partition {
                    None => payload.push(0),
                    Some(p) => {
                        payload.push(1);
                        payload.extend_from_slice(&p.to_le_bytes());
                    }
                }
            }
        }
        match &self.record {
            Record::In {
                bytes,
                client_id,
                client_seq,
            } => {
                payload.extend_from_slice(&client_id.to_le_bytes());
                payload.extend_from_slice(&client_seq.to_le_bytes());
                let len = u32::try_from(bytes.len()).map_err(|_| EnvelopeError::BadBodyLen)?;
                payload.extend_from_slice(&len.to_le_bytes());
                payload.extend_from_slice(bytes);
            }
            Record::Out(bytes) => {
                let len = u32::try_from(bytes.len()).map_err(|_| EnvelopeError::BadBodyLen)?;
                payload.extend_from_slice(&len.to_le_bytes());
                payload.extend_from_slice(bytes);
            }
            Record::Resize { cols, rows } => {
                payload.extend_from_slice(&cols.to_le_bytes());
                payload.extend_from_slice(&rows.to_le_bytes());
            }
            Record::Exit { code } => {
                payload.extend_from_slice(&code.to_le_bytes());
            }
        }
        Frame::new(payload).encode().map_err(EnvelopeError::Frame)
    }

    /// Parse one envelope out of a decoded frame's payload. Bounds-checks every
    /// read before it happens, so hostile bytes yield `Err`, never a panic.
    pub fn from_payload(payload: &[u8]) -> Result<Envelope, EnvelopeError> {
        if payload.len() < HEADER_LEN {
            return Err(EnvelopeError::Short);
        }
        let version = payload[0];
        if version != ENV_VERSION {
            return Err(EnvelopeError::BadVersion(version));
        }
        let tag = payload[1];
        let seq = Offset(u64::from_le_bytes([
            payload[2], payload[3], payload[4], payload[5], payload[6], payload[7], payload[8],
            payload[9],
        ]));
        let ts_logical = u64::from_le_bytes([
            payload[10],
            payload[11],
            payload[12],
            payload[13],
            payload[14],
            payload[15],
            payload[16],
            payload[17],
        ]);
        // Variable cause block (bounds-checked, like the body).
        let mut pos = HEADER_LEN;
        let cause_present = *payload.get(pos).ok_or(EnvelopeError::Short)?;
        pos += 1;
        let caused_by = if cause_present == 0 {
            None
        } else {
            let end = pos.checked_add(8).ok_or(EnvelopeError::BadBodyLen)?;
            let s = payload.get(pos..end).ok_or(EnvelopeError::Short)?;
            let offset = u64::from_le_bytes(s.try_into().unwrap());
            pos = end;
            let part_present = *payload.get(pos).ok_or(EnvelopeError::Short)?;
            pos += 1;
            let partition = if part_present == 0 {
                None
            } else {
                let end = pos.checked_add(8).ok_or(EnvelopeError::BadBodyLen)?;
                let s = payload.get(pos..end).ok_or(EnvelopeError::Short)?;
                pos = end;
                Some(u64::from_le_bytes(s.try_into().unwrap()))
            };
            Some(CausedBy { partition, offset })
        };
        let body = &payload[pos..];

        let record = match tag {
            TAG_IN => {
                // client_id(8) + client_seq(8) + len(4) + bytes
                if body.len() < 20 {
                    return Err(EnvelopeError::Short);
                }
                let client_id = u64::from_le_bytes([
                    body[0], body[1], body[2], body[3], body[4], body[5], body[6], body[7],
                ]);
                let client_seq = u64::from_le_bytes([
                    body[8], body[9], body[10], body[11], body[12], body[13], body[14], body[15],
                ]);
                let len = u32::from_le_bytes([body[16], body[17], body[18], body[19]]) as usize;
                let end = 20usize.checked_add(len).ok_or(EnvelopeError::BadBodyLen)?;
                if body.len() < end {
                    return Err(EnvelopeError::BadBodyLen);
                }
                Record::In {
                    bytes: body[20..end].to_vec(),
                    client_id,
                    client_seq,
                }
            }
            TAG_OUT => {
                if body.len() < 4 {
                    return Err(EnvelopeError::Short);
                }
                let len = u32::from_le_bytes([body[0], body[1], body[2], body[3]]) as usize;
                let end = 4usize.checked_add(len).ok_or(EnvelopeError::BadBodyLen)?;
                if body.len() < end {
                    return Err(EnvelopeError::BadBodyLen);
                }
                Record::Out(body[4..end].to_vec())
            }
            TAG_RESIZE => {
                if body.len() < 4 {
                    return Err(EnvelopeError::Short);
                }
                let cols = u16::from_le_bytes([body[0], body[1]]);
                let rows = u16::from_le_bytes([body[2], body[3]]);
                Record::Resize { cols, rows }
            }
            TAG_EXIT => {
                if body.len() < 4 {
                    return Err(EnvelopeError::Short);
                }
                let code = i32::from_le_bytes([body[0], body[1], body[2], body[3]]);
                Record::Exit { code }
            }
            other => return Err(EnvelopeError::BadTag(other)),
        };
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
        p[0] = ENV_VERSION;
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
