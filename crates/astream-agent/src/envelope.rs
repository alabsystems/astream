//! The cognition envelope: a versioned, CRC-framed skin over a [`CogRecord`].
//!
//! Disjoint from the VT record envelope (`astream_engine::envelope`, `ENV_VERSION`)
//! — a turn's cognition log is its own stream with its own `COG_VERSION`. Decoding
//! is panic-free on hostile input: every fixed read and every `u32` length is
//! bounds-checked before slicing (the same discipline as the VT envelope).

use crate::cog::{CogRecord, StopReason, ToolUse};
use astream_wire::{Frame, FrameError, Offset};

/// Current cognition envelope version.
pub const COG_VERSION: u8 = 1;
const TAG_COMPLETION: u8 = 1;
const TAG_TOOL_RESULT: u8 = 2;

/// One cognition record plus the header stamped onto it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CogEnvelope {
    /// This record's offset in the cognition log.
    pub seq: Offset,
    /// The logical clock at record time.
    pub ts_logical: u64,
    /// The cognition record itself.
    pub record: CogRecord,
}

/// Why a buffer is not a valid cognition envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CogError {
    /// The buffer ended before a fixed/declared read could complete.
    Short,
    /// The version byte is not understood.
    BadVersion(u8),
    /// The tag byte is unknown.
    BadTag(u8),
    /// A declared length runs past the buffer (or exceeds `u32` on encode).
    BadLen,
    /// A string field's bytes are not valid UTF-8.
    BadUtf8,
    /// The outer frame failed.
    Frame(FrameError),
}

/// A bounds-checked cursor over a payload — every read fails closed.
struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Reader<'a> {
        Reader { buf, pos: 0 }
    }
    fn u8(&mut self) -> Result<u8, CogError> {
        let b = *self.buf.get(self.pos).ok_or(CogError::Short)?;
        self.pos += 1;
        Ok(b)
    }
    fn u32(&mut self) -> Result<u32, CogError> {
        let end = self.pos.checked_add(4).ok_or(CogError::BadLen)?;
        let s = self.buf.get(self.pos..end).ok_or(CogError::Short)?;
        self.pos = end;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }
    fn u64(&mut self) -> Result<u64, CogError> {
        let end = self.pos.checked_add(8).ok_or(CogError::BadLen)?;
        let s = self.buf.get(self.pos..end).ok_or(CogError::Short)?;
        self.pos = end;
        let mut a = [0u8; 8];
        a.copy_from_slice(s);
        Ok(u64::from_le_bytes(a))
    }
    fn bytes(&mut self) -> Result<Vec<u8>, CogError> {
        let len = self.u32()? as usize;
        let end = self.pos.checked_add(len).ok_or(CogError::BadLen)?;
        let s = self.buf.get(self.pos..end).ok_or(CogError::BadLen)?;
        self.pos = end;
        Ok(s.to_vec())
    }
    fn string(&mut self) -> Result<String, CogError> {
        // Strict, not lossy: a corrupt (CRC-surviving) frame whose string bytes
        // are not valid UTF-8 must fail to decode rather than silently substitute
        // replacement characters into a recorded cognition record.
        String::from_utf8(self.bytes()?).map_err(|_| CogError::BadUtf8)
    }
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) -> Result<(), CogError> {
    let len = u32::try_from(b.len()).map_err(|_| CogError::BadLen)?;
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(b);
    Ok(())
}

impl CogEnvelope {
    /// Serialize header + body and wrap in a CRC [`Frame`].
    pub fn encode(&self) -> Result<Vec<u8>, CogError> {
        encode_record(self.seq, self.ts_logical, &self.record)
    }

    /// Parse one envelope from a decoded frame's payload. Panic-free on hostile bytes.
    pub fn from_payload(payload: &[u8]) -> Result<CogEnvelope, CogError> {
        let mut r = Reader::new(payload);
        let version = r.u8()?;
        if version != COG_VERSION {
            return Err(CogError::BadVersion(version));
        }
        let tag = r.u8()?;
        let seq = Offset(r.u64()?);
        let ts_logical = r.u64()?;
        let record = match tag {
            TAG_COMPLETION => {
                let text = r.string()?;
                let stop = match r.u8()? {
                    0 => StopReason::ToolUse,
                    _ => StopReason::EndTurn,
                };
                let n = r.u32()? as usize;
                let mut calls = Vec::with_capacity(n.min(64));
                for _ in 0..n {
                    let id = r.string()?;
                    let name = r.string()?;
                    let input = r.bytes()?;
                    calls.push(ToolUse { id, name, input });
                }
                CogRecord::Completion { text, calls, stop }
            }
            TAG_TOOL_RESULT => {
                let tool_use_id = r.string()?;
                let is_error = r.u8()? != 0;
                let content = r.bytes()?;
                CogRecord::ToolResult {
                    tool_use_id,
                    content,
                    is_error,
                }
            }
            other => return Err(CogError::BadTag(other)),
        };
        Ok(CogEnvelope {
            seq,
            ts_logical,
            record,
        })
    }
}

/// [`CogEnvelope::encode`] over a borrowed record, so a caller that holds the
/// records (a whole recorded turn) need not clone each one into an envelope.
pub(crate) fn encode_record(
    seq: Offset,
    ts_logical: u64,
    record: &CogRecord,
) -> Result<Vec<u8>, CogError> {
    let mut p = Vec::new();
    p.push(COG_VERSION);
    match record {
        CogRecord::Completion { text, calls, stop } => {
            p.push(TAG_COMPLETION);
            p.extend_from_slice(&seq.0.to_le_bytes());
            p.extend_from_slice(&ts_logical.to_le_bytes());
            put_bytes(&mut p, text.as_bytes())?;
            p.push(match stop {
                StopReason::ToolUse => 0,
                StopReason::EndTurn => 1,
            });
            let n = u32::try_from(calls.len()).map_err(|_| CogError::BadLen)?;
            p.extend_from_slice(&n.to_le_bytes());
            for c in calls {
                put_bytes(&mut p, c.id.as_bytes())?;
                put_bytes(&mut p, c.name.as_bytes())?;
                put_bytes(&mut p, &c.input)?;
            }
        }
        CogRecord::ToolResult {
            tool_use_id,
            content,
            is_error,
        } => {
            p.push(TAG_TOOL_RESULT);
            p.extend_from_slice(&seq.0.to_le_bytes());
            p.extend_from_slice(&ts_logical.to_le_bytes());
            put_bytes(&mut p, tool_use_id.as_bytes())?;
            p.push(*is_error as u8);
            put_bytes(&mut p, content)?;
        }
    }
    Frame::new(p).encode().map_err(CogError::Frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roundtrip(record: CogRecord) -> CogRecord {
        let env = CogEnvelope {
            seq: Offset(3),
            ts_logical: 9,
            record,
        };
        let bytes = env.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        CogEnvelope::from_payload(&decoded.frame.payload)
            .unwrap()
            .record
    }

    #[test]
    fn roundtrips_both_variants() {
        let comp = CogRecord::Completion {
            text: "let me build".into(),
            calls: vec![ToolUse {
                id: "t1".into(),
                name: "bash".into(),
                input: b"make".to_vec(),
            }],
            stop: StopReason::ToolUse,
        };
        assert_eq!(roundtrip(comp.clone()), comp);
        let tr = CogRecord::ToolResult {
            tool_use_id: "t1".into(),
            content: b"BUILD FAILED".to_vec(),
            is_error: true,
        };
        assert_eq!(roundtrip(tr.clone()), tr);
    }

    #[test]
    fn rejects_short_bad_version_and_bad_tag() {
        assert_eq!(CogEnvelope::from_payload(&[]), Err(CogError::Short));
        // valid header, bad version
        let mut p = vec![9u8, TAG_TOOL_RESULT];
        p.extend_from_slice(&[0u8; 16]);
        assert_eq!(CogEnvelope::from_payload(&p), Err(CogError::BadVersion(9)));
        // good version, bad tag
        let mut p = vec![COG_VERSION, 7];
        p.extend_from_slice(&[0u8; 16]);
        assert_eq!(CogEnvelope::from_payload(&p), Err(CogError::BadTag(7)));
        // completion claiming a huge text length with no bytes -> BadLen, not panic
        let mut p = vec![COG_VERSION, TAG_COMPLETION];
        p.extend_from_slice(&[0u8; 16]);
        p.extend_from_slice(&1000u32.to_le_bytes());
        assert_eq!(CogEnvelope::from_payload(&p), Err(CogError::BadLen));
    }

    #[test]
    fn rejects_non_utf8_string_field() {
        // A string field whose bytes are not valid UTF-8 must fail to decode
        // (strict), not silently become replacement characters (lossy).
        let mut p = vec![COG_VERSION, TAG_TOOL_RESULT];
        p.extend_from_slice(&0u64.to_le_bytes()); // seq
        p.extend_from_slice(&0u64.to_le_bytes()); // ts
        p.extend_from_slice(&1u32.to_le_bytes()); // tool_use_id length = 1
        p.push(0xFF); // an invalid UTF-8 byte
        p.push(0); // is_error = false
        p.extend_from_slice(&0u32.to_le_bytes()); // content length = 0
        assert_eq!(CogEnvelope::from_payload(&p), Err(CogError::BadUtf8));
    }
}
