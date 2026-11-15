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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "envelope_island.rs"]
mod envelope_island;
#[cfg(not(clean_islands))]
pub use crate::twins::envelope_clamp_call_cap;
#[cfg(clean_islands)]
pub use envelope_island::envelope_clamp_call_cap;

contract_fn! {
    /// Verified check that a cognition envelope's version byte matches `expected`
    /// (`version == expected`), linked via `clean-kernel-defeq` to `envelope_version_matches_isl`.
    #[must_use]
    pub const fn envelope_version_matches(version: u8, expected: u8) -> bool
    clauses [ensures result == (version == expected)]
    {
        version == expected
    }
}

const fn take_u8(buf: &[u8]) -> Result<(u8, &[u8]), CogError> {
    let &[b, ref rest @ ..] = buf else {
        return Err(CogError::Short);
    };
    Ok((b, rest))
}

const fn take_u32(buf: &[u8]) -> Result<(u32, &[u8]), CogError> {
    let &[b0, b1, b2, b3, ref rest @ ..] = buf else {
        return Err(CogError::Short);
    };
    let val = (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24);
    Ok((val, rest))
}

const fn take_u64(buf: &[u8]) -> Result<(u64, &[u8]), CogError> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = buf else {
        return Err(CogError::Short);
    };
    let val = (b0 as u64)
        | ((b1 as u64) << 8)
        | ((b2 as u64) << 16)
        | ((b3 as u64) << 24)
        | ((b4 as u64) << 32)
        | ((b5 as u64) << 40)
        | ((b6 as u64) << 48)
        | ((b7 as u64) << 56);
    Ok((val, rest))
}

const fn take_len_prefix(buf: &[u8]) -> Result<(usize, &[u8]), CogError> {
    let &[b0, b1, b2, b3, ref rest @ ..] = buf else {
        return Err(CogError::Short);
    };
    let len =
        ((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)) as usize;
    if rest.len() < len {
        return Err(CogError::BadLen);
    }
    Ok((len, rest))
}

/// Encode a 32-bit little-endian integer into its 4-byte wire representation.
#[must_use]
pub const fn encode_u32_le(v: u32) -> [u8; 4] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]
}

/// Decode a 32-bit little-endian integer from its 4-byte wire representation.
#[must_use]
pub const fn decode_u32_le(raw: &[u8; 4]) -> u32 {
    (raw[0] as u32) | ((raw[1] as u32) << 8) | ((raw[2] as u32) << 16) | ((raw[3] as u32) << 24)
}

/// Encode the 18-byte fixed cognition envelope header `(COG_VERSION, tag, seq: u64 LE, ts_logical: u64 LE)`.
#[inline]
#[must_use]
pub const fn encode_cog_header(tag: u8, seq: Offset, ts_logical: u64) -> [u8; 18] {
    let s = seq.0;
    let t = ts_logical;
    [
        COG_VERSION,
        tag,
        s as u8,
        (s >> 8) as u8,
        (s >> 16) as u8,
        (s >> 24) as u8,
        (s >> 32) as u8,
        (s >> 40) as u8,
        (s >> 48) as u8,
        (s >> 56) as u8,
        t as u8,
        (t >> 8) as u8,
        (t >> 16) as u8,
        (t >> 24) as u8,
        (t >> 32) as u8,
        (t >> 40) as u8,
        (t >> 48) as u8,
        (t >> 56) as u8,
    ]
}

/// Decode the 18-byte fixed cognition envelope header into `(version, tag, seq, ts_logical)`.
#[inline]
#[must_use]
pub const fn decode_cog_header(raw: &[u8; 18]) -> (u8, u8, Offset, u64) {
    let version = raw[0];
    let tag = raw[1];
    let seq = (raw[2] as u64)
        | ((raw[3] as u64) << 8)
        | ((raw[4] as u64) << 16)
        | ((raw[5] as u64) << 24)
        | ((raw[6] as u64) << 32)
        | ((raw[7] as u64) << 40)
        | ((raw[8] as u64) << 48)
        | ((raw[9] as u64) << 56);
    let ts_logical = (raw[10] as u64)
        | ((raw[11] as u64) << 8)
        | ((raw[12] as u64) << 16)
        | ((raw[13] as u64) << 24)
        | ((raw[14] as u64) << 32)
        | ((raw[15] as u64) << 40)
        | ((raw[16] as u64) << 48)
        | ((raw[17] as u64) << 56);
    (version, tag, Offset(seq), ts_logical)
}

/// A bounds-checked cursor over a payload — every read fails closed.
struct Reader<'a> {
    buf: &'a [u8],
}

impl<'a> Reader<'a> {
    const fn new(buf: &'a [u8]) -> Reader<'a> {
        Reader { buf }
    }
    fn u8(&mut self) -> Result<u8, CogError> {
        let (b, rest) = take_u8(self.buf)?;
        self.buf = rest;
        Ok(b)
    }
    fn u32(&mut self) -> Result<u32, CogError> {
        let (v, rest) = take_u32(self.buf)?;
        self.buf = rest;
        Ok(v)
    }
    fn u64(&mut self) -> Result<u64, CogError> {
        let (v, rest) = take_u64(self.buf)?;
        self.buf = rest;
        Ok(v)
    }
    fn bytes(&mut self) -> Result<Vec<u8>, CogError> {
        let (len, after_len) = take_len_prefix(self.buf)?;
        let s = after_len.get(..len).ok_or(CogError::BadLen)?;
        self.buf = after_len.get(len..).ok_or(CogError::BadLen)?;
        Ok(s.to_vec())
    }
    fn string(&mut self) -> Result<String, CogError> {
        // Strict, not lossy: a corrupt (CRC-surviving) frame whose string bytes
        // are not valid UTF-8 must fail to decode rather than silently substitute
        // replacement characters into a recorded cognition record.
        let (len, after_len) = take_len_prefix(self.buf)?;
        let s = after_len.get(..len).ok_or(CogError::BadLen)?;
        self.buf = after_len.get(len..).ok_or(CogError::BadLen)?;
        match core::str::from_utf8(s) {
            Ok(text) => Ok(text.to_owned()),
            Err(_) => Err(CogError::BadUtf8),
        }
    }
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) -> Result<(), CogError> {
    if b.len() > u32::MAX as usize {
        return Err(CogError::BadLen);
    }
    let len = b.len() as u32;
    out.extend_from_slice(&encode_u32_le(len));
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
        if !envelope_version_matches(version, COG_VERSION) {
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
                    1 => StopReason::EndTurn,
                    other => return Err(CogError::BadTag(other)),
                };
                let n = r.u32()? as usize;
                let clamped = envelope_clamp_call_cap(n as u64, 64) as usize;
                let cap = if clamped <= 64 { clamped } else { 64 };
                let _ = cap;
                if (n as u64).saturating_mul(12) > r.buf.len() as u64 {
                    return Err(CogError::Short);
                }
                let mut calls = Vec::new();
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
                let is_error = match r.u8()? {
                    0 => false,
                    1 => true,
                    other => return Err(CogError::BadTag(other)),
                };
                let content = r.bytes()?;
                CogRecord::ToolResult {
                    tool_use_id,
                    content,
                    is_error,
                }
            }
            other => return Err(CogError::BadTag(other)),
        };
        if !r.buf.is_empty() {
            return Err(CogError::BadLen);
        }
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
    match record {
        CogRecord::Completion { text, calls, stop } => {
            p.extend_from_slice(&encode_cog_header(TAG_COMPLETION, seq, ts_logical));
            put_bytes(&mut p, text.as_bytes())?;
            p.push(stop.code());
            if calls.len() > u32::MAX as usize {
                return Err(CogError::BadLen);
            }
            let n = calls.len() as u32;
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
            p.extend_from_slice(&encode_cog_header(TAG_TOOL_RESULT, seq, ts_logical));
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

    #[test]
    fn reader_fixed_width_reads_advance_exactly_and_fail_closed() {
        // Little-endian u32 then a u8, then end of buffer.
        let buf = [0x78, 0x56, 0x34, 0x12, 0xAB];
        let mut r = Reader::new(&buf);
        assert_eq!(r.u32(), Ok(0x1234_5678));
        assert_eq!(r.buf.len(), 1, "u32 advances exactly 4");
        assert_eq!(r.u8(), Ok(0xAB));
        assert_eq!(r.buf.len(), 0, "u8 advances exactly 1");
        assert_eq!(r.u8(), Err(CogError::Short), "u8 past the end");
        assert_eq!(r.buf.len(), 0, "a failed read does not move the cursor");
        // Three bytes left is Short for a u32, and the cursor stays put.
        let mut r = Reader::new(&buf[2..]);
        assert_eq!(r.u32(), Err(CogError::Short));
        assert_eq!(r.buf.len(), 3);
    }

    #[test]
    fn rejects_invalid_bool_or_stop_tag_and_trailing_bytes() {
        // Invalid stop reason code (2) on completion -> BadTag(2).
        let mut bad_stop = Vec::new();
        bad_stop.extend_from_slice(&encode_cog_header(TAG_COMPLETION, Offset(0), 0));
        bad_stop.extend_from_slice(&0u32.to_le_bytes()); // text = ""
        bad_stop.push(2); // invalid stop code
        bad_stop.extend_from_slice(&0u32.to_le_bytes()); // calls = 0
        assert_eq!(
            CogEnvelope::from_payload(&bad_stop),
            Err(CogError::BadTag(2))
        );

        // Invalid is_error byte (2) on tool result -> BadTag(2).
        let mut bad_err = Vec::new();
        bad_err.extend_from_slice(&encode_cog_header(TAG_TOOL_RESULT, Offset(0), 0));
        bad_err.extend_from_slice(&0u32.to_le_bytes()); // tool_use_id = ""
        bad_err.push(2); // invalid bool byte
        bad_err.extend_from_slice(&0u32.to_le_bytes()); // content = ""
        assert_eq!(
            CogEnvelope::from_payload(&bad_err),
            Err(CogError::BadTag(2))
        );

        // Trailing byte after valid payload -> BadLen.
        let mut trailing = Vec::new();
        trailing.extend_from_slice(&encode_cog_header(TAG_TOOL_RESULT, Offset(0), 0));
        trailing.extend_from_slice(&0u32.to_le_bytes());
        trailing.push(1);
        trailing.extend_from_slice(&0u32.to_le_bytes());
        trailing.push(0xAA);
        assert_eq!(CogEnvelope::from_payload(&trailing), Err(CogError::BadLen));
    }
}
