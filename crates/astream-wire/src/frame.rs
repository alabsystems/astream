//! The astream wire frame: a length-prefixed, CRC-checked envelope.
//!
//! Layout (little-endian), [`HEADER_SIZE`] = 12 bytes, then payload:
//!
//! ```text
//! | magic (2) | version (1) | flags (1) | payload_len: u32 (4) | crc32: u32 (4) | payload ... |
//! ```
//!
//! Both directions are panic-free:
//! * [`Frame::encode`] returns `Err(FrameError::TooLarge)` instead of
//!   `.expect()`-ing when the payload exceeds the [`MAX_PAYLOAD_LEN`] policy cap
//!   (16 MiB) or the `u32` length field.
//! * [`Frame::decode`] returns `Ok(None)` when more bytes are needed,
//!   `Err(..)` on malformed/corrupt input, and never indexes out of bounds.

use crate::hash::crc32_ieee;

/// Frame magic: identifies an astream frame (`0xA5 0x71`).
pub const MAGIC: [u8; 2] = [0xA5, 0x71];
/// Current frame format version.
pub const VERSION: u8 = 1;
/// Flag bits this version understands. Phase 0 defines none, so every bit is
/// reserved and MUST be zero. A decoder rejects any other bit (see
/// [`Frame::decode`]) rather than silently ignoring it — that is what turns a
/// future semantic flag (e.g. compression) into a detectable, version-safe
/// signal instead of a misread payload.
pub const KNOWN_FLAGS: u8 = 0x00;
/// Fixed header size in bytes: magic(2) + version(1) + flags(1) + len(4) + crc(4).
pub const HEADER_SIZE: usize = 12;
/// Maximum payload the wire will encode or accept on decode. A frame whose
/// length field exceeds this is rejected outright, so a transport is never
/// invited to buffer toward an attacker-chosen multi-GiB length. 16 MiB is a
/// deliberate Phase-0 cap; later phases may make it configurable.
pub const MAX_PAYLOAD_LEN: usize = 16 * 1024 * 1024;

/// Why a buffer is not a valid frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameError {
    /// Payload exceeds the [`MAX_PAYLOAD_LEN`] policy cap (16 MiB), or does not
    /// fit in the `u32` length field.
    TooLarge,
    /// Magic bytes did not match [`MAGIC`].
    BadMagic,
    /// Version byte did not match a version we understand.
    BadVersion,
    /// Payload CRC did not match the header.
    ChecksumMismatch,
    /// The flags byte set bits this version does not understand (forward-compat
    /// guard: an old decoder refuses a newer frame rather than misreading it).
    UnknownFlags,
}

impl std::fmt::Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            // Both documented causes are named: the 16 MiB policy cap is the one
            // an operator actually hits (every decode-path hit, and any encode of
            // 16 MiB..4 GiB); the u32 field is the theoretical encode-side ceiling.
            FrameError::TooLarge => "frame payload exceeds the 16 MiB cap or the u32 length field",
            FrameError::BadMagic => "frame magic mismatch",
            FrameError::BadVersion => "unsupported frame version",
            FrameError::ChecksumMismatch => "frame payload CRC mismatch",
            FrameError::UnknownFlags => "frame flags byte sets bits unknown to this version",
        };
        f.write_str(msg)
    }
}

impl std::error::Error for FrameError {}

/// An astream frame carrying an opaque payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frame {
    /// The opaque payload bytes.
    pub payload: Vec<u8>,
}

/// A successfully decoded frame plus how many bytes it consumed from the input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decoded {
    /// The decoded frame.
    pub frame: Frame,
    /// Total bytes consumed (header + payload).
    pub consumed: usize,
}

impl Frame {
    /// Wrap an opaque payload.
    pub fn new(payload: Vec<u8>) -> Self {
        Frame { payload }
    }

    /// Encode to bytes. Returns [`FrameError::TooLarge`] (never panics) if the
    /// payload exceeds the [`MAX_PAYLOAD_LEN`] policy cap (16 MiB) or the `u32`
    /// length field.
    pub fn encode(&self) -> Result<Vec<u8>, FrameError> {
        let len = u32::try_from(self.payload.len()).map_err(|_| FrameError::TooLarge)?;
        if self.payload.len() > MAX_PAYLOAD_LEN {
            return Err(FrameError::TooLarge);
        }
        let crc = crc32_ieee(&self.payload);

        let mut out = Vec::with_capacity(HEADER_SIZE + self.payload.len());
        out.extend_from_slice(&MAGIC);
        out.push(VERSION);
        out.push(0u8); // flags: reserved
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&crc.to_le_bytes());
        out.extend_from_slice(&self.payload);
        Ok(out)
    }

    /// Try to decode one frame from the front of `buf`.
    ///
    /// * `Ok(None)` — need more bytes (header incomplete, or payload not all
    ///   present yet).
    /// * `Ok(Some(_))` — a complete, CRC-valid frame plus bytes consumed.
    /// * `Err(_)` — the bytes are present but malformed/corrupt.
    pub fn decode(buf: &[u8]) -> Result<Option<Decoded>, FrameError> {
        if buf.len() < HEADER_SIZE {
            return Ok(None);
        }
        // All fixed-offset reads below are within the 12-byte header.
        if buf[0] != MAGIC[0] || buf[1] != MAGIC[1] {
            return Err(FrameError::BadMagic);
        }
        if buf[2] != VERSION {
            return Err(FrameError::BadVersion);
        }
        // Reserved flag bits MUST be zero; reject unknown bits rather than
        // silently ignoring them (forward-compat guard).
        if buf[3] & !KNOWN_FLAGS != 0 {
            return Err(FrameError::UnknownFlags);
        }
        let len = u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]) as usize;
        let crc = u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]);

        // Cap how much we will commit to before the bytes are even present: an
        // absurd-but-representable length is rejected, never buffered toward.
        if len > MAX_PAYLOAD_LEN {
            return Err(FrameError::TooLarge);
        }
        // Checked (defense-in-depth); cannot overflow given the cap above.
        let total = HEADER_SIZE.checked_add(len).ok_or(FrameError::TooLarge)?;
        if buf.len() < total {
            return Ok(None);
        }
        let payload = &buf[HEADER_SIZE..total];
        if crc32_ieee(payload) != crc {
            return Err(FrameError::ChecksumMismatch);
        }
        Ok(Some(Decoded {
            frame: Frame {
                payload: payload.to_vec(),
            },
            consumed: total,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_preserves_payload_and_reports_consumed() {
        let f = Frame::new(b"hello agent".to_vec());
        let bytes = f.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(decoded.frame, f);
        assert_eq!(decoded.consumed, bytes.len());
    }

    #[test]
    fn empty_payload_roundtrips() {
        let f = Frame::new(Vec::new());
        let bytes = f.encode().unwrap();
        assert_eq!(bytes.len(), HEADER_SIZE);
        assert_eq!(Frame::decode(&bytes).unwrap().unwrap().frame, f);
    }

    #[test]
    fn partial_header_and_partial_payload_need_more() {
        let bytes = Frame::new(b"abcd".to_vec()).encode().unwrap();
        assert_eq!(Frame::decode(&bytes[..5]).unwrap(), None); // header incomplete
        assert_eq!(Frame::decode(&bytes[..HEADER_SIZE + 1]).unwrap(), None); // payload incomplete
    }

    #[test]
    fn corruption_is_an_error_not_a_panic() {
        let mut bytes = Frame::new(b"payload".to_vec()).encode().unwrap();
        let last = bytes.len() - 1;
        bytes[last] ^= 0xFF; // flip a payload bit
        assert_eq!(Frame::decode(&bytes), Err(FrameError::ChecksumMismatch));

        bytes[0] = 0x00; // break magic
        assert_eq!(Frame::decode(&bytes), Err(FrameError::BadMagic));
    }

    /// A bare header claiming `len` with far fewer bytes actually present.
    fn header_with_len(len: u32) -> Vec<u8> {
        let mut h = vec![MAGIC[0], MAGIC[1], VERSION, 0];
        h.extend_from_slice(&len.to_le_bytes());
        h.extend_from_slice(&0u32.to_le_bytes()); // crc placeholder
        h.extend_from_slice(b"a few real bytes"); // far fewer than claimed
        h
    }

    #[test]
    fn oversized_length_field_is_rejected_not_buffered() {
        // An absurd-but-representable length (4 GiB) is rejected outright,
        // never Ok(None): the decoder must not invite buffering toward it.
        let huge = header_with_len(u32::MAX);
        assert_eq!(Frame::decode(&huge), Err(FrameError::TooLarge));

        // One past the policy cap is also rejected, with bytes still missing.
        let over = header_with_len((MAX_PAYLOAD_LEN as u32).wrapping_add(1));
        assert_eq!(Frame::decode(&over), Err(FrameError::TooLarge));
    }

    #[test]
    fn at_cap_is_legitimate_and_round_trips() {
        // Exactly the cap, mid-stream (bytes missing), is still need-more, not
        // an error — a legitimately large frame is allowed.
        let at_cap = header_with_len(MAX_PAYLOAD_LEN as u32);
        assert_eq!(Frame::decode(&at_cap).unwrap(), None);

        // A full payload of exactly the cap round-trips through the codec.
        let f = Frame::new(vec![0x5Au8; MAX_PAYLOAD_LEN]);
        let bytes = f.encode().unwrap();
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(decoded.frame.payload.len(), MAX_PAYLOAD_LEN);
        assert_eq!(decoded.consumed, bytes.len());

        // Encode rejects one past the cap (encode/decode symmetry).
        let too_big = Frame::new(vec![0u8; MAX_PAYLOAD_LEN + 1]);
        assert_eq!(too_big.encode(), Err(FrameError::TooLarge));
    }

    #[test]
    fn unknown_flag_bits_are_rejected_not_ignored() {
        let mut bytes = Frame::new(b"hi".to_vec()).encode().unwrap();
        bytes[3] = 0x01; // a flag bit not defined in this version
        assert_eq!(Frame::decode(&bytes), Err(FrameError::UnknownFlags));
        bytes[3] = 0x00; // the defined (all-reserved-zero) value still decodes
        assert!(Frame::decode(&bytes).unwrap().is_some());
    }

    #[test]
    fn bad_version_is_rejected() {
        let mut bytes = Frame::new(b"hi".to_vec()).encode().unwrap();
        bytes[2] = VERSION.wrapping_add(1);
        assert_eq!(Frame::decode(&bytes), Err(FrameError::BadVersion));
    }

    #[test]
    fn error_display_strings_are_distinct_and_named() {
        assert!(FrameError::TooLarge.to_string().contains("exceeds"));
        assert!(FrameError::BadMagic.to_string().contains("magic"));
        assert!(FrameError::BadVersion.to_string().contains("version"));
        assert!(FrameError::ChecksumMismatch.to_string().contains("CRC"));
        assert!(FrameError::UnknownFlags.to_string().contains("flags"));
    }

    #[test]
    fn too_large_display_names_both_documented_causes() {
        // `TooLarge` is returned for a payload over the 16 MiB policy cap AND for
        // one that cannot fit the u32 length field; the message must name both,
        // because the cap is the cause an operator actually hits (a 20 MiB
        // payload fits a u32 comfortably) and the decode path can ONLY hit the cap.
        let msg = FrameError::TooLarge.to_string();
        assert!(msg.contains("16 MiB"), "must name the policy cap: {msg}");
        assert!(msg.contains("u32"), "must name the length field: {msg}");

        // A 16 MiB + 1 payload: rejected by the cap on encode, and a header
        // advertising that length is rejected by the cap on decode -- both must
        // surface the same message.
        let over = Frame::new(vec![0u8; MAX_PAYLOAD_LEN + 1]);
        let err = over.encode().unwrap_err();
        assert_eq!(err, FrameError::TooLarge);
        assert!(err.to_string().contains("16 MiB"));

        let mut hdr = Vec::with_capacity(HEADER_SIZE);
        hdr.extend_from_slice(&MAGIC);
        hdr.push(VERSION);
        hdr.push(0);
        hdr.extend_from_slice(&((MAX_PAYLOAD_LEN as u32) + 1).to_le_bytes());
        hdr.extend_from_slice(&0u32.to_le_bytes());
        let err = Frame::decode(&hdr).unwrap_err();
        assert_eq!(err, FrameError::TooLarge);
        assert!(err.to_string().contains("16 MiB"));
    }

    #[test]
    fn trailing_bytes_are_left_for_the_next_frame() {
        let mut bytes = Frame::new(b"one".to_vec()).encode().unwrap();
        let first_len = bytes.len();
        bytes.extend_from_slice(b"leftover");
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(decoded.consumed, first_len);
    }
}
