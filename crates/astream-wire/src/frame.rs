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

use crate::hash::{crc32_ieee, crc32_ieee_prefix};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "frame_island.rs"]
mod frame_island;
#[cfg(not(clean_islands))]
pub use crate::twins::frame_clamp_payload_len;
#[cfg(clean_islands)]
pub use frame_island::frame_clamp_payload_len;

contract_fn! {
    /// Kernel-certified payload-cap check (`len <= cap`), backed by the Clean
    /// `payload_within_cap_isl` specification (`clean-kernel-defeq`) and the
    /// Clean-origin [`frame_clamp_payload_len`] (`min(len, cap)`).
    #[must_use]
    pub const fn payload_within_cap(len: u64, cap: u64) -> bool
    clauses [ensures result == (len <= cap)]
    {
        len <= cap
    }
}

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

impl FrameError {
    /// Human-readable static description of the frame error.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            // Both documented causes are named: the 16 MiB policy cap is the one
            // an operator actually hits (every decode-path hit, and any encode of
            // 16 MiB..4 GiB); the u32 field is the theoretical encode-side ceiling.
            FrameError::TooLarge => "frame payload exceeds the 16 MiB cap or the u32 length field",
            FrameError::BadMagic => "frame magic mismatch",
            FrameError::BadVersion => "unsupported frame version",
            FrameError::ChecksumMismatch => "frame payload CRC mismatch",
            FrameError::UnknownFlags => "frame flags byte sets bits unknown to this version",
        }
    }
}

impl std::fmt::Display for FrameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl std::error::Error for FrameError {}

/// Encode the 12-byte [`Frame`] header for `payload`, checking [`MAX_PAYLOAD_LEN`]
/// and computing the CRC-32 checksum.
pub const fn encode_frame_header(payload: &[u8]) -> Result<[u8; HEADER_SIZE], FrameError> {
    if payload.len() > MAX_PAYLOAD_LEN {
        return Err(FrameError::TooLarge);
    }
    // `MAX_PAYLOAD_LEN` is 16 MiB, which always fits in `u32`.
    let len_u32 = payload.len() as u32;
    let l0 = (len_u32 & 0xff) as u8;
    let l1 = ((len_u32 >> 8) & 0xff) as u8;
    let l2 = ((len_u32 >> 16) & 0xff) as u8;
    let l3 = ((len_u32 >> 24) & 0xff) as u8;
    let crc = crc32_ieee(payload);
    let c0 = (crc & 0xff) as u8;
    let c1 = ((crc >> 8) & 0xff) as u8;
    let c2 = ((crc >> 16) & 0xff) as u8;
    let c3 = ((crc >> 24) & 0xff) as u8;
    Ok([
        MAGIC[0], MAGIC[1], VERSION, 0u8, l0, l1, l2, l3, c0, c1, c2, c3,
    ])
}

/// Decode and validate a 12-byte [`Frame`] header `(payload_len, crc32)`.
pub const fn decode_frame_header_bytes(
    hdr: &[u8; HEADER_SIZE],
) -> Result<(usize, u32), FrameError> {
    let m0 = hdr[0];
    let m1 = hdr[1];
    let ver = hdr[2];
    let flags = hdr[3];
    let len = ((hdr[4] as u32)
        | ((hdr[5] as u32) << 8)
        | ((hdr[6] as u32) << 16)
        | ((hdr[7] as u32) << 24)) as usize;
    let crc = (hdr[8] as u32)
        | ((hdr[9] as u32) << 8)
        | ((hdr[10] as u32) << 16)
        | ((hdr[11] as u32) << 24);
    if m0 != MAGIC[0] || m1 != MAGIC[1] {
        return Err(FrameError::BadMagic);
    }
    if ver != VERSION {
        return Err(FrameError::BadVersion);
    }
    // Reserved flag bits MUST be zero; reject unknown bits rather than
    // silently ignoring them (forward-compat guard).
    if flags & !KNOWN_FLAGS != 0 {
        return Err(FrameError::UnknownFlags);
    }

    // Cap how much we will commit to before the bytes are even present: an
    // absurd-but-representable length is rejected, never buffered toward.
    if len > MAX_PAYLOAD_LEN {
        return Err(FrameError::TooLarge);
    }
    Ok((len, crc))
}

/// Validate a frame starting at `buf`, returning `(payload_len, rest_after_header)`
/// when a complete, CRC-valid frame is present, `Ok(None)` when more bytes are
/// needed, or `Err(..)` when the header or CRC is invalid.
///
/// Uses built-in slice pattern matching (`Subslice`) and [`crc32_ieee_prefix`],
/// avoiding `split_first_chunk` and `split_at_checked`.
pub const fn validate_frame_at(buf: &[u8]) -> Result<Option<(usize, &[u8])>, FrameError> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ref rest @ ..] = buf else {
        return Ok(None);
    };
    let (len, crc) =
        match decode_frame_header_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) {
            Ok(pair) => pair,
            Err(e) => return Err(e),
        };
    let Some(actual_crc) = crc32_ieee_prefix(rest, len) else {
        return Ok(None);
    };
    if actual_crc != crc {
        return Err(FrameError::ChecksumMismatch);
    }
    Ok(Some((len, rest)))
}

/// Zero-copy [`Frame`] decoder returning `(payload_slice, total_consumed)`.
pub fn decode_frame_slice(buf: &[u8]) -> Result<Option<(&[u8], usize)>, FrameError> {
    let (len, rest) = match validate_frame_at(buf) {
        Ok(Some(pair)) => pair,
        Ok(None) => return Ok(None),
        Err(e) => return Err(e),
    };
    let Some(payload) = rest.get(..len) else {
        return Ok(None);
    };
    Ok(Some((payload, HEADER_SIZE.saturating_add(len))))
}

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
    #[must_use]
    pub const fn new(payload: Vec<u8>) -> Self {
        Frame { payload }
    }

    /// Encode to bytes. Returns [`FrameError::TooLarge`] (never panics) if the
    /// payload exceeds the [`MAX_PAYLOAD_LEN`] policy cap (16 MiB) or the `u32`
    /// length field.
    pub fn encode(&self) -> Result<Vec<u8>, FrameError> {
        let hdr = encode_frame_header(&self.payload)?;
        let mut out = Vec::with_capacity(HEADER_SIZE + 256);
        out.extend_from_slice(&hdr);
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
        match decode_frame_slice(buf) {
            Ok(Some((payload, consumed))) => Ok(Some(Decoded {
                frame: Frame {
                    payload: payload.to_vec(),
                },
                consumed,
            })),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
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
    fn trailing_bytes_are_left_for_the_next_frame() {
        let mut bytes = Frame::new(b"one".to_vec()).encode().unwrap();
        let first_len = bytes.len();
        bytes.extend_from_slice(b"leftover");
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(decoded.consumed, first_len);
    }

    #[test]
    fn clean_origin_frame_clamp_and_payload_within_cap_match_policy_cap() {
        let cap = MAX_PAYLOAD_LEN as u64;
        assert!(payload_within_cap(0, cap));
        assert!(payload_within_cap(cap, cap));
        assert!(!payload_within_cap(cap + 1, cap));
        assert_eq!(frame_clamp_payload_len(0, cap), 0);
        assert_eq!(frame_clamp_payload_len(cap, cap), cap);
        assert_eq!(frame_clamp_payload_len(cap + 4096, cap), cap);
    }
}
