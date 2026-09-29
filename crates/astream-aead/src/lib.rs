//! The astream AEAD wire — the confidential + authenticated half of "SSH" that
//! the capability mint ([`astream_cap`](../astream_cap/index.html)) does not
//! cover. astream-cap answers *who may attach where*; this answers *nobody on
//! the wire may read or forge the bytes*.
//!
//! Two layers:
//!
//! * [`seal`] / [`open`] — one AEAD message under a 32-byte pre-shared key, using
//!   **XChaCha20-Poly1305** (the IETF-standard extended-nonce ChaCha20-Poly1305).
//!   A 192-bit nonce means a per-message RANDOM nonce is collision-safe even
//!   across the many independent producers on a bus — no cross-producer nonce
//!   coordination. Additional authenticated data (AAD) is bound but not
//!   encrypted.
//! * [`SealedStream`] — a transparent, ordered-record AEAD adapter over any
//!   `Read + Write`, opened by a handshake ([`SealedStream::handshake_client`] /
//!   [`SealedStream::handshake_server`]). Each side sends a fresh random HELLO
//!   in the clear, and every record's AAD is then
//!   `hello_client ‖ hello_server ‖ direction ‖ sequence`, so a record opens
//!   only on the connection, in the direction, and at the position it was
//!   sealed for: a record recorded from another connection, one reflected back
//!   at its sender, and one replayed, reordered, dropped, or truncated within
//!   the connection all fail their tag. The broker's existing `Frame` protocol
//!   runs over it byte-for-byte unchanged — the transport just becomes
//!   confidential.
//!
//! # Not hand-rolled
//! The primitive is the vetted RustCrypto `chacha20poly1305` (an upstream
//! known-answer-tested, widely-audited implementation of a standard AEAD), and
//! this crate's own known-answer test pins the full ciphertext and tag of the
//! draft-irtf-cfrg-xchacha §A.3.1 vector. This crate is the ONE place astream
//! pulls a cipher dependency — deliberately isolated, exactly as `astream-cap`
//! isolates `sha2`. `forbid(unsafe_code)` applies to this crate's own code.
#![forbid(unsafe_code)]

mod stream;
pub use stream::{
    SealedStream, TryCloneable, HELLO_LEN, HELLO_MAGIC, MAX_PLAINTEXT, MAX_RECORD,
    SESSION_NONCE_LEN,
};

#[cfg(feature = "handshake")]
mod handshake;
#[cfg(feature = "handshake")]
pub use handshake::{client_handshake, server_handshake};

#[cfg(feature = "identity")]
mod identity;
#[cfg(feature = "identity")]
pub use identity::{
    client_identity_handshake, server_identity_handshake, IdentityKeypair, ID_PUB_LEN,
};

use chacha20poly1305::aead::AeadInPlace;
use chacha20poly1305::{KeyInit, Tag, XChaCha20Poly1305, XNonce};

/// Pre-shared key length (XChaCha20-Poly1305 key), in bytes.
pub const KEY_LEN: usize = 32;
/// XChaCha20 nonce length, in bytes.
pub const NONCE_LEN: usize = 24;
/// Poly1305 authentication tag length, in bytes.
pub const TAG_LEN: usize = 16;
/// Bytes a sealed message adds over its plaintext: the prepended nonce plus the
/// appended tag.
pub const OVERHEAD: usize = NONCE_LEN + TAG_LEN;

/// Opening a sealed message failed: the key or AAD is wrong, or the bytes were
/// tampered with or truncated. Deliberately opaque — a caller learns only that
/// the message is not authentic, never *why* (no padding-oracle surface).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AeadError;

impl core::fmt::Display for AeadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("aead: message is not authentic")
    }
}

impl std::error::Error for AeadError {}

/// Seal `plaintext` under `key`, binding `aad`, with a fresh random 24-byte
/// nonce. Returns `nonce ‖ ciphertext ‖ tag` (length `plaintext.len() +
/// OVERHEAD`). The nonce is drawn from the OS CSPRNG; XChaCha's 192-bit nonce
/// makes random selection collision-safe.
#[must_use]
pub fn seal(key: &[u8; KEY_LEN], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
    let mut nonce = [0u8; NONCE_LEN];
    // getrandom draws from the OS CSPRNG; it only errors if the OS entropy
    // source is missing, which is not a recoverable condition for a wire.
    getrandom::getrandom(&mut nonce).expect("OS CSPRNG unavailable");
    seal_with_nonce(key, &nonce, aad, plaintext)
}

/// Seal with a caller-supplied nonce — deterministic, for callers that manage
/// their own unique nonces (and for known-answer tests). The nonce MUST be
/// unique per key; reuse breaks confidentiality. Returns `nonce ‖ ciphertext ‖
/// tag`.
#[must_use]
pub fn seal_with_nonce(
    key: &[u8; KEY_LEN],
    nonce: &[u8; NONCE_LEN],
    aad: &[u8],
    plaintext: &[u8],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(plaintext.len() + OVERHEAD);
    out.extend_from_slice(nonce);
    out.extend_from_slice(plaintext);
    seal_in_place(key, aad, &mut out, 0);
    out
}

/// Seal in place — the one primitive both [`seal`] and the record layer use.
/// On entry `buf[at..at + NONCE_LEN]` holds the nonce and `buf[at + NONCE_LEN..]`
/// the plaintext; on return those plaintext bytes are the ciphertext and the
/// 16-byte tag has been appended, so `buf[at..]` is exactly
/// `nonce ‖ ciphertext ‖ tag`. No copy of the plaintext is made.
pub(crate) fn seal_in_place(key: &[u8; KEY_LEN], aad: &[u8], buf: &mut Vec<u8>, at: usize) {
    let cipher = XChaCha20Poly1305::new(key.into());
    let (nonce, msg) = buf[at..].split_at_mut(NONCE_LEN);
    let tag = cipher
        .encrypt_in_place_detached(XNonce::from_slice(nonce), aad, msg)
        // encrypt only fails if the message exceeds the cipher's length ceiling
        // (~256 GiB) — never for a wire record.
        .expect("plaintext exceeds XChaCha20-Poly1305 length ceiling");
    buf.extend_from_slice(&tag);
}

/// Open a message produced by [`seal`] / [`seal_with_nonce`]: verify the tag
/// against `key` and `aad`, and return the plaintext. Any tampering, a wrong
/// key, a wrong AAD, or truncation yields [`AeadError`].
///
/// # Errors
/// [`AeadError`] if `sealed` is shorter than [`OVERHEAD`] or the tag does not
/// verify.
pub fn open(key: &[u8; KEY_LEN], aad: &[u8], sealed: &[u8]) -> Result<Vec<u8>, AeadError> {
    if sealed.len() < OVERHEAD {
        return Err(AeadError);
    }
    let (nonce, rest) = sealed.split_at(NONCE_LEN);
    let (ct, tag) = rest.split_at(rest.len() - TAG_LEN);
    // Only the ciphertext is copied, and decrypted in place once its tag has
    // verified.
    let mut plain = ct.to_vec();
    XChaCha20Poly1305::new(key.into())
        .decrypt_in_place_detached(
            XNonce::from_slice(nonce),
            aad,
            &mut plain,
            Tag::from_slice(tag),
        )
        .map_err(|_| AeadError)?;
    Ok(plain)
}

/// Open in place — the record layer's primitive.
/// `buf` is `nonce ‖ ciphertext ‖ tag`; the tag is verified FIRST (constant
/// time), and only then is the ciphertext decrypted in place, so on failure the
/// buffer is untouched and nothing derived from an unauthentic message ever
/// exists. On success the returned slice is the plaintext,
/// `buf[NONCE_LEN..len - TAG_LEN]`.
pub(crate) fn open_in_place<'a>(
    key: &[u8; KEY_LEN],
    aad: &[u8],
    buf: &'a mut [u8],
) -> Result<&'a [u8], AeadError> {
    if buf.len() < OVERHEAD {
        return Err(AeadError);
    }
    let cipher = XChaCha20Poly1305::new(key.into());
    let (nonce, rest) = buf.split_at_mut(NONCE_LEN);
    let (ct, tag) = rest.split_at_mut(rest.len() - TAG_LEN);
    cipher
        .decrypt_in_place_detached(XNonce::from_slice(nonce), aad, ct, Tag::from_slice(tag))
        .map_err(|_| AeadError)?;
    Ok(ct)
}

#[cfg(test)]
mod tests {
    use super::*;

    const KEY: [u8; KEY_LEN] = [
        0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e,
        0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d,
        0x9e, 0x9f,
    ];

    #[test]
    fn round_trips_with_random_nonce() {
        let aad = b"/a/stream/term/s1/out#42";
        let msg = b"the quick brown fox jumps over the lazy dog";
        let sealed = seal(&KEY, aad, msg);
        assert_eq!(sealed.len(), msg.len() + OVERHEAD);
        assert_eq!(open(&KEY, aad, &sealed).unwrap(), msg);
    }

    #[test]
    fn two_seals_differ_but_both_open() {
        // Random nonces ⇒ two seals of the same plaintext are distinct ciphertext
        // (no deterministic leakage), yet both authenticate.
        let msg = b"repeatme";
        let a = seal(&KEY, b"", msg);
        let b = seal(&KEY, b"", msg);
        assert_ne!(a, b);
        assert_eq!(open(&KEY, b"", &a).unwrap(), msg);
        assert_eq!(open(&KEY, b"", &b).unwrap(), msg);
    }

    #[test]
    fn every_single_byte_corruption_is_rejected() {
        // A real AEAD: flipping ANY bit of nonce, ciphertext, or tag fails to open.
        let aad = b"aad";
        let msg = b"authenticate every byte of me";
        let sealed = seal(&KEY, aad, msg);
        for i in 0..sealed.len() {
            let mut bad = sealed.clone();
            bad[i] ^= 0x01;
            assert_eq!(open(&KEY, aad, &bad), Err(AeadError), "byte {i} not caught");
        }
    }

    #[test]
    fn wrong_key_aad_and_truncation_are_rejected() {
        let aad = b"bind-me";
        let msg = b"secret";
        let sealed = seal(&KEY, aad, msg);

        let mut other = KEY;
        other[0] ^= 0xff;
        assert_eq!(open(&other, aad, &sealed), Err(AeadError));
        assert_eq!(open(&KEY, b"different-aad", &sealed), Err(AeadError));
        assert_eq!(open(&KEY, aad, &sealed[..sealed.len() - 1]), Err(AeadError));
        assert_eq!(open(&KEY, aad, &sealed[..OVERHEAD - 1]), Err(AeadError));
    }

    #[test]
    fn a_failed_open_leaves_the_buffer_untouched() {
        // The tag is verified BEFORE decryption: on failure nothing derived from an
        // unauthentic message is ever written back into the buffer.
        let sealed = seal(&KEY, b"aad", b"do not decrypt me on failure");
        let mut buf = sealed.clone();
        assert_eq!(open_in_place(&KEY, b"other-aad", &mut buf), Err(AeadError));
        assert_eq!(buf, sealed);
    }

    #[test]
    fn matches_the_draft_irtf_cfrg_xchacha_a_3_1_known_answer() {
        // draft-irtf-cfrg-xchacha-03 §A.3.1 (AEAD_XCHACHA20_POLY1305): the classic
        // 114-byte "sunscreen" plaintext under key 0x80..0x9f, nonce 0x40..0x57, AAD
        // 50 51 52 53 c0 c1 c2 c3 c4 c5 c6 c7. The FULL 114-byte ciphertext and the
        // 16-byte Poly1305 tag are asserted, so this pins the wire FORMAT
        // (nonce-prefixed, tag-suffixed) AND the primitive's conformance to the
        // standard (HChaCha20 subkey derivation, the keystream, and Poly1305 over
        // the padded AAD ‖ ciphertext ‖ lengths): a dependency that became
        // self-consistent-but-nonconformant (seal/open still round-tripping) would
        // fail here rather than silently produce a wire no conformant peer can read.
        let nonce: [u8; NONCE_LEN] = [
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d,
            0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
        ];
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let pt = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        const CIPHERTEXT: [u8; 114] = [
            0xbd, 0x6d, 0x17, 0x9d, 0x3e, 0x83, 0xd4, 0x3b, 0x95, 0x76, 0x57, 0x94, 0x93, 0xc0,
            0xe9, 0x39, 0x57, 0x2a, 0x17, 0x00, 0x25, 0x2b, 0xfa, 0xcc, 0xbe, 0xd2, 0x90, 0x2c,
            0x21, 0x39, 0x6c, 0xbb, 0x73, 0x1c, 0x7f, 0x1b, 0x0b, 0x4a, 0xa6, 0x44, 0x0b, 0xf3,
            0xa8, 0x2f, 0x4e, 0xda, 0x7e, 0x39, 0xae, 0x64, 0xc6, 0x70, 0x8c, 0x54, 0xc2, 0x16,
            0xcb, 0x96, 0xb7, 0x2e, 0x12, 0x13, 0xb4, 0x52, 0x2f, 0x8c, 0x9b, 0xa4, 0x0d, 0xb5,
            0xd9, 0x45, 0xb1, 0x1b, 0x69, 0xb9, 0x82, 0xc1, 0xbb, 0x9e, 0x3f, 0x3f, 0xac, 0x2b,
            0xc3, 0x69, 0x48, 0x8f, 0x76, 0xb2, 0x38, 0x35, 0x65, 0xd3, 0xff, 0xf9, 0x21, 0xf9,
            0x66, 0x4c, 0x97, 0x63, 0x7d, 0xa9, 0x76, 0x88, 0x12, 0xf6, 0x15, 0xc6, 0x8b, 0x13,
            0xb5, 0x2e,
        ];
        const TAG: [u8; TAG_LEN] = [
            0xc0, 0x87, 0x59, 0x24, 0xc1, 0xc7, 0x98, 0x79, 0x47, 0xde, 0xaf, 0xd8, 0x78, 0x0a,
            0xcf, 0x49,
        ];
        assert_eq!(pt.len(), CIPHERTEXT.len());

        // Seal: nonce prepended verbatim, then EXACTLY the draft's ciphertext, then
        // EXACTLY the draft's tag.
        let sealed = seal_with_nonce(&KEY, &nonce, &aad, pt);
        assert_eq!(sealed.len(), NONCE_LEN + CIPHERTEXT.len() + TAG_LEN);
        assert_eq!(&sealed[..NONCE_LEN], &nonce);
        assert_eq!(
            &sealed[NONCE_LEN..NONCE_LEN + CIPHERTEXT.len()],
            &CIPHERTEXT
        );
        assert_eq!(&sealed[NONCE_LEN + CIPHERTEXT.len()..], &TAG);
        assert_eq!(seal_with_nonce(&KEY, &nonce, &aad, pt), sealed);

        // Open: the draft's own `nonce ‖ ciphertext ‖ tag` (assembled from the
        // constants, not from our seal) yields the plaintext.
        let mut wire = nonce.to_vec();
        wire.extend_from_slice(&CIPHERTEXT);
        wire.extend_from_slice(&TAG);
        assert_eq!(open(&KEY, &aad, &wire).unwrap(), pt);
    }
}
