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
//! * [`SealedStream`] (feature `stream`, on by default) — a transparent, ordered-record
//!   AEAD adapter over any `Read + Write`, opened by a handshake
//!   ([`SealedStream::handshake_client`] / [`SealedStream::handshake_server`]). Each side
//!   sends a fresh random HELLO in the clear, and every record's AAD is then
//!   `hello_client ‖ hello_server ‖ direction ‖ sequence`, so a record opens
//!   only on the connection, in the direction, and at the position it was
//!   sealed for: a record recorded from another connection, one reflected back
//!   at its sender, and one replayed, reordered, dropped, or truncated within
//!   the connection all fail their tag. The broker's existing `Frame` protocol
//!   runs over it byte-for-byte unchanged — the transport just becomes
//!   confidential.
//!
//! # Not hand-rolled
//! The cipher and the MAC are ring's ChaCha20-Poly1305 (RFC 8439; ring 0.17, the one
//! aterm already ships under rustls), and XChaCha20-Poly1305 is built on it exactly as
//! draft-irtf-cfrg-xchacha-03 §2.3 defines it: the per-message subkey is HChaCha20 of
//! the key and nonce bytes 0..16, and ChaCha20-Poly1305's 96-bit nonce is four zero
//! bytes followed by nonce bytes 16..24. HChaCha20 (`hchacha.rs`) is the one part
//! computed here: the ChaCha20 block function's rounds without their final addition,
//! constant-time by construction (add, rotate, xor on 32-bit words), held to the
//! draft's §2.2.1 vector and to subkeys recorded from RustCrypto's `chacha20`. The wire
//! is the one this crate sealed over RustCrypto's `chacha20poly1305` until the move to
//! ring: `tests/recorded.rs` reproduces every seal recorded from it byte for byte and
//! opens a session recorded from it, and this crate's own known-answer test pins the
//! full ciphertext and tag of the draft's §A.3.1 vector. This crate is the ONE place
//! astream pulls a cipher dependency — deliberately isolated; the handshake's
//! HMAC/HKDF are the workspace's own, `astream-digest`'s, over its SHA-256.
//! `forbid(unsafe_code)` applies to this crate's own code.
//!
//! The `handshake` and `identity` features still delegate raw X25519 and Ed25519 to
//! `x25519-dalek` and `ed25519-dalek`: ring cannot build an X25519 secret from bytes
//! (its agreement keys come only from its own RNG). Both features are off by default.
//! `signature`, the raw Ed25519 astream-broker's `relay` checks a record's origin with, is
//! ring's: it adds no crate.
//!
//! # Keys in memory
//! The pre-shared key a [`SealedStream`] holds, each per-message subkey, and
//! HChaCha20's working state are wiped (`zeroize`) when dropped. ring keeps no wiping
//! hook on its key schedule and this crate forbids `unsafe`, so the subkey's copy
//! inside ring is overwritten in place with an all-zero key once the message is
//! sealed or opened. As with any wiping in Rust, a copy that a move left behind on the
//! stack is out of reach.
#![forbid(unsafe_code)]
// The crate docs name `SealedStream`, which a build without `stream` does not compile.
#![cfg_attr(not(feature = "stream"), allow(rustdoc::broken_intra_doc_links))]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

#[cfg(feature = "stream")]
mod stream;
#[cfg(feature = "stream")]
pub use stream::{
    aead_can_open_in_order, aead_seq_monotone, SealedStream, TryCloneable, HELLO_LEN, HELLO_MAGIC,
    MAX_PLAINTEXT, MAX_RECORD, SESSION_NONCE_LEN,
};

#[cfg(feature = "handshake")]
mod handshake;
#[cfg(feature = "handshake")]
pub use handshake::{
    client_handshake, handshake_clamp_info_len, handshake_version_valid, server_handshake,
};

#[cfg(feature = "handshake")]
mod roam;
#[cfg(feature = "handshake")]
pub use roam::{
    client_roam_connect, roam_amp_allows_send, roam_amp_budget_clamp, roam_contig_offset_matches,
    roam_epoch_advance, RoamCloser, RoamHandle, RoamListener, RoamStream, MAX_ROAM_CHUNK,
    MAX_ROAM_INFLIGHT_BYTES, ROAM_WIRE_MAGIC, ROAM_WIRE_VERSION,
};

#[cfg(feature = "identity")]
mod identity;
#[cfg(feature = "signature")]
pub mod signature;
#[cfg(feature = "identity")]
pub use identity::{
    client_identity_handshake, identity_auth_msg_len_valid, identity_clamp_ctx_len,
    server_identity_handshake, IdentityKeypair, ID_PUB_LEN,
};

#[cfg(feature = "identity")]
mod cert;
#[cfg(all(feature = "identity", unix))]
pub use cert::SshAgentServer;
#[cfg(feature = "identity")]
pub use cert::{
    cert_epoch_advance, cert_horizon_reached, cert_validity_clamp, cert_wire_version_valid,
    client_cert_handshake, decode_ssh_ed25519_key_blob, encode_ssh_ed25519_key_blob,
    server_cert_handshake, ssh_agent_list_over, ssh_agent_sign_over, CertRole, CertTrustStore,
    CertificateAuthority, HostCertRotator, IdentityCertificate, IdentitySigner, SharedCertTrust,
    SshAgentSigner, VerifiedPeerCert, CERT_WIRE_MAGIC, CERT_WIRE_VERSION, MAX_CERT_ISSUER_LEN,
    MAX_CERT_PRINCIPAL_LEN, MAX_CERT_REVOKED_SERIALS, MAX_CERT_VALIDITY_CAP_MS, MAX_CERT_WIRE_LEN,
    MAX_TRUSTED_CAS, MIN_CERT_WIRE_LEN,
};

mod hchacha;

use ring::aead::{Aad, LessSafeKey, Nonce, Tag, UnboundKey, CHACHA20_POLY1305};

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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
mod aead_island;
#[cfg(not(clean_islands))]
pub use crate::twins::aead_clamp_sealed_len;
#[cfg(clean_islands)]
pub use aead_island::aead_clamp_sealed_len;

contract_fn! {
    /// Verified check that a sealed AEAD box has at least `overhead` bytes (`overhead <= sealed_len`),
    /// linked via `clean-kernel-defeq` to `aead_sealed_has_overhead_isl`.
    #[must_use]
    pub const fn aead_sealed_has_overhead(sealed_len: usize, overhead: usize) -> bool
    clauses [ensures result == (overhead <= sealed_len)]
    {
        overhead <= sealed_len
    }
}

/// Seal `plaintext` under `key`, binding `aad`, with a fresh random 24-byte
/// nonce. Returns `nonce ‖ ciphertext ‖ tag` (length `plaintext.len() +
/// OVERHEAD`). The nonce is drawn from the OS CSPRNG; XChaCha's 192-bit nonce
/// makes random selection collision-safe.
#[must_use]
pub fn seal(key: &[u8; KEY_LEN], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
    let mut nonce = [0u8; NONCE_LEN];
    // getrandom draws from the OS CSPRNG; it only errors if the OS entropy
    // source is missing, which is not a recoverable condition for a wire.
    assert!(
        getrandom::getrandom(&mut nonce).is_ok(),
        "OS CSPRNG unavailable"
    );
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
    let mut out = Vec::with_capacity(OVERHEAD);
    out.extend_from_slice(nonce);
    out.extend_from_slice(plaintext);
    seal_in_place(key, aad, &mut out, 0);
    out
}

/// ring's ChaCha20-Poly1305 under one message's XChaCha20 subkey.
///
/// ring keeps no wiping hook on its key schedule, and this crate forbids `unsafe`, so
/// on drop the one place the subkey lives in ring's key is overwritten in place with
/// an all-zero key (and `black_box` keeps that store from being elided).
struct MessageKey(LessSafeKey);

impl MessageKey {
    /// The ChaCha20-Poly1305 key and nonce XChaCha20-Poly1305 seals one message under
    /// (draft-irtf-cfrg-xchacha-03 §2.3): HChaCha20 of `key` and `nonce[..16]` is the
    /// subkey, and `0x00000000 ‖ nonce[16..]` the 96-bit nonce. `None` only if `nonce`
    /// is not [`NONCE_LEN`] bytes.
    fn derive(key: &[u8; KEY_LEN], nonce: &[u8]) -> Option<(MessageKey, Nonce)> {
        let (head, tail) = nonce.split_first_chunk::<{ hchacha::HCHACHA_INPUT_LEN }>()?;
        let &[t0, t1, t2, t3, t4, t5, t6, t7] = tail else {
            return None;
        };
        let subkey = hchacha::hchacha20(key, head);
        let Ok(unbound) = UnboundKey::new(&CHACHA20_POLY1305, subkey.as_slice()) else {
            return None;
        };
        let nonce = [0, 0, 0, 0, t0, t1, t2, t3, t4, t5, t6, t7];
        Some((
            MessageKey(LessSafeKey::new(unbound)),
            Nonce::assume_unique_for_key(nonce),
        ))
    }
}

impl Drop for MessageKey {
    fn drop(&mut self) {
        if let Ok(zero) = UnboundKey::new(&CHACHA20_POLY1305, &[0u8; KEY_LEN]) {
            self.0 = LessSafeKey::new(zero);
        }
        core::hint::black_box(&self.0);
    }
}

/// Seal in place — the one primitive both [`seal`] and the record layer use.
/// On entry `buf[at..at + NONCE_LEN]` holds the nonce and `buf[at + NONCE_LEN..]`
/// the plaintext; on return those plaintext bytes are the ciphertext and the
/// 16-byte tag has been appended, so `buf[at..]` is exactly
/// `nonce ‖ ciphertext ‖ tag`. No copy of the plaintext is made.
pub(crate) fn seal_in_place(key: &[u8; KEY_LEN], aad: &[u8], buf: &mut Vec<u8>, at: usize) {
    let Some(tail) = buf.get_mut(at..) else {
        return;
    };
    let Some((nonce, msg)) = tail.split_at_mut_checked(NONCE_LEN) else {
        return;
    };
    let Some((cipher, nonce)) = MessageKey::derive(key, nonce) else {
        // A 24-byte nonce and a 32-byte subkey always make a key, so this does not
        // happen; were it to, no plaintext is left to reach the wire and no tag is
        // appended, so the record can never open.
        msg.fill(0);
        return;
    };
    let Ok(tag) = cipher
        .0
        .seal_in_place_separate_tag(nonce, Aad::from(aad), msg)
    else {
        // ring refuses only a message past ChaCha20-Poly1305's length ceiling
        // (~256 GiB) — never a wire record; were it to, zero msg and append no tag.
        msg.fill(0);
        return;
    };
    buf.extend_from_slice(tag.as_ref());
}

/// Open `ct` in place under `key`, the 24-byte `nonce`, `aad` and the 16-byte `tag`.
/// ring decrypts as it authenticates and compares the tag in constant time; on a
/// mismatch it zeroes `ct` before returning, so no plaintext of an unauthentic message
/// survives the call.
fn open_detached(
    key: &[u8; KEY_LEN],
    nonce: &[u8],
    aad: &[u8],
    ct: &mut [u8],
    tag: &[u8],
) -> Result<(), AeadError> {
    let (cipher, nonce) = MessageKey::derive(key, nonce).ok_or(AeadError)?;
    let tag = Tag::try_from(tag).map_err(|_| AeadError)?;
    cipher
        .0
        .open_in_place_separate_tag(nonce, Aad::from(aad), tag, ct, 0..)
        .map_err(|_| AeadError)?;
    Ok(())
}

/// Open a message produced by [`seal`] / [`seal_with_nonce`]: verify the tag
/// against `key` and `aad`, and return the plaintext. Any tampering, a wrong
/// key, a wrong AAD, or truncation yields [`AeadError`].
///
/// # Errors
/// [`AeadError`] if `sealed` is shorter than [`OVERHEAD`] or the tag does not
/// verify.
pub fn open(key: &[u8; KEY_LEN], aad: &[u8], sealed: &[u8]) -> Result<Vec<u8>, AeadError> {
    if !aead_sealed_has_overhead(sealed.len(), OVERHEAD) {
        return Err(AeadError);
    }
    let Some((nonce, rest)) = sealed.split_at_checked(NONCE_LEN) else {
        return Err(AeadError);
    };
    let Some(ct_len) = rest.len().checked_sub(TAG_LEN) else {
        return Err(AeadError);
    };
    let Some((ct, tag)) = rest.split_at_checked(ct_len) else {
        return Err(AeadError);
    };
    // Only the ciphertext is copied, and decrypted in place; a failed open leaves
    // the copy zeroed and drops it.
    let mut plain = ct.to_vec();
    open_detached(key, nonce, aad, &mut plain, tag)?;
    Ok(plain)
}

/// Open in place — the record layer's primitive.
/// `buf` is `nonce ‖ ciphertext ‖ tag`. On success the returned slice is the
/// plaintext, `buf[NONCE_LEN..len - TAG_LEN]`. On failure the ciphertext span is
/// zeroed (ring decrypts as it authenticates, then wipes what it decrypted) and the
/// nonce and tag are left as they were, so nothing derived from an unauthentic
/// message survives in the buffer.
#[cfg(any(test, feature = "stream"))]
pub(crate) fn open_in_place<'a>(
    key: &[u8; KEY_LEN],
    aad: &[u8],
    buf: &'a mut [u8],
) -> Result<&'a [u8], AeadError> {
    if !aead_sealed_has_overhead(buf.len(), OVERHEAD) {
        return Err(AeadError);
    }
    let Some((nonce, rest)) = buf.split_at_mut_checked(NONCE_LEN) else {
        return Err(AeadError);
    };
    let Some(ct_len) = rest.len().checked_sub(TAG_LEN) else {
        return Err(AeadError);
    };
    let Some((ct, tag)) = rest.split_at_mut_checked(ct_len) else {
        return Err(AeadError);
    };
    open_detached(key, nonce, aad, ct, tag)?;
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

        // The exported length gate is the one `open` applies: an empty message
        // passes it and opens, and one byte less fails both.
        let empty = seal(&KEY, aad, b"");
        assert_eq!(open(&KEY, aad, &empty), Ok(Vec::new()));
        for sealed in [&empty[..], &empty[..empty.len() - 1]] {
            assert_eq!(
                aead_sealed_has_overhead(sealed.len(), OVERHEAD),
                open(&KEY, aad, sealed).is_ok(),
                "{} bytes",
                sealed.len()
            );
        }
    }

    /// A transport whose peer is a fixed script: reads drain `peer`, then EOF,
    /// and writes are kept in `sent`. A read while a write is unflushed is
    /// refused with `WouldBlock`: over a buffering transport, a handshake that
    /// waits for its peer before flushing what it sent would deadlock. A handshake
    /// meets a malformed, silent or unkeyed peer through it with no socket.
    #[cfg(feature = "stream")]
    pub(crate) struct Scripted {
        peer: std::io::Cursor<Vec<u8>>,
        // Read by the handshake's wire pin only.
        #[cfg_attr(not(feature = "handshake"), allow(dead_code))]
        pub(crate) sent: Vec<u8>,
        unflushed: bool,
    }

    #[cfg(feature = "stream")]
    impl Scripted {
        pub(crate) fn new(peer: Vec<u8>) -> Self {
            Scripted {
                peer: std::io::Cursor::new(peer),
                sent: Vec::new(),
                unflushed: false,
            }
        }
    }

    #[cfg(feature = "stream")]
    impl std::io::Read for Scripted {
        fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
            if self.unflushed {
                return Err(std::io::ErrorKind::WouldBlock.into());
            }
            self.peer.read(out)
        }
    }

    #[cfg(feature = "stream")]
    impl std::io::Write for Scripted {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            self.sent.extend_from_slice(bytes);
            self.unflushed = true;
            Ok(bytes.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.unflushed = false;
            Ok(())
        }
    }

    #[test]
    fn a_failed_open_leaves_no_plaintext_in_the_buffer() {
        // ring decrypts as it authenticates, so a failed open has decrypted the
        // ciphertext span; it zeroes that span before returning. Nonce and tag are
        // untouched, and no byte of the plaintext is left behind.
        let msg = b"do not decrypt me on failure";
        let sealed = seal(&KEY, b"aad", msg);
        let mut buf = sealed.clone();
        assert_eq!(open_in_place(&KEY, b"other-aad", &mut buf), Err(AeadError));
        let ct = NONCE_LEN..NONCE_LEN + msg.len();
        assert_eq!(buf[..ct.start], sealed[..ct.start]);
        assert!(buf[ct.clone()].iter().all(|&b| b == 0));
        assert_eq!(buf[ct.end..], sealed[ct.end..]);
        // The control: the same buffer, opened with the right AAD, would have held
        // the plaintext there.
        let mut good = sealed.clone();
        assert_eq!(open_in_place(&KEY, b"aad", &mut good).unwrap(), msg);
        assert_eq!(&good[ct], msg);
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
