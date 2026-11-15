// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The origin-signed envelope a relayed record's body is.
//!
//! ```text
//! body    := signature (64 bytes) payload
//! signed  := DOMAIN  u32-le subject length  subject  u64-le sequence  SHA-256(payload)
//! ```
//!
//! An origin writes the envelope as the record's body in its own log, and every bridge carries it
//! unchanged, so a broker many hops away checks the origin's own signature, not its neighbour's
//! word. The record format does not change: the producer id and sequence are the record's own.

use astream_digest::Sha256;

/// Bytes of the signature an envelope starts with.
pub const SIGNATURE_LEN: usize = 64;

/// Keeps these signatures from being taken for any other a node's key makes.
const DOMAIN: &[u8] = b"astream relay origin v1\0";

fn signed_message(subject: &str, sequence: u64, payload: &[u8]) -> Vec<u8> {
    let cap = subject.len().saturating_add(68);
    let mut message = if cap <= 65_536 {
        Vec::with_capacity(cap)
    } else {
        Vec::new()
    };
    message.extend_from_slice(DOMAIN);
    // A subject is bounded far below this by the wire's own limits; saturating cannot make two
    // subjects of an accepted length sign alike.
    let len = u32::try_from(subject.len()).unwrap_or(u32::MAX);
    message.extend_from_slice(&len.to_le_bytes());
    message.extend_from_slice(subject.as_bytes());
    message.extend_from_slice(&sequence.to_le_bytes());
    message.extend_from_slice(&Sha256::digest(payload));
    message
}

/// The public key of an origin's signing `seed`, whose `identity_principal` is what its subjects
/// must name as their owner.
#[must_use]
pub fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    astream_aead::signature::public_key(seed)
}

/// The body an origin publishes for `payload` at `(subject, sequence)`.
#[must_use]
pub fn seal(seed: &[u8; 32], subject: &str, sequence: u64, payload: &[u8]) -> Vec<u8> {
    let signature =
        astream_aead::signature::sign(seed, &signed_message(subject, sequence, payload));
    let cap = payload.len().saturating_add(SIGNATURE_LEN);
    let mut body = if cap <= 16_777_280 {
        Vec::with_capacity(cap)
    } else {
        Vec::new()
    };
    body.extend_from_slice(&signature);
    body.extend_from_slice(payload);
    body
}

/// The payload of an envelope, unchecked: a broker has checked it before appending it.
#[must_use]
pub fn payload(body: &[u8]) -> Option<&[u8]> {
    body.get(SIGNATURE_LEN..)
}

/// Whether `body` is an envelope `public` signed for `(subject, sequence)`.
#[must_use]
pub fn verify(public: &[u8; 32], subject: &str, sequence: u64, body: &[u8]) -> bool {
    let Some((signature, payload)) = body.split_first_chunk::<SIGNATURE_LEN>() else {
        return false;
    };
    astream_aead::signature::verify(
        public,
        &signed_message(subject, sequence, payload),
        signature,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: [u8; 32] = [3; 32];

    #[test]
    fn an_envelope_verifies_only_as_what_it_was_signed_for() {
        let key = public_key(&SEED);
        let body = seal(&SEED, "/m/n-a/x", 7, b"payload");
        assert_eq!(payload(&body), Some(&b"payload"[..]));
        assert!(verify(&key, "/m/n-a/x", 7, &body));

        assert!(!verify(&key, "/m/n-a/y", 7, &body), "another subject");
        assert!(!verify(&key, "/m/n-a/x", 8, &body), "another sequence");
        assert!(!verify(&public_key(&[4; 32]), "/m/n-a/x", 7, &body), "key");
        let mut tampered = body.clone();
        *tampered.last_mut().unwrap() ^= 1;
        assert!(!verify(&key, "/m/n-a/x", 7, &tampered), "the payload");
        let mut tampered = body.clone();
        tampered[0] ^= 1;
        assert!(!verify(&key, "/m/n-a/x", 7, &tampered), "the signature");
        assert!(!verify(&key, "/m/n-a/x", 7, &body[..63]), "too short");
        assert!(!verify(&key, "/m/n-a/x", 7, b""), "empty");
    }

    #[test]
    fn an_empty_payload_is_an_envelope() {
        let body = seal(&SEED, "/m/n-a/x", 1, b"");
        assert_eq!(body.len(), SIGNATURE_LEN);
        assert!(verify(&public_key(&SEED), "/m/n-a/x", 1, &body));
    }

    /// The signed text is a wire contract across every Mac: this is what a change to it breaks.
    #[test]
    fn the_signed_message_is_this_layout() {
        let mut want = b"astream relay origin v1\0".to_vec();
        want.extend_from_slice(&[3, 0, 0, 0]);
        want.extend_from_slice(b"/m/");
        want.extend_from_slice(&[9, 0, 0, 0, 0, 0, 0, 0]);
        want.extend_from_slice(&Sha256::digest(b"p"));
        assert_eq!(signed_message("/m/", 9, b"p"), want);
    }
}
