// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Raw Ed25519 over a 32-byte seed, delegated to ring: the implementation rustls already brings to
//! an embedder, whose node keys are ring's.
//!
//! ring refuses a non-canonical scalar and an invalid point. It takes a small-order point, which
//! lets a key sign for every message, and so [`verify`] refuses those by their encodings, as
//! `ed25519-dalek`'s `verify_strict` does: one message has one signature per key.

use ring::signature::{Ed25519KeyPair, KeyPair, UnparsedPublicKey, ED25519};

/// Every encoding of a point of small order, with its sign bit clear: the eight points and the
/// non-canonical spellings of `y` they have (`p - 1`, `p` and `p + 1`).
const SMALL_ORDER: [[u8; 32]; 7] = [
    // y = 0, order 4.
    [0; 32],
    // y = 1, order 1.
    [
        0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ],
    // Order 8.
    [
        0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98,
        0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53,
        0xfc, 0x05,
    ],
    // Order 8.
    [
        0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67,
        0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac,
        0x03, 0x7a,
    ],
    // y = p - 1, order 2.
    [
        0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    // y = p, which is 0.
    [
        0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    // y = p + 1, which is 1.
    [
        0xee, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
];

/// Whether `point` encodes a point of small order, whichever its sign bit.
fn is_small_order(point: &[u8; 32]) -> bool {
    let mut y = *point;
    y[31] &= 0x7f;
    SMALL_ORDER.contains(&y)
}

/// The public key of `seed`.
#[must_use]
pub fn public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut public = [0u8; 32];
    if let Ok(pair) = Ed25519KeyPair::from_seed_unchecked(seed) {
        public.copy_from_slice(pair.public_key().as_ref());
    }
    public
}

/// `seed`'s signature over `message`.
#[must_use]
pub fn sign(seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    if let Ok(pair) = Ed25519KeyPair::from_seed_unchecked(seed) {
        let signature = pair.sign(message);
        out.copy_from_slice(signature.as_ref());
    }
    out
}

/// Whether `signature` is `public`'s over `message`. Strict: it refuses a small-order key or
/// commitment and a non-canonical signature, so one message has one signature per key.
#[must_use]
pub fn verify(public: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    let commitment = signature.first_chunk::<32>();
    if is_small_order(public) || commitment.is_some_and(is_small_order) {
        return false;
    }
    UnparsedPublicKey::new(&ED25519, public)
        .verify(message, signature)
        .is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap();
        }
        out
    }

    /// RFC 8032 §7.1, TEST 1 and TEST 2.
    #[test]
    fn the_rfc_8032_vectors_hold() {
        let vectors: [(&str, &str, &[u8], &str); 2] = [
            (
                "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                b"",
                "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
                 5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
            ),
            (
                "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                &[0x72],
                "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
                 085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
            ),
        ];
        for (seed, public, message, signature) in vectors {
            let seed: [u8; 32] = hex(seed);
            let public: [u8; 32] = hex(public);
            let signature: [u8; 64] = hex(&signature.replace([' ', '\n'], ""));
            assert_eq!(public_key(&seed), public);
            assert_eq!(sign(&seed, message), signature);
            assert!(verify(&public, message, &signature));
        }
    }

    #[test]
    fn a_changed_message_key_or_signature_fails() {
        let seed = [7u8; 32];
        let public = public_key(&seed);
        let signature = sign(&seed, b"message");
        assert!(verify(&public, b"message", &signature));
        assert!(!verify(&public, b"other", &signature));
        assert!(!verify(&public_key(&[8; 32]), b"message", &signature));
        for at in [0, 31, 32, 63] {
            let mut bad = signature;
            bad[at] ^= 1;
            assert!(!verify(&public, b"message", &bad), "byte {at}");
        }
    }

    /// `s + L` verifies under a lax check, and is the malleated twin of `s`.
    #[test]
    fn a_non_canonical_scalar_is_refused() {
        // L, the group order, little-endian.
        const L: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        let seed = [7u8; 32];
        let public = public_key(&seed);
        let mut signature = sign(&seed, b"message");
        let mut carry = 0u16;
        for i in 0..32 {
            let sum = u16::from(signature[32 + i]) + u16::from(L[i]) + carry;
            signature[32 + i] = sum as u8;
            carry = sum >> 8;
        }
        assert_eq!(carry, 0, "a canonical s has room for one L");
        assert!(!verify(&public, b"message", &signature));
    }

    /// With the identity as both key and commitment, `s = 0` satisfies the equation for every
    /// message. ring alone takes it: this is what the small-order check is for.
    #[test]
    fn a_small_order_key_signs_nothing() {
        for point in SMALL_ORDER {
            for sign_bit in [0u8, 0x80] {
                let mut key = point;
                key[31] |= sign_bit;
                let mut forged = [0u8; 64];
                forged[..32].copy_from_slice(&key);
                assert!(!verify(&key, b"anything", &forged), "{key:02x?}");
            }
        }
        let identity = SMALL_ORDER[1];
        let mut forged = [0u8; 64];
        forged[..32].copy_from_slice(&identity);
        assert!(
            UnparsedPublicKey::new(&ED25519, &identity)
                .verify(b"anything", &forged)
                .is_ok(),
            "not vacuous: ring alone takes this forgery"
        );
    }

    /// The table is the set `ed25519-dalek` calls weak, and on ordinary signatures the two agree.
    #[cfg(feature = "identity")]
    #[test]
    fn ring_and_dalek_agree() {
        use ed25519_dalek::{Signature, SigningKey, VerifyingKey};
        for point in SMALL_ORDER {
            if let Ok(key) = VerifyingKey::from_bytes(&point) {
                assert!(key.is_weak(), "{point:02x?}");
            }
        }
        for n in 0..64u8 {
            let seed = [n; 32];
            let message = [n; 7];
            let dalek = SigningKey::from_bytes(&seed);
            let public = dalek.verifying_key().to_bytes();
            assert_eq!(public_key(&seed), public);
            let signature = ed25519_dalek::Signer::sign(&dalek, &message).to_bytes();
            assert_eq!(sign(&seed, &message), signature);
            let mut bad = signature;
            bad[usize::from(n) % 64] ^= 1;
            assert_eq!(
                verify(&public, &message, &bad),
                dalek
                    .verifying_key()
                    .verify_strict(&message, &Signature::from_bytes(&bad))
                    .is_ok(),
                "{n}"
            );
        }
    }
}
