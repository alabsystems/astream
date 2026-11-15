// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The space between the published vectors (FIPS 180-4's beside the hash in
//! `src/lib.rs`, RFC 4231's beside the HMAC in `src/hmac.rs`): every message
//! length from 0 to 200, large inputs, every key length across the block
//! boundary, and arbitrary streaming splits.
//!
//! Moved here from aterm's `aterm-digest` with the HMAC it tests. The length
//! sweeps are pinned by one SHA-256 over all their outputs, recorded when every
//! output matched the `sha2`/`hmac` crates byte for byte. They were recorded
//! against aterm-digest's own SHA-256 and HMAC, before either moved here; the
//! same pins hold this crate's hash, and the HMAC astream-cap's core became, to
//! the answers those copies gave.

use astream_digest::{HmacSha256, Sha256};

/// A deterministic 64-bit LCG (Knuth's MMIX constants).
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| (self.next_u64() & 0xff) as u8).collect()
    }

    /// A value in `1..=max`, for chunk sizes.
    fn chunk_len(&mut self, max: usize) -> usize {
        (self.next_u64() as usize % max.max(1)) + 1
    }
}

fn hmac(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut m = HmacSha256::new_from_slice(key).expect("any key length");
    m.update(msg);
    m.finalize()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn sha256_over_every_length_and_large_inputs_is_pinned() {
    let mut all = Sha256::new();
    let mut rng = Lcg(0x005e_a11e_d0dd_beef);
    for len in 0..=200usize {
        all.update(Sha256::digest(rng.bytes(len)));
    }
    let mut rng = Lcg(0x00c0_ffee_cafe_f00d);
    for len in [
        255usize, 256, 511, 512, 1_000, 4_096, 8_192, 65_535, 65_536, 100_000,
    ] {
        all.update(Sha256::digest(rng.bytes(len)));
    }
    assert_eq!(hex(&all.finalize()), SHA256_SWEEP);
}

#[test]
fn hmac_over_every_message_and_key_length_is_pinned() {
    let mut all = Sha256::new();
    let mut rng = Lcg(0xa5a5_5a5a_a5a5_5a5a);
    let key = rng.bytes(32);
    for len in 0..=200usize {
        all.update(hmac(&key, &rng.bytes(len)));
    }
    // 0..=200 spans the 64-byte block boundary in both directions: keys at 64
    // are used verbatim, keys at 65 and above are hashed down first.
    let mut rng = Lcg(0x1357_9bdf_2468_ace0);
    let msg = rng.bytes(97);
    for len in 0..=200usize {
        all.update(hmac(&rng.bytes(len), &msg));
    }
    let mut rng = Lcg(0x2b2b_2b2b_7f7f_7f7f);
    for (klen, mlen) in [
        (0usize, 0usize),
        (1, 1),
        (63, 63),
        (64, 64),
        (65, 65),
        (128, 4_096),
        (1_000, 1),
        (4_096, 65_536),
    ] {
        let key = rng.bytes(klen);
        all.update(hmac(&key, &rng.bytes(mlen)));
    }
    assert_eq!(hex(&all.finalize()), HMAC_SWEEP);
}

const SHA256_SWEEP: &str = "9d4bc2aafe3aee89a1151bc4f5d74283aa15c992ed8a95b2f00219e9d84c2d68";
const HMAC_SWEEP: &str = "8988db5b4e91928c28ee9988644a55aec9ad30b0b1c6a5602d109ebbc5a2eb56";

/// Random splits of the same message reach the one-shot digest: what catches a
/// broken partial-block buffer, which one-shot vectors never would.
#[test]
fn sha256_fed_in_arbitrary_chunks_matches_one_shot() {
    let mut rng = Lcg(0x0123_4567_89ab_cdef);
    for len in 0..=200usize {
        let msg = rng.bytes(len);
        let expected = Sha256::digest(&msg);
        for split in 0..10 {
            let mut ours = Sha256::new();
            let mut rest: &[u8] = &msg;
            while !rest.is_empty() {
                let take = rng.chunk_len(rest.len().min(70));
                ours.update(&rest[..take]);
                rest = &rest[take..];
            }
            assert_eq!(ours.finalize(), expected, "length {len}, split {split}");
        }
    }
    let msg = rng.bytes(200_000);
    let mut h = Sha256::new();
    let mut rest: &[u8] = &msg;
    while !rest.is_empty() {
        let take = rng.chunk_len(rest.len().min(4_097));
        h.update(&rest[..take]);
        rest = &rest[take..];
    }
    assert_eq!(h.finalize(), Sha256::digest(&msg));
}

/// Random splits of the same message reach the one-shot tag through all three
/// doors: the streaming `HmacSha256`, `hmac_sha256_parts` and
/// `hmac_sha256_wiping` over the same chunks. Negative control: the message
/// with its last byte flipped is another tag, so agreement is not vacuous.
#[test]
fn hmac_fed_in_arbitrary_chunks_matches_one_shot() {
    let mut rng = Lcg(0x9e37_79b9_7f4a_7c15);
    for len in 0..=200usize {
        let key = rng.bytes(len % 97);
        let msg = rng.bytes(len);
        let expected = hmac(&key, &msg);
        for split in 0..5 {
            let mut ours = HmacSha256::new_from_slice(&key).expect("any key length");
            let mut chunks: Vec<&[u8]> = Vec::new();
            let mut rest: &[u8] = &msg;
            while !rest.is_empty() {
                let take = rng.chunk_len(rest.len().min(33));
                ours.update(&rest[..take]);
                chunks.push(&rest[..take]);
                rest = &rest[take..];
            }
            assert_eq!(ours.finalize(), expected, "length {len}, split {split}");
            assert_eq!(
                astream_digest::hmac_sha256_parts(&key, &chunks),
                expected,
                "parts: length {len}, split {split}"
            );
            assert_eq!(
                astream_digest::hmac_sha256_wiping(&key, &chunks),
                expected,
                "wiping: length {len}, split {split}"
            );
        }
        if let Some(last) = msg.last() {
            let mut other = msg.clone();
            *other.last_mut().expect("non-empty") = last ^ 1;
            assert_ne!(hmac(&key, &other), expected, "length {len}");
        }
    }
}

#[test]
fn hmac_verify_slice_accepts_the_tag_and_refuses_a_flipped_bit() {
    let mut rng = Lcg(0x4242_4242_dead_c0de);
    for len in 0..=200usize {
        let key = rng.bytes(len % 71);
        let msg = rng.bytes(len);
        let tag = hmac(&key, &msg);

        let mut ok = HmacSha256::new_from_slice(&key).expect("any key length");
        ok.update(&msg);
        assert!(ok.verify_slice(&tag).is_ok(), "length {len}");

        let mut bad = tag;
        let idx = (rng.next_u64() as usize) % bad.len();
        bad[idx] ^= 1 << (rng.next_u64() % 8);
        let mut nope = HmacSha256::new_from_slice(&key).expect("any key length");
        nope.update(&msg);
        assert!(nope.verify_slice(&bad).is_err(), "length {len}");
    }
}
