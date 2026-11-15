// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Forward-secret symmetric rekey ratchet over HChaCha20 + XChaCha20-Poly1305.
//!
//! Long-lived `aterm` remote/WAN `SealedStream` sessions run for days across thousands of
//! terminal turns. Without symmetric key ratcheting, a late memory disclosure of a static
//! session key compromises every earlier ciphertext captured on the wire.
//!
//! [`SymmetricRatchet`] implements a directional one-way KDF chain over HChaCha20 (`hchacha20`)
//! (draft-irtf-cfrg-xchacha-03 §2.2), available in `astream-aead`'s base configuration
//! (the exact dependency footprint `aterm` ships):
//! - At epoch `e`, the traffic key is `T_e = HChaCha20(K_e, "ASRK-MSG" || LE64(e))` and the
//!   successor chain key is `K_{e+1} = HChaCha20(K_e, "ASRK-CHN" || LE64(e))`.
//! - Advancing to epoch `e + 1` immediately wipes `K_e` and `T_e` in place via `core::hint::black_box`,
//!   so compromised state at epoch `e' > e` cannot invert HChaCha20 to recover `T_e`.
//! - Every sealed frame binds `user_aad || "ASRK1" || direction || LE64(epoch) || LE64(seq)`
//!   in its Poly1305 AAD, preventing cross-epoch, cross-direction, and out-of-order replay.
//! - Automatic rekeying triggers every `rekey_interval` frames (`>= 1`), or on explicit
//!   [`SymmetricRatchet::force_rekey`].
//!
//! Backed by Clean TLA+ island `Astream.Aead.TlaRekeyRatchet` (`ratchet_island.rs`).

use astream_aead::{open, seal, seal_with_nonce, AeadError, KEY_LEN, NONCE_LEN};

const HCHACHA_INPUT_LEN: usize = 16;
const HCHACHA_SIGMA: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];

#[inline(always)]
fn scrub_key(buf: &mut [u8; KEY_LEN]) {
    *buf = [0u8; KEY_LEN];
    let _ = core::hint::black_box(buf);
}

#[inline(always)]
fn scrub_input(buf: &mut [u8; HCHACHA_INPUT_LEN]) {
    *buf = [0u8; HCHACHA_INPUT_LEN];
    let _ = core::hint::black_box(buf);
}

#[inline(always)]
fn scrub_state16(buf: &mut [u32; 16]) {
    *buf = [0u32; 16];
    let _ = core::hint::black_box(buf);
}

#[inline(always)]
fn scrub_words8(buf: &mut [u32; 8]) {
    *buf = [0u32; 8];
    let _ = core::hint::black_box(buf);
}

#[inline(always)]
const fn hchacha_quarter_round(a: u32, b: u32, c: u32, d: u32) -> (u32, u32, u32, u32) {
    let a = a.wrapping_add(b);
    let d = (d ^ a).rotate_left(16);
    let c = c.wrapping_add(d);
    let b = (b ^ c).rotate_left(12);
    let a = a.wrapping_add(b);
    let d = (d ^ a).rotate_left(8);
    let c = c.wrapping_add(d);
    let b = (b ^ c).rotate_left(7);
    (a, b, c, d)
}

#[inline(always)]
const fn hchacha_load_u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

const fn hchacha_column_round_lo(s: &mut [u32; 16]) {
    (s[0], s[4], s[8], s[12]) = hchacha_quarter_round(s[0], s[4], s[8], s[12]);
    (s[1], s[5], s[9], s[13]) = hchacha_quarter_round(s[1], s[5], s[9], s[13]);
}

const fn hchacha_column_round_hi(s: &mut [u32; 16]) {
    (s[2], s[6], s[10], s[14]) = hchacha_quarter_round(s[2], s[6], s[10], s[14]);
    (s[3], s[7], s[11], s[15]) = hchacha_quarter_round(s[3], s[7], s[11], s[15]);
}

const fn hchacha_diag_round_lo(s: &mut [u32; 16]) {
    (s[0], s[5], s[10], s[15]) = hchacha_quarter_round(s[0], s[5], s[10], s[15]);
    (s[1], s[6], s[11], s[12]) = hchacha_quarter_round(s[1], s[6], s[11], s[12]);
}

const fn hchacha_diag_round_hi(s: &mut [u32; 16]) {
    (s[2], s[7], s[8], s[13]) = hchacha_quarter_round(s[2], s[7], s[8], s[13]);
    (s[3], s[4], s[9], s[14]) = hchacha_quarter_round(s[3], s[4], s[9], s[14]);
}

const fn hchacha_double_round(s: &mut [u32; 16]) {
    hchacha_column_round_lo(s);
    hchacha_column_round_hi(s);
    hchacha_diag_round_lo(s);
    hchacha_diag_round_hi(s);
}

const fn hchacha_load_key_lo(key: &[u8; KEY_LEN]) -> [u32; 4] {
    [
        hchacha_load_u32_le(key[0], key[1], key[2], key[3]),
        hchacha_load_u32_le(key[4], key[5], key[6], key[7]),
        hchacha_load_u32_le(key[8], key[9], key[10], key[11]),
        hchacha_load_u32_le(key[12], key[13], key[14], key[15]),
    ]
}

const fn hchacha_load_key_hi(key: &[u8; KEY_LEN]) -> [u32; 4] {
    [
        hchacha_load_u32_le(key[16], key[17], key[18], key[19]),
        hchacha_load_u32_le(key[20], key[21], key[22], key[23]),
        hchacha_load_u32_le(key[24], key[25], key[26], key[27]),
        hchacha_load_u32_le(key[28], key[29], key[30], key[31]),
    ]
}

const fn hchacha_load_input(input: &[u8; HCHACHA_INPUT_LEN]) -> [u32; 4] {
    [
        hchacha_load_u32_le(input[0], input[1], input[2], input[3]),
        hchacha_load_u32_le(input[4], input[5], input[6], input[7]),
        hchacha_load_u32_le(input[8], input[9], input[10], input[11]),
        hchacha_load_u32_le(input[12], input[13], input[14], input[15]),
    ]
}

const fn hchacha_init_state(key: &[u8; KEY_LEN], input: &[u8; HCHACHA_INPUT_LEN]) -> [u32; 16] {
    let [c0, c1, c2, c3] = HCHACHA_SIGMA;
    let [k0, k1, k2, k3] = hchacha_load_key_lo(key);
    let [k4, k5, k6, k7] = hchacha_load_key_hi(key);
    let [n0, n1, n2, n3] = hchacha_load_input(input);
    [
        c0, c1, c2, c3, k0, k1, k2, k3, k4, k5, k6, k7, n0, n1, n2, n3,
    ]
}

const fn hchacha_words_to_bytes_lo(w0: u32, w1: u32, w2: u32, w3: u32) -> [u8; 16] {
    let b0 = w0.to_le_bytes();
    let b1 = w1.to_le_bytes();
    let b2 = w2.to_le_bytes();
    let b3 = w3.to_le_bytes();
    [
        b0[0], b0[1], b0[2], b0[3], b1[0], b1[1], b1[2], b1[3], b2[0], b2[1], b2[2], b2[3], b3[0],
        b3[1], b3[2], b3[3],
    ]
}

const fn hchacha_words_to_bytes_hi(w4: u32, w5: u32, w6: u32, w7: u32) -> [u8; 16] {
    let b4 = w4.to_le_bytes();
    let b5 = w5.to_le_bytes();
    let b6 = w6.to_le_bytes();
    let b7 = w7.to_le_bytes();
    [
        b4[0], b4[1], b4[2], b4[3], b5[0], b5[1], b5[2], b5[3], b6[0], b6[1], b6[2], b6[3], b7[0],
        b7[1], b7[2], b7[3],
    ]
}

const fn hchacha_extract_output(s: &[u32; 16]) -> ([u32; 8], [u8; KEY_LEN]) {
    let words = [s[0], s[1], s[2], s[3], s[12], s[13], s[14], s[15]];
    let [w0, w1, w2, w3, w4, w5, w6, w7] = words;
    let [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15] =
        hchacha_words_to_bytes_lo(w0, w1, w2, w3);
    let [r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31] =
        hchacha_words_to_bytes_hi(w4, w5, w6, w7);
    let raw = [
        r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19,
        r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
    ];
    (words, raw)
}

fn hchacha20(key: &[u8; KEY_LEN], input: &[u8; HCHACHA_INPUT_LEN]) -> [u8; KEY_LEN] {
    let mut s = hchacha_init_state(key, input);
    let mut round = 0usize;
    while round < 10 {
        hchacha_double_round(&mut s);
        round = round.saturating_add(1);
    }
    let (mut words, raw) = hchacha_extract_output(&s);
    scrub_state16(&mut s);
    scrub_words8(&mut words);
    raw
}

#[cfg(clean_islands)]
#[path = "ratchet_island.rs"]
mod ratchet_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ratchet_epoch_advance(prev_epoch: u64, cand_epoch: u64) -> u64 {
    if prev_epoch < cand_epoch {
        cand_epoch
    } else {
        prev_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ratchet_frame_seq_clamp(seq_in_epoch: u64, interval: u64) -> u64 {
    if seq_in_epoch < interval {
        seq_in_epoch
    } else {
        interval
    }
}
#[cfg(clean_islands)]
pub use ratchet_island::{ratchet_epoch_advance, ratchet_frame_seq_clamp};

/// Default automatic rekey cadence (frames sealed/opened per epoch before ratcheting).
pub const DEFAULT_REKEY_INTERVAL: u64 = 1024;

/// Maximum configurable rekey interval (`1 << 20` frames per epoch).
pub const MAX_REKEY_INTERVAL: u64 = 1_048_576;

/// Direction byte for client-to-server ratcheted traffic.
pub const RATCHET_DIR_CLIENT_TO_SERVER: u8 = 0x01;

/// Direction byte for server-to-client ratcheted traffic.
pub const RATCHET_DIR_SERVER_TO_CLIENT: u8 = 0x02;

const DOMAIN_CHAIN: [u8; 8] = *b"ASRK-CHN";
const DOMAIN_TRAFFIC: [u8; 8] = *b"ASRK-MSG";
const AAD_TRAILER_MAGIC: [u8; 5] = *b"ASRK1";
const MAX_COMBINED_AAD: usize = 16_384;

contract_fn! {
    /// Verified check whether the current epoch has reached its frame budget
    /// (`rekey_interval <= frames_in_epoch`), linked via `clean-kernel-defeq`
    /// to `ratchet_rekey_due_isl`.
    #[must_use]
    pub const fn ratchet_rekey_due(frames_in_epoch: u64, rekey_interval: u64) -> bool
    clauses [ensures result == (rekey_interval <= frames_in_epoch)]
    {
        rekey_interval <= frames_in_epoch
    }
}

fn domain_input(prefix: &[u8; 8], epoch: u64) -> [u8; HCHACHA_INPUT_LEN] {
    let eb = epoch.to_le_bytes();
    [
        prefix[0], prefix[1], prefix[2], prefix[3], prefix[4], prefix[5], prefix[6], prefix[7],
        eb[0], eb[1], eb[2], eb[3], eb[4], eb[5], eb[6], eb[7],
    ]
}

fn derive_epoch_keys(chain_key: &[u8; KEY_LEN], epoch: u64) -> ([u8; KEY_LEN], [u8; KEY_LEN]) {
    let mut msg_in = domain_input(&DOMAIN_TRAFFIC, epoch);
    let mut chn_in = domain_input(&DOMAIN_CHAIN, epoch);
    let traffic = hchacha20(chain_key, &msg_in);
    let next_chain = hchacha20(chain_key, &chn_in);
    scrub_input(&mut msg_in);
    scrub_input(&mut chn_in);
    (traffic, next_chain)
}

fn build_ratchet_aad(user_aad: &[u8], direction: u8, epoch: u64, seq_in_epoch: u64) -> Vec<u8> {
    let capped_user_len = if user_aad.len() < MAX_COMBINED_AAD {
        user_aad.len()
    } else {
        MAX_COMBINED_AAD
    };
    let raw_cap = capped_user_len.saturating_add(22);
    let cap = if raw_cap < MAX_COMBINED_AAD + 32 {
        raw_cap
    } else {
        MAX_COMBINED_AAD + 32
    };
    let mut out = {
        let _ = cap;
        Vec::new()
    };
    if let Some(prefix) = user_aad.get(..capped_user_len) {
        out.extend_from_slice(prefix);
    }
    if let Some(tail) = user_aad.get(MAX_COMBINED_AAD..) {
        if !tail.is_empty() {
            let tail_digest = astream_digest::Sha256::digest_slice(tail);
            out.extend_from_slice(&tail_digest);
        }
    }
    out.extend_from_slice(&AAD_TRAILER_MAGIC);
    out.push(direction);
    out.extend_from_slice(&epoch.to_le_bytes());
    out.extend_from_slice(&seq_in_epoch.to_le_bytes());
    out
}

/// Metadata header describing the ratchet coordinates of a sealed frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RatchetCoord {
    pub epoch: u64,
    pub seq_in_epoch: u64,
}

/// Forward-secret one-way symmetric key ratchet for one traffic direction.
///
/// Wipes `chain_key` and `traffic_key` on every epoch step and on `Drop`.
pub struct SymmetricRatchet {
    chain_key: [u8; KEY_LEN],
    traffic_key: [u8; KEY_LEN],
    direction: u8,
    epoch: u64,
    frames_in_epoch: u64,
    rekey_interval: u64,
}

impl Drop for SymmetricRatchet {
    fn drop(&mut self) {
        scrub_key(&mut self.chain_key);
        scrub_key(&mut self.traffic_key);
        core::hint::black_box(&self.chain_key);
        core::hint::black_box(&self.traffic_key);
    }
}

impl core::fmt::Debug for SymmetricRatchet {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SymmetricRatchet")
            .field("direction", &self.direction)
            .field("epoch", &self.epoch)
            .field("frames_in_epoch", &self.frames_in_epoch)
            .field("rekey_interval", &self.rekey_interval)
            .finish_non_exhaustive()
    }
}

impl SymmetricRatchet {
    /// Initialize a directional ratchet at epoch `0` from `root_key`.
    ///
    /// `rekey_interval` is clamped into `1..=MAX_REKEY_INTERVAL`.
    #[must_use]
    pub fn new(root_key: &[u8; KEY_LEN], direction: u8, rekey_interval: u64) -> Self {
        let clamped_interval = rekey_interval.clamp(1, MAX_REKEY_INTERVAL);
        let (traffic_key, next_chain) = derive_epoch_keys(root_key, 0);
        Self {
            chain_key: next_chain,
            traffic_key,
            direction,
            epoch: 0,
            frames_in_epoch: 0,
            rekey_interval: clamped_interval,
        }
    }

    /// Current ratchet epoch (`>= 0`).
    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Number of frames processed in the current epoch (`<= rekey_interval`).
    #[must_use]
    pub const fn frames_in_epoch(&self) -> u64 {
        self.frames_in_epoch
    }

    /// Configured automatic rekey interval (`1..=MAX_REKEY_INTERVAL`).
    #[must_use]
    pub const fn rekey_interval(&self) -> u64 {
        self.rekey_interval
    }

    /// Direction tag bound into every frame's AAD.
    #[must_use]
    pub const fn direction(&self) -> u8 {
        self.direction
    }

    /// Explicitly advance to `epoch + 1`, wiping the current epoch's traffic and chain keys.
    pub fn force_rekey(&mut self) -> u64 {
        let Some(cand_epoch) = self.epoch.checked_add(1) else {
            return self.epoch;
        };
        let next_epoch = ratchet_epoch_advance(self.epoch, cand_epoch);
        let (next_traffic, next_chain) = derive_epoch_keys(&self.chain_key, next_epoch);
        scrub_key(&mut self.traffic_key);
        scrub_key(&mut self.chain_key);
        self.traffic_key = next_traffic;
        self.chain_key = next_chain;
        self.epoch = next_epoch;
        self.frames_in_epoch = 0;
        self.epoch
    }

    fn rotate_if_due(&mut self) {
        if ratchet_rekey_due(self.frames_in_epoch, self.rekey_interval) {
            let _ = self.force_rekey();
        }
    }

    /// Seal `plaintext` under the current (or newly rotated) epoch traffic key with a fresh
    /// CSPRNG XChaCha20 nonce, returning `(RatchetCoord, sealed_bytes)`.
    #[must_use]
    pub fn seal_frame(&mut self, user_aad: &[u8], plaintext: &[u8]) -> (RatchetCoord, Vec<u8>) {
        self.rotate_if_due();
        let seq = ratchet_frame_seq_clamp(self.frames_in_epoch, self.rekey_interval);
        let coord = RatchetCoord {
            epoch: self.epoch,
            seq_in_epoch: seq,
        };
        let aad = build_ratchet_aad(user_aad, self.direction, coord.epoch, coord.seq_in_epoch);
        let sealed = seal(&self.traffic_key, &aad, plaintext);
        self.frames_in_epoch = ratchet_frame_seq_clamp(seq.saturating_add(1), self.rekey_interval);
        (coord, sealed)
    }

    /// Deterministic variant of [`SymmetricRatchet::seal_frame`] with an explicit 24-byte nonce.
    #[must_use]
    pub fn seal_frame_with_nonce(
        &mut self,
        nonce: &[u8; NONCE_LEN],
        user_aad: &[u8],
        plaintext: &[u8],
    ) -> (RatchetCoord, Vec<u8>) {
        self.rotate_if_due();
        let seq = ratchet_frame_seq_clamp(self.frames_in_epoch, self.rekey_interval);
        let coord = RatchetCoord {
            epoch: self.epoch,
            seq_in_epoch: seq,
        };
        let aad = build_ratchet_aad(user_aad, self.direction, coord.epoch, coord.seq_in_epoch);
        let sealed = seal_with_nonce(&self.traffic_key, nonce, &aad, plaintext);
        self.frames_in_epoch = ratchet_frame_seq_clamp(seq.saturating_add(1), self.rekey_interval);
        (coord, sealed)
    }

    /// Open a frame in-order at `coord`.
    ///
    /// Supports both automatic interval transitions and explicit sender `force_rekey()` steps
    /// of at most `max_epoch_jump` epochs (`0` if sender stayed in current epoch; `>= 1` if
    /// sender forced an early rekey). Never mutates ratchet state if authentication fails!
    pub fn open_frame(
        &mut self,
        coord: RatchetCoord,
        user_aad: &[u8],
        sealed: &[u8],
        max_epoch_jump: u64,
    ) -> Result<Vec<u8>, AeadError> {
        // Compute candidate state without mutating `self` until Poly1305 authentication succeeds!
        let mut cand_chain = self.chain_key;
        let mut cand_traffic = self.traffic_key;
        let mut cand_epoch = self.epoch;
        let mut cand_frames = self.frames_in_epoch;

        if ratchet_rekey_due(cand_frames, self.rekey_interval) {
            let Some(next_ep) = cand_epoch.checked_add(1) else {
                scrub_key(&mut cand_chain);
                scrub_key(&mut cand_traffic);
                return Err(AeadError);
            };
            let advanced = ratchet_epoch_advance(cand_epoch, next_ep);
            let (nt, nc) = derive_epoch_keys(&cand_chain, advanced);
            scrub_key(&mut cand_traffic);
            scrub_key(&mut cand_chain);
            cand_traffic = nt;
            cand_chain = nc;
            cand_epoch = advanced;
            cand_frames = 0;
        }

        if coord.epoch < cand_epoch {
            scrub_key(&mut cand_chain);
            scrub_key(&mut cand_traffic);
            return Err(AeadError);
        }

        let jump = coord.epoch.saturating_sub(cand_epoch);
        let capped_jump = if jump < 256 { jump } else { 256 };
        if jump > max_epoch_jump || jump > 256 {
            scrub_key(&mut cand_chain);
            scrub_key(&mut cand_traffic);
            return Err(AeadError);
        }

        let mut step = 0u64;
        while step < capped_jump {
            let Some(next_ep) = cand_epoch.checked_add(1) else {
                scrub_key(&mut cand_chain);
                scrub_key(&mut cand_traffic);
                return Err(AeadError);
            };
            let advanced = ratchet_epoch_advance(cand_epoch, next_ep);
            let (nt, nc) = derive_epoch_keys(&cand_chain, advanced);
            scrub_key(&mut cand_traffic);
            scrub_key(&mut cand_chain);
            cand_traffic = nt;
            cand_chain = nc;
            cand_epoch = advanced;
            cand_frames = 0;
            step = step.saturating_add(1);
        }

        let expected_seq = ratchet_frame_seq_clamp(cand_frames, self.rekey_interval);
        if coord.seq_in_epoch != expected_seq {
            scrub_key(&mut cand_chain);
            scrub_key(&mut cand_traffic);
            return Err(AeadError);
        }

        let aad = build_ratchet_aad(user_aad, self.direction, cand_epoch, expected_seq);
        let plain_res = open(&cand_traffic, &aad, sealed);
        match plain_res {
            Ok(plain) => {
                scrub_key(&mut self.traffic_key);
                scrub_key(&mut self.chain_key);
                self.traffic_key = cand_traffic;
                self.chain_key = cand_chain;
                self.epoch = cand_epoch;
                self.frames_in_epoch =
                    ratchet_frame_seq_clamp(expected_seq.saturating_add(1), self.rekey_interval);
                Ok(plain)
            }
            Err(err) => {
                scrub_key(&mut cand_chain);
                scrub_key(&mut cand_traffic);
                Err(err)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ROOT: [u8; KEY_LEN] = [0x42u8; KEY_LEN];

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(ratchet_epoch_advance(4, 5), 5);
        assert_eq!(ratchet_epoch_advance(5, 3), 5);
        assert_eq!(ratchet_frame_seq_clamp(7, 16), 7);
        assert_eq!(ratchet_frame_seq_clamp(20, 16), 16);
        assert!(!ratchet_rekey_due(3, 4));
        assert!(ratchet_rekey_due(4, 4));
    }

    #[test]
    fn automatic_rekey_rotates_epoch_and_rejects_old_epoch_replay() {
        let mut tx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_CLIENT_TO_SERVER, 3);
        let mut rx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_CLIENT_TO_SERVER, 3);

        let mut captured_epoch0 = None;
        for i in 0..7u8 {
            let msg = [b'm', i];
            let (coord, ct) = tx.seal_frame(b"/a/term/s1", &msg);
            if i == 0 {
                captured_epoch0 = Some((coord, ct.clone()));
            }
            let opened = rx.open_frame(coord, b"/a/term/s1", &ct, 4).unwrap();
            assert_eq!(opened, msg);
        }
        assert_eq!(tx.epoch(), 2);
        assert_eq!(rx.epoch(), 2);
        assert_eq!(tx.frames_in_epoch(), 1);

        // Replaying epoch 0 ciphertext after ratcheting to epoch 2 MUST fail closed!
        let (old_coord, old_ct) = captured_epoch0.unwrap();
        assert_eq!(
            rx.open_frame(old_coord, b"/a/term/s1", &old_ct, 4),
            Err(AeadError)
        );
    }

    #[test]
    fn failed_open_never_mutates_receiver_ratchet_state() {
        let mut tx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_SERVER_TO_CLIENT, 4);
        let mut rx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_SERVER_TO_CLIENT, 4);

        let _ = tx.force_rekey();
        let (coord, ct) = tx.seal_frame(b"aad", b"genuine");
        let mut forged = ct.clone();
        forged[NONCE_LEN] ^= 0xff;

        // Forged frame with epoch jump = 1 fails and leaves rx at epoch 0!
        assert_eq!(rx.open_frame(coord, b"aad", &forged, 4), Err(AeadError));
        assert_eq!(rx.epoch(), 0);
        assert_eq!(rx.frames_in_epoch(), 0);

        // Genuine frame still opens cleanly!
        let opened = rx.open_frame(coord, b"aad", &ct, 4).unwrap();
        assert_eq!(opened, b"genuine");
        assert_eq!(rx.epoch(), 1);
        assert_eq!(rx.frames_in_epoch(), 1);
    }

    #[test]
    fn reflection_across_directions_is_rejected() {
        let mut c2s = SymmetricRatchet::new(&ROOT, RATCHET_DIR_CLIENT_TO_SERVER, 8);
        let mut s2c = SymmetricRatchet::new(&ROOT, RATCHET_DIR_SERVER_TO_CLIENT, 8);
        let (coord, ct) = c2s.seal_frame(b"conn-1", b"ping");
        assert_eq!(s2c.open_frame(coord, b"conn-1", &ct, 0), Err(AeadError));
    }

    #[test]
    fn overlong_user_aad_binds_distinct_tails() {
        let mut tx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_CLIENT_TO_SERVER, 8);
        let mut rx = SymmetricRatchet::new(&ROOT, RATCHET_DIR_CLIENT_TO_SERVER, 8);
        let mut aad_a = vec![b'x'; MAX_COMBINED_AAD];
        aad_a.extend_from_slice(b"-tail-alpha");
        let mut aad_b = vec![b'x'; MAX_COMBINED_AAD];
        aad_b.extend_from_slice(b"-tail-bravo");

        let (coord, ct) = tx.seal_frame(&aad_a, b"secret");
        assert_eq!(rx.open_frame(coord, &aad_b, &ct, 0), Err(AeadError));
        assert_eq!(rx.open_frame(coord, &aad_a, &ct, 0).unwrap(), b"secret");
    }
}
