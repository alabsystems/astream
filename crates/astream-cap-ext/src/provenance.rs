// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! HMAC-authenticated physical-keyboard vs synthetic/agent input provenance (`Astream.Cap.TlaInputProvenance`,
//! `DESIGN-aterm-fabric.md` §15 "Physical-keyboard input provenance").
//!
//! Lets an `aterm` window or terminal supervisor cryptographically bind each input chunk to:
//! - its origin class ([`InputOrigin::PhysicalHuman`], [`InputOrigin::SupervisorHarness`],
//!   or [`InputOrigin::RemoteAgent`]),
//! - the target `session_id`,
//! - a strictly increasing per-origin sequence number (`provenance_seq_fresh` /
//!   [`provenance_seq_advance`]) so captured physical-keystroke tags can never be replayed,
//! - the wall-clock timestamp `stamped_ms` (bounded within `MAX_PROVENANCE_SKEW_MS` via
//!   [`provenance_skew_clamp`]), and
//! - the SHA-256 digest of the exact input payload bytes.
//!
//! Tag comparison folds all 32 bytes in constant time with no early exit.

use astream_digest::{hmac_sha256_parts, Sha256};

#[cfg(clean_islands)]
#[path = "provenance_island.rs"]
mod provenance_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn provenance_seq_advance(cur_seq: u64, next_seq: u64) -> u64 {
    if cur_seq < next_seq {
        next_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn provenance_skew_clamp(skew_ms: u64, max_skew_ms: u64) -> u64 {
    if skew_ms < max_skew_ms {
        skew_ms
    } else {
        max_skew_ms
    }
}
#[cfg(clean_islands)]
pub use provenance_island::{provenance_seq_advance, provenance_skew_clamp};

/// Domain separator for input provenance HMAC tags, disjoint from root caps, attach proofs,
/// `producer_id_of`, and Macaroon `via=` chains.
const PROVENANCE_DOMAIN: &[u8] = b"astream-input-provenance-v1\0";

/// Maximum permitted clock skew (`ms`) when verifying live input provenance stamps (`30_000 ms`).
pub const MAX_PROVENANCE_SKEW_MS: u64 = 30_000;

contract_fn! {
    /// Kernel-certified strict sequence freshness predicate (`last_seq < seq`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `provenance_seq_fresh_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn provenance_seq_fresh(last_seq: u64, seq: u64) -> bool
    clauses [ensures result == (last_seq < seq)]
    {
        last_seq < seq
    }
}

/// Origin class of a terminal input event (`DESIGN-aterm-fabric.md` §15).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputOrigin {
    /// Direct physical HID/window keyboard event from the human operator (`aterm` GUI/TTY).
    PhysicalHuman,
    /// Local `aterm` Autopilot harness continuation (`cruise` / `land`).
    SupervisorHarness,
    /// Programmatic / remote agent tool or step-in command.
    RemoteAgent,
}

impl InputOrigin {
    /// Canonical single-byte wire code for HMAC domain framing.
    #[must_use]
    pub const fn wire_code(self) -> u8 {
        match self {
            Self::PhysicalHuman => 1,
            Self::SupervisorHarness => 2,
            Self::RemoteAgent => 3,
        }
    }

    /// Decode an [`InputOrigin`] from its wire code.
    #[must_use]
    pub const fn from_wire_code(code: u8) -> Option<Self> {
        match code {
            1 => Some(Self::PhysicalHuman),
            2 => Some(Self::SupervisorHarness),
            3 => Some(Self::RemoteAgent),
            _ => None,
        }
    }
}

/// Authenticated provenance stamp attached to a terminal input payload.
#[derive(Clone, PartialEq, Eq)]
pub struct InputProvenanceStamp {
    /// Origin class (`PhysicalHuman`, `SupervisorHarness`, `RemoteAgent`).
    pub origin: InputOrigin,
    /// Strictly positive per-origin monotone sequence (`>= 1`).
    pub seq: u64,
    /// Timestamp (`unix_ms`) when the input was captured.
    pub stamped_ms: u64,
    /// SHA-256 digest of the exact input payload bytes.
    pub payload_sha256: [u8; 32],
    /// 32-byte HMAC-SHA256 provenance seal (redacted in `Debug`).
    pub tag: [u8; 32],
}

impl std::fmt::Debug for InputProvenanceStamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InputProvenanceStamp")
            .field("origin", &self.origin)
            .field("seq", &self.seq)
            .field("stamped_ms", &self.stamped_ms)
            .field("payload_sha256", &self.payload_sha256)
            .field("tag", &"<redacted>")
            .finish()
    }
}

const fn ct_diff_q0(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    (a[0] ^ b[0])
        | (a[1] ^ b[1])
        | (a[2] ^ b[2])
        | (a[3] ^ b[3])
        | (a[4] ^ b[4])
        | (a[5] ^ b[5])
        | (a[6] ^ b[6])
        | (a[7] ^ b[7])
}

const fn ct_diff_q1(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    (a[8] ^ b[8])
        | (a[9] ^ b[9])
        | (a[10] ^ b[10])
        | (a[11] ^ b[11])
        | (a[12] ^ b[12])
        | (a[13] ^ b[13])
        | (a[14] ^ b[14])
        | (a[15] ^ b[15])
}

const fn ct_diff_q2(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    (a[16] ^ b[16])
        | (a[17] ^ b[17])
        | (a[18] ^ b[18])
        | (a[19] ^ b[19])
        | (a[20] ^ b[20])
        | (a[21] ^ b[21])
        | (a[22] ^ b[22])
        | (a[23] ^ b[23])
}

const fn ct_diff_q3(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    (a[24] ^ b[24])
        | (a[25] ^ b[25])
        | (a[26] ^ b[26])
        | (a[27] ^ b[27])
        | (a[28] ^ b[28])
        | (a[29] ^ b[29])
        | (a[30] ^ b[30])
        | (a[31] ^ b[31])
}

const fn ct_diff_32(a: &[u8; 32], b: &[u8; 32]) -> u8 {
    ct_diff_q0(a, b) | ct_diff_q1(a, b) | ct_diff_q2(a, b) | ct_diff_q3(a, b)
}

fn sha256_payload(payload: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(payload);
    h.finalize()
}

fn compute_provenance_tag(
    secret: &[u8],
    session_id: &str,
    origin: InputOrigin,
    seq: u64,
    stamped_ms: u64,
    payload_sha256: &[u8; 32],
) -> [u8; 32] {
    let origin_byte = [origin.wire_code()];
    let sid_len_le = (session_id.len() as u64).to_le_bytes();
    let seq_le = seq.to_le_bytes();
    let ts_le = stamped_ms.to_le_bytes();
    hmac_sha256_parts(
        secret,
        &[
            PROVENANCE_DOMAIN,
            &origin_byte,
            &sid_len_le,
            session_id.as_bytes(),
            &seq_le,
            &ts_le,
            payload_sha256,
        ],
    )
}

/// Mint a signed [`InputProvenanceStamp`] for `payload` on `session_id`.
#[must_use]
pub fn stamp_input_provenance(
    secret: &[u8],
    session_id: &str,
    origin: InputOrigin,
    seq: u64,
    stamped_ms: u64,
    payload: &[u8],
) -> InputProvenanceStamp {
    let eff_seq = if seq == 0 { 1 } else { seq };
    let payload_sha256 = sha256_payload(payload);
    let tag = compute_provenance_tag(
        secret,
        session_id,
        origin,
        eff_seq,
        stamped_ms,
        &payload_sha256,
    );
    InputProvenanceStamp {
        origin,
        seq: eff_seq,
        stamped_ms,
        payload_sha256,
        tag,
    }
}

/// Stateful per-session verifier enforcing HMAC authenticity, payload integrity, bounded
/// clock skew, and per-origin anti-replay sequence monotonicity.
#[derive(Debug, Clone)]
pub struct InputProvenanceVerifier {
    session_id: String,
    max_skew_ms: u64,
    last_human_seq: u64,
    last_harness_seq: u64,
    last_agent_seq: u64,
}

impl InputProvenanceVerifier {
    /// Create a verifier for `session_id` clamping `max_skew_ms` to [`MAX_PROVENANCE_SKEW_MS`].
    #[must_use]
    pub fn new(session_id: &str, max_skew_ms: u64) -> Self {
        let clamped_skew = provenance_skew_clamp(max_skew_ms, MAX_PROVENANCE_SKEW_MS);
        Self {
            session_id: session_id.to_string(),
            max_skew_ms: clamped_skew,
            last_human_seq: 0,
            last_harness_seq: 0,
            last_agent_seq: 0,
        }
    }

    /// Configured maximum clock skew (`<= MAX_PROVENANCE_SKEW_MS`).
    #[must_use]
    pub const fn max_skew_ms(&self) -> u64 {
        self.max_skew_ms
    }

    /// Last accepted sequence number for `origin` (`0` if none yet).
    #[must_use]
    pub const fn last_seq_for(&self, origin: InputOrigin) -> u64 {
        match origin {
            InputOrigin::PhysicalHuman => self.last_human_seq,
            InputOrigin::SupervisorHarness => self.last_harness_seq,
            InputOrigin::RemoteAgent => self.last_agent_seq,
        }
    }

    /// Verify `stamp` against `secret`, `payload`, and `now_ms` in constant time, advancing
    /// the per-origin anti-replay watermark via [`provenance_seq_advance`] iff valid.
    pub fn verify_and_admit(
        &mut self,
        secret: &[u8],
        stamp: &InputProvenanceStamp,
        payload: &[u8],
        now_ms: u64,
    ) -> bool {
        let actual_digest = sha256_payload(payload);
        let expected_tag = compute_provenance_tag(
            secret,
            &self.session_id,
            stamp.origin,
            stamp.seq,
            stamp.stamped_ms,
            &stamp.payload_sha256,
        );
        let diff = ct_diff_32(&actual_digest, &stamp.payload_sha256)
            | ct_diff_32(&expected_tag, &stamp.tag);
        if diff != 0 {
            return false;
        }
        let skew = stamp.stamped_ms.abs_diff(now_ms);
        if skew > self.max_skew_ms {
            return false;
        }
        let prev = self.last_seq_for(stamp.origin);
        if !provenance_seq_fresh(prev, stamp.seq) {
            return false;
        }
        let next = provenance_seq_advance(prev, stamp.seq);
        match stamp.origin {
            InputOrigin::PhysicalHuman => self.last_human_seq = next,
            InputOrigin::SupervisorHarness => self.last_harness_seq = next,
            InputOrigin::RemoteAgent => self.last_agent_seq = next,
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_and_wire_codes_roundtrip() {
        assert_eq!(provenance_seq_advance(3, 7), 7);
        assert_eq!(provenance_seq_advance(7, 3), 7);
        assert_eq!(
            provenance_skew_clamp(99_999, MAX_PROVENANCE_SKEW_MS),
            MAX_PROVENANCE_SKEW_MS
        );
        assert!(provenance_seq_fresh(0, 1));
        assert!(!provenance_seq_fresh(5, 5));
        for o in [
            InputOrigin::PhysicalHuman,
            InputOrigin::SupervisorHarness,
            InputOrigin::RemoteAgent,
        ] {
            assert_eq!(InputOrigin::from_wire_code(o.wire_code()), Some(o));
        }
        assert_eq!(InputOrigin::from_wire_code(99), None);
    }

    #[test]
    fn authenticates_physical_human_input_and_rejects_forgery_replay_or_cross_session() {
        let secret = b"window-hid-provenance-key-32byte";
        let mut verifier = InputProvenanceVerifier::new("s-tab1", 5_000);

        let stamp1 = stamp_input_provenance(
            secret,
            "s-tab1",
            InputOrigin::PhysicalHuman,
            1,
            10_000,
            b"git status\r",
        );
        assert!(format!("{stamp1:?}").contains("<redacted>"));
        assert!(verifier.verify_and_admit(secret, &stamp1, b"git status\r", 10_200));
        assert_eq!(verifier.last_seq_for(InputOrigin::PhysicalHuman), 1);

        // Replay of seq=1 is refused!
        assert!(!verifier.verify_and_admit(secret, &stamp1, b"git status\r", 10_250));

        // Agent trying to relabel its SupervisorHarness stamp as PhysicalHuman fails HMAC!
        let mut forged = stamp_input_provenance(
            secret,
            "s-tab1",
            InputOrigin::SupervisorHarness,
            2,
            10_300,
            b"rm -rf /\r",
        );
        forged.origin = InputOrigin::PhysicalHuman;
        assert!(!verifier.verify_and_admit(secret, &forged, b"rm -rf /\r", 10_300));

        // Cross-session replay fails HMAC!
        let other_tab = stamp_input_provenance(
            secret,
            "s-tab2",
            InputOrigin::PhysicalHuman,
            2,
            10_300,
            b"ls\r",
        );
        assert!(!verifier.verify_and_admit(secret, &other_tab, b"ls\r", 10_300));

        // Stale skew (> 5_000ms) is refused!
        let stale = stamp_input_provenance(
            secret,
            "s-tab1",
            InputOrigin::PhysicalHuman,
            2,
            10_300,
            b"ls\r",
        );
        assert!(!verifier.verify_and_admit(secret, &stale, b"ls\r", 20_000));
    }
}
