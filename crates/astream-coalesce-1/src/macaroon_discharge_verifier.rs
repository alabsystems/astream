// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Third-party caveat & root-bound discharge Macaroon verifier (`astream-cap`).
//!
//! Enables root capability tokens to carry third-party caveats (`cid_id`, e.g. an
//! `aterm` identity / MFA / hardware-key attestation challenge) satisfied by presenting
//! a companion discharge Macaroon whose tail HMAC tag is cryptographically bound to the
//! primary capability's signature (`bind_discharge_tag`), preventing stolen discharge
//! token replay across unrelated capabilities.
//! Zero closures (`0 mandated`), `#![deny(dead_code)]`-clean, backed by Clean TLA+
//! island `Astream.Cap.TlaDischargeMacaroon`.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use astream_digest::{ct_eq, hmac_sha256_parts};

#[cfg(clean_islands)]
#[path = "macaroon_discharge_verifier_island.rs"]
mod macaroon_discharge_verifier_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn discharge_caveats_clamp(proposed_total: u64, max_caveats: u64) -> u64 {
    if proposed_total < max_caveats {
        proposed_total
    } else {
        max_caveats
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn discharge_verified_clamp(verified: u64, total: u64) -> u64 {
    if verified < total {
        verified
    } else {
        total
    }
}
#[cfg(clean_islands)]
pub use macaroon_discharge_verifier_island::{discharge_caveats_clamp, discharge_verified_clamp};

contract_fn! {
    /// Kernel-certified check that a discharge caveat expiration `exp_ms` is strictly
    /// in the future (`now_ms < exp_ms`), linked via `clean-kernel-defeq` to
    /// `discharge_not_expired_isl`.
    #[must_use]
    pub const fn discharge_not_expired(now_ms: u64, exp_ms: u64) -> bool
    clauses [ensures result == (now_ms < exp_ms)]
    {
        now_ms < exp_ms
    }
}

/// Maximum number of first-party attenuation caveats permitted on a single discharge Macaroon.
pub const MAX_DISCHARGE_CAVEATS: usize = 16;

const DISCHARGE_INIT_DOMAIN: &[u8] = b"astream-cap/discharge-init/v1";
const DISCHARGE_STEP_DOMAIN: &[u8] = b"astream-cap/discharge-step/v1";
const DISCHARGE_BIND_DOMAIN: &[u8] = b"astream-cap/discharge-bind/v1";

/// First-party caveat chained onto a third-party discharge Macaroon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DischargeCaveat<'a> {
    /// Strict expiration timestamp (`now_ms < exp_ms`).
    ExpiresAtMs(u64),
    /// Exact peer principal binding (`n-<hash>` or Ed25519 key digest).
    Principal(&'a [u8]),
    /// Exact broker or session target audience (`aud=`).
    Audience(&'a [u8]),
}

/// Presentation of a root-bound discharge Macaroon satisfying `caveat_id`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundDischargeToken<'a> {
    /// Identifier of the third-party caveat on the primary capability.
    pub caveat_id: &'a [u8],
    /// First-party caveats chained onto the discharge root key.
    pub caveats: &'a [DischargeCaveat<'a>],
    /// 32-byte tag output by [`bind_discharge_tag`] binding this discharge to `primary_sig`.
    pub bound_tag: [u8; 32],
}

/// Error returned when minting or verifying a [`BoundDischargeToken`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DischargeVerifyError {
    /// Caveat chain exceeds [`MAX_DISCHARGE_CAVEATS`].
    TooManyCaveats { count: usize },
    /// Discharge caveat expired at `now_ms >= exp_ms`.
    Expired { now_ms: u64, exp_ms: u64 },
    /// Discharge `Principal` caveat did not match `presented_principal`.
    PrincipalMismatch,
    /// Discharge `Audience` caveat did not match `presented_audience`.
    AudienceMismatch,
    /// Bound HMAC tag failed constant-time verification against `(caveat_root_key, primary_sig)`.
    InvalidBoundSignature,
}

#[inline(never)]
fn hmac_discharge_init(key: &[u8; 32], caveat_id: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(key, &[DISCHARGE_INIT_DOMAIN, caveat_id])
}

#[inline(never)]
fn hmac_discharge_step(key: &[u8; 32], tag_byte: &[u8; 1], body: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(key, &[DISCHARGE_STEP_DOMAIN, tag_byte, body])
}

fn step_discharge_caveat(chain_tag: &[u8; 32], caveat: DischargeCaveat<'_>) -> [u8; 32] {
    match caveat {
        DischargeCaveat::ExpiresAtMs(exp_ms) => {
            let bytes = exp_ms.to_le_bytes();
            hmac_discharge_step(chain_tag, &[0x01], &bytes)
        }
        DischargeCaveat::Principal(p) => hmac_discharge_step(chain_tag, &[0x02], p),
        DischargeCaveat::Audience(a) => hmac_discharge_step(chain_tag, &[0x03], a),
    }
}

/// Mint the unbound discharge Macaroon signature from `(caveat_root_key, caveat_id, caveats)`.
pub fn mint_discharge_signature(
    caveat_root_key: &[u8; 32],
    caveat_id: &[u8],
    caveats: &[DischargeCaveat<'_>],
) -> Result<[u8; 32], DischargeVerifyError> {
    if caveats.len() > MAX_DISCHARGE_CAVEATS {
        return Err(DischargeVerifyError::TooManyCaveats {
            count: caveats.len(),
        });
    }
    let total =
        discharge_caveats_clamp(caveats.len() as u64, MAX_DISCHARGE_CAVEATS as u64) as usize;
    let bounded = match caveats.get(..total) {
        Some(s) => s,
        None => caveats,
    };
    let mut sig = hmac_discharge_init(caveat_root_key, caveat_id);
    let mut cur = bounded;
    while let &[cav, ref rest @ ..] = cur {
        sig = step_discharge_caveat(&sig, cav);
        cur = rest;
    }
    Ok(sig)
}

/// Cryptographically bind an unbound `discharge_sig` to the authorizing capability's
/// `primary_sig` so the discharge cannot be detached and reused with another capability.
#[must_use]
pub const fn bind_discharge_tag(primary_sig: &[u8; 32], discharge_sig: &[u8; 32]) -> [u8; 32] {
    hmac_sha256_parts(primary_sig, &[DISCHARGE_BIND_DOMAIN, discharge_sig])
}

/// Verify a [`BoundDischargeToken`] against `caveat_root_key`, `primary_sig`, and request context,
/// returning the clamped count of verified caveats on success.
pub fn verify_bound_discharge(
    caveat_root_key: &[u8; 32],
    primary_sig: &[u8; 32],
    token: &BoundDischargeToken<'_>,
    now_ms: u64,
    presented_principal: &[u8],
    presented_audience: &[u8],
) -> Result<u64, DischargeVerifyError> {
    if token.caveats.len() > MAX_DISCHARGE_CAVEATS {
        return Err(DischargeVerifyError::TooManyCaveats {
            count: token.caveats.len(),
        });
    }
    let total = discharge_caveats_clamp(token.caveats.len() as u64, MAX_DISCHARGE_CAVEATS as u64);
    let limit = total as usize;
    let bounded = match token.caveats.get(..limit) {
        Some(s) => s,
        None => token.caveats,
    };
    let mut sig = hmac_discharge_init(caveat_root_key, token.caveat_id);
    let mut verified = 0u64;
    let mut cur = bounded;
    while let &[cav, ref rest @ ..] = cur {
        match cav {
            DischargeCaveat::ExpiresAtMs(exp_ms) => {
                if !discharge_not_expired(now_ms, exp_ms) {
                    return Err(DischargeVerifyError::Expired { now_ms, exp_ms });
                }
            }
            DischargeCaveat::Principal(want_p) => {
                if !ct_eq(want_p, presented_principal) {
                    return Err(DischargeVerifyError::PrincipalMismatch);
                }
            }
            DischargeCaveat::Audience(want_a) => {
                if !ct_eq(want_a, presented_audience) {
                    return Err(DischargeVerifyError::AudienceMismatch);
                }
            }
        }
        sig = step_discharge_caveat(&sig, cav);
        verified = verified.saturating_add(1);
        cur = rest;
    }

    let expected_bound = bind_discharge_tag(primary_sig, &sig);
    if !ct_eq(&expected_bound, &token.bound_tag) {
        return Err(DischargeVerifyError::InvalidBoundSignature);
    }
    Ok(discharge_verified_clamp(verified, total))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_discharge_verifies_caveats_and_prevents_cross_capability_replay() {
        let caveat_key = [0x42u8; 32];
        let primary_sig_a = [0xAAu8; 32];
        let primary_sig_b = [0xBBu8; 32];
        let caveats = [
            DischargeCaveat::ExpiresAtMs(5_000),
            DischargeCaveat::Principal(b"n-alice"),
            DischargeCaveat::Audience(b"broker://us-west"),
        ];
        let d_sig = mint_discharge_signature(&caveat_key, b"mfa-1", &caveats).unwrap();
        let tok = BoundDischargeToken {
            caveat_id: b"mfa-1",
            caveats: &caveats,
            bound_tag: bind_discharge_tag(&primary_sig_a, &d_sig),
        };

        assert_eq!(
            verify_bound_discharge(
                &caveat_key,
                &primary_sig_a,
                &tok,
                4_999,
                b"n-alice",
                b"broker://us-west"
            ),
            Ok(3)
        );
        // Replay alongside `primary_sig_b` MUST fail!
        assert_eq!(
            verify_bound_discharge(
                &caveat_key,
                &primary_sig_b,
                &tok,
                4_999,
                b"n-alice",
                b"broker://us-west"
            ),
            Err(DischargeVerifyError::InvalidBoundSignature)
        );
        // Expired at `now_ms == 5_000` MUST fail!
        assert_eq!(
            verify_bound_discharge(
                &caveat_key,
                &primary_sig_a,
                &tok,
                5_000,
                b"n-alice",
                b"broker://us-west"
            ),
            Err(DischargeVerifyError::Expired {
                now_ms: 5_000,
                exp_ms: 5_000,
            })
        );
    }
}
