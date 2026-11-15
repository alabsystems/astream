// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ed25519 SIGMA peer-identity -> `n-<hex32>` principal binder & channel-bound attach proof
//! (`docs/REQUIREMENTS-fabric-operations-2026-09-14.md` R6).
//!
//! Cryptographically binds a transport's authenticated 32-byte Ed25519 peer public key to:
//! 1. Its canonical 34-byte principal identifier `n-<32 lowercase hex chars>` (first 16 bytes
//!    of `SHA-256("astream-identity/principal/v1" || peer_ed25519_pk)`), checked via
//!    kernel-certified [`sigma_principal_len_valid`].
//! 2. A channel-bound attach proof `HMAC-SHA256(hkdf_key, transcript_hash || cap_tag || principal)`
//!    so a bearer capability minted for `n-<hash>` cannot be replayed over a MITM or
//!    different peer's encrypted session!
//!
//! Zero closures (`0 mandated`), backed by Clean TLA+ island `Astream.Aead.TlaSigmaPrincipalBind`.

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

use astream_digest::{ct_eq, hkdf_expand_32, hkdf_extract, hmac_sha256_parts, Sha256};

#[cfg(clean_islands)]
#[path = "sigma_identity_binder_island.rs"]
mod sigma_identity_binder_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn sigma_peers_clamp(checked: u64, max_peers: u64) -> u64 {
    if checked < max_peers {
        checked
    } else {
        max_peers
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sigma_bound_clamp(bound: u64, checked: u64) -> u64 {
    if bound < checked {
        bound
    } else {
        checked
    }
}
#[cfg(clean_islands)]
pub use sigma_identity_binder_island::{sigma_bound_clamp, sigma_peers_clamp};

contract_fn! {
    /// Kernel-certified check that a canonical `n-<hex32>` principal string has at
    /// least `34` bytes (`34 <= len`), linked via `clean-kernel-defeq` to
    /// `sigma_principal_len_valid_isl`.
    #[must_use]
    pub const fn sigma_principal_len_valid(len: u64) -> bool
    clauses [ensures result == (34 <= len)]
    {
        34 <= len
    }
}

/// Exact byte length of `"n-"` (`2`) + `16` bytes lowercase hex (`32`) = `34`.
pub const PRINCIPAL_NAME_LEN: usize = 34;
/// Maximum peer bindings evaluated in a single batch (`256`).
pub const MAX_SIGMA_PEER_BATCH: usize = 256;

const PRINCIPAL_HASH_DOMAIN: &[u8] = b"astream-identity/principal/v1\x00";
const CHANNEL_BIND_SALT: &[u8] = b"astream-aead/sigma-channel-bind/salt/v1";
const CHANNEL_BIND_INFO: &[u8] = b"astream-aead/sigma-channel-bind/info/v1";
const ATTACH_PROOF_DOMAIN: &[u8] = b"astream-aead/channel-bound-attach/v1";

const fn hex_nibble(n: u8) -> u8 {
    let low = n & 0x0F;
    if low < 10 {
        b'0'.saturating_add(low)
    } else {
        b'a'.saturating_add(low.saturating_sub(10))
    }
}

/// Derive the canonical 34-byte ASCII principal name `n-<32 hex chars>` for `peer_ed25519_pk`.
#[must_use]
pub fn derive_principal_name(peer_ed25519_pk: &[u8; 32]) -> [u8; PRINCIPAL_NAME_LEN] {
    let mut h = Sha256::new();
    h.update_slice(PRINCIPAL_HASH_DOMAIN);
    h.update_slice(peer_ed25519_pk);
    let digest = h.finalize();

    let mut out = [
        b'n', b'-', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0,
    ];
    let mut i = 0usize;
    let mut cur_digest: &[u8] = match digest.get(..16) {
        Some(s) => s,
        None => &digest,
    };
    while let &[b, ref rest @ ..] = cur_digest {
        let hi = hex_nibble(b >> 4);
        let lo = hex_nibble(b);
        if let Some(s0) = out.get_mut(2usize.saturating_add(i.saturating_mul(2))) {
            *s0 = hi;
        }
        if let Some(s1) = out.get_mut(3usize.saturating_add(i.saturating_mul(2))) {
            *s1 = lo;
        }
        i = i.saturating_add(1);
        cur_digest = rest;
    }
    out
}

/// Verify in constant time that `claimed_principal` equals `derive_principal_name(peer_ed25519_pk)`.
#[must_use]
pub fn verify_peer_matches_principal(peer_ed25519_pk: &[u8; 32], claimed_principal: &[u8]) -> bool {
    if claimed_principal.len() != PRINCIPAL_NAME_LEN
        || !sigma_principal_len_valid(claimed_principal.len() as u64)
    {
        return false;
    }
    let expected = derive_principal_name(peer_ed25519_pk);
    ct_eq(&expected, claimed_principal)
}

/// Compute a 32-byte channel-bound attach proof tying `(session_shared_secret, sigma_transcript_hash)`
/// to `(peer_ed25519_pk, capability_tag)`.
#[must_use]
#[inline(never)]
pub fn compute_channel_bound_attach_proof(
    session_shared_secret: &[u8; 32],
    sigma_transcript_hash: &[u8; 32],
    peer_ed25519_pk: &[u8; 32],
    capability_tag: &[u8; 32],
) -> [u8; 32] {
    let prk = hkdf_extract(CHANNEL_BIND_SALT, session_shared_secret);
    let bind_key = hkdf_expand_32(&prk, CHANNEL_BIND_INFO);
    let principal = derive_principal_name(peer_ed25519_pk);
    hmac_sha256_parts(
        &bind_key,
        &[
            ATTACH_PROOF_DOMAIN,
            sigma_transcript_hash,
            &principal,
            capability_tag,
        ],
    )
}

/// Verify both R6 principal-key binding AND channel-bound attach proof in constant time.
#[must_use]
pub fn verify_channel_bound_attach(
    session_shared_secret: &[u8; 32],
    sigma_transcript_hash: &[u8; 32],
    peer_ed25519_pk: &[u8; 32],
    claimed_principal: &[u8],
    capability_tag: &[u8; 32],
    presented_proof: &[u8; 32],
) -> bool {
    if !verify_peer_matches_principal(peer_ed25519_pk, claimed_principal) {
        return false;
    }
    let expected = compute_channel_bound_attach_proof(
        session_shared_secret,
        sigma_transcript_hash,
        peer_ed25519_pk,
        capability_tag,
    );
    ct_eq(&expected, presented_proof)
}

/// Batch-evaluate `(peer_pk, claimed_principal)` pairs, returning `(checked_peers, bound_principals)`.
#[must_use]
pub fn audit_peer_principal_bindings(pairs: &[([u8; 32], &[u8])]) -> (u64, u64) {
    let checked = sigma_peers_clamp(pairs.len() as u64, MAX_SIGMA_PEER_BATCH as u64);
    let limit = checked as usize;
    let bounded = match pairs.get(..limit) {
        Some(s) => s,
        None => pairs,
    };
    let mut raw_bound = 0u64;
    let mut cur = bounded;
    while let &[(ref pk, claimed), ref rest @ ..] = cur {
        if verify_peer_matches_principal(pk, claimed) {
            raw_bound = raw_bound.saturating_add(1);
        }
        cur = rest;
    }
    (checked, sigma_bound_clamp(raw_bound, checked))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_ed25519_peer_key_to_principal_and_rejects_mitm_transcript_replay() {
        let peer_pk = [0x5Au8; 32];
        let wrong_pk = [0x5Bu8; 32];
        let secret = [0x99u8; 32];
        let transcript_a = [0x10u8; 32];
        let transcript_b = [0x20u8; 32];
        let cap_tag = [0x77u8; 32];

        let principal = derive_principal_name(&peer_pk);
        assert_eq!(&principal[..2], b"n-");
        assert!(verify_peer_matches_principal(&peer_pk, &principal));
        assert!(!verify_peer_matches_principal(&wrong_pk, &principal));

        let proof = compute_channel_bound_attach_proof(&secret, &transcript_a, &peer_pk, &cap_tag);
        assert!(verify_channel_bound_attach(
            &secret,
            &transcript_a,
            &peer_pk,
            &principal,
            &cap_tag,
            &proof
        ));
        // Replay on a different SIGMA session transcript MUST fail!
        assert!(!verify_channel_bound_attach(
            &secret,
            &transcript_b,
            &peer_pk,
            &principal,
            &cap_tag,
            &proof
        ));

        let (checked, bound) =
            audit_peer_principal_bindings(&[(peer_pk, &principal), (wrong_pk, &principal)]);
        assert_eq!((checked, bound), (2, 1));
    }
}
