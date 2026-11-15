//! Rung 8 — static public-key identity: mutual authentication with NO shared
//! secret.
//!
//! Rung 7 authenticates with a pre-shared key. This replaces that secret with
//! long-term **Ed25519 identity keypairs** and a signed-Diffie-Hellman
//! (SIGMA/TLS-1.3-style) handshake: the client verifies the broker's *host key*
//! and the broker authorizes the client's key against an allow-list. Two peers
//! authenticate each other by proving possession of an identity private key over
//! a fresh ephemeral exchange — no secret is shared out of band, only public
//! keys.
//!
//! # Why the identity keys only sign
//! The session key is derived from the EPHEMERAL X25519 DH alone (Rung 7's
//! machinery, reused). The static identity keys are used ONLY to sign the
//! ephemeral transcript. So forward secrecy survives even a compromise of the
//! long-term identity keys: an attacker who later steals an identity private key
//! still cannot decrypt a past session (its ephemeral secrets are gone, and the
//! identity key never touched the key schedule). This separation is the whole
//! point of the signed-DH (SIGMA) approach.
//!
//! # Protocol (mutual, 4 messages)
//! ```text
//! M1 client → server : magic|ver|ec_pub                      (clear ephemeral)
//! M2 server → client : magic|ver|es_pub                      (clear ephemeral)
//!    both derive k = HKDF-SHA256(ikm = X25519(ec,es), info = label‖ec_pub‖es_pub)
//!    and wrap SealedStream(k)   -- everything after is AEAD-sealed under k
//! M3 server → client : server_id_pub ‖ Sign_s("…server-auth"‖ec_pub‖es_pub)
//!    client: verify sig under server_id_pub; require server_id_pub == the PINNED host key
//! M4 client → server : client_id_pub ‖ Sign_c("…client-auth"‖ec_pub‖es_pub)
//!    server: verify sig under client_id_pub; require client_id_pub ∈ allow-list
//! ```
//! Each party signs the ephemeral keys **as it saw them**, so an active MITM —
//! which must substitute different ephemerals on each leg — produces a signature
//! that fails to verify against the other party's transcript view. Role-tagged
//! signature contexts (`server-auth` / `client-auth`) prevent reflection. The
//! auth messages ride inside the AEAD, so the tag also proves the sender derived
//! the session key (it completed the DH). App data flows only after M4 verifies.
//!
//! We own the protocol, the framing, the transcript, and (via Rung 7) the
//! X25519 glue and the key schedule over astream-digest's HKDF/HMAC; the only
//! delegated primitive here is the raw Ed25519 sign/verify, to the vetted
//! `ed25519-dalek`.

use crate::handshake::{
    ephemeral, hkdf_sha256_32, read_hs_msg, transcript as record_binding, write_hs_msg,
    x25519_shared,
};
use crate::{SealedStream, KEY_LEN};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use std::io::{self, Read, Write};

#[cfg(clean_islands)]
#[path = "identity_island.rs"]
mod identity_island;
#[cfg(not(clean_islands))]
pub use crate::twins::identity_clamp_ctx_len;
#[cfg(clean_islands)]
pub use identity_island::identity_clamp_ctx_len;

contract_fn! {
    /// Verified check that an identity auth message has the exact wire length (`len == 96`),
    /// linked via `clean-kernel-defeq` to `identity_auth_msg_len_valid_isl`.
    #[must_use]
    pub const fn identity_auth_msg_len_valid(len: usize) -> bool
    clauses [ensures result == (len == 96)]
    {
        len == 96
    }
}

const ID_LABEL: &[u8; 19] = b"astream-identity-v1";
const SIG_CTX_LEN: usize = 31;
const SIG_CTX_SERVER: &[u8; SIG_CTX_LEN] = b"astream-identity-v1 server-auth";
const SIG_CTX_CLIENT: &[u8; SIG_CTX_LEN] = b"astream-identity-v1 client-auth";
/// An Ed25519 public identity key.
pub const ID_PUB_LEN: usize = 32;
const SIG_LEN: usize = 64;
const AUTH_MSG_LEN: usize = ID_PUB_LEN + SIG_LEN; // id_pub ‖ signature

/// A long-term Ed25519 identity: a broker's host key, or a client's identity.
/// The private half never leaves this type; [`public`](Self::public) is the
/// shareable identity a peer pins or allow-lists. `Clone` so a caller can reuse
/// one identity across reconnections (the per-connection handshake consumes it).
#[derive(Clone)]
pub struct IdentityKeypair {
    signing: SigningKey,
}

impl IdentityKeypair {
    /// Generate a fresh identity from the OS CSPRNG.
    #[must_use]
    pub fn generate() -> Self {
        let mut seed = [0u8; 32];
        assert!(
            getrandom::getrandom(&mut seed).is_ok(),
            "OS CSPRNG unavailable"
        );
        let kp = Self::from_seed(seed);
        seed.fill(0);
        core::hint::black_box(&mut seed);
        kp
    }

    /// Load an identity from a stored 32-byte Ed25519 seed (a persisted host key).
    #[must_use]
    pub fn from_seed(mut seed: [u8; 32]) -> Self {
        let signing = SigningKey::from_bytes(&seed);
        seed.fill(0);
        core::hint::black_box(&mut seed);
        IdentityKeypair { signing }
    }

    /// This identity's public key — the value a peer pins (host key) or puts on
    /// its allow-list.
    #[must_use]
    pub fn public(&self) -> [u8; ID_PUB_LEN] {
        self.signing.verifying_key().to_bytes()
    }

    /// Sign an arbitrary `message` with this Ed25519 private key, returning the
    /// raw 64-byte Ed25519 signature (used by [`crate::CertificateAuthority`] and
    /// [`crate::IdentitySigner`]).
    #[must_use]
    pub fn sign_raw(&self, message: &[u8]) -> [u8; SIG_LEN] {
        self.signing.sign(message).to_bytes()
    }
}

impl Drop for IdentityKeypair {
    fn drop(&mut self) {
        self.signing = SigningKey::from_bytes(&[0u8; 32]);
        core::hint::black_box(&mut self.signing);
    }
}

#[inline(always)]
const fn id_ctx_lo(ctx: &[u8; SIG_CTX_LEN]) -> [u8; 16] {
    [
        ctx[0], ctx[1], ctx[2], ctx[3], ctx[4], ctx[5], ctx[6], ctx[7], ctx[8], ctx[9], ctx[10],
        ctx[11], ctx[12], ctx[13], ctx[14], ctx[15],
    ]
}

#[inline(always)]
const fn id_ctx_hi(ctx: &[u8; SIG_CTX_LEN]) -> [u8; 15] {
    [
        ctx[16], ctx[17], ctx[18], ctx[19], ctx[20], ctx[21], ctx[22], ctx[23], ctx[24], ctx[25],
        ctx[26], ctx[27], ctx[28], ctx[29], ctx[30],
    ]
}

#[inline(always)]
const fn id_transcript_ec_lo(ec_pub: &[u8; 32]) -> [u8; 16] {
    [
        ec_pub[0], ec_pub[1], ec_pub[2], ec_pub[3], ec_pub[4], ec_pub[5], ec_pub[6], ec_pub[7],
        ec_pub[8], ec_pub[9], ec_pub[10], ec_pub[11], ec_pub[12], ec_pub[13], ec_pub[14],
        ec_pub[15],
    ]
}

#[inline(always)]
const fn id_transcript_ec_hi(ec_pub: &[u8; 32]) -> [u8; 16] {
    [
        ec_pub[16], ec_pub[17], ec_pub[18], ec_pub[19], ec_pub[20], ec_pub[21], ec_pub[22],
        ec_pub[23], ec_pub[24], ec_pub[25], ec_pub[26], ec_pub[27], ec_pub[28], ec_pub[29],
        ec_pub[30], ec_pub[31],
    ]
}

#[inline(always)]
const fn id_transcript_es_lo(es_pub: &[u8; 32]) -> [u8; 16] {
    [
        es_pub[0], es_pub[1], es_pub[2], es_pub[3], es_pub[4], es_pub[5], es_pub[6], es_pub[7],
        es_pub[8], es_pub[9], es_pub[10], es_pub[11], es_pub[12], es_pub[13], es_pub[14],
        es_pub[15],
    ]
}

#[inline(always)]
const fn id_transcript_es_hi(es_pub: &[u8; 32]) -> [u8; 16] {
    [
        es_pub[16], es_pub[17], es_pub[18], es_pub[19], es_pub[20], es_pub[21], es_pub[22],
        es_pub[23], es_pub[24], es_pub[25], es_pub[26], es_pub[27], es_pub[28], es_pub[29],
        es_pub[30], es_pub[31],
    ]
}

/// The exact bytes each side signs: a role-tagged context over both ephemeral
/// public keys, in the fixed order (client then server) both sides agree on.
const fn transcript(
    ctx: &[u8; SIG_CTX_LEN],
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
) -> [u8; SIG_CTX_LEN + 64] {
    let [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] = id_ctx_lo(ctx);
    let [x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30] =
        id_ctx_hi(ctx);
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] =
        id_transcript_ec_lo(ec_pub);
    let [c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31] =
        id_transcript_ec_hi(ec_pub);
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] =
        id_transcript_es_lo(es_pub);
    let [s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] =
        id_transcript_es_hi(es_pub);
    [
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
        x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, c0, c1, c2, c3, c4, c5, c6, c7, c8,
        c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26,
        c27, c28, c29, c30, c31, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14,
        s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31,
    ]
}

#[inline(always)]
const fn id_info_label_lo() -> [u8; 16] {
    [
        ID_LABEL[0],
        ID_LABEL[1],
        ID_LABEL[2],
        ID_LABEL[3],
        ID_LABEL[4],
        ID_LABEL[5],
        ID_LABEL[6],
        ID_LABEL[7],
        ID_LABEL[8],
        ID_LABEL[9],
        ID_LABEL[10],
        ID_LABEL[11],
        ID_LABEL[12],
        ID_LABEL[13],
        ID_LABEL[14],
        ID_LABEL[15],
    ]
}

#[inline(always)]
const fn id_info_label_hi() -> [u8; 3] {
    [ID_LABEL[16], ID_LABEL[17], ID_LABEL[18]]
}

#[inline(always)]
const fn id_info_ec_lo(ec_pub: &[u8; 32]) -> [u8; 16] {
    [
        ec_pub[0], ec_pub[1], ec_pub[2], ec_pub[3], ec_pub[4], ec_pub[5], ec_pub[6], ec_pub[7],
        ec_pub[8], ec_pub[9], ec_pub[10], ec_pub[11], ec_pub[12], ec_pub[13], ec_pub[14],
        ec_pub[15],
    ]
}

#[inline(always)]
const fn id_info_ec_hi(ec_pub: &[u8; 32]) -> [u8; 16] {
    [
        ec_pub[16], ec_pub[17], ec_pub[18], ec_pub[19], ec_pub[20], ec_pub[21], ec_pub[22],
        ec_pub[23], ec_pub[24], ec_pub[25], ec_pub[26], ec_pub[27], ec_pub[28], ec_pub[29],
        ec_pub[30], ec_pub[31],
    ]
}

#[inline(always)]
const fn id_info_es_lo(es_pub: &[u8; 32]) -> [u8; 16] {
    [
        es_pub[0], es_pub[1], es_pub[2], es_pub[3], es_pub[4], es_pub[5], es_pub[6], es_pub[7],
        es_pub[8], es_pub[9], es_pub[10], es_pub[11], es_pub[12], es_pub[13], es_pub[14],
        es_pub[15],
    ]
}

#[inline(always)]
const fn id_info_es_hi(es_pub: &[u8; 32]) -> [u8; 16] {
    [
        es_pub[16], es_pub[17], es_pub[18], es_pub[19], es_pub[20], es_pub[21], es_pub[22],
        es_pub[23], es_pub[24], es_pub[25], es_pub[26], es_pub[27], es_pub[28], es_pub[29],
        es_pub[30], es_pub[31],
    ]
}

const fn build_id_info(ec_pub: &[u8; 32], es_pub: &[u8; 32]) -> [u8; 83] {
    let [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15] = id_info_label_lo();
    let [l16, l17, l18] = id_info_label_hi();
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] =
        id_info_ec_lo(ec_pub);
    let [c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31] =
        id_info_ec_hi(ec_pub);
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] =
        id_info_es_lo(es_pub);
    let [s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] =
        id_info_es_hi(es_pub);
    [
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, c0,
        c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20,
        c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, s0, s1, s2, s3, s4, s5, s6, s7, s8,
        s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
        s27, s28, s29, s30, s31,
    ]
}

/// Derive the session key from the ephemeral DH ONLY (identity keys never enter
/// the key schedule — that is what keeps forward secrecy under identity-key
/// compromise).
fn session_key(dh: &[u8; 32], ec_pub: &[u8; 32], es_pub: &[u8; 32]) -> [u8; KEY_LEN] {
    let info = build_id_info(ec_pub, es_pub);
    let _ = identity_clamp_ctx_len(info.len() as u64, 83);
    hkdf_sha256_32(&[], dh, &info)
}

#[inline(always)]
const fn auth_join_id_lo(id_pub: &[u8; ID_PUB_LEN]) -> [u8; 16] {
    [
        id_pub[0], id_pub[1], id_pub[2], id_pub[3], id_pub[4], id_pub[5], id_pub[6], id_pub[7],
        id_pub[8], id_pub[9], id_pub[10], id_pub[11], id_pub[12], id_pub[13], id_pub[14],
        id_pub[15],
    ]
}

#[inline(always)]
const fn auth_join_id_hi(id_pub: &[u8; ID_PUB_LEN]) -> [u8; 16] {
    [
        id_pub[16], id_pub[17], id_pub[18], id_pub[19], id_pub[20], id_pub[21], id_pub[22],
        id_pub[23], id_pub[24], id_pub[25], id_pub[26], id_pub[27], id_pub[28], id_pub[29],
        id_pub[30], id_pub[31],
    ]
}

#[inline(always)]
const fn auth_join_sig_q0(sig: &[u8; SIG_LEN]) -> [u8; 16] {
    [
        sig[0], sig[1], sig[2], sig[3], sig[4], sig[5], sig[6], sig[7], sig[8], sig[9], sig[10],
        sig[11], sig[12], sig[13], sig[14], sig[15],
    ]
}

#[inline(always)]
const fn auth_join_sig_q1(sig: &[u8; SIG_LEN]) -> [u8; 16] {
    [
        sig[16], sig[17], sig[18], sig[19], sig[20], sig[21], sig[22], sig[23], sig[24], sig[25],
        sig[26], sig[27], sig[28], sig[29], sig[30], sig[31],
    ]
}

#[inline(always)]
const fn auth_join_sig_q2(sig: &[u8; SIG_LEN]) -> [u8; 16] {
    [
        sig[32], sig[33], sig[34], sig[35], sig[36], sig[37], sig[38], sig[39], sig[40], sig[41],
        sig[42], sig[43], sig[44], sig[45], sig[46], sig[47],
    ]
}

#[inline(always)]
const fn auth_join_sig_q3(sig: &[u8; SIG_LEN]) -> [u8; 16] {
    [
        sig[48], sig[49], sig[50], sig[51], sig[52], sig[53], sig[54], sig[55], sig[56], sig[57],
        sig[58], sig[59], sig[60], sig[61], sig[62], sig[63],
    ]
}

const fn join_auth_message(id_pub: &[u8; ID_PUB_LEN], sig: &[u8; SIG_LEN]) -> [u8; AUTH_MSG_LEN] {
    let [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15] =
        auth_join_id_lo(id_pub);
    let [k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31] =
        auth_join_id_hi(id_pub);
    let [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] =
        auth_join_sig_q0(sig);
    let [g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31] =
        auth_join_sig_q1(sig);
    let [g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47] =
        auth_join_sig_q2(sig);
    let [g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63] =
        auth_join_sig_q3(sig);
    [
        k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
        k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, g0, g1, g2, g3, g4, g5, g6, g7,
        g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25,
        g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43,
        g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61,
        g62, g63,
    ]
}

/// Build an auth message: our identity public key followed by our signature over
/// the role-tagged ephemeral transcript.
fn auth_message(
    me: &IdentityKeypair,
    ctx: &[u8; SIG_CTX_LEN],
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
) -> [u8; AUTH_MSG_LEN] {
    let sig: Signature = me.signing.sign(&transcript(ctx, ec_pub, es_pub));
    let msg = join_auth_message(&me.public(), &sig.to_bytes());
    let _ = identity_auth_msg_len_valid(msg.len());
    msg
}

#[inline(always)]
const fn auth_split_id_lo(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[0], msg[1], msg[2], msg[3], msg[4], msg[5], msg[6], msg[7], msg[8], msg[9], msg[10],
        msg[11], msg[12], msg[13], msg[14], msg[15],
    ]
}

#[inline(always)]
const fn auth_split_id_hi(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[16], msg[17], msg[18], msg[19], msg[20], msg[21], msg[22], msg[23], msg[24], msg[25],
        msg[26], msg[27], msg[28], msg[29], msg[30], msg[31],
    ]
}

#[inline(always)]
const fn auth_split_sig_q0(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[32], msg[33], msg[34], msg[35], msg[36], msg[37], msg[38], msg[39], msg[40], msg[41],
        msg[42], msg[43], msg[44], msg[45], msg[46], msg[47],
    ]
}

#[inline(always)]
const fn auth_split_sig_q1(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[48], msg[49], msg[50], msg[51], msg[52], msg[53], msg[54], msg[55], msg[56], msg[57],
        msg[58], msg[59], msg[60], msg[61], msg[62], msg[63],
    ]
}

#[inline(always)]
const fn auth_split_sig_q2(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[64], msg[65], msg[66], msg[67], msg[68], msg[69], msg[70], msg[71], msg[72], msg[73],
        msg[74], msg[75], msg[76], msg[77], msg[78], msg[79],
    ]
}

#[inline(always)]
const fn auth_split_sig_q3(msg: &[u8; AUTH_MSG_LEN]) -> [u8; 16] {
    [
        msg[80], msg[81], msg[82], msg[83], msg[84], msg[85], msg[86], msg[87], msg[88], msg[89],
        msg[90], msg[91], msg[92], msg[93], msg[94], msg[95],
    ]
}

/// Split a received auth message into (identity public key, signature).
const fn split_auth(msg: &[u8; AUTH_MSG_LEN]) -> ([u8; ID_PUB_LEN], [u8; SIG_LEN]) {
    let [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15] =
        auth_split_id_lo(msg);
    let [k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31] =
        auth_split_id_hi(msg);
    let [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15] =
        auth_split_sig_q0(msg);
    let [g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31] =
        auth_split_sig_q1(msg);
    let [g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47] =
        auth_split_sig_q2(msg);
    let [g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63] =
        auth_split_sig_q3(msg);
    let id = [
        k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
        k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31,
    ];
    let sig = [
        g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
        g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37,
        g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55,
        g56, g57, g58, g59, g60, g61, g62, g63,
    ];
    (id, sig)
}

/// Strictly verify `sig` over the role-tagged transcript under `id_pub`.
/// `verify_strict` rejects small-order/non-canonical keys and malleable sigs.
fn verify_auth(
    id_pub: &[u8; ID_PUB_LEN],
    sig: &[u8; SIG_LEN],
    ctx: &[u8; SIG_CTX_LEN],
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
) -> io::Result<()> {
    let vk = match VerifyingKey::from_bytes(id_pub) {
        Ok(vk) => vk,
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream identity: malformed key",
            ));
        }
    };
    let signature = Signature::from_bytes(sig);
    match vk.verify_strict(&transcript(ctx, ec_pub, es_pub), &signature) {
        Ok(()) => Ok(()),
        Err(_) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream identity: signature verification failed (MITM or wrong identity)",
        )),
    }
}

fn is_authorized_client(
    authorized_clients: &[[u8; ID_PUB_LEN]],
    client_id: &[u8; ID_PUB_LEN],
) -> bool {
    let mut i = 0usize;
    while i < authorized_clients.len() {
        if &authorized_clients[i] == client_id {
            return true;
        }
        i = i.saturating_add(1);
    }
    false
}

/// Run the CLIENT side of the mutual identity handshake over `stream`. Verifies
/// the server is exactly `expected_server` (a pinned host key), proves our own
/// identity `me`, and returns the forward-secret [`SealedStream`].
///
/// # Errors
/// A socket error, a non-contributory DH, a server that is not the pinned host
/// key, or any signature that fails to verify.
pub fn client_identity_handshake<S: Read + Write>(
    mut stream: S,
    me: &IdentityKeypair,
    expected_server: &[u8; ID_PUB_LEN],
) -> io::Result<SealedStream<S>> {
    // M1/M2: ephemeral exchange (client speaks first).
    let (secret, ec_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &ec_pub)?;
    let es_pub = read_hs_msg(&mut stream)?;
    let dh = x25519_shared(&secret, &es_pub)?;
    // The transcript both sides SIGN below is also what the record layer binds into
    // every record's AAD, so an authenticated session's records cannot be replayed
    // into any other session or direction.
    let mut sealed = SealedStream::with_transcript(
        stream,
        session_key(dh.as_bytes(), &ec_pub, &es_pub),
        &record_binding(&ec_pub, &es_pub),
        true,
    );

    // M3: the server proves its identity; require it to be the pinned host key.
    let mut m3 = [0u8; AUTH_MSG_LEN];
    sealed.read_exact(&mut m3)?;
    let (server_id, sig_s) = split_auth(&m3);
    if server_id != *expected_server {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream identity: server is not the pinned host key",
        ));
    }
    verify_auth(&server_id, &sig_s, SIG_CTX_SERVER, &ec_pub, &es_pub)?;

    // M4: prove our own identity to the server.
    let m4 = auth_message(me, SIG_CTX_CLIENT, &ec_pub, &es_pub);
    sealed.write_all(&m4)?;
    sealed.flush()?;
    Ok(sealed)
}

/// Run the SERVER side of the mutual identity handshake over `stream`. Proves our
/// host identity `me`, then requires the client's identity to be in
/// `authorized_clients`. Returns the forward-secret [`SealedStream`] and the
/// authenticated client identity key.
///
/// # Errors
/// A socket error, a non-contributory DH, a client signature that fails to
/// verify, or a client whose identity is not authorized.
pub fn server_identity_handshake<S: Read + Write>(
    mut stream: S,
    me: &IdentityKeypair,
    authorized_clients: &[[u8; ID_PUB_LEN]],
) -> io::Result<(SealedStream<S>, [u8; ID_PUB_LEN])> {
    // M1/M2: ephemeral exchange.
    let ec_pub = read_hs_msg(&mut stream)?;
    let (secret, es_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &es_pub)?;
    let dh = x25519_shared(&secret, &ec_pub)?;
    let mut sealed = SealedStream::with_transcript(
        stream,
        session_key(dh.as_bytes(), &ec_pub, &es_pub),
        &record_binding(&ec_pub, &es_pub),
        false,
    );

    // M3: prove our host identity to the client.
    let m3 = auth_message(me, SIG_CTX_SERVER, &ec_pub, &es_pub);
    sealed.write_all(&m3)?;
    sealed.flush()?;

    // M4: the client proves its identity; verify the signature, THEN authorize.
    let mut m4 = [0u8; AUTH_MSG_LEN];
    sealed.read_exact(&mut m4)?;
    let (client_id, sig_c) = split_auth(&m4);
    verify_auth(&client_id, &sig_c, SIG_CTX_CLIENT, &ec_pub, &es_pub)?;
    if !is_authorized_client(authorized_clients, &client_id) {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "astream identity: client identity is not authorized",
        ));
    }
    Ok((sealed, client_id))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{TcpListener, TcpStream};
    use x25519_dalek::PublicKey;

    fn keys() -> (&'static IdentityKeypair, &'static IdentityKeypair) {
        // Leaked so the loopback threads can borrow 'static; fine for a test.
        let server: &'static IdentityKeypair = Box::leak(Box::new(IdentityKeypair::generate()));
        let client: &'static IdentityKeypair = Box::leak(Box::new(IdentityKeypair::generate()));
        (server, client)
    }

    #[test]
    fn server_rejects_an_unauthorized_client() {
        // The allow-list admits exactly its members, wherever they stand in it.
        let (a, b, c) = ([1u8; 32], [2u8; 32], [3u8; 32]);
        for (list, admitted) in [
            (&[][..], false),
            (&[a][..], true),
            (&[b, a][..], true),
            (&[a, b][..], true),
            (&[b, c][..], false),
        ] {
            assert_eq!(is_authorized_client(list, &a), admitted, "{list:?}");
        }
    }

    #[test]
    fn a_forged_client_signature_is_rejected() {
        // verify_auth, directly: it accepts the genuine signature over this
        // session's role-tagged transcript and nothing else.
        let (_, client) = keys();
        let (ec, es, elsewhere) = ([1u8; 32], [2u8; 32], [3u8; 32]);
        let good = auth_message(client, SIG_CTX_CLIENT, &ec, &es);
        let (id, sig) = split_auth(&good);
        let mut flipped = sig;
        flipped[0] ^= 0x01;
        // A small-order key (the Edwards identity point) with R = identity and
        // s = 0 satisfies the unhardened verification equation for EVERY message;
        // strict verification refuses the key.
        let mut weak = [0u8; ID_PUB_LEN];
        weak[0] = 1;
        let mut any = [0u8; SIG_LEN];
        any[0] = 1;
        // No curve point has y = 2: a pinned or allow-listed key that does not
        // decode must refuse every peer, never admit one.
        let mut not_a_point = [0u8; ID_PUB_LEN];
        not_a_point[0] = 2;
        assert!(verify_auth(&id, &sig, SIG_CTX_CLIENT, &ec, &es).is_ok());
        for (what, id, sig, ctx, ec, es) in [
            ("a flipped byte", id, flipped, SIG_CTX_CLIENT, ec, es),
            ("reflected", id, sig, SIG_CTX_SERVER, ec, es),
            ("another ec", id, sig, SIG_CTX_CLIENT, elsewhere, es),
            ("another es", id, sig, SIG_CTX_CLIENT, ec, elsewhere),
            ("a small-order key", weak, any, SIG_CTX_CLIENT, ec, es),
            ("not a point", not_a_point, sig, SIG_CTX_CLIENT, ec, es),
        ] {
            let got = verify_auth(&id, &sig, ctx, &ec, &es).map_err(|e| e.kind());
            assert_eq!(got, Err(io::ErrorKind::InvalidData), "{what}");
        }
        // The exported length check accepts exactly what auth_message builds.
        let n = good.len();
        assert_eq!(
            [n - 1, n, n + 1].map(identity_auth_msg_len_valid),
            [false, true, false]
        );
    }

    // The protocol as the module docs specify it, spelled out here rather than
    // through the code under test: a session over the ephemerals `ec`, `es` keys
    // its records with HKDF-SHA256(salt = empty, X25519, label ‖ ec ‖ es) and binds
    // ec ‖ es into their AAD, and an auth message is id ‖ Sign(ctx ‖ ec ‖ es).

    fn spec_session<S: Read + Write>(
        inner: S,
        dh: &[u8; 32],
        ec: &[u8; 32],
        es: &[u8; 32],
        is_client: bool,
    ) -> SealedStream<S> {
        let key = hkdf_sha256_32(&[], dh, &[ID_LABEL, &ec[..], &es[..]].concat());
        SealedStream::with_transcript(inner, key, &[&ec[..], &es[..]].concat(), is_client)
    }

    /// The auth message of a peer that NAMES the identity `named` and signs with
    /// `signer`'s private key.
    fn spec_auth(
        named: &[u8; ID_PUB_LEN],
        signer: &IdentityKeypair,
        ctx: &[u8],
        ec: &[u8; 32],
        es: &[u8; 32],
    ) -> Vec<u8> {
        let sig = signer.signing.sign(&[ctx, &ec[..], &es[..]].concat());
        [&named[..], &sig.to_bytes()[..]].concat()
    }

    /// Whether `msg` names `id` and carries id's strict signature over
    /// ctx ‖ ec ‖ es.
    fn spec_verifies(
        msg: &[u8],
        id: &[u8; ID_PUB_LEN],
        ctx: &[u8],
        ec: &[u8; 32],
        es: &[u8; 32],
    ) -> bool {
        let Some((named, sig)) = msg.split_at_checked(ID_PUB_LEN) else {
            return false;
        };
        let (Ok(vk), Ok(sig)) = (VerifyingKey::from_bytes(id), Signature::from_slice(sig)) else {
            return false;
        };
        named == id
            && vk
                .verify_strict(&[ctx, &ec[..], &es[..]].concat(), &sig)
                .is_ok()
    }

    fn tcp_pair() -> (TcpStream, TcpStream) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let near = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        let (far, _) = listener.accept().unwrap();
        for s in [&near, &far] {
            // A hang detector, not a latency budget.
            s.set_read_timeout(Some(std::time::Duration::from_secs(60)))
                .unwrap();
        }
        (near, far)
    }

    #[test]
    fn each_half_admits_exactly_a_trusted_peer_that_signs_this_session() {
        // Each fake peer runs the spec above, so its auth message arrives
        // authentic on the wire; the rows vary only which identity it names and
        // which key signs. The genuine trusted peer is admitted, which holds each
        // real half's key schedule, record binding and signed transcript to the
        // spec. A peer that names a trusted identity (read off a pin or an
        // allow-list) without its private key is refused as InvalidData, and a
        // genuine peer that is not trusted is refused too.
        let (server, client) = keys();
        let impostor: &'static IdentityKeypair = Box::leak(Box::new(IdentityKeypair::generate()));

        // Fake SERVERS; the client pins `server`. It sends its own identity (M4)
        // only to a server it has verified.
        for (what, named, signer, admitted) in [
            ("the pinned host", server.public(), server, true),
            ("a forged pinned host", server.public(), impostor, false),
            ("an unpinned host", impostor.public(), impostor, false),
        ] {
            let (near, far) = tcp_pair();
            let fake = std::thread::spawn(move || -> io::Result<_> {
                let mut s = far;
                let ec = read_hs_msg(&mut s)?;
                let (secret, es) = ephemeral()?;
                write_hs_msg(&mut s, &es)?;
                let dh = secret.diffie_hellman(&PublicKey::from(ec));
                let mut sealed = spec_session(s, dh.as_bytes(), &ec, &es, false);
                sealed.write_all(&spec_auth(&named, signer, SIG_CTX_SERVER, &ec, &es))?;
                sealed.flush()?;
                // Everything the client sends after M3, up to its close.
                let mut after = Vec::new();
                sealed.read_to_end(&mut after)?;
                Ok((ec, es, after))
            });
            let got = client_identity_handshake(near, client, &server.public())
                .map(drop)
                .map_err(|e| e.kind());
            let (ec, es, after) = fake.join().unwrap().unwrap();
            if admitted {
                assert_eq!(got, Ok(()), "{what}");
                let m4 = spec_verifies(&after, &client.public(), SIG_CTX_CLIENT, &ec, &es);
                assert!(m4, "{what}: the client's M4");
            } else {
                assert_eq!(got, Err(io::ErrorKind::InvalidData), "{what}");
                assert!(after.is_empty(), "{what}: the client named itself");
            }
        }

        // Fake CLIENTS; the server allow-lists `client`.
        for (what, named, signer, want) in [
            (
                "the listed client",
                client.public(),
                client,
                Ok(client.public()),
            ),
            (
                "a forged listed client",
                client.public(),
                impostor,
                Err(io::ErrorKind::InvalidData),
            ),
            (
                "an unlisted client",
                impostor.public(),
                impostor,
                Err(io::ErrorKind::PermissionDenied),
            ),
            // PermissionDenied names an identity that proved its key; a forgery
            // is InvalidData whatever it names.
            (
                "a forged unlisted client",
                impostor.public(),
                client,
                Err(io::ErrorKind::InvalidData),
            ),
        ] {
            let (near, far) = tcp_pair();
            let allowed = vec![client.public()];
            let real = std::thread::spawn(move || {
                server_identity_handshake(far, server, &allowed)
                    .map(|(_, id)| id)
                    .map_err(|e| e.kind())
            });
            let mut c = near;
            let (secret, ec) = ephemeral().unwrap();
            write_hs_msg(&mut c, &ec).unwrap();
            let es = read_hs_msg(&mut c).unwrap();
            let dh = secret.diffie_hellman(&PublicKey::from(es));
            let mut sealed = spec_session(c, dh.as_bytes(), &ec, &es, true);
            let mut m3 = [0u8; AUTH_MSG_LEN];
            sealed.read_exact(&mut m3).unwrap();
            let m3 = spec_verifies(&m3, &server.public(), SIG_CTX_SERVER, &ec, &es);
            assert!(m3, "{what}: the server's M3");
            sealed
                .write_all(&spec_auth(&named, signer, SIG_CTX_CLIENT, &ec, &es))
                .unwrap();
            assert_eq!(real.join().unwrap(), want, "{what}");
        }
    }
}
