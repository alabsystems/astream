//! Rung 7 — the online key-agreement handshake: forward secrecy on top of the
//! pre-shared key.
//!
//! The Rung-6 sealed wire keys the transport directly from the PSK, so a
//! recorded session is decryptable forever by anyone who later learns the PSK.
//! This handshake fixes that: each connection derives a FRESH per-session key
//! from an ephemeral X25519 exchange, and the ephemeral secrets are discarded
//! afterwards — so a later PSK compromise cannot decrypt past traffic (forward
//! secrecy), while the PSK still authenticates (a peer without it derives a
//! different key and its first sealed record fails to open).
//!
//! # Construction (the NNpsk pattern) — WE own it
//! We own the whole protocol: the message framing, the transcript binding, and
//! the key schedule. HMAC-SHA256 / HKDF-SHA256 are the workspace's own, in
//! `astream-digest` (the one HMAC astream-cap tags with too; this crate's copy
//! moved there, its zeroization with it). The ONE primitive we delegate is the raw X25519
//! scalar multiplication — hand-rolling constant-time curve25519 field arithmetic
//! is where DIY crypto breaks — to the vetted `x25519-dalek`.
//!
//! ```text
//! client ── magic|ver|e_client_pub ─▶ server      (1-RTT, client speaks first)
//! client ◀─ magic|ver|e_server_pub ── server
//! both: dh = X25519(e_local_priv, e_remote_pub)             // shared, commutative
//!       key = HKDF-SHA256(salt = PSK,                       // PSK authenticates
//!                         ikm  = dh,                        // ephemeral ⇒ forward secrecy
//!                         info = "astream-handshake-v1" ‖ e_client_pub ‖ e_server_pub)
//!       transport = SealedStream(stream, key)               // the Rung-6 record layer
//! ```
//!
//! `info` fixes the two ephemeral keys in ROLE order (client then server), so a
//! reflected message derives a different key. The DH output is checked
//! contributory (a low-order remote point that would force a zero shared secret
//! is rejected). Mutual authentication is by key confirmation: the first sealed
//! record each side opens proves the peer derived the same key, i.e. holds the
//! PSK — no explicit confirmation message needed.

use crate::{SealedStream, KEY_LEN};
use astream_digest::{hkdf_expand_32, hkdf_extract};
use std::io::{self, Read, Write};
use x25519_dalek::{PublicKey, SharedSecret, StaticSecret};

#[cfg(clean_islands)]
#[path = "handshake_island.rs"]
mod handshake_island;
#[cfg(not(clean_islands))]
pub use crate::twins::handshake_clamp_info_len;
#[cfg(clean_islands)]
pub use handshake_island::handshake_clamp_info_len;

contract_fn! {
    /// Verified check that a handshake message carries version 1 (`ver == 1`),
    /// linked via `clean-kernel-defeq` to `handshake_version_valid_isl`.
    #[must_use]
    pub const fn handshake_version_valid(ver: u8) -> bool
    clauses [ensures result == (ver == 1)]
    {
        ver == 1
    }
}

/// HKDF-SHA256 (RFC 5869) producing exactly 32 bytes (a single expand block,
/// L = 32 ≤ 255·32): `astream-digest`'s Extract then Expand.
///
/// Both run through astream-digest's wiping HMAC, which zeroes the key block and
/// pads it derives from the salt (the PSK, in the NNpsk handshake) and from the
/// PRK before it returns: the zeroization this crate's own HMAC copy did, until
/// that copy was replaced by astream-digest's one HMAC (astream-cap's core moved
/// there too, and aterm's copy has gone the same way). The PRK
/// itself is this function's to wipe, and it does.
pub(crate) fn hkdf_sha256_32(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; 32] {
    let mut prk = hkdf_extract(salt, ikm);
    let okm = hkdf_expand_32(&prk, info);
    prk.fill(0); // wipe the intermediate pseudo-random key
    core::hint::black_box(&mut prk);
    okm
}

const HS_MAGIC: [u8; 4] = *b"aSH1";
const HS_VERSION: u8 = 1;
const HS_MSG_LEN: usize = 4 + 1 + 32; // magic ‖ version ‖ ephemeral pubkey
const HS_LABEL: &[u8; 20] = b"astream-handshake-v1";

const fn build_hs_msg(pubkey: &[u8; 32]) -> [u8; HS_MSG_LEN] {
    [
        HS_MAGIC[0],
        HS_MAGIC[1],
        HS_MAGIC[2],
        HS_MAGIC[3],
        HS_VERSION,
        pubkey[0],
        pubkey[1],
        pubkey[2],
        pubkey[3],
        pubkey[4],
        pubkey[5],
        pubkey[6],
        pubkey[7],
        pubkey[8],
        pubkey[9],
        pubkey[10],
        pubkey[11],
        pubkey[12],
        pubkey[13],
        pubkey[14],
        pubkey[15],
        pubkey[16],
        pubkey[17],
        pubkey[18],
        pubkey[19],
        pubkey[20],
        pubkey[21],
        pubkey[22],
        pubkey[23],
        pubkey[24],
        pubkey[25],
        pubkey[26],
        pubkey[27],
        pubkey[28],
        pubkey[29],
        pubkey[30],
        pubkey[31],
    ]
}

const fn has_hs_magic(msg: &[u8; HS_MSG_LEN]) -> bool {
    msg[0] == HS_MAGIC[0] && msg[1] == HS_MAGIC[1] && msg[2] == HS_MAGIC[2] && msg[3] == HS_MAGIC[3]
}

const fn hs_msg_version(msg: &[u8; HS_MSG_LEN]) -> u8 {
    msg[4]
}

const fn extract_hs_pubkey(msg: &[u8; HS_MSG_LEN]) -> [u8; 32] {
    [
        msg[5], msg[6], msg[7], msg[8], msg[9], msg[10], msg[11], msg[12], msg[13], msg[14],
        msg[15], msg[16], msg[17], msg[18], msg[19], msg[20], msg[21], msg[22], msg[23], msg[24],
        msg[25], msg[26], msg[27], msg[28], msg[29], msg[30], msg[31], msg[32], msg[33], msg[34],
        msg[35], msg[36],
    ]
}

pub(crate) fn write_hs_msg<W: Write>(w: &mut W, pubkey: &[u8; 32]) -> io::Result<()> {
    let msg = build_hs_msg(pubkey);
    w.write_all(&msg)?;
    w.flush()
}

pub(crate) fn read_hs_msg<R: Read>(r: &mut R) -> io::Result<[u8; 32]> {
    let mut msg = [0u8; HS_MSG_LEN];
    let read_exact_op: fn(&mut R, &mut [u8]) -> io::Result<()> = Read::read_exact;
    read_exact_op(r, &mut msg)?;
    if !has_hs_magic(&msg) || !handshake_version_valid(hs_msg_version(&msg)) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream handshake: bad magic/version (peer not speaking the sealed handshake)",
        ));
    }
    Ok(extract_hs_pubkey(&msg))
}

/// A fresh ephemeral X25519 keypair, seeded from the OS CSPRNG (`getrandom`, which
/// we already depend on). We use `StaticSecret` (byte-seedable) as a one-shot
/// ephemeral and drop it after the single DH — `x25519-dalek`'s `zeroize` wipes it
/// on drop, and we wipe our transient seed too.
pub(crate) fn ephemeral() -> io::Result<(StaticSecret, [u8; 32])> {
    let mut seed = [0u8; 32];
    if getrandom::getrandom(&mut seed).is_err() {
        return Err(io::Error::other("OS CSPRNG unavailable"));
    }
    let secret = StaticSecret::from(seed);
    seed.fill(0);
    core::hint::black_box(&mut seed);
    let public = *PublicKey::from(&secret).as_bytes();
    Ok((secret, public))
}

#[inline(always)]
const fn hs_info_label_lo() -> [u8; 16] {
    [
        HS_LABEL[0],
        HS_LABEL[1],
        HS_LABEL[2],
        HS_LABEL[3],
        HS_LABEL[4],
        HS_LABEL[5],
        HS_LABEL[6],
        HS_LABEL[7],
        HS_LABEL[8],
        HS_LABEL[9],
        HS_LABEL[10],
        HS_LABEL[11],
        HS_LABEL[12],
        HS_LABEL[13],
        HS_LABEL[14],
        HS_LABEL[15],
    ]
}

#[inline(always)]
const fn hs_info_label_hi() -> [u8; 4] {
    [HS_LABEL[16], HS_LABEL[17], HS_LABEL[18], HS_LABEL[19]]
}

#[inline(always)]
const fn hs_info_client_lo(client_pub: &[u8; 32]) -> [u8; 16] {
    [
        client_pub[0],
        client_pub[1],
        client_pub[2],
        client_pub[3],
        client_pub[4],
        client_pub[5],
        client_pub[6],
        client_pub[7],
        client_pub[8],
        client_pub[9],
        client_pub[10],
        client_pub[11],
        client_pub[12],
        client_pub[13],
        client_pub[14],
        client_pub[15],
    ]
}

#[inline(always)]
const fn hs_info_client_hi(client_pub: &[u8; 32]) -> [u8; 16] {
    [
        client_pub[16],
        client_pub[17],
        client_pub[18],
        client_pub[19],
        client_pub[20],
        client_pub[21],
        client_pub[22],
        client_pub[23],
        client_pub[24],
        client_pub[25],
        client_pub[26],
        client_pub[27],
        client_pub[28],
        client_pub[29],
        client_pub[30],
        client_pub[31],
    ]
}

#[inline(always)]
const fn hs_info_server_lo(server_pub: &[u8; 32]) -> [u8; 16] {
    [
        server_pub[0],
        server_pub[1],
        server_pub[2],
        server_pub[3],
        server_pub[4],
        server_pub[5],
        server_pub[6],
        server_pub[7],
        server_pub[8],
        server_pub[9],
        server_pub[10],
        server_pub[11],
        server_pub[12],
        server_pub[13],
        server_pub[14],
        server_pub[15],
    ]
}

#[inline(always)]
const fn hs_info_server_hi(server_pub: &[u8; 32]) -> [u8; 16] {
    [
        server_pub[16],
        server_pub[17],
        server_pub[18],
        server_pub[19],
        server_pub[20],
        server_pub[21],
        server_pub[22],
        server_pub[23],
        server_pub[24],
        server_pub[25],
        server_pub[26],
        server_pub[27],
        server_pub[28],
        server_pub[29],
        server_pub[30],
        server_pub[31],
    ]
}

const fn build_hs_info(client_pub: &[u8; 32], server_pub: &[u8; 32]) -> [u8; 84] {
    let [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15] = hs_info_label_lo();
    let [l16, l17, l18, l19] = hs_info_label_hi();
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] =
        hs_info_client_lo(client_pub);
    let [c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31] =
        hs_info_client_hi(client_pub);
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] =
        hs_info_server_lo(server_pub);
    let [s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] =
        hs_info_server_hi(server_pub);
    [
        l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, s0, s1, s2, s3, s4, s5, s6, s7,
        s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25,
        s26, s27, s28, s29, s30, s31,
    ]
}

/// The session key: HKDF over the PSK (salt/authenticator) and the DH secret
/// (IKM/forward-secrecy), transcript-bound to both ephemeral keys in ROLE order.
fn derive_session_key(
    psk: &[u8; KEY_LEN],
    dh: &[u8; 32],
    client_pub: &[u8; 32],
    server_pub: &[u8; 32],
) -> [u8; KEY_LEN] {
    let info = build_hs_info(client_pub, server_pub);
    let _ = handshake_clamp_info_len(info.len() as u64, 84);
    hkdf_sha256_32(psk, dh, &info)
}

/// The raw ephemeral X25519 shared secret against `their_pub`, rejecting a
/// non-contributory (low-order) point that would force a zero output. Shared by
/// the PSK handshake and the identity handshake.
///
/// Returned as `x25519-dalek`'s own type, which wipes itself on drop: a copy
/// into a plain array would outlive the handshake in memory, and this value
/// (with the PSK, if any) is all a later reader needs to decrypt the session.
pub(crate) fn x25519_shared(
    secret: &StaticSecret,
    their_pub: &[u8; 32],
) -> io::Result<SharedSecret> {
    let shared = secret.diffie_hellman(&PublicKey::from(*their_pub));
    if !shared.was_contributory() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream handshake: non-contributory X25519 (low-order point)",
        ));
    }
    Ok(shared)
}

/// Complete the DH and derive the PSK-authenticated session key.
fn agree(
    secret: &StaticSecret,
    psk: &[u8; KEY_LEN],
    their_pub: &[u8; 32],
    client_pub: &[u8; 32],
    server_pub: &[u8; 32],
) -> io::Result<[u8; KEY_LEN]> {
    let dh = x25519_shared(secret, their_pub)?;
    Ok(derive_session_key(
        psk,
        dh.as_bytes(),
        client_pub,
        server_pub,
    ))
}

#[inline(always)]
const fn hs_transcript_q0(client_pub: &[u8; 32]) -> [u8; 16] {
    [
        client_pub[0],
        client_pub[1],
        client_pub[2],
        client_pub[3],
        client_pub[4],
        client_pub[5],
        client_pub[6],
        client_pub[7],
        client_pub[8],
        client_pub[9],
        client_pub[10],
        client_pub[11],
        client_pub[12],
        client_pub[13],
        client_pub[14],
        client_pub[15],
    ]
}

#[inline(always)]
const fn hs_transcript_q1(client_pub: &[u8; 32]) -> [u8; 16] {
    [
        client_pub[16],
        client_pub[17],
        client_pub[18],
        client_pub[19],
        client_pub[20],
        client_pub[21],
        client_pub[22],
        client_pub[23],
        client_pub[24],
        client_pub[25],
        client_pub[26],
        client_pub[27],
        client_pub[28],
        client_pub[29],
        client_pub[30],
        client_pub[31],
    ]
}

#[inline(always)]
const fn hs_transcript_q2(server_pub: &[u8; 32]) -> [u8; 16] {
    [
        server_pub[0],
        server_pub[1],
        server_pub[2],
        server_pub[3],
        server_pub[4],
        server_pub[5],
        server_pub[6],
        server_pub[7],
        server_pub[8],
        server_pub[9],
        server_pub[10],
        server_pub[11],
        server_pub[12],
        server_pub[13],
        server_pub[14],
        server_pub[15],
    ]
}

#[inline(always)]
const fn hs_transcript_q3(server_pub: &[u8; 32]) -> [u8; 16] {
    [
        server_pub[16],
        server_pub[17],
        server_pub[18],
        server_pub[19],
        server_pub[20],
        server_pub[21],
        server_pub[22],
        server_pub[23],
        server_pub[24],
        server_pub[25],
        server_pub[26],
        server_pub[27],
        server_pub[28],
        server_pub[29],
        server_pub[30],
        server_pub[31],
    ]
}

/// The bytes both sides bind into every record's AAD: the ephemeral public keys in
/// a fixed order (client, then server), as THIS side observed them. An active MITM
/// that relays different ephemerals to each leg produces different transcripts, so
/// its records fail to open on the far side. The identity handshake binds the same
/// bytes, which are also what its peers sign.
pub(crate) const fn transcript(client_pub: &[u8; 32], server_pub: &[u8; 32]) -> [u8; 64] {
    let [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15] =
        hs_transcript_q0(client_pub);
    let [c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31] =
        hs_transcript_q1(client_pub);
    let [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] =
        hs_transcript_q2(server_pub);
    let [s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] =
        hs_transcript_q3(server_pub);
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, s0, s1, s2, s3, s4, s5, s6, s7,
        s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25,
        s26, s27, s28, s29, s30, s31,
    ]
}

/// Run the client (initiator) side of the handshake over `stream` and return the
/// forward-secret [`SealedStream`]. Sends our ephemeral key first, then reads the
/// peer's.
///
/// # Errors
/// A socket error, a peer not speaking the handshake (bad magic/version), or a
/// non-contributory DH.
pub fn client_handshake<S: Read + Write>(
    mut stream: S,
    psk: &[u8; KEY_LEN],
) -> io::Result<SealedStream<S>> {
    let (secret, our_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &our_pub)?;
    let their_pub = read_hs_msg(&mut stream)?;
    // We are the client: our key is client_pub, theirs is server_pub.
    let key = agree(&secret, psk, &their_pub, &our_pub, &their_pub)?;
    // The record layer binds the TRANSCRIPT — the two ephemeral public keys as we
    // saw them — into every record's AAD, so a record is valid only for this
    // session and this direction. No hello exchange and no confirm record: the
    // agreement above already supplied the freshness and the key confirmation
    // those exist to provide for a bare PSK.
    Ok(SealedStream::with_transcript(
        stream,
        key,
        &transcript(&our_pub, &their_pub),
        true,
    ))
}

/// Run the server (responder) side of the handshake over `stream`: read the
/// client's ephemeral key, reply with ours, and return the forward-secret
/// [`SealedStream`].
///
/// # Errors
/// A socket error, a peer not speaking the handshake (bad magic/version), or a
/// non-contributory DH.
pub fn server_handshake<S: Read + Write>(
    mut stream: S,
    psk: &[u8; KEY_LEN],
) -> io::Result<SealedStream<S>> {
    // The client speaks first.
    let their_pub = read_hs_msg(&mut stream)?;
    let (secret, our_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &our_pub)?;
    // They are the client, we are the server.
    let key = agree(&secret, psk, &their_pub, &their_pub, &our_pub)?;
    Ok(SealedStream::with_transcript(
        stream,
        key,
        &transcript(&their_pub, &our_pub),
        false,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{TcpListener, TcpStream};

    /// Recorded from this crate over the `sha2` crate (0.10.9) on 2026-10-15, before
    /// it moved to `astream-digest`, and unchanged over it and over the HMAC that
    /// moved there after it: both ends of a handshake must derive this key, so
    /// nothing under it may change unless the key does not. The HKDF's own pins (RFC
    /// 5869, and this same answer from the raw bytes) are astream-digest's; this one
    /// is the INFO layout's (`build_hs_info`: the label, then the two ephemerals in
    /// role order), which only this crate builds. Negative control: the ephemerals
    /// swapped are another key (`transcript_role_order_changes_the_key`), and so is
    /// another PSK, below.
    #[test]
    fn the_session_key_is_the_recorded_answer() {
        let key = derive_session_key(&[9u8; KEY_LEN], &[7u8; 32], &[1u8; 32], &[2u8; 32]);
        let expected = hex("0d5a777ebe43ec2044188fa05d226c609e80df383b6cfce2b3cfa2bacbc64c24");
        assert_eq!(key.as_slice(), expected.as_slice());
        let other = derive_session_key(&[8u8; KEY_LEN], &[7u8; 32], &[1u8; 32], &[2u8; 32]);
        assert_ne!(other.as_slice(), expected.as_slice());
    }

    #[test]
    fn a_bad_magic_version_short_or_low_order_handshake_message_is_refused() {
        let point = [0x42u8; 32];
        let good = build_hs_msg(&point);
        assert_eq!(read_hs_msg(&mut &good[..]).unwrap(), point);
        let mut rows = Vec::new();
        for i in 0..HS_MAGIC.len() {
            let mut bad = good;
            bad[i] ^= 0x80;
            rows.push((
                format!("magic byte {i}"),
                bad.to_vec(),
                io::ErrorKind::InvalidData,
            ));
        }
        for ver in [HS_VERSION - 1, HS_VERSION + 1] {
            let mut bad = good;
            bad[4] = ver;
            rows.push((
                format!("version {ver}"),
                bad.to_vec(),
                io::ErrorKind::InvalidData,
            ));
        }
        rows.push((
            "a short message".to_string(),
            good[..HS_MSG_LEN - 1].to_vec(),
            io::ErrorKind::UnexpectedEof,
        ));
        for (what, msg, kind) in rows {
            assert_eq!(
                read_hs_msg(&mut &msg[..]).unwrap_err().kind(),
                kind,
                "{what}"
            );
        }

        // u = 0 and u = 1 are small-order points: X25519 against either is zero
        // whatever our secret, so a peer sending one would choose the DH input of
        // the session key. Every half, the identity handshake's included, refuses
        // it before any record.
        let mut one = [0u8; 32];
        one[0] = 1;
        for low in [[0u8; 32], one] {
            let peer = || crate::tests::Scripted::new(build_hs_msg(&low).to_vec());
            let psk = [0x42; KEY_LEN];
            let refusals = vec![
                ("server", server_handshake(peer(), &psk).err()),
                ("client", client_handshake(peer(), &psk).err()),
            ];
            #[cfg(feature = "identity")]
            let refusals = {
                let me = crate::IdentityKeypair::from_seed([3; 32]);
                let server = crate::server_identity_handshake(peer(), &me, &[me.public()]);
                let client = crate::client_identity_handshake(peer(), &me, &me.public());
                let mut all = refusals;
                all.extend([
                    ("identity server", server.err()),
                    ("identity client", client.err()),
                ]);
                all
            };
            for (side, got) in refusals {
                let e = got.unwrap_or_else(|| panic!("{side} accepted u = {}", low[0]));
                assert_eq!(e.kind(), io::ErrorKind::InvalidData, "{side}");
            }
        }
    }

    #[test]
    fn each_half_seals_under_the_agreed_key_and_transcript_with_a_fresh_ephemeral() {
        // Pins the forward-secret wire against a scripted peer that holds its own
        // X25519 secret, as `every_record_aad_is_hello_client_hello_server_direction_seq`
        // pins the PSK wire: each half seals its first record under
        // HKDF(psk, X25519, label ‖ client_pub ‖ server_pub) with the AAD
        // client_pub ‖ server_pub ‖ direction ‖ seq (0x01 client→server, 0x02
        // server→client), and draws a fresh ephemeral for every handshake.
        let psk = [0x42; KEY_LEN];
        let peer = StaticSecret::from([0x5a; 32]);
        let peer_pub = *PublicKey::from(&peer).as_bytes();
        let mut ephemerals = Vec::new();
        for is_client in [true, true, false, false] {
            let script = crate::tests::Scripted::new(build_hs_msg(&peer_pub).to_vec());
            let mut half = if is_client {
                client_handshake(script, &psk)
            } else {
                server_handshake(script, &psk)
            }
            .unwrap();
            half.write_all(b"first record").unwrap();
            let sent = &half.get_ref().sent;
            let ours = read_hs_msg(&mut &sent[..HS_MSG_LEN]).unwrap();
            let (client_pub, server_pub, direction) = if is_client {
                (ours, peer_pub, 0x01)
            } else {
                (peer_pub, ours, 0x02)
            };
            let dh = peer.diffie_hellman(&PublicKey::from(ours));
            let key = derive_session_key(&psk, dh.as_bytes(), &client_pub, &server_pub);
            let aad = [
                &client_pub[..],
                &server_pub[..],
                &[direction][..],
                &0u64.to_le_bytes()[..],
            ]
            .concat();
            let record = &sent[HS_MSG_LEN + 4..];
            assert_eq!(
                crate::open(&key, &aad, record).ok().as_deref(),
                Some(&b"first record"[..]),
                "client: {is_client}"
            );
            ephemerals.push(ours);
        }
        assert_ne!(ephemerals[0], ephemerals[1], "a fresh client ephemeral");
        assert_ne!(ephemerals[2], ephemerals[3], "a fresh server ephemeral");
    }

    #[test]
    fn transcript_role_order_changes_the_key() {
        // Reflection resistance at the KDF: swapping client/server pub derives a
        // different key, so a reflected transcript cannot agree.
        let psk = [9u8; KEY_LEN];
        let dh = [7u8; 32];
        let a = [1u8; 32];
        let b = [2u8; 32];
        assert_ne!(
            derive_session_key(&psk, &dh, &a, &b),
            derive_session_key(&psk, &dh, &b, &a)
        );
    }

    // Drive both handshake halves over a real loopback socket pair, then exchange a
    // sealed frame each way. Returns Ok(()) iff the whole path works.
    fn run_handshake(client_psk: [u8; KEY_LEN], server_psk: [u8; KEY_LEN]) -> io::Result<()> {
        let listener = TcpListener::bind("127.0.0.1:0")?;
        let addr = listener.local_addr()?;
        let server = std::thread::spawn(move || -> io::Result<()> {
            let (sock, _) = listener.accept()?;
            let mut s = server_handshake(sock, &server_psk)?;
            // Read the client's sealed frame, reply with our own.
            let mut buf = [0u8; 5];
            s.read_exact(&mut buf)?;
            assert_eq!(&buf, b"hello");
            s.write_all(b"world")?;
            s.flush()
        });
        let sock = TcpStream::connect(addr)?;
        let mut c = client_handshake(sock, &client_psk)?;
        c.write_all(b"hello")?;
        c.flush()?;
        let mut buf = [0u8; 5];
        c.read_exact(&mut buf)?;
        assert_eq!(&buf, b"world");
        server.join().unwrap()
    }

    #[test]
    fn matching_psk_agrees_and_talks() {
        run_handshake([0x42; KEY_LEN], [0x42; KEY_LEN]).expect("matching PSK must agree");
    }

    #[test]
    fn mismatched_psk_cannot_talk() {
        // The DH succeeds but the derived keys differ, so the first sealed frame
        // fails to open — the sealed exchange errors on one or both sides.
        let mut wrong = [0x42; KEY_LEN];
        wrong[0] ^= 0xff;
        assert!(
            run_handshake([0x42; KEY_LEN], wrong).is_err(),
            "a mismatched PSK must not establish a working session"
        );
    }

    fn hex(s: &str) -> Vec<u8> {
        assert!(s.len().is_multiple_of(2), "an odd hex digit: {s}");
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
            .collect()
    }
}
