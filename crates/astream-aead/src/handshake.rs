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
//! HMAC-SHA256 / HKDF-SHA256, composed here over the workspace `sha2` exactly as
//! `astream-cap` owns its HMAC. The ONE primitive we delegate is the raw X25519
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
use sha2::{Digest, Sha256};
use std::io::{self, Read, Write};
use x25519_dalek::{PublicKey, SharedSecret, StaticSecret};

const SHA256_BLOCK: usize = 64;
const SHA256_OUT: usize = 32;

/// HMAC-SHA256 (RFC 2104), composed over the workspace `sha2`. Ours, not a
/// dependency — the same stance `astream-cap` takes.
fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; SHA256_OUT] {
    // Derive the block-sized key K0: hash an over-long key, else right-zero-pad.
    let mut k0 = [0u8; SHA256_BLOCK];
    if key.len() > SHA256_BLOCK {
        k0[..SHA256_OUT].copy_from_slice(&Sha256::digest(key));
    } else {
        k0[..key.len()].copy_from_slice(key);
    }
    let mut ipad = [0x36u8; SHA256_BLOCK];
    let mut opad = [0x5cu8; SHA256_BLOCK];
    for i in 0..SHA256_BLOCK {
        ipad[i] ^= k0[i];
        opad[i] ^= k0[i];
    }
    let inner = {
        let mut h = Sha256::new();
        h.update(ipad);
        h.update(msg);
        h.finalize()
    };
    let mut h = Sha256::new();
    h.update(opad);
    h.update(inner);
    let mut out = [0u8; SHA256_OUT];
    out.copy_from_slice(&h.finalize());
    out
}

/// HKDF-SHA256 (RFC 5869) producing exactly 32 bytes (a single expand block,
/// L = 32 ≤ 255·32). Extract then Expand, ours over `hmac_sha256`.
pub(crate) fn hkdf_sha256_32(salt: &[u8], ikm: &[u8], info: &[u8]) -> [u8; 32] {
    // Extract.
    let mut prk = hmac_sha256(salt, ikm);
    // Expand, N = 1: T(1) = HMAC(PRK, T(0)=<empty> ‖ info ‖ 0x01).
    let mut t1_input = Vec::with_capacity(info.len() + 1);
    t1_input.extend_from_slice(info);
    t1_input.push(0x01);
    let okm = hmac_sha256(&prk, &t1_input);
    prk.fill(0); // wipe the intermediate pseudo-random key
    core::hint::black_box(&mut prk);
    okm
}

const HS_MAGIC: [u8; 4] = *b"aSH1";
const HS_VERSION: u8 = 1;
const HS_MSG_LEN: usize = 4 + 1 + 32; // magic ‖ version ‖ ephemeral pubkey
const HS_LABEL: &[u8] = b"astream-handshake-v1";

pub(crate) fn write_hs_msg<W: Write>(w: &mut W, pubkey: &[u8; 32]) -> io::Result<()> {
    let mut msg = [0u8; HS_MSG_LEN];
    msg[..4].copy_from_slice(&HS_MAGIC);
    msg[4] = HS_VERSION;
    msg[5..].copy_from_slice(pubkey);
    w.write_all(&msg)?;
    w.flush()
}

pub(crate) fn read_hs_msg<R: Read>(r: &mut R) -> io::Result<[u8; 32]> {
    let mut msg = [0u8; HS_MSG_LEN];
    r.read_exact(&mut msg)?;
    if msg[..4] != HS_MAGIC || msg[4] != HS_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream handshake: bad magic/version (peer not speaking the sealed handshake)",
        ));
    }
    let mut pk = [0u8; 32];
    pk.copy_from_slice(&msg[5..]);
    Ok(pk)
}

/// A fresh ephemeral X25519 keypair, seeded from the OS CSPRNG (`getrandom`, which
/// we already depend on). We use `StaticSecret` (byte-seedable) as a one-shot
/// ephemeral and drop it after the single DH — `x25519-dalek`'s `zeroize` wipes it
/// on drop, and we wipe our transient seed too.
pub(crate) fn ephemeral() -> (StaticSecret, [u8; 32]) {
    let mut seed = [0u8; 32];
    getrandom::getrandom(&mut seed).expect("OS CSPRNG unavailable");
    let secret = StaticSecret::from(seed);
    seed.fill(0);
    core::hint::black_box(&mut seed);
    let public = *PublicKey::from(&secret).as_bytes();
    (secret, public)
}

/// The session key: HKDF over the PSK (salt/authenticator) and the DH secret
/// (IKM/forward-secrecy), transcript-bound to both ephemeral keys in ROLE order.
fn derive_session_key(
    psk: &[u8; KEY_LEN],
    dh: &[u8; 32],
    client_pub: &[u8; 32],
    server_pub: &[u8; 32],
) -> [u8; KEY_LEN] {
    let mut info = Vec::with_capacity(HS_LABEL.len() + 64);
    info.extend_from_slice(HS_LABEL);
    info.extend_from_slice(client_pub);
    info.extend_from_slice(server_pub);
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

/// The bytes both sides bind into every record's AAD: the ephemeral public keys in
/// a fixed order (client, then server), as THIS side observed them. An active MITM
/// that relays different ephemerals to each leg produces different transcripts, so
/// its records fail to open on the far side. The identity handshake binds the same
/// bytes, which are also what its peers sign.
pub(crate) fn transcript(client_pub: &[u8; 32], server_pub: &[u8; 32]) -> [u8; 64] {
    let mut t = [0u8; 64];
    t[..32].copy_from_slice(client_pub);
    t[32..].copy_from_slice(server_pub);
    t
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
    let (secret, our_pub) = ephemeral();
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
    let (secret, our_pub) = ephemeral();
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

    #[test]
    fn hmac_sha256_matches_rfc4231_case2() {
        // RFC 4231 Test Case 2.
        let mac = hmac_sha256(b"Jefe", b"what do ya want for nothing?");
        let expected = hex("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
        assert_eq!(mac.as_slice(), expected.as_slice());
    }

    #[test]
    fn hkdf_sha256_matches_rfc5869_a1() {
        // RFC 5869 Appendix A.1 (SHA-256); we emit the first 32 bytes of the OKM.
        let ikm = [0x0bu8; 22];
        let salt = hex("000102030405060708090a0b0c");
        let info = hex("f0f1f2f3f4f5f6f7f8f9");
        let okm = hkdf_sha256_32(&salt, &ikm, &info);
        let expected = hex("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf3");
        assert_eq!(okm.as_slice(), expected.as_slice());
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
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
            .collect()
    }
}
