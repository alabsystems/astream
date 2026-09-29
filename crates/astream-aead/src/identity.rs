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
//! HKDF/HMAC and X25519 glue; the only delegated primitive here is the raw
//! Ed25519 sign/verify, to the vetted `ed25519-dalek`.

use crate::handshake::{
    ephemeral, hkdf_sha256_32, read_hs_msg, transcript as record_binding, write_hs_msg,
    x25519_shared,
};
use crate::{SealedStream, KEY_LEN};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use std::io::{self, Read, Write};

const ID_LABEL: &[u8] = b"astream-identity-v1";
const SIG_CTX_SERVER: &[u8] = b"astream-identity-v1 server-auth";
const SIG_CTX_CLIENT: &[u8] = b"astream-identity-v1 client-auth";
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
        getrandom::getrandom(&mut seed).expect("OS CSPRNG unavailable");
        let kp = Self::from_seed(seed);
        seed.fill(0);
        core::hint::black_box(&mut seed);
        kp
    }

    /// Load an identity from a stored 32-byte Ed25519 seed (a persisted host key).
    #[must_use]
    pub fn from_seed(seed: [u8; 32]) -> Self {
        IdentityKeypair {
            signing: SigningKey::from_bytes(&seed),
        }
    }

    /// This identity's public key — the value a peer pins (host key) or puts on
    /// its allow-list.
    #[must_use]
    pub fn public(&self) -> [u8; ID_PUB_LEN] {
        self.signing.verifying_key().to_bytes()
    }
}

/// The exact bytes each side signs: a role-tagged context over both ephemeral
/// public keys, in the fixed order (client then server) both sides agree on.
fn transcript(ctx: &[u8], ec_pub: &[u8; 32], es_pub: &[u8; 32]) -> Vec<u8> {
    let mut m = Vec::with_capacity(ctx.len() + 64);
    m.extend_from_slice(ctx);
    m.extend_from_slice(ec_pub);
    m.extend_from_slice(es_pub);
    m
}

/// Derive the session key from the ephemeral DH ONLY (identity keys never enter
/// the key schedule — that is what keeps forward secrecy under identity-key
/// compromise).
fn session_key(dh: &[u8; 32], ec_pub: &[u8; 32], es_pub: &[u8; 32]) -> [u8; KEY_LEN] {
    let mut info = Vec::with_capacity(ID_LABEL.len() + 64);
    info.extend_from_slice(ID_LABEL);
    info.extend_from_slice(ec_pub);
    info.extend_from_slice(es_pub);
    hkdf_sha256_32(&[], dh, &info)
}

/// Build an auth message: our identity public key followed by our signature over
/// the role-tagged ephemeral transcript.
fn auth_message(
    me: &IdentityKeypair,
    ctx: &[u8],
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
) -> [u8; AUTH_MSG_LEN] {
    let sig: Signature = me.signing.sign(&transcript(ctx, ec_pub, es_pub));
    let mut msg = [0u8; AUTH_MSG_LEN];
    msg[..ID_PUB_LEN].copy_from_slice(&me.public());
    msg[ID_PUB_LEN..].copy_from_slice(&sig.to_bytes());
    msg
}

/// Split a received auth message into (identity public key, signature).
fn split_auth(msg: &[u8; AUTH_MSG_LEN]) -> ([u8; ID_PUB_LEN], [u8; SIG_LEN]) {
    let mut id = [0u8; ID_PUB_LEN];
    let mut sig = [0u8; SIG_LEN];
    id.copy_from_slice(&msg[..ID_PUB_LEN]);
    sig.copy_from_slice(&msg[ID_PUB_LEN..]);
    (id, sig)
}

/// Strictly verify `sig` over the role-tagged transcript under `id_pub`.
/// `verify_strict` rejects small-order/non-canonical keys and malleable sigs.
fn verify_auth(
    id_pub: &[u8; ID_PUB_LEN],
    sig: &[u8; SIG_LEN],
    ctx: &[u8],
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
) -> io::Result<()> {
    let vk = VerifyingKey::from_bytes(id_pub).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "astream identity: malformed key",
        )
    })?;
    let signature = Signature::from_bytes(sig);
    vk.verify_strict(&transcript(ctx, ec_pub, es_pub), &signature)
        .map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "astream identity: signature verification failed (MITM or wrong identity)",
            )
        })
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
    let (secret, ec_pub) = ephemeral();
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
    let (secret, es_pub) = ephemeral();
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
    if !authorized_clients.contains(&client_id) {
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

    // Drive both identity halves over a real loopback socket pair with the given
    // trust config, then exchange a sealed frame each way. The server thread
    // returns Ok(authenticated_client_id) or the handshake error.
    fn run(
        server: &'static IdentityKeypair,
        authorized: Vec<[u8; 32]>,
        client: &'static IdentityKeypair,
        expected_server: [u8; 32],
    ) -> io::Result<[u8; 32]> {
        let listener = TcpListener::bind("127.0.0.1:0")?;
        let addr = listener.local_addr()?;
        let jh = std::thread::spawn(move || -> io::Result<[u8; 32]> {
            let (sock, _) = listener.accept()?;
            let (mut s, client_id) = server_identity_handshake(sock, server, &authorized)?;
            let mut buf = [0u8; 5];
            s.read_exact(&mut buf)?;
            assert_eq!(&buf, b"hello");
            s.write_all(b"world")?;
            s.flush()?;
            Ok(client_id)
        });
        let sock = TcpStream::connect(addr)?;
        let mut c = client_identity_handshake(sock, client, &expected_server)?;
        c.write_all(b"hello")?;
        c.flush()?;
        let mut buf = [0u8; 5];
        c.read_exact(&mut buf)?;
        assert_eq!(&buf, b"world");
        jh.join().unwrap()
    }

    fn keys() -> (&'static IdentityKeypair, &'static IdentityKeypair) {
        // Leaked so the loopback threads can borrow 'static; fine for a test.
        let server: &'static IdentityKeypair = Box::leak(Box::new(IdentityKeypair::generate()));
        let client: &'static IdentityKeypair = Box::leak(Box::new(IdentityKeypair::generate()));
        (server, client)
    }

    #[test]
    fn mutual_authentication_succeeds_and_returns_the_client_id() {
        let (server, client) = keys();
        let got = run(server, vec![client.public()], client, server.public())
            .expect("mutual auth must succeed");
        assert_eq!(
            got,
            client.public(),
            "server learns the authenticated client id"
        );
    }

    #[test]
    fn client_rejects_a_server_that_is_not_the_pinned_host_key() {
        let (server, client) = keys();
        let impostor = server.public()[0] ^ 0xff; // pin a different key
        let mut wrong = server.public();
        wrong[0] = impostor;
        let r = run(server, vec![client.public()], client, wrong);
        assert!(r.is_err(), "client must reject an unpinned server");
    }

    #[test]
    fn server_rejects_an_unauthorized_client() {
        let (server, client) = keys();
        // Allow-list does NOT contain the client's identity.
        let stranger = IdentityKeypair::generate();
        let r = run(server, vec![stranger.public()], client, server.public());
        assert!(
            r.is_err(),
            "server must reject a client not on the allow-list"
        );
    }

    #[test]
    fn a_forged_client_signature_is_rejected() {
        // verify_auth, directly: a tampered signature under a genuine id fails.
        let (_, client) = keys();
        let ec = [1u8; 32];
        let es = [2u8; 32];
        let mut msg = auth_message(client, SIG_CTX_CLIENT, &ec, &es);
        msg[ID_PUB_LEN] ^= 0x01; // flip a signature byte
        let (id, sig) = split_auth(&msg);
        assert!(verify_auth(&id, &sig, SIG_CTX_CLIENT, &ec, &es).is_err());
        // And a role-context mismatch (reflection) fails too.
        let good = auth_message(client, SIG_CTX_CLIENT, &ec, &es);
        let (id2, sig2) = split_auth(&good);
        assert!(verify_auth(&id2, &sig2, SIG_CTX_SERVER, &ec, &es).is_err());
    }
}
