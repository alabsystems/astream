// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Rung 9 — external identity authority, certificate-authenticated SIGMA,
//! overlapping host-key/certificate rotation, and external `ssh-agent` signing.
//!
//! Rung 8 ([`crate::identity`]) authenticates peers with locally pinned host keys
//! and static client Ed25519 allow-lists. This module binds transport identity to an
//! **external authority** (`docs/ROADMAP.md` §1, `docs/DESIGN-astream-term.md` §11):
//!
//! 1. **External `ssh-agent` key custody ([`SshAgentSigner`], [`IdentitySigner`]):**
//!    speaks the OpenSSH `SSH_AUTH_SOCK` binary wire protocol (`draft-miller-ssh-agent`,
//!    `SSH_AGENTC_REQUEST_IDENTITIES` + `SSH_AGENTC_SIGN_REQUEST` for `"ssh-ed25519"`)
//!    over a Unix-domain socket with zero `unsafe` and zero new dependencies, so
//!    long-term Ed25519 private keys stay inside the external agent process and never
//!    enter `astream` memory. Every signature returned by an agent is strictly verified
//!    against the expected Ed25519 verifying key before leaving [`SshAgentSigner::sign`].
//! 2. **CA-signed identity & host certificates ([`IdentityCertificate`],
//!    [`CertificateAuthority`]):** canonical `ACRT` v1 binary certificates signed by an
//!    external Ed25519 Certificate Authority (an SSH CA or an OIDC-token-to-short-lived-cert
//!    issuer), binding a subject Ed25519 public key to a role ([`CertRole::Host`] or
//!    [`CertRole::Client`]), a named principal (`h-alice`, `a-worker7`, `n-...`, `s-...`),
//!    an optional authority/OIDC issuer URI, a strictly positive `serial`, and a bounded
//!    `[valid_after_ms, valid_before_ms)` validity window.
//! 3. **Key distribution, multi-root CA rotation, monotonic KRL revocation, and
//!    zero-downtime overlapping host rotation ([`CertTrustStore`], [`SharedCertTrust`],
//!    [`HostCertRotator`]):** trust stores accept overlapping root CAs during CA key
//!    rollover, enforce bounded certificate lifetimes, and advance revocation epochs and
//!    serial floors monotonically (refusing KRL rollback); [`HostCertRotator`] rotates a
//!    live listener's host signer + certificate with an explicit retiring-key overlap
//!    window.
//! 4. **Mutual certificate-authenticated SIGMA ([`client_cert_handshake`],
//!    [`server_cert_handshake`]):** ephemeral X25519 alone keys [`SealedStream`] (so
//!    forward secrecy survives compromise of client, host, and CA private keys alike),
//!    while M3 and M4 carry AEAD-sealed `ACRT` certificates and strict Ed25519 signatures
//!    over the role-tagged ephemeral transcript bound to the SHA-256 digests of the
//!    exchanged certificates.

use crate::handshake::{
    ephemeral, hkdf_sha256_32, read_hs_msg, transcript as record_binding, write_hs_msg,
    x25519_shared,
};
use crate::identity::{IdentityKeypair, ID_PUB_LEN};
use crate::{SealedStream, KEY_LEN};
use astream_digest::{ct_eq, Sha256};
use ed25519_dalek::{Signature, VerifyingKey};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
#[cfg(unix)]
use std::time::Duration;

#[cfg(clean_islands)]
#[path = "cert_island.rs"]
mod cert_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{cert_epoch_advance, cert_validity_clamp};
#[cfg(clean_islands)]
pub use cert_island::{cert_epoch_advance, cert_validity_clamp};

contract_fn! {
    /// Verified check that `observed` has reached `threshold` (`threshold <= observed`),
    /// linked via `clean-kernel-defeq` to `cert_horizon_reached_isl`.
    #[must_use]
    pub const fn cert_horizon_reached(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

contract_fn! {
    /// Verified check that an `ACRT` certificate carries wire format version 1 (`ver == 1`),
    /// linked via `clean-kernel-defeq` to `cert_wire_version_valid_isl`.
    #[must_use]
    pub const fn cert_wire_version_valid(ver: u8) -> bool
    clauses [ensures result == (ver == 1)]
    {
        ver == 1
    }
}

/// Four-byte magic prefix (`"ACRT"`) of a canonical `astream` certificate.
pub const CERT_WIRE_MAGIC: [u8; 4] = *b"ACRT";
/// Wire format version for `ACRT` certificates.
pub const CERT_WIRE_VERSION: u8 = 1;
/// Hard ceiling on certificate validity span (`30` days in milliseconds).
pub const MAX_CERT_VALIDITY_CAP_MS: u64 = 30 * 86_400_000;
/// Maximum byte length of a certificate's `principal` string.
pub const MAX_CERT_PRINCIPAL_LEN: usize = 64;
/// Maximum byte length of a certificate's `issuer` URI/identifier.
pub const MAX_CERT_ISSUER_LEN: usize = 128;
/// Maximum number of concurrent root CA keys in a [`CertTrustStore`].
pub const MAX_TRUSTED_CAS: usize = 16;
/// Maximum number of revoked serials in one [`CertTrustStore`] KRL snapshot.
pub const MAX_CERT_REVOKED_SERIALS: usize = 65_536;
/// Minimum encoded wire byte length of an [`IdentityCertificate`] (1-byte principal, empty issuer).
pub const MIN_CERT_WIRE_LEN: usize = 161;
/// Maximum encoded wire byte length of an [`IdentityCertificate`] (64-byte principal, 128-byte issuer).
pub const MAX_CERT_WIRE_LEN: usize = 160 + MAX_CERT_PRINCIPAL_LEN + MAX_CERT_ISSUER_LEN;

const CERT_SIGN_DOMAIN: &[u8] = b"astream-cert-v1\0";
const CERT_SIGMA_LABEL: &[u8] = b"astream-cert-sigma-v1";
const CERT_SIG_CTX_SERVER: &[u8] = b"astream-cert-sigma-v1 server-auth";
const CERT_SIG_CTX_CLIENT: &[u8] = b"astream-cert-sigma-v1 client-auth";
const CERT_SIG_LEN: usize = 64;

const SSH_AGENT_FAILURE: u8 = 5;
const SSH_AGENTC_REQUEST_IDENTITIES: u8 = 11;
const SSH_AGENT_IDENTITIES_ANSWER: u8 = 12;
const SSH_AGENTC_SIGN_REQUEST: u8 = 13;
const SSH_AGENT_SIGN_RESPONSE: u8 = 14;
const SSH_ED25519_ALG: &[u8] = b"ssh-ed25519";
const MAX_SSH_AGENT_FRAME: usize = 64 * 1024;
#[cfg(unix)]
const SSH_AGENT_TIMEOUT: Duration = Duration::from_secs(5);

/// Role bound into an [`IdentityCertificate`]: prevents a client certificate from
/// authenticating as a broker host and vice versa.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CertRole {
    /// Broker / server host certificate (`1` on wire).
    Host = 1,
    /// Client / peer user or workload certificate (`2` on wire).
    Client = 2,
}

impl CertRole {
    const fn to_wire(self) -> u8 {
        match self {
            CertRole::Host => 1,
            CertRole::Client => 2,
        }
    }

    const fn from_wire(b: u8) -> Option<Self> {
        match b {
            1 => Some(CertRole::Host),
            2 => Some(CertRole::Client),
            _ => None,
        }
    }
}

fn validate_cert_principal(principal: &str) -> io::Result<()> {
    if principal.is_empty() || principal.len() > MAX_CERT_PRINCIPAL_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert: principal must be 1..=64 ASCII bytes",
        ));
    }
    let mut cur = principal.as_bytes();
    while let Some((&b, rest)) = cur.split_first() {
        cur = rest;
        if !b.is_ascii()
            || b.is_ascii_control()
            || b.is_ascii_whitespace()
            || b == b':'
            || b == b','
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: principal contains forbidden delimiter or non-ASCII byte",
            ));
        }
    }
    Ok(())
}

fn validate_cert_issuer(issuer: &str) -> io::Result<()> {
    if issuer.len() > MAX_CERT_ISSUER_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert: issuer exceeds 128 ASCII bytes",
        ));
    }
    let mut cur = issuer.as_bytes();
    while let Some((&b, rest)) = cur.split_first() {
        cur = rest;
        if !b.is_ascii() || b.is_ascii_control() || b == b'\0' {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: issuer contains non-printable ASCII byte",
            ));
        }
    }
    Ok(())
}

fn verify_ed25519_strict(
    pubkey: &[u8; ID_PUB_LEN],
    msg: &[u8],
    sig_bytes: &[u8; CERT_SIG_LEN],
    err_msg: &'static str,
) -> io::Result<()> {
    let vk = match VerifyingKey::from_bytes(pubkey) {
        Ok(vk) => vk,
        Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidData, err_msg)),
    };
    let sig = Signature::from_bytes(sig_bytes);
    match vk.verify_strict(msg, &sig) {
        Ok(()) => Ok(()),
        Err(_) => Err(io::Error::new(io::ErrorKind::InvalidData, err_msg)),
    }
}

fn ensure_canonical_pubkey(pubkey: &[u8; ID_PUB_LEN], err_msg: &'static str) -> io::Result<()> {
    match VerifyingKey::from_bytes(pubkey) {
        Ok(_) => Ok(()),
        Err(_) => Err(io::Error::new(io::ErrorKind::InvalidData, err_msg)),
    }
}

// ============================================================================
// SSH-Agent Wire Protocol & Signer (`SSH_AUTH_SOCK`, zero unsafe, zero new deps)
// ============================================================================

fn push_ssh_string(out: &mut Vec<u8>, bytes: &[u8]) {
    let len = bytes.len() as u32;
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(bytes);
}

fn read_ssh_u32(cursor: &mut &[u8]) -> io::Result<u32> {
    let Some((head, rest)) = cursor.split_first_chunk::<4>() else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: truncated u32 field",
        ));
    };
    *cursor = rest;
    Ok(u32::from_be_bytes(*head))
}

fn read_ssh_string<'a>(cursor: &mut &'a [u8]) -> io::Result<&'a [u8]> {
    let len = read_ssh_u32(cursor)? as usize;
    let Some((body, rest)) = cursor.split_at_checked(len) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: truncated string field",
        ));
    };
    *cursor = rest;
    Ok(body)
}

/// Encode the canonical 51-byte OpenSSH `"ssh-ed25519"` public-key blob for `pubkey`.
#[must_use]
pub fn encode_ssh_ed25519_key_blob(pubkey: &[u8; ID_PUB_LEN]) -> Vec<u8> {
    let mut blob = Vec::with_capacity(51);
    push_ssh_string(&mut blob, SSH_ED25519_ALG);
    push_ssh_string(&mut blob, pubkey);
    blob
}

/// Parse an OpenSSH public-key blob; returns `Some(pubkey)` if it is a canonical
/// `"ssh-ed25519"` key blob and `None` for any other algorithm (e.g. RSA/ECDSA).
#[must_use]
pub fn decode_ssh_ed25519_key_blob(mut blob: &[u8]) -> Option<[u8; ID_PUB_LEN]> {
    let Ok(alg) = read_ssh_string(&mut blob) else {
        return None;
    };
    if alg != SSH_ED25519_ALG {
        return None;
    }
    let Ok(raw_key) = read_ssh_string(&mut blob) else {
        return None;
    };
    if !blob.is_empty() {
        return None;
    }
    let (pk, tail) = raw_key.split_first_chunk::<ID_PUB_LEN>()?;
    if !tail.is_empty() {
        return None;
    }
    if VerifyingKey::from_bytes(pk).is_err() {
        return None;
    }
    Some(*pk)
}

fn write_agent_frame<W: Write>(w: &mut W, payload: &[u8]) -> io::Result<()> {
    if payload.is_empty() || payload.len() > MAX_SSH_AGENT_FRAME {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "ssh-agent: invalid outgoing frame size",
        ));
    }
    let len = (payload.len() as u32).to_be_bytes();
    w.write_all(&len)?;
    w.write_all(payload)?;
    w.flush()
}

fn read_agent_frame<R: Read>(r: &mut R) -> io::Result<Vec<u8>> {
    let read_exact_op: fn(&mut R, &mut [u8]) -> io::Result<()> = Read::read_exact;
    let mut len_buf = [0u8; 4];
    read_exact_op(r, &mut len_buf)?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len == 0 || len > MAX_SSH_AGENT_FRAME {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: response frame size out of bounds",
        ));
    }
    let mut body = vec![0u8; len];
    read_exact_op(r, &mut body)?;
    Ok(body)
}

/// Query `SSH_AGENTC_REQUEST_IDENTITIES` over any `Read + Write` stream (e.g. a Unix
/// `SSH_AUTH_SOCK` socket or a Windows `\\.\pipe\openssh-ssh-agent` named pipe) and
/// return all canonical `"ssh-ed25519"` `(pubkey, comment)` pairs.
///
/// # Errors
/// Fails on transport I/O error, `SSH_AGENT_FAILURE`, or malformed agent wire framing.
pub fn ssh_agent_list_over<S: Read + Write>(
    stream: &mut S,
) -> io::Result<Vec<([u8; ID_PUB_LEN], String)>> {
    write_agent_frame(stream, &[SSH_AGENTC_REQUEST_IDENTITIES])?;
    let reply = read_agent_frame(stream)?;
    let mut cur = reply.as_slice();
    let Some((&msg_type, rest)) = cur.split_first() else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: empty reply",
        ));
    };
    cur = rest;
    if msg_type == SSH_AGENT_FAILURE {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "ssh-agent: agent refused identity listing",
        ));
    }
    if msg_type != SSH_AGENT_IDENTITIES_ANSWER {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: unexpected reply tag for REQUEST_IDENTITIES",
        ));
    }
    let count = read_ssh_u32(&mut cur)? as usize;
    if count > 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: identity count exceeds bound",
        ));
    }
    let mut out = Vec::new();
    let mut idx = 0usize;
    while idx < count {
        let key_blob = read_ssh_string(&mut cur)?;
        let comment_bytes = read_ssh_string(&mut cur)?;
        if let Some(pk) = decode_ssh_ed25519_key_blob(key_blob) {
            let comment = String::from_utf8_lossy(comment_bytes).into_owned();
            out.push((pk, comment));
        }
        idx = idx.saturating_add(1);
    }
    if !cur.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: trailing bytes in IDENTITIES_ANSWER",
        ));
    }
    Ok(out)
}

/// Send `SSH_AGENTC_SIGN_REQUEST` for `pubkey` and `message` over any `Read + Write`
/// agent stream and strictly verify the returned 64-byte `"ssh-ed25519"` signature
/// under `pubkey` before returning it.
///
/// # Errors
/// Fails on transport I/O error, `SSH_AGENT_FAILURE`, malformed wire framing, or
/// strict Ed25519 verification failure.
pub fn ssh_agent_sign_over<S: Read + Write>(
    stream: &mut S,
    pubkey: &[u8; ID_PUB_LEN],
    message: &[u8],
) -> io::Result<[u8; CERT_SIG_LEN]> {
    if message.len() > 32 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "ssh-agent: sign message exceeds 32 KiB bound",
        ));
    }
    let key_blob = encode_ssh_ed25519_key_blob(pubkey);
    let cap = 13usize
        .saturating_add(key_blob.len())
        .saturating_add(message.len());
    let mut req = Vec::with_capacity(cap);
    req.push(SSH_AGENTC_SIGN_REQUEST);
    push_ssh_string(&mut req, &key_blob);
    push_ssh_string(&mut req, message);
    req.extend_from_slice(&0u32.to_be_bytes());
    write_agent_frame(stream, &req)?;

    let reply = read_agent_frame(stream)?;
    let mut cur = reply.as_slice();
    let Some((&msg_type, rest)) = cur.split_first() else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: empty sign response",
        ));
    };
    cur = rest;
    if msg_type == SSH_AGENT_FAILURE {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "ssh-agent: agent refused signing request",
        ));
    }
    if msg_type != SSH_AGENT_SIGN_RESPONSE {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: unexpected reply tag for SIGN_REQUEST",
        ));
    }
    let mut sig_blob = read_ssh_string(&mut cur)?;
    if !cur.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: trailing bytes in SIGN_RESPONSE",
        ));
    }
    let alg = read_ssh_string(&mut sig_blob)?;
    if alg != SSH_ED25519_ALG {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: sign response algorithm is not ssh-ed25519",
        ));
    }
    let raw_sig = read_ssh_string(&mut sig_blob)?;
    if !sig_blob.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: malformed ssh-ed25519 signature blob",
        ));
    }
    let Some((sig_ref, sig_tail)) = raw_sig.split_first_chunk::<CERT_SIG_LEN>() else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: malformed ssh-ed25519 signature blob",
        ));
    };
    if !sig_tail.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "ssh-agent: malformed ssh-ed25519 signature blob",
        ));
    }
    let sig = *sig_ref;
    // Verify the agent's returned signature under `pubkey` before trusting it, so a
    // faulty or untrusted agent socket can never inject a wrong-key or malleable sig.
    verify_ed25519_strict(
        pubkey,
        message,
        &sig,
        "ssh-agent: returned signature failed strict Ed25519 verification",
    )?;
    Ok(sig)
}

/// External Ed25519 signer backed by an OpenSSH `ssh-agent` Unix socket (`SSH_AUTH_SOCK`).
///
/// Holds only the socket path and the 32-byte public key; the Ed25519 private seed
/// stays inside the external agent process and never enters `astream` memory.
#[derive(Debug, Clone)]
pub struct SshAgentSigner {
    sock_path: PathBuf,
    pubkey: [u8; ID_PUB_LEN],
}

impl SshAgentSigner {
    /// Construct an [`SshAgentSigner`] for a known `pubkey` served at `sock_path`.
    #[must_use]
    pub fn new(sock_path: impl Into<PathBuf>, pubkey: [u8; ID_PUB_LEN]) -> Self {
        Self {
            sock_path: sock_path.into(),
            pubkey,
        }
    }

    /// List all canonical `"ssh-ed25519"` `(pubkey, comment)` identities offered by the
    /// agent listening on `sock_path`. Non-Ed25519 keys in the agent are skipped.
    ///
    /// # Errors
    /// Returns an error if connecting to `sock_path` fails or the agent speaks a malformed frame.
    #[cfg(unix)]
    pub fn list_identities(sock_path: &Path) -> io::Result<Vec<([u8; ID_PUB_LEN], String)>> {
        let mut sock = std::os::unix::net::UnixStream::connect(sock_path)?;
        sock.set_read_timeout(Some(SSH_AGENT_TIMEOUT))?;
        sock.set_write_timeout(Some(SSH_AGENT_TIMEOUT))?;
        ssh_agent_list_over(&mut sock)
    }

    /// List all canonical `"ssh-ed25519"` identities on `sock_path` (unsupported on non-Unix).
    ///
    /// # Errors
    /// Always returns [`io::ErrorKind::Unsupported`] on non-Unix platforms.
    #[cfg(not(unix))]
    pub fn list_identities(_sock_path: &Path) -> io::Result<Vec<([u8; ID_PUB_LEN], String)>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "ssh-agent Unix sockets are only supported on Unix targets",
        ))
    }

    /// Connect to `sock_path` and select the first `"ssh-ed25519"` identity registered in the agent.
    ///
    /// # Errors
    /// Fails if the socket cannot be reached or holds no `"ssh-ed25519"` key.
    pub fn connect_first(sock_path: impl Into<PathBuf>) -> io::Result<Self> {
        let path = sock_path.into();
        let keys = Self::list_identities(&path)?;
        let Some((pk, _)) = keys.first() else {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "ssh-agent: no ssh-ed25519 identities loaded",
            ));
        };
        Ok(Self {
            sock_path: path,
            pubkey: *pk,
        })
    }

    /// Connect to `sock_path` and verify that `pubkey` is currently loaded in the agent.
    ///
    /// # Errors
    /// Fails if the socket cannot be reached or `pubkey` is not among the agent's Ed25519 keys.
    pub fn connect_for_key(
        sock_path: impl Into<PathBuf>,
        pubkey: [u8; ID_PUB_LEN],
    ) -> io::Result<Self> {
        let path = sock_path.into();
        let keys = Self::list_identities(&path)?;
        let keys_s = keys.as_slice();
        let mut found = false;
        let mut i = 0usize;
        while let Some((cand_pk, _)) = keys_s.get(i) {
            if ct_eq(cand_pk, &pubkey) {
                found = true;
                break;
            }
            i = i.saturating_add(1);
        }
        if !found {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "ssh-agent: requested ssh-ed25519 public key is not loaded",
            ));
        }
        Ok(Self {
            sock_path: path,
            pubkey,
        })
    }

    /// Connect via the `SSH_AUTH_SOCK` environment variable and select the first `"ssh-ed25519"` key.
    ///
    /// # Errors
    /// Fails if `SSH_AUTH_SOCK` is unset or the agent holds no `"ssh-ed25519"` key.
    pub fn from_env_first() -> io::Result<Self> {
        let Some(sock) = std::env::var_os("SSH_AUTH_SOCK") else {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "SSH_AUTH_SOCK is not set",
            ));
        };
        Self::connect_first(PathBuf::from(sock))
    }

    /// Connect via `SSH_AUTH_SOCK` for a specific Ed25519 `pubkey`.
    ///
    /// # Errors
    /// Fails if `SSH_AUTH_SOCK` is unset or `pubkey` is not loaded in the agent.
    pub fn from_env_for_key(pubkey: [u8; ID_PUB_LEN]) -> io::Result<Self> {
        let Some(sock) = std::env::var_os("SSH_AUTH_SOCK") else {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "SSH_AUTH_SOCK is not set",
            ));
        };
        Self::connect_for_key(PathBuf::from(sock), pubkey)
    }

    /// This signer's 32-byte Ed25519 public key.
    #[must_use]
    pub const fn public(&self) -> [u8; ID_PUB_LEN] {
        self.pubkey
    }

    /// Path to the `ssh-agent` Unix-domain socket.
    #[must_use]
    pub fn sock_path(&self) -> &Path {
        &self.sock_path
    }

    /// Ask the external `ssh-agent` to sign `message` under `self.pubkey`, then verify
    /// the returned 64-byte Ed25519 signature strictly before returning it.
    ///
    /// # Errors
    /// Fails on socket I/O failure, agent refusal, or signature verification mismatch.
    #[cfg(unix)]
    pub fn sign(&self, message: &[u8]) -> io::Result<[u8; CERT_SIG_LEN]> {
        let mut sock = std::os::unix::net::UnixStream::connect(&self.sock_path)?;
        sock.set_read_timeout(Some(SSH_AGENT_TIMEOUT))?;
        sock.set_write_timeout(Some(SSH_AGENT_TIMEOUT))?;
        ssh_agent_sign_over(&mut sock, &self.pubkey, message)
    }

    /// Ask the external `ssh-agent` to sign `message` (unsupported on non-Unix).
    ///
    /// # Errors
    /// Always returns [`io::ErrorKind::Unsupported`] on non-Unix platforms.
    #[cfg(not(unix))]
    pub fn sign(&self, _message: &[u8]) -> io::Result<[u8; CERT_SIG_LEN]> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "ssh-agent Unix sockets are only supported on Unix targets",
        ))
    }
}

/// Closed signer sum type supporting either in-memory [`IdentityKeypair`] signing or
/// out-of-process [`SshAgentSigner`] signing (`SSH_AUTH_SOCK`) with static dispatch.
#[derive(Clone)]
pub enum IdentitySigner {
    /// Sign directly with an in-memory [`IdentityKeypair`].
    Local(IdentityKeypair),
    /// Delegate signing over `SSH_AUTH_SOCK` to an external [`SshAgentSigner`].
    SshAgent(SshAgentSigner),
}

impl From<IdentityKeypair> for IdentitySigner {
    fn from(kp: IdentityKeypair) -> Self {
        Self::Local(kp)
    }
}

impl From<SshAgentSigner> for IdentitySigner {
    fn from(agent: SshAgentSigner) -> Self {
        Self::SshAgent(agent)
    }
}

impl IdentitySigner {
    /// The 32-byte Ed25519 public key corresponding to this signer.
    #[must_use]
    pub fn public(&self) -> [u8; ID_PUB_LEN] {
        match self {
            Self::Local(kp) => kp.public(),
            Self::SshAgent(ag) => ag.public(),
        }
    }

    /// Sign `message`, returning a 64-byte Ed25519 signature.
    ///
    /// # Errors
    /// Propagates `ssh-agent` transport or refusal errors for [`IdentitySigner::SshAgent`].
    pub fn sign(&self, message: &[u8]) -> io::Result<[u8; CERT_SIG_LEN]> {
        match self {
            Self::Local(kp) => Ok(kp.sign_raw(message)),
            Self::SshAgent(ag) => ag.sign(message),
        }
    }
}

/// Minimal privilege-separated Ed25519 `ssh-agent` Unix-socket server (`#[cfg(unix)]`),
/// speaking `SSH_AGENTC_REQUEST_IDENTITIES` and `SSH_AGENTC_SIGN_REQUEST` so an embedded
/// custody helper or hermetic test can hold [`IdentityKeypair`]s out-of-band.
#[cfg(unix)]
pub struct SshAgentServer {
    sock_path: PathBuf,
    stop: Arc<std::sync::atomic::AtomicBool>,
    worker: Option<std::thread::JoinHandle<()>>,
}

#[cfg(unix)]
impl SshAgentServer {
    /// Bind a new `ssh-agent` Unix socket at `sock_path` serving `keys` (`(keypair, comment)`).
    ///
    /// # Errors
    /// Returns any filesystem/socket bind or thread-spawn failure.
    pub fn bind(
        sock_path: impl Into<PathBuf>,
        keys: Vec<(IdentityKeypair, String)>,
    ) -> io::Result<Self> {
        Self::bind_with_raw_blobs(sock_path, keys, Vec::new())
    }

    /// Like [`Self::bind`], plus extra raw `(key_blob, comment)` entries (e.g. non-Ed25519
    /// keys) advertised in `IDENTITIES_ANSWER` so callers can test multi-algorithm filtering.
    ///
    /// # Errors
    /// Returns any socket bind or thread-spawn failure.
    pub fn bind_with_raw_blobs(
        sock_path: impl Into<PathBuf>,
        keys: Vec<(IdentityKeypair, String)>,
        extra_blobs: Vec<(Vec<u8>, String)>,
    ) -> io::Result<Self> {
        let path = sock_path.into();
        let _ = std::fs::remove_file(&path);
        let listener = std::os::unix::net::UnixListener::bind(&path)?;
        let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let stop_bg = Arc::clone(&stop);
        let keys = Arc::new(keys);
        let extra = Arc::new(extra_blobs);
        let worker = std::thread::Builder::new().spawn(move || {
            for incoming in listener.incoming() {
                if stop_bg.load(std::sync::atomic::Ordering::Acquire) {
                    break;
                }
                let Ok(mut stream) = incoming else {
                    break;
                };
                let _ = stream.set_read_timeout(Some(SSH_AGENT_TIMEOUT));
                let _ = stream.set_write_timeout(Some(SSH_AGENT_TIMEOUT));
                let keys_conn = Arc::clone(&keys);
                let extra_conn = Arc::clone(&extra);
                let _ = std::thread::Builder::new().spawn(move || {
                    while let Ok(req) = read_agent_frame(&mut stream) {
                        let resp = handle_ssh_agent_request(&req, &keys_conn, &extra_conn);
                        if write_agent_frame(&mut stream, &resp).is_err() {
                            break;
                        }
                    }
                });
            }
        })?;
        Ok(Self {
            sock_path: path,
            stop,
            worker: Some(worker),
        })
    }

    /// Socket path clients pass to [`SshAgentSigner`] or `SSH_AUTH_SOCK`.
    #[must_use]
    pub fn sock_path(&self) -> &Path {
        &self.sock_path
    }

    /// Stop accepting new agent requests and remove the socket file.
    pub fn shutdown(mut self) {
        self.stop_inner();
    }

    fn stop_inner(&mut self) {
        if !self.stop.swap(true, std::sync::atomic::Ordering::AcqRel) {
            let _ = std::os::unix::net::UnixStream::connect(&self.sock_path);
            let _ = std::fs::remove_file(&self.sock_path);
        }
        if let Some(h) = self.worker.take() {
            let _ = h.join();
        }
    }
}

#[cfg(unix)]
impl Drop for SshAgentServer {
    fn drop(&mut self) {
        self.stop_inner();
    }
}

#[cfg(unix)]
fn handle_ssh_agent_request(
    req: &[u8],
    keys: &[(IdentityKeypair, String)],
    extra_blobs: &[(Vec<u8>, String)],
) -> Vec<u8> {
    let Some((&tag, mut cur)) = req.split_first() else {
        return vec![SSH_AGENT_FAILURE];
    };
    if tag == SSH_AGENTC_REQUEST_IDENTITIES {
        if !cur.is_empty() {
            return vec![SSH_AGENT_FAILURE];
        }
        let total = keys.len().saturating_add(extra_blobs.len()) as u32;
        let mut out = Vec::new();
        out.push(SSH_AGENT_IDENTITIES_ANSWER);
        out.extend_from_slice(&total.to_be_bytes());
        let mut i = 0usize;
        while let Some((eb_blob, eb_comment)) = extra_blobs.get(i) {
            push_ssh_string(&mut out, eb_blob);
            push_ssh_string(&mut out, eb_comment.as_bytes());
            i = i.saturating_add(1);
        }
        let mut j = 0usize;
        while let Some((kp, comment)) = keys.get(j) {
            let blob = encode_ssh_ed25519_key_blob(&kp.public());
            push_ssh_string(&mut out, &blob);
            push_ssh_string(&mut out, comment.as_bytes());
            j = j.saturating_add(1);
        }
        return out;
    }
    if tag == SSH_AGENTC_SIGN_REQUEST {
        let Ok(key_blob) = read_ssh_string(&mut cur) else {
            return vec![SSH_AGENT_FAILURE];
        };
        let Ok(data) = read_ssh_string(&mut cur) else {
            return vec![SSH_AGENT_FAILURE];
        };
        let Ok(_flags) = read_ssh_u32(&mut cur) else {
            return vec![SSH_AGENT_FAILURE];
        };
        if !cur.is_empty() {
            return vec![SSH_AGENT_FAILURE];
        }
        let Some(target_pk) = decode_ssh_ed25519_key_blob(key_blob) else {
            return vec![SSH_AGENT_FAILURE];
        };
        let mut i = 0usize;
        while let Some((kp, _)) = keys.get(i) {
            let cand = kp.public();
            if ct_eq(&cand, &target_pk) {
                let sig = kp.sign_raw(data);
                let cap_blob = SSH_ED25519_ALG
                    .len()
                    .saturating_add(CERT_SIG_LEN)
                    .saturating_add(8);
                let mut sig_blob = Vec::with_capacity(cap_blob);
                push_ssh_string(&mut sig_blob, SSH_ED25519_ALG);
                push_ssh_string(&mut sig_blob, &sig);
                let mut out = Vec::with_capacity(5usize.saturating_add(sig_blob.len()));
                out.push(SSH_AGENT_SIGN_RESPONSE);
                push_ssh_string(&mut out, &sig_blob);
                return out;
            }
            i = i.saturating_add(1);
        }
        return vec![SSH_AGENT_FAILURE];
    }
    vec![SSH_AGENT_FAILURE]
}

// ============================================================================
// External Authority Certificates (`ACRT` v1), CA, Trust Store & Rotation
// ============================================================================

/// Canonical Ed25519-signed certificate (`ACRT` v1) binding a subject public key to a
/// [`CertRole`], `principal`, optional external `issuer` (SSH CA name or OIDC issuer URI),
/// monotonic `serial`, and `[valid_after_ms, valid_before_ms)` validity window.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentityCertificate {
    role: CertRole,
    serial: u64,
    valid_after_ms: u64,
    valid_before_ms: u64,
    ca_pub: [u8; ID_PUB_LEN],
    subject_pub: [u8; ID_PUB_LEN],
    principal: String,
    issuer: String,
    ca_sig: [u8; CERT_SIG_LEN],
}

impl IdentityCertificate {
    /// Certificate role ([`CertRole::Host`] or [`CertRole::Client`]).
    #[must_use]
    pub const fn role(&self) -> CertRole {
        self.role
    }

    /// Strictly positive CA-assigned serial number.
    #[must_use]
    pub const fn serial(&self) -> u64 {
        self.serial
    }

    /// Inclusive start of certificate validity (Unix milliseconds).
    #[must_use]
    pub const fn valid_after_ms(&self) -> u64 {
        self.valid_after_ms
    }

    /// Exclusive end of certificate validity (Unix milliseconds).
    #[must_use]
    pub const fn valid_before_ms(&self) -> u64 {
        self.valid_before_ms
    }

    /// Issuing Certificate Authority's 32-byte Ed25519 public key.
    #[must_use]
    pub const fn ca_pub(&self) -> [u8; ID_PUB_LEN] {
        self.ca_pub
    }

    /// Certified subject's 32-byte Ed25519 public key.
    #[must_use]
    pub const fn subject_pub(&self) -> [u8; ID_PUB_LEN] {
        self.subject_pub
    }

    /// Principal attested by the CA (e.g. `"h-alice"`, `"a-worker7"`, `"n-..."`).
    #[must_use]
    pub fn principal(&self) -> &str {
        &self.principal
    }

    /// Optional external authority / OIDC issuer URI attested in the certificate.
    #[must_use]
    pub fn issuer(&self) -> &str {
        &self.issuer
    }

    fn encode_unsigned_body_into(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&CERT_WIRE_MAGIC);
        out.push(CERT_WIRE_VERSION);
        out.push(self.role.to_wire());
        out.extend_from_slice(&self.serial.to_be_bytes());
        out.extend_from_slice(&self.valid_after_ms.to_be_bytes());
        out.extend_from_slice(&self.valid_before_ms.to_be_bytes());
        out.extend_from_slice(&self.ca_pub);
        out.extend_from_slice(&self.subject_pub);
        out.push(self.principal.len() as u8);
        out.extend_from_slice(self.principal.as_bytes());
        out.push(self.issuer.len() as u8);
        out.extend_from_slice(self.issuer.as_bytes());
    }

    fn signing_payload(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(640);
        msg.extend_from_slice(CERT_SIGN_DOMAIN);
        self.encode_unsigned_body_into(&mut msg);
        msg
    }

    /// Encode this certificate into its canonical injective `ACRT` v1 binary wire format.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MAX_CERT_WIRE_LEN);
        self.encode_unsigned_body_into(&mut out);
        out.extend_from_slice(&self.ca_sig);
        out
    }

    /// Decode an `ACRT` v1 binary certificate and validate structural invariants (canonical
    /// curve points, non-zero serial, non-empty valid window, ASCII principal/issuer, and
    /// exact byte length with no trailing garbage). Call [`CertTrustStore::verify_cert`]
    /// (or [`Self::verify_signature`]) to verify cryptographic authenticity and trust policy.
    ///
    /// # Errors
    /// Returns [`io::ErrorKind::InvalidData`] on any malformed, truncated, or non-canonical byte.
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() < MIN_CERT_WIRE_LEN || bytes.len() > MAX_CERT_WIRE_LEN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: wire length outside ACRT v1 bounds",
            ));
        }
        let Some((magic, cur)) = bytes.split_first_chunk::<4>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated magic",
            ));
        };
        let Some((hdr_tags, cur)) = cur.split_first_chunk::<2>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated header tags",
            ));
        };
        let [ver_tag, role_tag] = *hdr_tags;
        if *magic != CERT_WIRE_MAGIC || !cert_wire_version_valid(ver_tag) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: bad ACRT magic or version",
            ));
        }
        let Some(role) = CertRole::from_wire(role_tag) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: invalid certificate role tag",
            ));
        };
        let Some((ser_b, cur)) = cur.split_first_chunk::<8>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated serial",
            ));
        };
        let Some((va_b, cur)) = cur.split_first_chunk::<8>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated valid_after_ms",
            ));
        };
        let Some((vb_b, cur)) = cur.split_first_chunk::<8>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated valid_before_ms",
            ));
        };
        let serial = u64::from_be_bytes(*ser_b);
        let valid_after_ms = u64::from_be_bytes(*va_b);
        let valid_before_ms = u64::from_be_bytes(*vb_b);
        if serial == 0 || valid_after_ms >= valid_before_ms {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: serial must be > 0 and valid_after_ms < valid_before_ms",
            ));
        }
        let Some((ca_pub_ref, cur)) = cur.split_first_chunk::<ID_PUB_LEN>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated CA public key",
            ));
        };
        let ca_pub = *ca_pub_ref;
        ensure_canonical_pubkey(&ca_pub, "astream cert: non-canonical CA public key")?;
        let Some((subj_pub_ref, cur)) = cur.split_first_chunk::<ID_PUB_LEN>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated subject public key",
            ));
        };
        let subject_pub = *subj_pub_ref;
        ensure_canonical_pubkey(
            &subject_pub,
            "astream cert: non-canonical subject public key",
        )?;

        let Some((&plen_u8, cur)) = cur.split_first() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated principal length",
            ));
        };
        let plen = plen_u8 as usize;
        if plen == 0 || plen > MAX_CERT_PRINCIPAL_LEN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: malformed principal length",
            ));
        }
        let Some((principal_raw, cur)) = cur.split_at_checked(plen) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated principal bytes",
            ));
        };
        let Ok(principal_str) = core::str::from_utf8(principal_raw) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: non-UTF8 principal",
            ));
        };
        if validate_cert_principal(principal_str).is_err() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: invalid principal characters",
            ));
        }

        let Some((&ilen_u8, cur)) = cur.split_first() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated issuer length",
            ));
        };
        let ilen = ilen_u8 as usize;
        if ilen > MAX_CERT_ISSUER_LEN {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: malformed issuer length",
            ));
        }
        let Some((issuer_raw, cur)) = cur.split_at_checked(ilen) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated issuer bytes",
            ));
        };
        let Ok(issuer_str) = core::str::from_utf8(issuer_raw) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: non-UTF8 issuer",
            ));
        };
        if validate_cert_issuer(issuer_str).is_err() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: invalid issuer characters",
            ));
        }

        let Some((ca_sig_ref, tail)) = cur.split_first_chunk::<CERT_SIG_LEN>() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: truncated CA signature",
            ));
        };
        if !tail.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: trailing bytes after CA signature",
            ));
        }
        let ca_sig = *ca_sig_ref;

        Ok(Self {
            role,
            serial,
            valid_after_ms,
            valid_before_ms,
            ca_pub,
            subject_pub,
            principal: principal_str.to_owned(),
            issuer: issuer_str.to_owned(),
            ca_sig,
        })
    }

    /// Strictly verify the CA signature on this certificate against its embedded `ca_pub`.
    /// Note: callers MUST check `ca_pub`, validity window, role, and revocation against a
    /// [`CertTrustStore`] before trusting the certificate.
    ///
    /// # Errors
    /// Returns [`io::ErrorKind::InvalidData`] if the signature fails strict Ed25519 verification.
    pub fn verify_signature(&self) -> io::Result<()> {
        let payload = self.signing_payload();
        verify_ed25519_strict(
            &self.ca_pub,
            &payload,
            &self.ca_sig,
            "astream cert: CA signature verification failed",
        )
    }

    /// Hex-encode the canonical binary wire representation for config/file distribution.
    #[must_use]
    pub fn to_hex(&self) -> String {
        let raw = self.encode();
        let mut cur = raw.as_slice();
        let mut out = String::with_capacity(MAX_CERT_WIRE_LEN * 2);
        while let Some((&b, rest)) = cur.split_first() {
            cur = rest;
            out.push(nibble_to_hex((b >> 4) & 0x0f));
            out.push(nibble_to_hex(b & 0x0f));
        }
        out
    }

    /// Decode a hex-encoded `ACRT` v1 certificate (trimmed of surrounding ASCII whitespace).
    ///
    /// # Errors
    /// Fails if the string is not even-length hex or [`Self::decode`] rejects the bytes.
    pub fn from_hex(hex: &str) -> io::Result<Self> {
        let trimmed = hex.trim();
        if trimmed.is_empty() || trimmed.len() > MAX_CERT_WIRE_LEN.saturating_mul(2) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: invalid hex certificate length",
            ));
        }
        let mut cur = trimmed.as_bytes();
        let mut raw = Vec::with_capacity(cur.len() / 2);
        while let Some((pair, rest)) = cur.split_first_chunk::<2>() {
            cur = rest;
            let [h_byte, l_byte] = *pair;
            let Some(hi) = hex_nibble(h_byte) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "astream cert: non-hex digit in certificate",
                ));
            };
            let Some(lo) = hex_nibble(l_byte) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "astream cert: non-hex digit in certificate",
                ));
            };
            raw.push(((hi & 0x0f) << 4) | (lo & 0x0f));
        }
        if !cur.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "astream cert: invalid hex certificate length",
            ));
        }
        Self::decode(&raw)
    }
}

const fn nibble_to_hex(nib: u8) -> char {
    match nib & 0x0f {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'a',
        11 => 'b',
        12 => 'c',
        13 => 'd',
        14 => 'e',
        _ => 'f',
    }
}

const fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a').saturating_add(10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A').saturating_add(10)),
        _ => None,
    }
}

/// External or embedded Certificate Authority that mints [`IdentityCertificate`]s.
///
/// Backed by [`IdentitySigner`], so the CA root key itself may reside in an external
/// `ssh-agent` / HSM agent socket rather than in process memory.
#[derive(Clone)]
pub struct CertificateAuthority {
    signer: IdentitySigner,
    issuer: String,
}

impl CertificateAuthority {
    /// Create a Certificate Authority backed by `signer` and stamping `issuer` (may be `""`
    /// or a URI such as `"ssh-ca://prod"` or `"https://idp.example.com"`).
    ///
    /// # Errors
    /// Fails if `issuer` exceeds [`MAX_CERT_ISSUER_LEN`] or contains control bytes, or if
    /// `signer`'s public key is non-canonical.
    pub fn new(signer: impl Into<IdentitySigner>, issuer: impl Into<String>) -> io::Result<Self> {
        let signer = signer.into();
        let issuer = issuer.into();
        validate_cert_issuer(&issuer)?;
        ensure_canonical_pubkey(
            &signer.public(),
            "astream cert: CA signer public key is non-canonical",
        )?;
        Ok(Self { signer, issuer })
    }

    /// Public key of this Certificate Authority (`ca_pub` for [`CertTrustStore`]).
    #[must_use]
    pub fn public(&self) -> [u8; ID_PUB_LEN] {
        self.signer.public()
    }

    /// Issuer identifier stamped into minted certificates.
    #[must_use]
    pub fn issuer(&self) -> &str {
        &self.issuer
    }

    /// Issue a signed [`IdentityCertificate`] for `subject_pub`.
    ///
    /// # Errors
    /// Fails if `serial == 0`, `valid_after_ms >= valid_before_ms`, the validity span exceeds
    /// [`MAX_CERT_VALIDITY_CAP_MS`], `principal` is malformed, `subject_pub` is non-canonical,
    /// or the underlying [`IdentitySigner`] refuses to sign.
    pub fn issue(
        &self,
        role: CertRole,
        subject_pub: [u8; ID_PUB_LEN],
        principal: &str,
        serial: u64,
        valid_after_ms: u64,
        valid_before_ms: u64,
    ) -> io::Result<IdentityCertificate> {
        validate_cert_principal(principal)?;
        ensure_canonical_pubkey(
            &subject_pub,
            "astream cert: subject public key is non-canonical",
        )?;
        if serial == 0 || valid_after_ms >= valid_before_ms {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: serial must be > 0 and valid_after_ms < valid_before_ms",
            ));
        }
        let span = valid_before_ms.saturating_sub(valid_after_ms);
        if !cert_horizon_reached(MAX_CERT_VALIDITY_CAP_MS, span) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: validity span exceeds MAX_CERT_VALIDITY_CAP_MS",
            ));
        }
        let mut cert = IdentityCertificate {
            role,
            serial,
            valid_after_ms,
            valid_before_ms,
            ca_pub: self.signer.public(),
            subject_pub,
            principal: principal.to_owned(),
            issuer: self.issuer.clone(),
            ca_sig: [0u8; CERT_SIG_LEN],
        };
        let payload = cert.signing_payload();
        cert.ca_sig = self.signer.sign(&payload)?;
        Ok(cert)
    }
}

/// Authenticated peer metadata extracted from a verified [`IdentityCertificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedPeerCert {
    /// Subject's verified Ed25519 public key (which signed the ephemeral SIGMA transcript).
    pub subject_pub: [u8; ID_PUB_LEN],
    /// Trusted CA root key that signed the certificate.
    pub ca_pub: [u8; ID_PUB_LEN],
    /// Verified certificate serial number.
    pub serial: u64,
    /// Certificate `valid_after_ms` timestamp.
    pub valid_after_ms: u64,
    /// Certificate `valid_before_ms` deadline.
    pub valid_before_ms: u64,
    /// Attested principal (e.g. `"h-alice"`, `"a-worker7"`, `"n-..."`).
    pub principal: String,
    /// Attested issuer URI/name.
    pub issuer: String,
}

/// Trust store for verifying [`IdentityCertificate`]s: supports overlapping multi-CA root
/// rotation, optional OIDC/authority issuer allow-listing, bounded certificate TTLs, and
/// monotonic KRL/CRL serial + subject-key revocation.
#[derive(Debug, Clone)]
pub struct CertTrustStore {
    trusted_cas: Vec<[u8; ID_PUB_LEN]>,
    allowed_issuers: Vec<String>,
    max_validity_ms: u64,
    crl_epoch: u64,
    serial_floor: u64,
    revoked_serials: Vec<u64>,
    revoked_subjects: Vec<[u8; ID_PUB_LEN]>,
}

impl CertTrustStore {
    /// Build a trust store anchored at `trusted_cas` (`1..=MAX_TRUSTED_CAS` canonical Ed25519
    /// public keys) and capping accepted certificate lifetimes to `max_validity_ms` (clamped
    /// to `1..=MAX_CERT_VALIDITY_CAP_MS`).
    ///
    /// # Errors
    /// Fails if `trusted_cas` is empty, exceeds [`MAX_TRUSTED_CAS`], `max_validity_ms == 0`,
    /// or any CA public key is non-canonical.
    pub fn new(trusted_cas: Vec<[u8; ID_PUB_LEN]>, max_validity_ms: u64) -> io::Result<Self> {
        validate_ca_list(&trusted_cas)?;
        if max_validity_ms == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: max_validity_ms must be > 0",
            ));
        }
        let clamped = cert_validity_clamp(max_validity_ms, MAX_CERT_VALIDITY_CAP_MS);
        Ok(Self {
            trusted_cas,
            allowed_issuers: Vec::new(),
            max_validity_ms: clamped,
            crl_epoch: 0,
            serial_floor: 1,
            revoked_serials: Vec::new(),
            revoked_subjects: Vec::new(),
        })
    }

    /// Require certificates to carry an `issuer` matching one of `issuers` (exact match).
    /// An empty `issuers` list disables issuer filtering.
    ///
    /// # Errors
    /// Fails if any issuer string fails [`MAX_CERT_ISSUER_LEN`] / ASCII validation.
    pub fn with_allowed_issuers(mut self, issuers: Vec<String>) -> io::Result<Self> {
        let iss_s = issuers.as_slice();
        let mut i = 0usize;
        while let Some(iss) = iss_s.get(i) {
            validate_cert_issuer(iss)?;
            i = i.saturating_add(1);
        }
        self.allowed_issuers = issuers;
        Ok(self)
    }

    /// Replace the trusted CA root list (e.g. adding a new CA root alongside the retiring
    /// root, then later dropping the retiring root).
    ///
    /// # Errors
    /// Fails if `next_cas` is empty, exceeds [`MAX_TRUSTED_CAS`], or contains a non-canonical key.
    pub fn rotate_trusted_cas(&mut self, next_cas: Vec<[u8; ID_PUB_LEN]>) -> io::Result<()> {
        validate_ca_list(&next_cas)?;
        self.trusted_cas = next_cas;
        Ok(())
    }

    /// Install a fresher Key Revocation List (`crl_epoch` MUST strictly exceed the current
    /// `crl_epoch`, preventing KRL rollback attacks). `serial_floor` advances monotonically.
    ///
    /// # Errors
    /// Fails if `crl_epoch <= self.crl_epoch` or `revoked_serials` exceeds [`MAX_CERT_REVOKED_SERIALS`].
    pub fn install_krl(
        &mut self,
        crl_epoch: u64,
        serial_floor: u64,
        revoked_serials: &[u64],
        revoked_subjects: &[[u8; ID_PUB_LEN]],
    ) -> io::Result<()> {
        if revoked_serials.len() > MAX_CERT_REVOKED_SERIALS
            || revoked_subjects.len() > MAX_CERT_REVOKED_SERIALS
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: KRL exceeds MAX_CERT_REVOKED_SERIALS",
            ));
        }
        let Some(min_next) = self.crl_epoch.checked_add(1) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: crl_epoch exhausted",
            ));
        };
        if !cert_horizon_reached(crl_epoch, min_next) {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: refused KRL rollback (crl_epoch must strictly advance)",
            ));
        }
        let mut sorted = revoked_serials.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        self.revoked_serials = sorted;
        self.revoked_subjects = revoked_subjects.to_vec();
        self.serial_floor = cert_epoch_advance(self.serial_floor, serial_floor);
        self.crl_epoch = cert_epoch_advance(self.crl_epoch, crl_epoch);
        Ok(())
    }

    /// Current monotonic revocation epoch.
    #[must_use]
    pub const fn crl_epoch(&self) -> u64 {
        self.crl_epoch
    }

    /// Current minimum accepted certificate serial floor.
    #[must_use]
    pub const fn serial_floor(&self) -> u64 {
        self.serial_floor
    }

    /// Trusted CA public keys currently anchored in this store.
    #[must_use]
    pub fn trusted_cas(&self) -> &[[u8; ID_PUB_LEN]] {
        &self.trusted_cas
    }

    /// Verify `cert`'s cryptographic CA signature AND authorize its role, CA root, optional
    /// issuer, optional expected principal, `[valid_after_ms, valid_before_ms)` window at
    /// `now_ms`, bounded TTL span, and non-revoked serial/subject status.
    ///
    /// Forged/corrupt CA signatures return [`io::ErrorKind::InvalidData`]; policy, expiry,
    /// untrusted-CA, role, principal, or revocation rejections return
    /// [`io::ErrorKind::PermissionDenied`].
    ///
    /// # Errors
    /// Returns `InvalidData` on cryptographic verification failure or `PermissionDenied` on
    /// policy/trust/expiry/revocation failure.
    pub fn verify_cert(
        &self,
        cert: &IdentityCertificate,
        expected_role: CertRole,
        expected_principal: Option<&str>,
        now_ms: u64,
    ) -> io::Result<VerifiedPeerCert> {
        cert.verify_signature()?;

        if cert.role != expected_role {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: certificate role does not match peer role",
            ));
        }

        let cas = self.trusted_cas.as_slice();
        let mut ca_trusted = false;
        let mut i = 0usize;
        while let Some(cand_ca) = cas.get(i) {
            if ct_eq(cand_ca, &cert.ca_pub) {
                ca_trusted = true;
            }
            i = i.saturating_add(1);
        }
        if !ca_trusted {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: issuing CA is not in trust store",
            ));
        }

        let allowed_iss = self.allowed_issuers.as_slice();
        if !allowed_iss.is_empty() {
            let mut issuer_ok = false;
            let mut j = 0usize;
            while let Some(cand_iss) = allowed_iss.get(j) {
                if cand_iss == &cert.issuer {
                    issuer_ok = true;
                    break;
                }
                j = j.saturating_add(1);
            }
            if !issuer_ok {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "astream cert: certificate issuer is not allowed",
                ));
            }
        }

        if let Some(want_p) = expected_principal {
            if !cert.principal.eq_ignore_ascii_case(want_p) {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "astream cert: certificate principal does not match expected peer principal",
                ));
            }
        }

        if !cert_horizon_reached(now_ms, cert.valid_after_ms) {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: certificate is not yet valid",
            ));
        }
        if cert_horizon_reached(now_ms, cert.valid_before_ms) {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: certificate has expired",
            ));
        }
        let span = cert.valid_before_ms.saturating_sub(cert.valid_after_ms);
        if !cert_horizon_reached(self.max_validity_ms, span) {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: certificate validity span exceeds trust store maximum",
            ));
        }

        if !cert_horizon_reached(cert.serial, self.serial_floor)
            || self.revoked_serials.binary_search(&cert.serial).is_ok()
        {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "astream cert: certificate serial has been revoked",
            ));
        }

        let rev_subs = self.revoked_subjects.as_slice();
        let mut k = 0usize;
        while let Some(rev_pk) = rev_subs.get(k) {
            if ct_eq(rev_pk, &cert.subject_pub) {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "astream cert: certificate subject public key has been revoked",
                ));
            }
            k = k.saturating_add(1);
        }

        Ok(VerifiedPeerCert {
            subject_pub: cert.subject_pub,
            ca_pub: cert.ca_pub,
            serial: cert.serial,
            valid_after_ms: cert.valid_after_ms,
            valid_before_ms: cert.valid_before_ms,
            principal: cert.principal.clone(),
            issuer: cert.issuer.clone(),
        })
    }
}

fn validate_ca_list(cas: &[[u8; ID_PUB_LEN]]) -> io::Result<()> {
    if cas.is_empty() || cas.len() > MAX_TRUSTED_CAS {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert: trusted_cas must contain 1..=16 CA public keys",
        ));
    }
    let mut i = 0usize;
    while let Some(cand_ca) = cas.get(i) {
        ensure_canonical_pubkey(cand_ca, "astream cert: non-canonical CA root public key")?;
        i = i.saturating_add(1);
    }
    Ok(())
}

/// Thread-safe shared [`CertTrustStore`] handle allowing live CA root rotation and
/// monotonic KRL updates across concurrent TCP listener accept threads.
#[derive(Clone)]
pub struct SharedCertTrust {
    inner: Arc<Mutex<CertTrustStore>>,
}

impl SharedCertTrust {
    /// Wrap a [`CertTrustStore`] for concurrent sharing and live rotation.
    #[must_use]
    pub fn new(store: CertTrustStore) -> Self {
        Self {
            inner: Arc::new(Mutex::new(store)),
        }
    }

    /// Snapshot the current [`CertTrustStore`].
    #[must_use]
    pub fn snapshot(&self) -> CertTrustStore {
        let guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.clone()
    }

    /// Rotate the trusted CA root list on the live store.
    ///
    /// # Errors
    /// Propagates [`CertTrustStore::rotate_trusted_cas`] validation errors.
    pub fn rotate_trusted_cas(&self, next_cas: Vec<[u8; ID_PUB_LEN]>) -> io::Result<()> {
        let mut guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.rotate_trusted_cas(next_cas)
    }

    /// Install a fresher monotonic KRL on the live store.
    ///
    /// # Errors
    /// Propagates [`CertTrustStore::install_krl`] rollback or bound errors.
    pub fn install_krl(
        &self,
        crl_epoch: u64,
        serial_floor: u64,
        revoked_serials: &[u64],
        revoked_subjects: &[[u8; ID_PUB_LEN]],
    ) -> io::Result<()> {
        let mut guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.install_krl(crl_epoch, serial_floor, revoked_serials, revoked_subjects)
    }

    /// Verify `cert` against the current live trust store state.
    ///
    /// # Errors
    /// Propagates [`CertTrustStore::verify_cert`] errors.
    pub fn verify_cert(
        &self,
        cert: &IdentityCertificate,
        expected_role: CertRole,
        expected_principal: Option<&str>,
        now_ms: u64,
    ) -> io::Result<VerifiedPeerCert> {
        let store = self.snapshot();
        store.verify_cert(cert, expected_role, expected_principal, now_ms)
    }
}

struct HostSlotState {
    primary: (IdentitySigner, IdentityCertificate),
    retiring: Option<(IdentitySigner, IdentityCertificate, u64)>,
    generation: u64,
}

/// Live dual-slot host key & [`IdentityCertificate`] rotator for zero-downtime broker
/// host-key rollover (`docs/ROADMAP.md` §1).
///
/// Holds the current primary `(IdentitySigner, IdentityCertificate)` plus an optional
/// retiring slot valid until `overlap_until_ms`. If the primary certificate has not yet
/// entered its `valid_after_ms` window during a staged pre-rollover, [`Self::select_for_now`]
/// seamlessly serves the still-valid retiring host certificate until cutover!
#[derive(Clone)]
pub struct HostCertRotator {
    inner: Arc<Mutex<HostSlotState>>,
}

impl HostCertRotator {
    /// Initialize a [`HostCertRotator`] with its generation-1 host signer and [`CertRole::Host`]
    /// certificate.
    ///
    /// # Errors
    /// Fails if `cert.role() != CertRole::Host`, `cert.subject_pub() != signer.public()`, or
    /// `cert.verify_signature()` fails.
    pub fn new(signer: impl Into<IdentitySigner>, cert: IdentityCertificate) -> io::Result<Self> {
        let signer = signer.into();
        validate_host_pair(&signer, &cert)?;
        Ok(Self {
            inner: Arc::new(Mutex::new(HostSlotState {
                primary: (signer, cert),
                retiring: None,
                generation: 1,
            })),
        })
    }

    /// Stage a new primary `(next_signer, next_cert)` while keeping the previous primary
    /// in the retiring overlap slot until `overlap_until_ms` (`overlap_until_ms > now_ms`).
    ///
    /// # Errors
    /// Fails if `next_cert` does not match `next_signer` as a valid [`CertRole::Host`] cert,
    /// `overlap_until_ms <= now_ms`, or `next_cert.serial()` is not distinct from the current cert.
    pub fn rotate(
        &self,
        next_signer: impl Into<IdentitySigner>,
        next_cert: IdentityCertificate,
        overlap_until_ms: u64,
        now_ms: u64,
    ) -> io::Result<u64> {
        let next_signer = next_signer.into();
        validate_host_pair(&next_signer, &next_cert)?;
        let Some(min_until) = now_ms.checked_add(1) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: timestamp overflow in host rotation",
            ));
        };
        if !cert_horizon_reached(overlap_until_ms, min_until) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: overlap_until_ms must be strictly greater than now_ms",
            ));
        }
        let mut st = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        if st.primary.1.serial == next_cert.serial && ct_eq(&st.primary.1.ca_pub, &next_cert.ca_pub)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "astream cert: rotated host certificate must advance serial or CA",
            ));
        }
        let prev = st.primary.clone();
        st.retiring = Some((prev.0, prev.1, overlap_until_ms));
        st.primary = (next_signer, next_cert);
        st.generation = cert_epoch_advance(st.generation, st.generation.saturating_add(1));
        Ok(st.generation)
    }

    /// Current monotonic host-key rotation generation (`>= 1`).
    #[must_use]
    pub fn generation(&self) -> u64 {
        let st = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        st.generation
    }

    /// Select the active `(IdentitySigner, IdentityCertificate)` for a handshake at `now_ms`:
    /// prefers `primary` whenever `now_ms >= primary.valid_after_ms`, falling back to the
    /// `retiring` slot during its overlap window if `primary` is pre-staged for a future start.
    #[must_use]
    pub fn select_for_now(&self, now_ms: u64) -> (IdentitySigner, IdentityCertificate) {
        let st = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        if cert_horizon_reached(now_ms, st.primary.1.valid_after_ms)
            && !cert_horizon_reached(now_ms, st.primary.1.valid_before_ms)
        {
            return st.primary.clone();
        }
        if let Some((ref ret_s, ref ret_c, until_ms)) = st.retiring {
            if cert_horizon_reached(until_ms, now_ms)
                && cert_horizon_reached(now_ms, ret_c.valid_after_ms)
                && !cert_horizon_reached(now_ms, ret_c.valid_before_ms)
            {
                return (ret_s.clone(), ret_c.clone());
            }
        }
        st.primary.clone()
    }

    /// Return the currently active host Ed25519 public keys (`primary`, plus `retiring` while
    /// `now_ms <= overlap_until_ms`), for diagnostics or transitional pin distribution.
    #[must_use]
    pub fn active_host_pubkeys(&self, now_ms: u64) -> Vec<[u8; ID_PUB_LEN]> {
        let st = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        let primary_pk = st.primary.0.public();
        let mut out = vec![primary_pk];
        if let Some((ref ret_s, _, until_ms)) = st.retiring {
            if cert_horizon_reached(until_ms, now_ms) {
                let pk = ret_s.public();
                if !ct_eq(&pk, &primary_pk) {
                    out.push(pk);
                }
            }
        }
        out
    }
}

fn validate_host_pair(signer: &IdentitySigner, cert: &IdentityCertificate) -> io::Result<()> {
    if cert.role != CertRole::Host {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert: HostCertRotator requires a CertRole::Host certificate",
        ));
    }
    let pk = signer.public();
    if !ct_eq(&pk, &cert.subject_pub) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert: host certificate subject_pub does not match host signer",
        ));
    }
    cert.verify_signature()
}

// ============================================================================
// Mutual Certificate-Authenticated SIGMA Handshake + Signer-Generic Raw SIGMA
// ============================================================================

fn cert_sigma_session_key(dh: &[u8; 32], ec_pub: &[u8; 32], es_pub: &[u8; 32]) -> [u8; KEY_LEN] {
    let mut info = Vec::with_capacity(96);
    info.extend_from_slice(CERT_SIGMA_LABEL);
    info.extend_from_slice(ec_pub);
    info.extend_from_slice(es_pub);
    hkdf_sha256_32(&[], dh, &info)
}

fn cert_server_sig_transcript(
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
    server_cert_hash: &[u8; 32],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(144);
    out.extend_from_slice(CERT_SIG_CTX_SERVER);
    out.extend_from_slice(ec_pub);
    out.extend_from_slice(es_pub);
    out.extend_from_slice(server_cert_hash);
    out
}

fn cert_client_sig_transcript(
    ec_pub: &[u8; 32],
    es_pub: &[u8; 32],
    server_cert_hash: &[u8; 32],
    client_cert_hash: &[u8; 32],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(176);
    out.extend_from_slice(CERT_SIG_CTX_CLIENT);
    out.extend_from_slice(ec_pub);
    out.extend_from_slice(es_pub);
    out.extend_from_slice(server_cert_hash);
    out.extend_from_slice(client_cert_hash);
    out
}

fn write_cert_auth_frame<S: Read + Write>(
    sealed: &mut SealedStream<S>,
    cert_bytes: &[u8],
    sig: &[u8; CERT_SIG_LEN],
) -> io::Result<()> {
    if cert_bytes.len() < MIN_CERT_WIRE_LEN || cert_bytes.len() > MAX_CERT_WIRE_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert handshake: local certificate size out of bounds",
        ));
    }
    let len_be = (cert_bytes.len() as u16).to_be_bytes();
    let cap = 2usize
        .saturating_add(cert_bytes.len())
        .saturating_add(CERT_SIG_LEN);
    let mut frame = Vec::with_capacity(cap);
    frame.extend_from_slice(&len_be);
    frame.extend_from_slice(cert_bytes);
    frame.extend_from_slice(sig);
    sealed.write_all(&frame)?;
    sealed.flush()
}

fn read_cert_auth_frame<S: Read + Write>(
    sealed: &mut SealedStream<S>,
) -> io::Result<(IdentityCertificate, [u8; 32], [u8; CERT_SIG_LEN])> {
    let mut len_be = [0u8; 2];
    sealed.read_exact(&mut len_be)?;
    let cert_len = u16::from_be_bytes(len_be) as usize;
    if !(MIN_CERT_WIRE_LEN..=MAX_CERT_WIRE_LEN).contains(&cert_len) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "astream cert handshake: peer certificate length out of bounds",
        ));
    }
    let mut cert_bytes = vec![0u8; cert_len];
    sealed.read_exact(&mut cert_bytes)?;
    let mut sig = [0u8; CERT_SIG_LEN];
    sealed.read_exact(&mut sig)?;
    let cert_hash = Sha256::digest_slice(&cert_bytes);
    let cert = IdentityCertificate::decode(&cert_bytes)?;
    Ok((cert, cert_hash, sig))
}

/// Run the CLIENT side of the mutual certificate-authenticated SIGMA handshake over `stream`.
///
/// * `client_signer` may be either an in-memory [`IdentityKeypair`] or an external
///   [`SshAgentSigner`] (`SSH_AUTH_SOCK`).
/// * Verifies the server's `ACRT` [`CertRole::Host`] certificate against `server_trust`
///   (and `expected_host_principal` when `Some`) and its strict Ed25519 signature over the
///   ephemeral DH transcript BEFORE revealing `client_cert` in M4.
/// * Session encryption keys derive from the ephemeral X25519 exchange alone, preserving
///   forward secrecy even if CA, host, and client private keys are later compromised.
///
/// # Errors
/// Fails on transport I/O failure, non-contributory DH, malformed/forged certificate or
/// transcript signature (`InvalidData`), or untrusted/expired/revoked/wrong-principal host
/// certificate (`PermissionDenied`).
pub fn client_cert_handshake<S: Read + Write>(
    mut stream: S,
    client_signer: &IdentitySigner,
    client_cert: &IdentityCertificate,
    server_trust: &CertTrustStore,
    expected_host_principal: Option<&str>,
    now_ms: u64,
) -> io::Result<(SealedStream<S>, VerifiedPeerCert)> {
    if client_cert.role != CertRole::Client
        || !ct_eq(&client_signer.public(), &client_cert.subject_pub)
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "astream cert handshake: client_cert must be a Client cert matching client_signer",
        ));
    }
    let client_cert_bytes = client_cert.encode();
    let client_cert_hash = Sha256::digest_slice(&client_cert_bytes);

    let (secret, ec_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &ec_pub)?;
    let es_pub = read_hs_msg(&mut stream)?;
    let dh = x25519_shared(&secret, &es_pub)?;

    let mut sealed = SealedStream::with_transcript(
        stream,
        cert_sigma_session_key(dh.as_bytes(), &ec_pub, &es_pub),
        &record_binding(&ec_pub, &es_pub),
        true,
    );

    // M3: read and verify server's host certificate + transcript signature BEFORE sending M4.
    let (server_cert, server_cert_hash, sig_s) = read_cert_auth_frame(&mut sealed)?;
    let s_msg = cert_server_sig_transcript(&ec_pub, &es_pub, &server_cert_hash);
    verify_ed25519_strict(
        &server_cert.subject_pub,
        &s_msg,
        &sig_s,
        "astream cert handshake: server transcript signature failed",
    )?;
    let verified_host = server_trust.verify_cert(
        &server_cert,
        CertRole::Host,
        expected_host_principal,
        now_ms,
    )?;

    // M4: sign transcript (binding both server and client certificates) and send client cert.
    let c_msg = cert_client_sig_transcript(&ec_pub, &es_pub, &server_cert_hash, &client_cert_hash);
    let sig_c = client_signer.sign(&c_msg)?;
    write_cert_auth_frame(&mut sealed, &client_cert_bytes, &sig_c)?;

    Ok((sealed, verified_host))
}

/// Run the SERVER side of the mutual certificate-authenticated SIGMA handshake over `stream`.
///
/// Uses `host_rotator.select_for_now(now_ms)` to select the active host signer + certificate
/// (supporting live overlapping host-key rollover and `ssh-agent`-backed host keys), then
/// verifies the client's `ACRT` [`CertRole::Client`] certificate and transcript signature
/// against `client_trust`.
///
/// # Errors
/// Fails on transport I/O failure, non-contributory DH, malformed/forged client certificate
/// or signature (`InvalidData`), or untrusted/expired/revoked client certificate
/// (`PermissionDenied`).
pub fn server_cert_handshake<S: Read + Write>(
    mut stream: S,
    host_rotator: &HostCertRotator,
    client_trust: &CertTrustStore,
    now_ms: u64,
) -> io::Result<(SealedStream<S>, VerifiedPeerCert)> {
    let (host_signer, host_cert) = host_rotator.select_for_now(now_ms);
    let host_cert_bytes = host_cert.encode();
    let host_cert_hash = Sha256::digest_slice(&host_cert_bytes);

    let ec_pub = read_hs_msg(&mut stream)?;
    let (secret, es_pub) = ephemeral()?;
    write_hs_msg(&mut stream, &es_pub)?;
    let dh = x25519_shared(&secret, &ec_pub)?;

    let mut sealed = SealedStream::with_transcript(
        stream,
        cert_sigma_session_key(dh.as_bytes(), &ec_pub, &es_pub),
        &record_binding(&ec_pub, &es_pub),
        false,
    );

    // M3: prove host certificate and sign transcript.
    let s_msg = cert_server_sig_transcript(&ec_pub, &es_pub, &host_cert_hash);
    let sig_s = host_signer.sign(&s_msg)?;
    write_cert_auth_frame(&mut sealed, &host_cert_bytes, &sig_s)?;

    // M4: verify client's transcript signature first (InvalidData on forgery), then
    // authorize client certificate against `client_trust` (PermissionDenied on policy/revocation).
    let (client_cert, client_cert_hash, sig_c) = read_cert_auth_frame(&mut sealed)?;
    let c_msg = cert_client_sig_transcript(&ec_pub, &es_pub, &host_cert_hash, &client_cert_hash);
    verify_ed25519_strict(
        &client_cert.subject_pub,
        &c_msg,
        &sig_c,
        "astream cert handshake: client transcript signature failed",
    )?;
    let verified_client = client_trust.verify_cert(&client_cert, CertRole::Client, None, now_ms)?;

    Ok((sealed, verified_client))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{TcpListener, TcpStream};

    fn tcp_pair() -> (TcpStream, TcpStream) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let near = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        let (far, _) = listener.accept().unwrap();
        for s in [&near, &far] {
            s.set_read_timeout(Some(std::time::Duration::from_secs(30)))
                .unwrap();
        }
        (near, far)
    }

    #[test]
    fn cert_wire_roundtrips_and_rejects_forgery_role_expiry_and_krl_rollback() {
        let ca_kp = IdentityKeypair::generate();
        let wrong_ca_kp = IdentityKeypair::generate();
        let ca = CertificateAuthority::new(ca_kp, "https://idp.example.com").unwrap();
        let wrong_ca = CertificateAuthority::new(wrong_ca_kp, "https://idp.example.com").unwrap();

        let subj = IdentityKeypair::generate();
        let cert = ca
            .issue(
                CertRole::Client,
                subj.public(),
                "h-alice",
                42,
                1_000_000,
                1_600_000,
            )
            .unwrap();

        // Hex + binary canonical roundtrip.
        let hex = cert.to_hex();
        let decoded = IdentityCertificate::from_hex(&hex).unwrap();
        assert_eq!(decoded, cert);
        decoded.verify_signature().unwrap();

        // Trailing byte is rejected (canonical injectivity).
        let mut with_tail = cert.encode();
        with_tail.push(0);
        assert_eq!(
            IdentityCertificate::decode(&with_tail).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );

        // Tampered principal byte fails strict Ed25519 verification with InvalidData.
        let mut tampered = cert.encode();
        tampered[97] = b'b';
        let bad_cert = IdentityCertificate::decode(&tampered).unwrap();
        let store = CertTrustStore::new(vec![ca.public()], 3_600_000)
            .unwrap()
            .with_allowed_issuers(vec!["https://idp.example.com".to_owned()])
            .unwrap();
        assert_eq!(
            store
                .verify_cert(&bad_cert, CertRole::Client, None, 1_200_000)
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );

        // Valid cert passes within window, fails before `valid_after_ms`, at `valid_before_ms`,
        // and for wrong role (`CertRole::Host`).
        let verified = store
            .verify_cert(&cert, CertRole::Client, Some("H-ALICE"), 1_200_000)
            .unwrap();
        assert_eq!(verified.principal, "h-alice");
        assert_eq!(verified.serial, 42);
        assert_eq!(
            store
                .verify_cert(&cert, CertRole::Client, None, 999_999)
                .unwrap_err()
                .kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(
            store
                .verify_cert(&cert, CertRole::Client, None, 1_600_000)
                .unwrap_err()
                .kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(
            store
                .verify_cert(&cert, CertRole::Host, None, 1_200_000)
                .unwrap_err()
                .kind(),
            io::ErrorKind::PermissionDenied
        );

        // Cert issued by untrusted CA is PermissionDenied.
        let foreign = wrong_ca
            .issue(
                CertRole::Client,
                subj.public(),
                "h-alice",
                43,
                1_000_000,
                1_600_000,
            )
            .unwrap();
        assert_eq!(
            store
                .verify_cert(&foreign, CertRole::Client, None, 1_200_000)
                .unwrap_err()
                .kind(),
            io::ErrorKind::PermissionDenied
        );

        // Monotonic KRL refuses epoch rollback and blocks revoked serials / serial floor.
        let mut rev_store = store.clone();
        rev_store.install_krl(5, 10, &[42, 99], &[]).unwrap();
        assert_eq!(rev_store.crl_epoch(), 5);
        assert_eq!(
            rev_store.install_krl(5, 10, &[], &[]).unwrap_err().kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(
            rev_store
                .verify_cert(&cert, CertRole::Client, None, 1_200_000)
                .unwrap_err()
                .kind(),
            io::ErrorKind::PermissionDenied
        );
    }

    #[test]
    fn mutual_cert_sigma_handshake_ca_rotation_and_host_rollover() {
        let ca_v1 =
            CertificateAuthority::new(IdentityKeypair::generate(), "ssh-ca://fleet").unwrap();
        let ca_v2 =
            CertificateAuthority::new(IdentityKeypair::generate(), "ssh-ca://fleet").unwrap();

        let host_k1 = IdentityKeypair::generate();
        let host_cert_1 = ca_v1
            .issue(
                CertRole::Host,
                host_k1.public(),
                "n-broker-primary",
                1,
                1_000,
                90_000,
            )
            .unwrap();
        let rotator = HostCertRotator::new(host_k1, host_cert_1).unwrap();

        let client_k = IdentityKeypair::generate();
        let client_cert = ca_v1
            .issue(
                CertRole::Client,
                client_k.public(),
                "a-worker-7",
                10,
                1_000,
                90_000,
            )
            .unwrap();
        let client_signer = IdentitySigner::from(client_k);

        // Overlapping root CA store trusts both ca_v1 and ca_v2 during CA rotation.
        let trust = CertTrustStore::new(vec![ca_v1.public(), ca_v2.public()], 300_000).unwrap();

        // Rotate host key to host_k2 signed by ca_v2 with a future start (`valid_after_ms = 50_000`),
        // keeping host_k1 retiring until `60_000`.
        let host_k2 = IdentityKeypair::generate();
        let host_cert_2 = ca_v2
            .issue(
                CertRole::Host,
                host_k2.public(),
                "n-broker-primary",
                2,
                50_000,
                150_000,
            )
            .unwrap();
        let gen = rotator
            .rotate(host_k2, host_cert_2, 60_000, 20_000)
            .unwrap();
        assert_eq!(gen, 2);
        assert_eq!(rotator.active_host_pubkeys(30_000).len(), 2);

        // At t = 30_000 (before host_cert_2 starts), rotator serves retiring host_cert_1;
        // at t = 55_000 (inside overlap after host_cert_2 starts), rotator serves host_cert_2!
        for (now_ms, expected_serial) in [(30_000u64, 1u64), (55_000u64, 2u64)] {
            let (c_sock, s_sock) = tcp_pair();
            let rot_bg = rotator.clone();
            let trust_bg = trust.clone();
            let server_thr = std::thread::spawn(move || {
                let (mut s_stream, peer) =
                    server_cert_handshake(s_sock, &rot_bg, &trust_bg, now_ms)?;
                let mut msg = [0u8; 5];
                s_stream.read_exact(&mut msg)?;
                s_stream.write_all(b"pong!")?;
                s_stream.flush()?;
                Ok::<_, io::Error>((msg, peer))
            });

            let (mut c_stream, host_peer) = client_cert_handshake(
                c_sock,
                &client_signer,
                &client_cert,
                &trust,
                Some("n-broker-primary"),
                now_ms,
            )
            .unwrap();
            assert_eq!(host_peer.serial, expected_serial);
            c_stream.write_all(b"ping?").unwrap();
            c_stream.flush().unwrap();
            let mut reply = [0u8; 5];
            c_stream.read_exact(&mut reply).unwrap();
            assert_eq!(&reply, b"pong!");

            let (got_msg, client_peer) = server_thr.join().unwrap().unwrap();
            assert_eq!(&got_msg, b"ping?");
            assert_eq!(client_peer.principal, "a-worker-7");
            assert_eq!(client_peer.serial, 10);
        }
    }

    #[cfg(unix)]
    #[test]
    fn ssh_agent_signer_authenticates_sigma_without_in_process_private_key() {
        let dir = PathBuf::from(format!(
            "/tmp/asag-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .subsec_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let sock_path = dir.join("a.s");

        // External agent holds CA key, host key, and client key; also advertises a non-Ed25519
        // ssh-rsa decoy key blob to verify algorithm filtering.
        let ca_kp = IdentityKeypair::generate();
        let host_kp = IdentityKeypair::generate();
        let client_kp = IdentityKeypair::generate();
        let ca_pub = ca_kp.public();
        let host_pub = host_kp.public();
        let client_pub = client_kp.public();

        let mut rsa_decoy = Vec::new();
        push_ssh_string(&mut rsa_decoy, b"ssh-rsa");
        push_ssh_string(&mut rsa_decoy, &[0x01, 0x00, 0x01]);

        let agent = SshAgentServer::bind_with_raw_blobs(
            &sock_path,
            vec![
                (ca_kp, "ca@fleet".to_owned()),
                (host_kp, "host@broker".to_owned()),
                (client_kp, "alice@workstation".to_owned()),
            ],
            vec![(rsa_decoy, "legacy-rsa".to_owned())],
        )
        .unwrap();

        let listed = SshAgentSigner::list_identities(&sock_path).unwrap();
        assert_eq!(listed.len(), 3);

        // Even the CA signs over SSH_AUTH_SOCK!
        let ca_agent = SshAgentSigner::connect_for_key(&sock_path, ca_pub).unwrap();
        let ca = CertificateAuthority::new(ca_agent, "ssh-ca://agent-root").unwrap();

        let host_signer = SshAgentSigner::connect_for_key(&sock_path, host_pub).unwrap();
        let client_signer =
            IdentitySigner::from(SshAgentSigner::connect_for_key(&sock_path, client_pub).unwrap());

        let host_cert = ca
            .issue(CertRole::Host, host_pub, "n-agent-broker", 1, 100, 50_000)
            .unwrap();
        let client_cert = ca
            .issue(CertRole::Client, client_pub, "h-alice", 2, 100, 50_000)
            .unwrap();

        let trust = CertTrustStore::new(vec![ca_pub], 100_000).unwrap();
        let rotator = HostCertRotator::new(host_signer, host_cert).unwrap();

        let (c_sock, s_sock) = tcp_pair();
        let trust_bg = trust.clone();
        let srv = std::thread::spawn(move || {
            let (mut s, peer) = server_cert_handshake(s_sock, &rotator, &trust_bg, 5_000)?;
            let mut buf = [0u8; 11];
            s.read_exact(&mut buf)?;
            Ok::<_, io::Error>((buf, peer))
        });

        let (mut c, host_info) = client_cert_handshake(
            c_sock,
            &client_signer,
            &client_cert,
            &trust,
            Some("n-agent-broker"),
            5_000,
        )
        .unwrap();
        assert_eq!(host_info.principal, "n-agent-broker");
        c.write_all(b"hello-agent").unwrap();
        c.flush().unwrap();

        let (got, peer_info) = srv.join().unwrap().unwrap();
        assert_eq!(&got, b"hello-agent");
        assert_eq!(peer_info.principal, "h-alice");

        agent.shutdown();
        let _ = std::fs::remove_dir_all(&dir);
    }
}
