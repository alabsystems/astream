// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OpenSSH `ssh-ed25519-cert-v01@openssh.com` binary wire parser, encoder, validity-window
//! verifier, and monotone serial floor (`Astream.CertAuth.TlaOpensshCert`).
//!
//! Parses and encodes the OpenSSH `PROTOCOL.certkeys` binary wire format (RFC 4251 big-endian
//! length-prefixed strings and integers) with zero third-party dependencies and zero panics:
//! - Exact key-type header `"ssh-ed25519-cert-v01@openssh.com"`.
//! - 32-byte subject Ed25519 public key and 32-byte CA `signature_key` (`"ssh-ed25519"`).
//! - `uint64 serial`, `uint32 cert_type` (`1 = User`, `2 = Host`), `key_id`, nested
//!   `valid_principals` list (clamped via Clean-origin `ssh_cert_principals_clamp`),
//!   half-open `[valid_after, valid_before)` validity window checked via `ssh_cert_time_valid`,
//!   fail-closed `critical_options` rejection, and exact `signed_bytes` slice extraction up to
//!   the trailing signature string so an Ed25519 verifier checks the CA signature directly.

#[cfg(clean_islands)]
#[path = "openssh_cert_island.rs"]
mod openssh_cert_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ssh_cert_principals_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ssh_cert_serial_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use openssh_cert_island::{ssh_cert_principals_clamp, ssh_cert_serial_advance};

/// OpenSSH certificate algorithm identifier for Ed25519 v01 certificates.
pub const SSH_ED25519_CERT_ALGO: &[u8] = b"ssh-ed25519-cert-v01@openssh.com";
/// OpenSSH raw Ed25519 key/signature algorithm identifier.
pub const SSH_ED25519_KEY_ALGO: &[u8] = b"ssh-ed25519";
/// Maximum principals accepted per certificate (`ssh_cert_principals_clamp`).
pub const MAX_CERT_PRINCIPALS: u64 = 32;
/// `SSH_CERT_TYPE_USER` (`1`).
pub const SSH_CERT_TYPE_USER: u32 = 1;
/// `SSH_CERT_TYPE_HOST` (`2`).
pub const SSH_CERT_TYPE_HOST: u32 = 2;

contract_fn! {
    /// Verified lower-bound check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ssh_cert_time_valid_isl`.
    #[must_use]
    pub const fn ssh_cert_time_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Decoded `ssh-ed25519-cert-v01@openssh.com` certificate view and canonical fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenSshEd25519Cert {
    /// Per-certificate CSPRNG nonce (`16..=64` bytes in OpenSSH).
    pub nonce: Vec<u8>,
    /// Subject's 32-byte Ed25519 public key.
    pub subject_pk: [u8; 32],
    /// Certificate serial number assigned by the CA.
    pub serial: u64,
    /// `SSH_CERT_TYPE_USER` (`1`) or `SSH_CERT_TYPE_HOST` (`2`).
    pub cert_type: u32,
    /// Human-readable audit key identifier.
    pub key_id: String,
    /// Clamped list of authorized principals (`<= MAX_CERT_PRINCIPALS`).
    pub principals: Vec<String>,
    /// Inclusive start timestamp (Unix seconds).
    pub valid_after: u64,
    /// Exclusive end timestamp (Unix seconds; `u64::MAX` in OpenSSH means forever).
    pub valid_before: u64,
    /// Raw critical options tuple block (non-empty unknown options fail closed on policy check).
    pub critical_options_raw: Vec<u8>,
    /// Issuing CA's 32-byte Ed25519 public key.
    pub ca_pk: [u8; 32],
    /// Raw 64-byte Ed25519 CA signature over `signed_len` prefix bytes.
    pub signature: [u8; 64],
    /// Byte length of the signed prefix in the encoded wire buffer.
    pub signed_len: usize,
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn copy_bytes(slice: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(slice);
    out
}

fn put_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_be_bytes());
}

fn put_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_be_bytes());
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) -> Result<(), &'static str> {
    let n = match u32::try_from(b.len()) {
        Ok(len) => len,
        Err(_) => return Err("ssh string exceeds u32"),
    };
    put_u32(out, n);
    out.extend_from_slice(b);
    Ok(())
}

fn take_u32(inp: &[u8], pos: &mut usize) -> Result<u32, &'static str> {
    let end = match pos.checked_add(4) {
        Some(e) => e,
        None => return Err("ssh u32 overflow"),
    };
    let slice = match inp.get(*pos..end) {
        Some(s) => s,
        None => return Err("truncated ssh u32"),
    };
    let mut b = [0u8; 4];
    b.copy_from_slice(slice);
    *pos = end;
    Ok(u32::from_be_bytes(b))
}

fn take_u64(inp: &[u8], pos: &mut usize) -> Result<u64, &'static str> {
    let end = match pos.checked_add(8) {
        Some(e) => e,
        None => return Err("ssh u64 overflow"),
    };
    let slice = match inp.get(*pos..end) {
        Some(s) => s,
        None => return Err("truncated ssh u64"),
    };
    let mut b = [0u8; 8];
    b.copy_from_slice(slice);
    *pos = end;
    Ok(u64::from_be_bytes(b))
}

fn take_bytes<'a>(inp: &'a [u8], pos: &mut usize) -> Result<&'a [u8], &'static str> {
    let len = take_u32(inp, pos)? as usize;
    let end = match pos.checked_add(len) {
        Some(e) => e,
        None => return Err("ssh string len overflow"),
    };
    let out = match inp.get(*pos..end) {
        Some(s) => s,
        None => return Err("truncated ssh string"),
    };
    *pos = end;
    Ok(out)
}

impl OpenSshEd25519Cert {
    /// Encodes this certificate into canonical `PROTOCOL.certkeys` binary wire format.
    pub fn encode_wire(&self) -> Result<Vec<u8>, &'static str> {
        if self.cert_type != SSH_CERT_TYPE_USER && self.cert_type != SSH_CERT_TYPE_HOST {
            return Err("unsupported ssh cert_type");
        }
        if self.valid_after > self.valid_before {
            return Err("inverted ssh cert validity window");
        }
        let max_p =
            ssh_cert_principals_clamp(self.principals.len() as u64, MAX_CERT_PRINCIPALS) as usize;
        if self.principals.len() > max_p {
            return Err("too many cert principals");
        }
        let mut out = Vec::new();
        put_bytes(&mut out, SSH_ED25519_CERT_ALGO)?;
        put_bytes(&mut out, &self.nonce)?;
        put_bytes(&mut out, &self.subject_pk)?;
        put_u64(&mut out, self.serial);
        put_u32(&mut out, self.cert_type);
        put_bytes(&mut out, self.key_id.as_bytes())?;

        let mut pbuf = Vec::new();
        for p in &self.principals {
            if p.is_empty() {
                return Err("empty principal in cert");
            }
            put_bytes(&mut pbuf, p.as_bytes())?;
        }
        put_bytes(&mut out, &pbuf)?;
        put_u64(&mut out, self.valid_after);
        put_u64(&mut out, self.valid_before);
        put_bytes(&mut out, &self.critical_options_raw)?;
        put_bytes(&mut out, &[])?; // extensions
        put_bytes(&mut out, &[])?; // reserved

        let mut ca_blob = Vec::new();
        put_bytes(&mut ca_blob, SSH_ED25519_KEY_ALGO)?;
        put_bytes(&mut ca_blob, &self.ca_pk)?;
        put_bytes(&mut out, &ca_blob)?;

        let mut sig_blob = Vec::new();
        put_bytes(&mut sig_blob, SSH_ED25519_KEY_ALGO)?;
        put_bytes(&mut sig_blob, &self.signature)?;
        put_bytes(&mut out, &sig_blob)?;
        Ok(out)
    }

    /// Parses canonical `ssh-ed25519-cert-v01@openssh.com` binary bytes fail-closed.
    pub fn decode_wire(wire: &[u8]) -> Result<Self, &'static str> {
        let mut pos = 0usize;
        let algo = take_bytes(wire, &mut pos)?;
        if algo != SSH_ED25519_CERT_ALGO {
            return Err("unexpected ssh cert algorithm");
        }
        let nonce = copy_bytes(take_bytes(wire, &mut pos)?);
        if nonce.is_empty() || nonce.len() > 128 {
            return Err("invalid ssh cert nonce length");
        }
        let pk_raw = take_bytes(wire, &mut pos)?;
        if pk_raw.len() != 32 {
            return Err("subject ed25519 key must be 32 bytes");
        }
        let mut subject_pk = [0u8; 32];
        subject_pk.copy_from_slice(pk_raw);

        let serial = take_u64(wire, &mut pos)?;
        let cert_type = take_u32(wire, &mut pos)?;
        if cert_type != SSH_CERT_TYPE_USER && cert_type != SSH_CERT_TYPE_HOST {
            return Err("unknown ssh cert_type");
        }
        let key_id_bytes = take_bytes(wire, &mut pos)?;
        let key_id_str = match core::str::from_utf8(key_id_bytes) {
            Ok(s) => s,
            Err(_) => return Err("invalid utf8 key_id"),
        };
        let key_id = clone_str(key_id_str);

        let principals_blob = take_bytes(wire, &mut pos)?;
        let mut ppos = 0usize;
        let mut principals = Vec::new();
        while ppos < principals_blob.len() {
            let p_bytes = take_bytes(principals_blob, &mut ppos)?;
            if p_bytes.is_empty() {
                return Err("empty principal entry");
            }
            let p_str = match core::str::from_utf8(p_bytes) {
                Ok(s) => s,
                Err(_) => return Err("invalid utf8 principal"),
            };
            if (principals.len() as u64) >= MAX_CERT_PRINCIPALS {
                return Err("principals exceed MAX_CERT_PRINCIPALS");
            }
            principals.push(clone_str(p_str));
        }

        let valid_after = take_u64(wire, &mut pos)?;
        let valid_before = take_u64(wire, &mut pos)?;
        if valid_after > valid_before {
            return Err("inverted ssh cert validity window");
        }
        let critical_options_raw = copy_bytes(take_bytes(wire, &mut pos)?);
        let _extensions = take_bytes(wire, &mut pos)?;
        let _reserved = take_bytes(wire, &mut pos)?;

        let ca_blob = take_bytes(wire, &mut pos)?;
        let mut cpos = 0usize;
        if take_bytes(ca_blob, &mut cpos)? != SSH_ED25519_KEY_ALGO {
            return Err("ca signature_key must be ssh-ed25519");
        }
        let ca_raw = take_bytes(ca_blob, &mut cpos)?;
        if ca_raw.len() != 32 || cpos != ca_blob.len() {
            return Err("malformed ca signature_key blob");
        }
        let mut ca_pk = [0u8; 32];
        ca_pk.copy_from_slice(ca_raw);

        let signed_len = pos;
        let sig_blob = take_bytes(wire, &mut pos)?;
        if pos != wire.len() {
            return Err("trailing bytes past ssh cert signature");
        }
        let mut spos = 0usize;
        if take_bytes(sig_blob, &mut spos)? != SSH_ED25519_KEY_ALGO {
            return Err("cert signature must be ssh-ed25519");
        }
        let sig_raw = take_bytes(sig_blob, &mut spos)?;
        if sig_raw.len() != 64 || spos != sig_blob.len() {
            return Err("malformed ed25519 signature blob");
        }
        let mut signature = [0u8; 64];
        signature.copy_from_slice(sig_raw);

        Ok(Self {
            nonce,
            subject_pk,
            serial,
            cert_type,
            key_id,
            principals,
            valid_after,
            valid_before,
            critical_options_raw,
            ca_pk,
            signature,
            signed_len,
        })
    }

    /// Checks half-open validity `[valid_after, valid_before)` at `now_sec`.
    #[must_use]
    pub const fn is_valid_at(&self, now_sec: u64) -> bool {
        ssh_cert_time_valid(now_sec, self.valid_after) && now_sec < self.valid_before
    }
}

/// Policy evaluator enforcing trusted CA root, half-open validity window, principal match,
/// fail-closed critical options, and monotone serial high-water mark.
#[derive(Debug, Clone)]
pub struct OpenSshCertPolicy {
    trusted_ca_pk: [u8; 32],
    min_serial_floor: u64,
}

impl OpenSshCertPolicy {
    /// Creates a policy pinned to `trusted_ca_pk` with initial `min_serial_floor`.
    #[must_use]
    pub const fn new(trusted_ca_pk: [u8; 32], min_serial_floor: u64) -> Self {
        Self {
            trusted_ca_pk,
            min_serial_floor,
        }
    }

    /// Current monotone serial floor (`ssh_cert_serial_advance`).
    #[must_use]
    pub const fn min_serial_floor(&self) -> u64 {
        self.min_serial_floor
    }

    /// Advances the minimum accepted certificate serial monotonically (e.g. on CRL rollover).
    pub fn advance_serial_floor(&mut self, candidate_floor: u64) -> u64 {
        let next = ssh_cert_serial_advance(self.min_serial_floor, candidate_floor);
        self.min_serial_floor = next;
        next
    }

    /// Verifies CA pin, serial floor, half-open validity, empty critical options, and required principal.
    pub fn evaluate(
        &self,
        cert: &OpenSshEd25519Cert,
        expected_cert_type: u32,
        required_principal: &str,
        now_sec: u64,
    ) -> Result<(), &'static str> {
        if !astream_digest::ct_eq(&cert.ca_pk, &self.trusted_ca_pk) {
            return Err("untrusted ssh ca key");
        }
        if cert.cert_type != expected_cert_type {
            return Err("cert_type mismatch");
        }
        if !ssh_cert_time_valid(cert.serial, self.min_serial_floor) {
            return Err("certificate serial below floor");
        }
        if !cert.is_valid_at(now_sec) {
            return Err("certificate expired or not yet valid");
        }
        if !cert.critical_options_raw.is_empty() {
            return Err("unrecognized critical_options refused");
        }
        let mut found = false;
        for p in &cert.principals {
            if p == required_principal {
                found = true;
                break;
            }
        }
        if !found {
            return Err("principal not authorized by certificate");
        }
        let mut grant_probe = String::new();
        grant_probe.push_str("rw,p=");
        grant_probe.push_str(required_principal);
        grant_probe.push_str(":/f/alpha/>");
        if astream_cap::Grant::parse(&grant_probe).is_err() {
            return Err("principal incompatible with astream-cap grammar");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_origin_twins_and_ssh_cert_wire_roundtrip_and_policy() {
        for &a in &[0u64, 1, 31, 32, 33, u64::MAX] {
            for &b in &[0u64, 1, 32, 100, u64::MAX] {
                assert_eq!(ssh_cert_principals_clamp(a, b), if a < b { a } else { b });
                assert_eq!(ssh_cert_serial_advance(a, b), if a < b { b } else { a });
                assert_eq!(ssh_cert_time_valid(a, b), b <= a);
            }
        }

        let ca_pk = [0xAA; 32];
        let cert = OpenSshEd25519Cert {
            nonce: vec![0x11; 32],
            subject_pk: [0x22; 32],
            serial: 42,
            cert_type: SSH_CERT_TYPE_USER,
            key_id: "alice@aterm".to_owned(),
            principals: vec!["h-alice".to_owned(), "n-0123456789abcdef".to_owned()],
            valid_after: 1_700_000_000,
            valid_before: 1_700_003_600,
            critical_options_raw: Vec::new(),
            ca_pk,
            signature: [0x55; 64],
            signed_len: 0,
        };
        let wire = cert.encode_wire().unwrap();
        let decoded = OpenSshEd25519Cert::decode_wire(&wire).unwrap();
        assert_eq!(decoded.serial, 42);
        assert_eq!(decoded.principals, cert.principals);
        assert!(decoded.signed_len > 100 && decoded.signed_len < wire.len());

        let mut policy = OpenSshCertPolicy::new(ca_pk, 40);
        assert!(policy
            .evaluate(&decoded, SSH_CERT_TYPE_USER, "h-alice", 1_700_000_000)
            .is_ok());
        // Half-open boundary: valid_before is expired!
        assert!(policy
            .evaluate(&decoded, SSH_CERT_TYPE_USER, "h-alice", 1_700_003_600)
            .is_err());
        assert!(policy
            .evaluate(&decoded, SSH_CERT_TYPE_USER, "h-bob", 1_700_000_100)
            .is_err());

        // Advancing serial floor past 42 fences older cert serials monotonically.
        assert_eq!(policy.advance_serial_floor(50), 50);
        assert_eq!(policy.advance_serial_floor(10), 50);
        assert!(policy
            .evaluate(&decoded, SSH_CERT_TYPE_USER, "h-alice", 1_700_000_100)
            .is_err());
    }
}
