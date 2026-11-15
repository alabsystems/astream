// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(
    clippy::manual_is_multiple_of,
    clippy::manual_ok_err,
    clippy::manual_unwrap_or_default,
    clippy::match_ref_pats,
    clippy::needless_borrows_for_generic_args
)]

//! Pure-Rust Kafka SASL authentication (`SASL_HANDSHAKE` key 17 v0..=1,
//! `SASL_AUTHENTICATE` key 36 v0..=2 including KIP-482 flexible v2) with RFC 4616
//! `PLAIN` and RFC 5802 / RFC 7677 `SCRAM-SHA-256` (`Astream.Kafka.TlaSaslAuth`).
//!
//! Built directly on `astream-digest` (`Sha256`, `hmac_sha256_parts`, `ct_eq`) with
//! zero third-party dependencies, zero closures, and bounded allocations.

use crate::record_batch::encode_i64_be;
use crate::{
    frame_response_for, put_compact_nullable_str, put_empty_tags, put_i16, put_i32, put_str,
    put_uvarint, skip_tag_buffer, take_i32, take_kstring_len, take_uvarint, ReqHeader,
    API_VERSIONS, NONE, UNSUPPORTED_VERSION,
};
use astream_digest::{ct_eq, hmac_sha256_parts, Sha256};

#[cfg(clean_islands)]
#[path = "sasl_island.rs"]
mod sasl_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{kafka_sasl_pbkdf2_clamp, kafka_sasl_phase_advance};
#[cfg(clean_islands)]
pub use sasl_island::{kafka_sasl_pbkdf2_clamp, kafka_sasl_phase_advance};

contract_fn! {
    /// Verified check that a SASL connection phase equals `PHASE_AUTHENTICATED` (`3`),
    /// linked via `clean-kernel-defeq` to `kafka_sasl_is_authenticated_isl`.
    #[must_use]
    pub const fn kafka_sasl_is_authenticated(phase: u64) -> bool
    clauses [ensures result == (phase == 3)]
    {
        phase == 3
    }
}

/// Kafka API key 17: `SaslHandshake` (v0..=1).
pub const SASL_HANDSHAKE: i16 = 17;

/// Kafka API key 36: `SaslAuthenticate` (v0..=2, KIP-152 / KIP-482).
pub const SASL_AUTHENTICATE: i16 = 36;

/// Kafka error code 33: requested SASL mechanism is not enabled on this broker.
pub const UNSUPPORTED_SASL_MECHANISM: i16 = 33;

/// Kafka error code 34: request is not valid given the current SASL state.
pub const ILLEGAL_SASL_STATE: i16 = 34;

/// Kafka error code 58: SASL authentication failed.
pub const SASL_AUTHENTICATION_FAILED: i16 = 58;

/// Maximum SASL token size accepted by the codec (`64 KiB`).
pub const MAX_SASL_TOKEN_BYTES: usize = 64 * 1024;

/// Maximum PBKDF2-HMAC-SHA-256 iteration count (`65_536`).
pub const MAX_PBKDF2_ITERS: u32 = 65_536;

/// Default SCRAM-SHA-256 iteration count (`4_096`, RFC 7677 §4 minimum).
pub const DEFAULT_SCRAM_ITERS: u32 = 4_096;

/// Phase 0: initial unauthenticated connection state.
pub const PHASE_UNAUTHENTICATED: u64 = 0;
/// Phase 1: `SaslHandshake` succeeded and selected a mechanism.
pub const PHASE_HANDSHAKEN: u64 = 1;
/// Phase 2: `SCRAM-SHA-256` server-first challenge emitted, awaiting client-final proof.
pub const PHASE_SCRAM_CHALLENGE: u64 = 2;
/// Phase 3: SASL authentication succeeded; data-plane APIs are unlocked.
pub const PHASE_AUTHENTICATED: u64 = 3;
/// Phase 4: terminal authentication failure; no subsequent transition can reach `3`.
pub const PHASE_FAILED: u64 = 4;

/// Supported Kafka SASL mechanisms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SaslMechanism {
    /// RFC 4616 `PLAIN`.
    Plain,
    /// RFC 5802 / RFC 7677 `SCRAM-SHA-256`.
    ScramSha256,
}

impl SaslMechanism {
    /// Canonical IANA / Kafka wire name for this mechanism.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Plain => "PLAIN",
            Self::ScramSha256 => "SCRAM-SHA-256",
        }
    }

    /// Parse a wire mechanism name (`"PLAIN"` or `"SCRAM-SHA-256"`).
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        if name == "PLAIN" {
            Some(Self::Plain)
        } else if name == "SCRAM-SHA-256" {
            Some(Self::ScramSha256)
        } else {
            None
        }
    }
}

/// Pre-hashed credential record for one SASL user (stores no plaintext password).
#[derive(Debug, Clone)]
pub struct SaslUserRecord {
    pub username: String,
    pub salt: [u8; 16],
    pub iterations: u32,
    pub stored_key: [u8; 32],
    pub server_key: [u8; 32],
    pub plain_verifier: [u8; 32],
}

/// Broker-side SASL authenticator configuration.
#[derive(Debug, Clone)]
pub struct SaslConfig {
    mechanisms: Vec<SaslMechanism>,
    users: Vec<SaslUserRecord>,
    server_nonce_seed: [u8; 32],
    session_lifetime_ms: i64,
}

/// Per-connection SASL state machine (`Astream.Kafka.TlaSaslAuth`).
#[derive(Debug, Clone)]
pub struct SaslSession {
    phase: u64,
    mechanism: Option<SaslMechanism>,
    authenticated_user: Option<String>,
    scram_pending: Option<ScramServerPending>,
    turn_counter: u64,
}

#[derive(Debug, Clone)]
struct ScramServerPending {
    username: String,
    stored_key: [u8; 32],
    server_key: [u8; 32],
    full_nonce: String,
    client_first_bare: String,
    server_first: String,
}

/// Decoded `SaslAuthenticate` response payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SaslAuthOutcome {
    pub error_code: i16,
    pub error_message: Option<String>,
    pub auth_bytes: Vec<u8>,
    pub session_lifetime_ms: i64,
}

#[must_use]
const fn b64_char(v: u32) -> u8 {
    let idx = (v & 0x3f) as u8;
    if idx < 26 {
        b'A' + idx
    } else if idx < 52 {
        b'a' + (idx - 26)
    } else if idx < 62 {
        b'0' + (idx - 52)
    } else if idx == 62 {
        b'+'
    } else {
        b'/'
    }
}

#[must_use]
const fn xor_32(a: [u8; 32], b: [u8; 32]) -> [u8; 32] {
    let [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31] =
        a;
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
        b;
    [
        a0 ^ b0,
        a1 ^ b1,
        a2 ^ b2,
        a3 ^ b3,
        a4 ^ b4,
        a5 ^ b5,
        a6 ^ b6,
        a7 ^ b7,
        a8 ^ b8,
        a9 ^ b9,
        a10 ^ b10,
        a11 ^ b11,
        a12 ^ b12,
        a13 ^ b13,
        a14 ^ b14,
        a15 ^ b15,
        a16 ^ b16,
        a17 ^ b17,
        a18 ^ b18,
        a19 ^ b19,
        a20 ^ b20,
        a21 ^ b21,
        a22 ^ b22,
        a23 ^ b23,
        a24 ^ b24,
        a25 ^ b25,
        a26 ^ b26,
        a27 ^ b27,
        a28 ^ b28,
        a29 ^ b29,
        a30 ^ b30,
        a31 ^ b31,
    ]
}

#[must_use]
const fn clamp_usize(val: usize, cap: usize) -> usize {
    if val < cap {
        val
    } else {
        cap
    }
}

/// Pure-Rust RFC 4648 standard Base64 encoder.
#[must_use]
pub fn base64_encode(input: &[u8]) -> String {
    let clamped_len = clamp_usize(input.len(), MAX_SASL_TOKEN_BYTES);
    let src = input.get(..clamped_len).unwrap_or(input);
    let mut out = Vec::new();
    let mut rest = src;
    while let &[b0, b1, b2, ref tail @ ..] = rest {
        let triple = ((b0 as u32) << 16) | ((b1 as u32) << 8) | (b2 as u32);
        out.push(b64_char(triple >> 18));
        out.push(b64_char(triple >> 12));
        out.push(b64_char(triple >> 6));
        out.push(b64_char(triple));
        rest = tail;
    }
    match rest {
        &[b0] => {
            let triple = (b0 as u32) << 16;
            out.push(b64_char(triple >> 18));
            out.push(b64_char(triple >> 12));
            out.push(b'=');
            out.push(b'=');
        }
        &[b0, b1] => {
            let triple = ((b0 as u32) << 16) | ((b1 as u32) << 8);
            out.push(b64_char(triple >> 18));
            out.push(b64_char(triple >> 12));
            out.push(b64_char(triple >> 6));
            out.push(b'=');
        }
        _ => {}
    }
    match String::from_utf8(out) {
        Ok(s) => s,
        Err(_) => String::new(),
    }
}

#[must_use]
const fn b64_val(b: u8) -> Option<u8> {
    match b {
        b'A'..=b'Z' => Some(b - b'A'),
        b'a'..=b'z' => Some(b - b'a' + 26),
        b'0'..=b'9' => Some(b - b'0' + 52),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

/// Pure-Rust RFC 4648 standard Base64 decoder with strict length and canonical-padding checks.
#[must_use]
pub fn base64_decode(s: &str) -> Option<Vec<u8>> {
    let raw = s.as_bytes();
    if raw.is_empty() {
        return Some(Vec::new());
    }
    if raw.len() > MAX_SASL_TOKEN_BYTES * 2 || raw.len() % 4 != 0 {
        return None;
    }
    let mut out = Vec::new();
    let mut rest = raw;
    while let &[c0, c1, c2, c3, ref tail @ ..] = rest {
        let v0 = b64_val(c0)? as u32;
        let v1 = b64_val(c1)? as u32;
        let is_last = tail.is_empty();
        if c2 == b'=' {
            if !is_last || c3 != b'=' || (v1 & 0x0f) != 0 {
                return None;
            }
            let triple = (v0 << 18) | (v1 << 12);
            out.push(((triple >> 16) & 0xff) as u8);
        } else if c3 == b'=' {
            if !is_last {
                return None;
            }
            let v2 = b64_val(c2)? as u32;
            if (v2 & 0x03) != 0 {
                return None;
            }
            let triple = (v0 << 18) | (v1 << 12) | (v2 << 6);
            out.push(((triple >> 16) & 0xff) as u8);
            out.push(((triple >> 8) & 0xff) as u8);
        } else {
            let v2 = b64_val(c2)? as u32;
            let v3 = b64_val(c3)? as u32;
            let triple = (v0 << 18) | (v1 << 12) | (v2 << 6) | v3;
            out.push(((triple >> 16) & 0xff) as u8);
            out.push(((triple >> 8) & 0xff) as u8);
            out.push((triple & 0xff) as u8);
        }
        rest = tail;
    }
    Some(out)
}

/// Pure-Rust PBKDF2-HMAC-SHA-256 (RFC 2898 / RFC 5802 `Hi`), producing one 32-byte derived block
/// with iteration count clamped to `1..=MAX_PBKDF2_ITERS` via Clean-origin [`kafka_sasl_pbkdf2_clamp`].
#[must_use]
pub fn pbkdf2_hmac_sha256_32(password: &[u8], salt: &[u8], iterations: u32) -> [u8; 32] {
    let clamped = kafka_sasl_pbkdf2_clamp(iterations as u64, MAX_PBKDF2_ITERS as u64) as u32;
    let iters = if clamped == 0 { 1 } else { clamped };
    let block_idx: [u8; 4] = [0, 0, 0, 1];
    let mut u = hmac_sha256_parts(password, &[salt, &block_idx]);
    let mut acc = u;
    let mut step = 1u32;
    while step < iters {
        u = hmac_sha256_parts(password, &[&u]);
        acc = xor_32(acc, u);
        step = step.saturating_add(1);
    }
    acc
}

/// Derive `(stored_key, server_key)` per RFC 5802 §3 from `(password, salt, iterations)`.
#[must_use]
pub fn scram_sha256_keys(password: &[u8], salt: &[u8], iterations: u32) -> ([u8; 32], [u8; 32]) {
    let salted = pbkdf2_hmac_sha256_32(password, salt, iterations);
    let client_key = hmac_sha256_parts(&salted, &[b"Client Key"]);
    let stored_key = Sha256::digest(&client_key);
    let server_key = hmac_sha256_parts(&salted, &[b"Server Key"]);
    (stored_key, server_key)
}

fn plain_verifier_tag(salt: &[u8; 16], password: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(salt, &[b"astream-kafka-plain-v1:", password])
}

/// Escape `=` (`=3D`) and `,` (`=2C`) in a SCRAM username (`saslname`, RFC 5802 §5.1).
#[must_use]
pub fn scram_escape_username(username: &str) -> String {
    let bytes = username.as_bytes();
    let mut out = Vec::new();
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b == b'=' {
            out.extend_from_slice(b"=3D");
        } else if b == b',' {
            out.extend_from_slice(b"=2C");
        } else {
            out.push(b);
        }
        rest = tail;
    }
    match String::from_utf8(out) {
        Ok(s) => s,
        Err(_) => String::new(),
    }
}

/// Unescape `=3D` (`=`) and `=2C` (`,`) in a SCRAM `saslname` attribute, failing closed on bare
/// `=` sequences as required by RFC 5802 §5.1.
#[must_use]
pub fn scram_unescape_username(escaped: &str) -> Option<String> {
    let raw = escaped.as_bytes();
    if raw.len() > MAX_SASL_TOKEN_BYTES {
        return None;
    }
    let mut out = Vec::new();
    let mut rest = raw;
    while let &[b, ref tail @ ..] = rest {
        if b == b'=' {
            let &[c1, c2, ref after_esc @ ..] = tail else {
                return None;
            };
            if c1 == b'3' && (c2 == b'D' || c2 == b'd') {
                out.push(b'=');
                rest = after_esc;
            } else if c1 == b'2' && (c2 == b'C' || c2 == b'c') {
                out.push(b',');
                rest = after_esc;
            } else {
                return None;
            }
        } else if b == b'\0' {
            return None;
        } else {
            out.push(b);
            rest = tail;
        }
    }
    match String::from_utf8(out) {
        Ok(s) => Some(s),
        Err(_) => None,
    }
}

impl SaslConfig {
    /// Construct a SASL configuration advertising both `PLAIN` and `SCRAM-SHA-256`.
    #[must_use]
    pub fn new(server_nonce_seed: [u8; 32]) -> Self {
        Self {
            mechanisms: vec![SaslMechanism::Plain, SaslMechanism::ScramSha256],
            users: Vec::new(),
            server_nonce_seed,
            session_lifetime_ms: 0,
        }
    }

    /// Restrict the advertised/accepted mechanisms (for example `[SaslMechanism::ScramSha256]` only).
    #[must_use]
    pub fn with_mechanisms(mut self, mechanisms: &[SaslMechanism]) -> Self {
        let count = clamp_usize(mechanisms.len(), 8);
        let head = mechanisms.get(..count).unwrap_or(mechanisms);
        let mut list = Vec::new();
        let mut rest = head;
        while let &[m, ref tail @ ..] = rest {
            list.push(m);
            rest = tail;
        }
        self.mechanisms = list;
        self
    }

    /// Configure the positive session lifetime (ms) reported in `SaslAuthenticate` v1+ responses.
    #[must_use]
    pub const fn with_session_lifetime_ms(mut self, ms: i64) -> Self {
        self.session_lifetime_ms = if ms < 0 { 0 } else { ms };
        self
    }

    /// Register a user credential with explicit salt and SCRAM iteration count (`1..=65_536`).
    pub fn add_user(&mut self, username: &str, password: &[u8], salt: [u8; 16], iterations: u32) {
        let clamped_iters =
            kafka_sasl_pbkdf2_clamp(iterations as u64, MAX_PBKDF2_ITERS as u64) as u32;
        let iters = if clamped_iters == 0 { 1 } else { clamped_iters };
        let (stored_key, server_key) = scram_sha256_keys(password, &salt, iters);
        let plain_verifier = plain_verifier_tag(&salt, password);
        let rec = SaslUserRecord {
            username: username.to_owned(),
            salt,
            iterations: iters,
            stored_key,
            server_key,
            plain_verifier,
        };
        for existing in &mut self.users {
            if existing.username == username {
                *existing = rec;
                return;
            }
        }
        self.users.push(rec);
    }

    /// Enabled SASL mechanisms in advertisement order.
    #[must_use]
    pub fn mechanisms(&self) -> &[SaslMechanism] {
        &self.mechanisms
    }

    fn supports(&self, m: SaslMechanism) -> bool {
        let mut rest = self.mechanisms.as_slice();
        while let &[cand, ref tail @ ..] = rest {
            if cand == m {
                return true;
            }
            rest = tail;
        }
        false
    }

    fn find_user(&self, username: &str) -> Option<&SaslUserRecord> {
        let mut rest = self.users.as_slice();
        while let [user, ref tail @ ..] = rest {
            if user.username == username {
                return Some(user);
            }
            rest = tail;
        }
        None
    }

    fn derive_server_nonce(&self, client_nonce: &str, turn: u64) -> String {
        let turn_bytes = turn.to_le_bytes();
        let digest = hmac_sha256_parts(
            &self.server_nonce_seed,
            &[b"scram-server-nonce:", client_nonce.as_bytes(), &turn_bytes],
        );
        base64_encode(digest.get(..18).unwrap_or(&digest))
    }
}

impl Default for SaslSession {
    fn default() -> Self {
        Self::new()
    }
}

impl SaslSession {
    /// Start a new connection in `PHASE_UNAUTHENTICATED` (`0`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            phase: PHASE_UNAUTHENTICATED,
            mechanism: None,
            authenticated_user: None,
            scram_pending: None,
            turn_counter: 0,
        }
    }

    /// Current Clean-verified monotone phase (`0..=4`).
    #[must_use]
    pub const fn phase(&self) -> u64 {
        self.phase
    }

    /// Whether this session has completed SASL authentication (`phase == 3`).
    #[must_use]
    pub const fn is_authenticated(&self) -> bool {
        kafka_sasl_is_authenticated(self.phase)
    }

    /// Whether this session has permanently failed authentication (`phase == 4`).
    #[must_use]
    pub const fn is_failed(&self) -> bool {
        self.phase >= PHASE_FAILED
    }

    /// Username authenticated on this connection, once [`Self::is_authenticated`] holds.
    #[must_use]
    pub fn authenticated_user(&self) -> Option<&str> {
        if self.is_authenticated() {
            self.authenticated_user.as_deref()
        } else {
            None
        }
    }

    /// Check whether `(api_key)` is permitted in the current SASL session state.
    ///
    /// Before `PHASE_AUTHENTICATED`, only `ApiVersions` (`18`), `SaslHandshake` (`17`),
    /// and `SaslAuthenticate` (`36`) may execute.
    #[must_use]
    pub const fn allows_api(&self, api_key: i16) -> bool {
        if self.is_failed() {
            return false;
        }
        if self.is_authenticated() {
            return true;
        }
        api_key == API_VERSIONS || api_key == SASL_HANDSHAKE || api_key == SASL_AUTHENTICATE
    }

    fn advance_to(&mut self, next_phase: u64) {
        self.phase = kafka_sasl_phase_advance(self.phase, next_phase);
    }

    fn fail(&mut self) {
        self.scram_pending = None;
        self.authenticated_user = None;
        self.advance_to(PHASE_FAILED);
    }

    /// Process a `SaslHandshake` (`v0..=1`) mechanism selection.
    pub fn handle_handshake(&mut self, cfg: &SaslConfig, mechanism_name: &str) -> i16 {
        if self.phase != PHASE_UNAUTHENTICATED {
            self.fail();
            return ILLEGAL_SASL_STATE;
        }
        let Some(mech) = SaslMechanism::parse(mechanism_name) else {
            self.fail();
            return UNSUPPORTED_SASL_MECHANISM;
        };
        if !cfg.supports(mech) {
            self.fail();
            return UNSUPPORTED_SASL_MECHANISM;
        }
        self.mechanism = Some(mech);
        self.advance_to(PHASE_HANDSHAKEN);
        NONE
    }

    /// Process one `SaslAuthenticate` (`v0..=2`) token exchange step.
    pub fn handle_authenticate(&mut self, cfg: &SaslConfig, auth_bytes: &[u8]) -> SaslAuthOutcome {
        if auth_bytes.len() > MAX_SASL_TOKEN_BYTES {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SASL token exceeds maximum allowed size".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        let Some(mech) = self.mechanism else {
            self.fail();
            return SaslAuthOutcome {
                error_code: ILLEGAL_SASL_STATE,
                error_message: Some("SaslAuthenticate sent before SaslHandshake".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        match mech {
            SaslMechanism::Plain => self.authenticate_plain(cfg, auth_bytes),
            SaslMechanism::ScramSha256 => self.authenticate_scram(cfg, auth_bytes),
        }
    }

    fn authenticate_plain(&mut self, cfg: &SaslConfig, auth_bytes: &[u8]) -> SaslAuthOutcome {
        if self.phase != PHASE_HANDSHAKEN {
            self.fail();
            return SaslAuthOutcome {
                error_code: ILLEGAL_SASL_STATE,
                error_message: Some("PLAIN requires PHASE_HANDSHAKEN".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        let Some((authzid, authcid, passwd)) = parse_plain_token(auth_bytes) else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("malformed SASL PLAIN token".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        if !authzid.is_empty() && authzid != authcid {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SASL PLAIN authzid mismatch".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        let Some(user) = cfg.find_user(authcid) else {
            // Constant-time dummy HMAC so unknown-user and bad-password paths do equal work.
            let dummy = plain_verifier_tag(&[0u8; 16], passwd);
            let _ = ct_eq(&dummy, &[0xffu8; 32]);
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("invalid SASL PLAIN credentials".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        let candidate = plain_verifier_tag(&user.salt, passwd);
        if !ct_eq(&candidate, &user.plain_verifier) {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("invalid SASL PLAIN credentials".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        self.authenticated_user = Some(user.username.clone());
        self.advance_to(PHASE_AUTHENTICATED);
        SaslAuthOutcome {
            error_code: NONE,
            error_message: None,
            auth_bytes: Vec::new(),
            session_lifetime_ms: cfg.session_lifetime_ms,
        }
    }

    fn authenticate_scram(&mut self, cfg: &SaslConfig, auth_bytes: &[u8]) -> SaslAuthOutcome {
        let Ok(msg) = core::str::from_utf8(auth_bytes) else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SCRAM message is not valid UTF-8".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        if self.phase == PHASE_HANDSHAKEN {
            self.scram_step_first(cfg, msg)
        } else if self.phase == PHASE_SCRAM_CHALLENGE {
            self.scram_step_final(cfg, msg)
        } else {
            self.fail();
            SaslAuthOutcome {
                error_code: ILLEGAL_SASL_STATE,
                error_message: Some("unexpected SCRAM state".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            }
        }
    }

    fn scram_step_first(&mut self, cfg: &SaslConfig, msg: &str) -> SaslAuthOutcome {
        let Some((username, client_nonce, bare)) = parse_scram_client_first(msg) else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("malformed SCRAM client-first-message".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        let Some(user) = cfg.find_user(&username) else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("unknown SCRAM principal".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        self.turn_counter = self.turn_counter.saturating_add(1);
        let s_nonce = cfg.derive_server_nonce(client_nonce, self.turn_counter);
        let mut full_nonce = String::new();
        full_nonce.push_str(client_nonce);
        full_nonce.push_str(&s_nonce);
        let salt_b64 = base64_encode(&user.salt);
        let server_first = format!("r={full_nonce},s={salt_b64},i={}", user.iterations);
        let reply_bytes = server_first.as_bytes().to_vec();
        self.scram_pending = Some(ScramServerPending {
            username: user.username.clone(),
            stored_key: user.stored_key,
            server_key: user.server_key,
            full_nonce,
            client_first_bare: bare.to_owned(),
            server_first,
        });
        self.advance_to(PHASE_SCRAM_CHALLENGE);
        SaslAuthOutcome {
            error_code: NONE,
            error_message: None,
            auth_bytes: reply_bytes,
            session_lifetime_ms: 0,
        }
    }

    fn scram_step_final(&mut self, cfg: &SaslConfig, msg: &str) -> SaslAuthOutcome {
        let Some(pending) = self.scram_pending.take() else {
            self.fail();
            return SaslAuthOutcome {
                error_code: ILLEGAL_SASL_STATE,
                error_message: Some("missing pending SCRAM challenge".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        let Some((channel_binding, nonce, without_proof, proof_b64)) =
            parse_scram_client_final(msg)
        else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("malformed SCRAM client-final-message".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        // "biws" is base64("n,,") for GS2 header without channel binding.
        if channel_binding != "biws" || nonce != pending.full_nonce {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SCRAM nonce or channel-binding mismatch".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        let Some(proof_bytes) = base64_decode(proof_b64) else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("invalid base64 in SCRAM client proof".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        let Ok(proof_arr): Result<[u8; 32], _> = proof_bytes.as_slice().try_into() else {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SCRAM client proof must be 32 bytes".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        };
        let client_sig = hmac_sha256_parts(
            &pending.stored_key,
            &[
                pending.client_first_bare.as_bytes(),
                b",",
                pending.server_first.as_bytes(),
                b",",
                without_proof.as_bytes(),
            ],
        );
        let recovered_client_key = xor_32(proof_arr, client_sig);
        let candidate_stored = Sha256::digest(&recovered_client_key);
        if !ct_eq(&candidate_stored, &pending.stored_key) {
            self.fail();
            return SaslAuthOutcome {
                error_code: SASL_AUTHENTICATION_FAILED,
                error_message: Some("SCRAM client proof verification failed".to_owned()),
                auth_bytes: Vec::new(),
                session_lifetime_ms: 0,
            };
        }
        let server_sig = hmac_sha256_parts(
            &pending.server_key,
            &[
                pending.client_first_bare.as_bytes(),
                b",",
                pending.server_first.as_bytes(),
                b",",
                without_proof.as_bytes(),
            ],
        );
        let server_final = format!("v={}", base64_encode(&server_sig));
        self.authenticated_user = Some(pending.username);
        self.advance_to(PHASE_AUTHENTICATED);
        SaslAuthOutcome {
            error_code: NONE,
            error_message: None,
            auth_bytes: server_final.into_bytes(),
            session_lifetime_ms: cfg.session_lifetime_ms,
        }
    }
}

/// Build an RFC 4616 `PLAIN` client token (`[authzid] \0 authcid \0 password`).
#[must_use]
pub fn build_plain_token(authzid: &str, username: &str, password: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(authzid.as_bytes());
    out.push(0);
    out.extend_from_slice(username.as_bytes());
    out.push(0);
    out.extend_from_slice(password);
    out
}

fn split_once_nul(raw: &[u8]) -> Option<(&[u8], &[u8])> {
    let mut i = 0usize;
    let mut rest = raw;
    while let &[b, ref tail @ ..] = rest {
        if b == 0 {
            let head = raw.get(..i)?;
            return Some((head, tail));
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    None
}

fn contains_nul(raw: &[u8]) -> bool {
    let mut rest = raw;
    while let &[b, ref tail @ ..] = rest {
        if b == 0 {
            return true;
        }
        rest = tail;
    }
    false
}

fn parse_plain_token(raw: &[u8]) -> Option<(&str, &str, &[u8])> {
    let (authzid_raw, after_first) = split_once_nul(raw)?;
    let (authcid_raw, passwd) = split_once_nul(after_first)?;
    if contains_nul(passwd) {
        // Embedded NUL inside password or extra delimiter is forbidden by RFC 4616.
        return None;
    }
    let Ok(authzid) = core::str::from_utf8(authzid_raw) else {
        return None;
    };
    let Ok(authcid) = core::str::from_utf8(authcid_raw) else {
        return None;
    };
    if authcid.is_empty() || passwd.is_empty() {
        return None;
    }
    Some((authzid, authcid, passwd))
}

fn parse_scram_client_first(msg: &str) -> Option<(String, &str, &str)> {
    // GS2 header without channel binding must start with "n,," (RFC 5802 §7).
    let bare = msg.strip_prefix("n,,")?;
    // Allow optional `m=` rejection: mandatory extensions (`m=`) are unsupported and MUST fail.
    if bare.starts_with("m=") {
        return None;
    }
    let rest_after_n = bare.strip_prefix("n=")?;
    let (escaped_user, after_user) = rest_after_n.split_once(',')?;
    let username = scram_unescape_username(escaped_user)?;
    if username.is_empty() {
        return None;
    }
    let r_part = after_user.strip_prefix("r=")?;
    let nonce = match r_part.split_once(',') {
        Some((head, _)) => head,
        None => r_part,
    };
    if nonce.is_empty() {
        return None;
    }
    Some((username, nonce, bare))
}

fn parse_scram_client_final(msg: &str) -> Option<(&str, &str, &str, &str)> {
    // Format: `c=<b64>,r=<nonce>[,ext...],p=<b64_proof>`
    let (without_proof, proof_b64) = msg.rsplit_once(",p=")?;
    if proof_b64.is_empty() || proof_b64.contains(',') {
        return None;
    }
    let after_c = without_proof.strip_prefix("c=")?;
    let (c_val, after_comma) = after_c.split_once(',')?;
    let r_part = after_comma.strip_prefix("r=")?;
    let nonce = match r_part.split_once(',') {
        Some((head, _)) => head,
        None => r_part,
    };
    if c_val.is_empty() || nonce.is_empty() {
        return None;
    }
    Some((c_val, nonce, without_proof, proof_b64))
}

/// Client-side RFC 5802 / RFC 7677 `SCRAM-SHA-256` handshake helper.
#[derive(Debug, Clone)]
pub struct ScramSha256Client {
    client_nonce: String,
    client_first_bare: String,
    server_first: Option<String>,
    server_sig_expected: Option<[u8; 32]>,
}

impl ScramSha256Client {
    /// Construct a client SCRAM-SHA-256 handshake state and return the `client-first-message` bytes.
    #[must_use]
    pub fn start(username: &str, client_nonce: &str) -> (Self, Vec<u8>) {
        let escaped = scram_escape_username(username);
        let bare = format!("n={escaped},r={client_nonce}");
        let msg = format!("n,,{bare}");
        (
            Self {
                client_nonce: client_nonce.to_owned(),
                client_first_bare: bare,
                server_first: None,
                server_sig_expected: None,
            },
            msg.into_bytes(),
        )
    }

    /// Consume `server-first-message` bytes and compute the `client-final-message` bytes.
    pub fn step_server_first(
        &mut self,
        password: &[u8],
        server_first_bytes: &[u8],
    ) -> Option<Vec<u8>> {
        let Ok(server_first) = core::str::from_utf8(server_first_bytes) else {
            return None;
        };
        // Parse `r=<nonce>,s=<salt_b64>,i=<iters>`
        let after_r = server_first.strip_prefix("r=")?;
        let (full_nonce, after_c1) = after_r.split_once(',')?;
        if !full_nonce.starts_with(&self.client_nonce)
            || full_nonce.len() <= self.client_nonce.len()
        {
            return None;
        }
        let after_s = after_c1.strip_prefix("s=")?;
        let (salt_b64, after_c2) = after_s.split_once(',')?;
        let salt = base64_decode(salt_b64)?;
        let i_str = after_c2.strip_prefix("i=")?;
        let iters_str = match i_str.split_once(',') {
            Some((head, _)) => head,
            None => i_str,
        };
        let Ok(iters) = iters_str.parse::<u32>() else {
            return None;
        };
        if iters == 0 || iters > MAX_PBKDF2_ITERS {
            return None;
        }

        let salted = pbkdf2_hmac_sha256_32(password, &salt, iters);
        let client_key = hmac_sha256_parts(&salted, &[b"Client Key"]);
        let stored_key = Sha256::digest(&client_key);
        let server_key = hmac_sha256_parts(&salted, &[b"Server Key"]);

        let without_proof = format!("c=biws,r={full_nonce}");
        let client_sig = hmac_sha256_parts(
            &stored_key,
            &[
                self.client_first_bare.as_bytes(),
                b",",
                server_first.as_bytes(),
                b",",
                without_proof.as_bytes(),
            ],
        );
        let proof = xor_32(client_key, client_sig);
        let server_sig = hmac_sha256_parts(
            &server_key,
            &[
                self.client_first_bare.as_bytes(),
                b",",
                server_first.as_bytes(),
                b",",
                without_proof.as_bytes(),
            ],
        );
        self.server_first = Some(server_first.to_owned());
        self.server_sig_expected = Some(server_sig);
        let final_msg = format!("{without_proof},p={}", base64_encode(&proof));
        Some(final_msg.into_bytes())
    }

    /// Verify the broker's `server-final-message` (`v=<base64(server_sig)>`) in constant time.
    #[must_use]
    pub fn verify_server_final(&self, server_final_bytes: &[u8]) -> bool {
        let Some(expected) = &self.server_sig_expected else {
            return false;
        };
        let Ok(s) = core::str::from_utf8(server_final_bytes) else {
            return false;
        };
        let Some(v_b64) = s.strip_prefix("v=") else {
            return false;
        };
        let Some(decoded) = base64_decode(v_b64) else {
            return false;
        };
        ct_eq(&decoded, expected)
    }
}

// ---- Kafka wire codec for SaslHandshake (17) and SaslAuthenticate (36) ----

/// Encode a `SaslHandshake` (`v0..=1`) request frame (without outer 4-byte size prefix).
#[must_use]
pub fn encode_sasl_handshake_request(
    api_version: i16,
    correlation_id: i32,
    client_id: &str,
    mechanism: &str,
) -> Vec<u8> {
    let mut out = Vec::new();
    put_i16(&mut out, SASL_HANDSHAKE);
    put_i16(&mut out, api_version);
    put_i32(&mut out, correlation_id);
    put_str(&mut out, client_id);
    put_str(&mut out, mechanism);
    out
}

/// Encode a `SaslAuthenticate` (`v0..=2`) request body (without outer 4-byte size prefix).
#[must_use]
pub fn encode_sasl_authenticate_request(
    api_version: i16,
    correlation_id: i32,
    client_id: &str,
    auth_bytes: &[u8],
) -> Vec<u8> {
    let clamped_len = clamp_usize(auth_bytes.len(), MAX_SASL_TOKEN_BYTES);
    let clamped = auth_bytes.get(..clamped_len).unwrap_or(auth_bytes);
    let mut out = Vec::new();
    put_i16(&mut out, SASL_AUTHENTICATE);
    put_i16(&mut out, api_version);
    put_i32(&mut out, correlation_id);
    put_str(&mut out, client_id);
    if api_version >= 2 {
        // KIP-482 Request Header v2 empty TAG_BUFFER
        put_empty_tags(&mut out);
        // COMPACT_BYTES: uvarint(len + 1) + bytes
        put_uvarint(&mut out, (clamped.len() as u32).saturating_add(1));
        out.extend_from_slice(clamped);
        put_empty_tags(&mut out);
    } else {
        put_i32(&mut out, clamped.len() as i32);
        out.extend_from_slice(clamped);
    }
    out
}

/// Answer a `SaslHandshake` (`api_key = 17`, `v0..=1`) request against `session` and `cfg`.
pub fn respond_sasl_handshake(
    hdr: &ReqHeader,
    body: &[u8],
    cfg: &SaslConfig,
    session: &mut SaslSession,
) -> Option<Vec<u8>> {
    if hdr.api_version < 0 || hdr.api_version > 1 {
        let mut p = Vec::with_capacity(8);
        put_i16(&mut p, UNSUPPORTED_VERSION);
        put_i32(&mut p, 0);
        return frame_response_for(hdr.api_key, hdr.api_version, hdr.correlation_id, &p);
    }
    let (Some(len), after_len) = take_kstring_len(body)? else {
        return None;
    };
    let mech_slice = after_len.get(..len)?;
    let tail = after_len.get(len..)?;
    if !tail.is_empty() {
        return None;
    }
    let Ok(mech_name) = core::str::from_utf8(mech_slice) else {
        return None;
    };
    let err = session.handle_handshake(cfg, mech_name);
    let mechs = cfg.mechanisms();
    let mut payload = Vec::new();
    put_i16(&mut payload, err);
    put_i32(&mut payload, mechs.len() as i32);
    let mut rest = mechs;
    while let &[m, ref tail @ ..] = rest {
        put_str(&mut payload, m.as_str());
        rest = tail;
    }
    frame_response_for(hdr.api_key, hdr.api_version, hdr.correlation_id, &payload)
}

/// Answer a `SaslAuthenticate` (`api_key = 36`, `v0..=2`) request against `session` and `cfg`.
pub fn respond_sasl_authenticate(
    hdr: &ReqHeader,
    body: &[u8],
    cfg: &SaslConfig,
    session: &mut SaslSession,
) -> Option<Vec<u8>> {
    if hdr.api_version < 0 || hdr.api_version > 2 {
        return None;
    }
    let auth_bytes = if hdr.api_version >= 2 {
        let (raw_len, rest) = take_uvarint(body)?;
        if raw_len == 0 {
            return None;
        }
        let blen = (raw_len - 1) as usize;
        if blen > MAX_SASL_TOKEN_BYTES {
            return None;
        }
        let slice = rest.get(..blen)?;
        let after_bytes = rest.get(blen..)?;
        let after_tags = skip_tag_buffer(after_bytes)?;
        if !after_tags.is_empty() {
            return None;
        }
        slice
    } else {
        let (blen_i32, rest) = take_i32(body)?;
        if blen_i32 < 0 {
            return None;
        }
        let blen = blen_i32 as usize;
        if blen > MAX_SASL_TOKEN_BYTES {
            return None;
        }
        let slice = rest.get(..blen)?;
        let tail = rest.get(blen..)?;
        if !tail.is_empty() {
            return None;
        }
        slice
    };

    let outcome = session.handle_authenticate(cfg, auth_bytes);
    let mut payload = Vec::new();
    put_i16(&mut payload, outcome.error_code);
    if hdr.api_version >= 2 {
        put_compact_nullable_str(&mut payload, outcome.error_message.as_deref());
        put_uvarint(
            &mut payload,
            (outcome.auth_bytes.len() as u32).saturating_add(1),
        );
        payload.extend_from_slice(&outcome.auth_bytes);
        payload.extend_from_slice(&encode_i64_be(outcome.session_lifetime_ms));
        put_empty_tags(&mut payload);
    } else {
        match &outcome.error_message {
            Some(msg) => put_str(&mut payload, msg),
            None => put_i16(&mut payload, -1),
        }
        put_i32(&mut payload, outcome.auth_bytes.len() as i32);
        payload.extend_from_slice(&outcome.auth_bytes);
        if hdr.api_version >= 1 {
            payload.extend_from_slice(&encode_i64_be(outcome.session_lifetime_ms));
        }
    }
    frame_response_for(hdr.api_key, hdr.api_version, hdr.correlation_id, &payload)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_header;

    #[test]
    fn base64_rfc4648_vectors_and_strict_padding() {
        assert_eq!(base64_encode(b""), "");
        assert_eq!(base64_encode(b"f"), "Zg==");
        assert_eq!(base64_encode(b"fo"), "Zm8=");
        assert_eq!(base64_encode(b"foo"), "Zm9v");
        assert_eq!(base64_encode(b"foob"), "Zm9vYg==");
        assert_eq!(base64_encode(b"fooba"), "Zm9vYmE=");
        assert_eq!(base64_encode(b"foobar"), "Zm9vYmFy");
        assert_eq!(base64_encode(b"n,,"), "biws");

        assert_eq!(base64_decode("Zm9vYmFy").as_deref(), Some(&b"foobar"[..]));
        assert_eq!(base64_decode("biws").as_deref(), Some(&b"n,,"[..]));
        // Non-zero pad bits must fail closed.
        assert!(base64_decode("Zg==").is_some());
        assert!(base64_decode("Zh==").is_none());
    }

    #[test]
    fn rfc7677_scram_sha256_vector_matches_standard() {
        // RFC 7677 §3 test vector:
        //   user = "user", password = "pencil"
        //   salt = base64("W22ZaJ0SNY7soEsUEjb6gQ==")
        //   iterations = 4096
        let salt_vec = base64_decode("W22ZaJ0SNY7soEsUEjb6gQ==").expect("valid salt b64");
        let mut salt = [0u8; 16];
        salt.copy_from_slice(&salt_vec);
        let salted = pbkdf2_hmac_sha256_32(b"pencil", &salt, 4096);
        // RFC 7677 §3 SaltedPassword hex:
        // 1f 40 9c 2b 4a 85 b8 e9 2f 97 30 c9 2d e4 56 67
        // 13 b5 b4 b7 0a d7 79 97 e8 b2 e2 27 89 46 66 57 -> check via ClientKey/ServerSignature!
        let client_key = hmac_sha256_parts(&salted, &[b"Client Key"]);
        let stored_key = Sha256::digest(&client_key);
        let server_key = hmac_sha256_parts(&salted, &[b"Server Key"]);
        let auth_msg = concat!(
            "n=user,r=rOprNGfwEbeRWgbNEkqO,",
            "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,",
            "s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096,",
            "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0"
        );
        let client_sig = hmac_sha256_parts(&stored_key, &[auth_msg.as_bytes()]);
        let mut proof = [0u8; 32];
        for i in 0..32 {
            proof[i] = client_key[i] ^ client_sig[i];
        }
        assert_eq!(
            base64_encode(&proof),
            "dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="
        );
        let server_sig = hmac_sha256_parts(&server_key, &[auth_msg.as_bytes()]);
        assert_eq!(
            base64_encode(&server_sig),
            "6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="
        );
    }

    #[test]
    fn sasl_plain_and_scram_sha256_end_to_end_and_failure_absorption() {
        let mut cfg = SaslConfig::new([0x42; 32]).with_session_lifetime_ms(3_600_000);
        cfg.add_user("alice", b"correct-horse", [0x11; 16], 4096);

        // 1. PLAIN happy path over v1 handshake + v2 flexible SaslAuthenticate
        let mut s_plain = SaslSession::new();
        assert!(!s_plain.allows_api(0)); // Produce blocked before auth!
        assert!(s_plain.allows_api(API_VERSIONS));
        let hs_req = encode_sasl_handshake_request(1, 7, "cli", "PLAIN");
        let (hdr, body_at) = parse_header(&hs_req).expect("parse hs");
        let hs_resp =
            respond_sasl_handshake(&hdr, &hs_req[body_at..], &cfg, &mut s_plain).expect("hs resp");
        assert!(!hs_resp.is_empty());
        assert_eq!(s_plain.phase(), PHASE_HANDSHAKEN);

        let tok = build_plain_token("", "alice", b"correct-horse");
        let auth_req = encode_sasl_authenticate_request(2, 8, "cli", &tok);
        let (ahdr, abody_at) = parse_header(&auth_req).expect("parse auth v2");
        let _ = respond_sasl_authenticate(&ahdr, &auth_req[abody_at..], &cfg, &mut s_plain)
            .expect("auth resp");
        assert!(s_plain.is_authenticated());
        assert_eq!(s_plain.authenticated_user(), Some("alice"));
        assert!(s_plain.allows_api(0));

        // 2. SCRAM-SHA-256 full challenge-response handshake
        let mut s_scram = SaslSession::new();
        assert_eq!(s_scram.handle_handshake(&cfg, "SCRAM-SHA-256"), NONE);
        let (mut client, c_first) = ScramSha256Client::start("alice", "clientNonce12345");
        let step1 = s_scram.handle_authenticate(&cfg, &c_first);
        assert_eq!(step1.error_code, NONE);
        assert_eq!(s_scram.phase(), PHASE_SCRAM_CHALLENGE);
        assert!(!s_scram.is_authenticated());

        let c_final = client
            .step_server_first(b"correct-horse", &step1.auth_bytes)
            .expect("client final");
        let step2 = s_scram.handle_authenticate(&cfg, &c_final);
        assert_eq!(step2.error_code, NONE);
        assert!(s_scram.is_authenticated());
        assert!(client.verify_server_final(&step2.auth_bytes));

        // 3. Bad password transitions to terminal PHASE_FAILED (4) and absorbs all retries!
        let mut s_bad = SaslSession::new();
        assert_eq!(s_bad.handle_handshake(&cfg, "PLAIN"), NONE);
        let bad_tok = build_plain_token("", "alice", b"wrong-password");
        let out_bad = s_bad.handle_authenticate(&cfg, &bad_tok);
        assert_eq!(out_bad.error_code, SASL_AUTHENTICATION_FAILED);
        assert!(s_bad.is_failed());
        assert!(!s_bad.is_authenticated());
        assert!(!s_bad.allows_api(API_VERSIONS));
        // Even sending valid credentials afterwards stays in PHASE_FAILED (monotone advance)!
        let retry = s_bad.handle_authenticate(&cfg, &tok);
        assert_eq!(retry.error_code, ILLEGAL_SASL_STATE);
        assert!(s_bad.is_failed());
        assert!(!s_bad.is_authenticated());
    }
}
