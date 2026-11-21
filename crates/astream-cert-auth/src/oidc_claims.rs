// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Zero-dependency RFC 4648 base64url + deterministic JSON OIDC claim verifier (`iss`, `aud`,
//! `sub`, `iat`, `nbf`, `exp`) and `h-<principal>` mapper
//! (`Astream.CertAuth.TlaOidcClaims`).
//!
//! Validates external OIDC/JWT claim payloads without third-party JSON or JWT crates:
//! - Decodes RFC 4648 §5 base64url segments (rejecting padding or non-alphabet bytes).
//! - Extracts flat JSON string/integer claims (`iss`, `aud`, `sub`, `iat`, `nbf`, `exp`) fail-closed.
//! - Clamps allowed clock skew via Clean-origin `oidc_skew_clamp` (`<= MAX_CLOCK_SKEW_MS`).
//! - Enforces half-open `[nbf - skew, exp + skew)` validity via `oidc_not_expired`, advances
//!   per-subject `iat` floor monotonically via `oidc_iat_advance`, and derives a deterministic
//!   `astream-cap`-compatible `h-<16 hex>` human/external principal token via `Sha256`.

use astream_digest::Sha256;

#[cfg(clean_islands)]
#[path = "oidc_claims_island.rs"]
mod oidc_claims_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn oidc_skew_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn oidc_iat_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use oidc_claims_island::{oidc_iat_advance, oidc_skew_clamp};

/// Maximum tolerated wall-clock skew (`60` seconds).
pub const MAX_CLOCK_SKEW_MS: u64 = 60_000;

contract_fn! {
    /// Verified timestamp ordering predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `oidc_not_expired_isl`.
    #[must_use]
    pub const fn oidc_not_expired(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn b64url_val(b: u8) -> Option<u8> {
    match b {
        b'A'..=b'Z' => Some(b.saturating_sub(b'A')),
        b'a'..=b'z' => Some(b.saturating_sub(b'a').saturating_add(26)),
        b'0'..=b'9' => Some(b.saturating_sub(b'0').saturating_add(52)),
        b'-' => Some(62),
        b'_' => Some(63),
        _ => None,
    }
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

#[allow(clippy::question_mark)]
fn parse_u64_dec(s: &str) -> Option<u64> {
    if s.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in s.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = match acc.checked_mul(10) {
            Some(v) => v,
            None => return None,
        };
        acc = match acc.checked_add((b - b'0') as u64) {
            Some(v) => v,
            None => return None,
        };
    }
    Some(acc)
}

fn unquote_json_str(s: &str) -> Result<&str, &'static str> {
    let Some(rest) = s.strip_prefix('"') else {
        return Err("expected quoted json string");
    };
    let Some(inner) = rest.strip_suffix('"') else {
        return Err("expected quoted json string");
    };
    for &b in inner.as_bytes() {
        if b == b'"' || b == b'\\' || b < 0x20 {
            return Err("unsupported json string escape or control byte");
        }
    }
    Ok(inner)
}

fn lut_char(lut: &[u8], idx: usize, fallback: u8) -> char {
    match lut.get(idx) {
        Some(&b) => b as char,
        None => fallback as char,
    }
}

/// Decodes an unpadded RFC 4648 §5 base64url slice into raw bytes fail-closed.
pub fn decode_base64url(inp: &str) -> Result<Vec<u8>, &'static str> {
    let raw = inp.as_bytes();
    if raw.len() % 4 == 1 {
        return Err("invalid base64url length");
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < raw.len() {
        let rem = raw.len().saturating_sub(i);
        let c0 = match raw.get(i) {
            Some(&b) => b,
            None => return Err("b64 oob"),
        };
        let v0 = match b64url_val(c0) {
            Some(v) => v,
            None => return Err("bad b64url char"),
        };
        let c1 = match raw.get(i.saturating_add(1)) {
            Some(&b) => b,
            None => return Err("b64 oob"),
        };
        let v1 = match b64url_val(c1) {
            Some(v) => v,
            None => return Err("bad b64url char"),
        };
        out.push((v0 << 2) | (v1 >> 4));
        if rem >= 3 {
            let c2 = match raw.get(i.saturating_add(2)) {
                Some(&b) => b,
                None => return Err("b64 oob"),
            };
            let v2 = match b64url_val(c2) {
                Some(v) => v,
                None => return Err("bad b64url char"),
            };
            if rem == 3 && (v2 & 0x03) != 0 {
                return Err("non-canonical base64url tail bits");
            }
            out.push((v1 << 4) | (v2 >> 2));
            if rem >= 4 {
                let c3 = match raw.get(i.saturating_add(3)) {
                    Some(&b) => b,
                    None => return Err("b64 oob"),
                };
                let v3 = match b64url_val(c3) {
                    Some(v) => v,
                    None => return Err("bad b64url char"),
                };
                out.push((v2 << 6) | v3);
            }
        } else if (v1 & 0x0F) != 0 {
            return Err("non-canonical base64url 2-char tail bits");
        }
        i = i.saturating_add(4);
    }
    Ok(out)
}

/// Encodes raw bytes as unpadded RFC 4648 §5 base64url.
#[must_use]
pub fn encode_base64url(data: &[u8]) -> String {
    let lut = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = String::new();
    let mut i = 0usize;
    while i < data.len() {
        let b0 = match data.get(i) {
            Some(&b) => b,
            None => 0,
        };
        let rem = data.len().saturating_sub(i);
        out.push(lut_char(lut, ((b0 >> 2) & 0x3F) as usize, b'A'));
        if rem == 1 {
            out.push(lut_char(lut, ((b0 & 0x03) << 4) as usize, b'A'));
        } else {
            let b1 = match data.get(i.saturating_add(1)) {
                Some(&b) => b,
                None => 0,
            };
            out.push(lut_char(
                lut,
                (((b0 & 0x03) << 4) | (b1 >> 4)) as usize,
                b'A',
            ));
            if rem == 2 {
                out.push(lut_char(lut, ((b1 & 0x0F) << 2) as usize, b'A'));
            } else {
                let b2 = match data.get(i.saturating_add(2)) {
                    Some(&b) => b,
                    None => 0,
                };
                out.push(lut_char(
                    lut,
                    (((b1 & 0x0F) << 2) | (b2 >> 6)) as usize,
                    b'A',
                ));
                out.push(lut_char(lut, (b2 & 0x3F) as usize, b'A'));
            }
        }
        i = i.saturating_add(3);
    }
    out
}

/// Parsed OIDC identity claims (`iat_ms`, `nbf_ms`, `exp_ms` in Unix milliseconds).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OidcClaims {
    pub iss: String,
    pub aud: String,
    pub sub: String,
    pub iat_ms: u64,
    pub nbf_ms: u64,
    pub exp_ms: u64,
}

impl OidcClaims {
    /// Parses a minimal canonical JSON object `{"iss":"...","aud":"...","sub":"...","iat":N,"nbf":N,"exp":N}`.
    pub fn parse_json_payload(json: &str) -> Result<Self, &'static str> {
        let Some(after_open) = json.trim().strip_prefix('{') else {
            return Err("expected json object");
        };
        let Some(body) = after_open.strip_suffix('}') else {
            return Err("expected json object");
        };
        let mut iss = None;
        let mut aud = None;
        let mut sub = None;
        let mut iat = None;
        let mut nbf = None;
        let mut exp = None;

        for field in body.split(',') {
            let (raw_k, raw_v) = match field.split_once(':') {
                Some(pair) => pair,
                None => return Err("expected key:value"),
            };
            let k = match unquote_json_str(raw_k.trim()) {
                Ok(key) => key,
                Err(_) => return Err("unquoted json key"),
            };
            let v = raw_v.trim();
            match k {
                "iss" => {
                    if iss.is_some() {
                        return Err("duplicate iss");
                    }
                    let s = match unquote_json_str(v) {
                        Ok(val) => val,
                        Err(_) => return Err("bad iss"),
                    };
                    iss = Some(clone_str(s));
                }
                "aud" => {
                    if aud.is_some() {
                        return Err("duplicate aud");
                    }
                    let s = match unquote_json_str(v) {
                        Ok(val) => val,
                        Err(_) => return Err("bad aud"),
                    };
                    aud = Some(clone_str(s));
                }
                "sub" => {
                    if sub.is_some() {
                        return Err("duplicate sub");
                    }
                    let s = match unquote_json_str(v) {
                        Ok(val) => val,
                        Err(_) => return Err("bad sub"),
                    };
                    sub = Some(clone_str(s));
                }
                "iat" => {
                    if iat.is_some() {
                        return Err("duplicate iat");
                    }
                    let sec = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad iat"),
                    };
                    iat = Some(sec.saturating_mul(1000));
                }
                "nbf" => {
                    if nbf.is_some() {
                        return Err("duplicate nbf");
                    }
                    let sec = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad nbf"),
                    };
                    nbf = Some(sec.saturating_mul(1000));
                }
                "exp" => {
                    if exp.is_some() {
                        return Err("duplicate exp");
                    }
                    let sec = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad exp"),
                    };
                    exp = Some(sec.saturating_mul(1000));
                }
                _ => {}
            }
        }
        let iat_ms = match iat {
            Some(v) => v,
            None => return Err("missing iat"),
        };
        let nbf_ms = match nbf {
            Some(v) => v,
            None => iat_ms,
        };
        let exp_ms = match exp {
            Some(v) => v,
            None => return Err("missing exp"),
        };
        if iat_ms > exp_ms || nbf_ms > exp_ms {
            return Err("oidc timestamps inverted");
        }
        let iss_str = match iss {
            Some(v) => v,
            None => return Err("missing iss"),
        };
        let aud_str = match aud {
            Some(v) => v,
            None => return Err("missing aud"),
        };
        let sub_str = match sub {
            Some(v) => v,
            None => return Err("missing sub"),
        };
        Ok(Self {
            iss: iss_str,
            aud: aud_str,
            sub: sub_str,
            iat_ms,
            nbf_ms,
            exp_ms,
        })
    }

    /// Derives the canonical `h-<16 lowercase hex>` principal bound to `(iss, sub)`.
    #[must_use]
    pub fn bound_human_principal(&self) -> String {
        let mut h = Sha256::new();
        h.update_slice(b"ASTREAM-OIDC-PRINCIPAL-V1\0");
        h.update_slice(&(self.iss.len() as u64).to_le_bytes());
        h.update_slice(self.iss.as_bytes());
        h.update_slice(b"\0");
        h.update_slice(&(self.sub.len() as u64).to_le_bytes());
        h.update_slice(self.sub.as_bytes());
        let d = h.finalize();
        let lut = b"0123456789abcdef";
        let mut out = String::new();
        out.push_str("h-");
        let mut i = 0usize;
        while i < 8 {
            let b = match d.get(i) {
                Some(&v) => v,
                None => 0,
            };
            out.push(lut_char(lut, ((b >> 4) & 0x0F) as usize, b'0'));
            out.push(lut_char(lut, (b & 0x0F) as usize, b'0'));
            i = i.saturating_add(1);
        }
        out
    }
}

/// Stateful OIDC claim verifier enforcing issuer, audience, clamped skew, and monotone `iat`.
#[derive(Debug, Clone)]
pub struct OidcClaimVerifier {
    expected_iss: String,
    expected_aud: String,
    skew_ms: u64,
    min_iat_ms: u64,
}

impl OidcClaimVerifier {
    #[must_use]
    pub fn new(expected_iss: &str, expected_aud: &str, skew_ms: u64) -> Self {
        Self {
            expected_iss: clone_str(expected_iss),
            expected_aud: clone_str(expected_aud),
            skew_ms: oidc_skew_clamp(skew_ms, MAX_CLOCK_SKEW_MS),
            min_iat_ms: 0,
        }
    }

    pub fn verify_b64_payload(
        &mut self,
        b64_payload: &str,
        now_ms: u64,
    ) -> Result<String, &'static str> {
        let raw = decode_base64url(b64_payload)?;
        let txt = match core::str::from_utf8(&raw) {
            Ok(s) => s,
            Err(_) => return Err("invalid utf8 oidc payload"),
        };
        let claims = OidcClaims::parse_json_payload(txt)?;
        if claims.iss != self.expected_iss
            || claims.aud != self.expected_aud
            || claims.sub.is_empty()
        {
            return Err("oidc iss/aud/sub mismatch");
        }
        if !oidc_not_expired(claims.iat_ms, self.min_iat_ms) {
            return Err("oidc token iat below replay floor");
        }
        let earliest = claims.nbf_ms.saturating_sub(self.skew_ms);
        let latest = claims.exp_ms.saturating_add(self.skew_ms);
        if !oidc_not_expired(now_ms, earliest) || now_ms >= latest {
            return Err("oidc token outside validity window");
        }
        self.min_iat_ms = oidc_iat_advance(self.min_iat_ms, claims.iat_ms);
        let principal = claims.bound_human_principal();
        let mut probe = String::new();
        probe.push_str("rw,p=");
        probe.push_str(&principal);
        probe.push_str(":/f/alpha/in/p/>");
        if astream_cap::Grant::parse(&probe).is_err() {
            return Err("derived principal rejected by astream-cap");
        }
        Ok(principal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64url_and_oidc_claims_verify_and_bind_valid_human_principal() {
        let json = r#"{"iss":"https://id.aterm.dev","aud":"astream-broker","sub":"user-42","iat":1700000,"nbf":1700000,"exp":1700300}"#;
        let b64 = encode_base64url(json.as_bytes());
        assert_eq!(decode_base64url(&b64).unwrap(), json.as_bytes());

        let mut verifier = OidcClaimVerifier::new("https://id.aterm.dev", "astream-broker", 5_000);
        let p = verifier.verify_b64_payload(&b64, 1_700_100_000).unwrap();
        assert!(p.starts_with("h-") && p.len() == 18);

        // Expired past exp + skew is refused.
        assert!(verifier.verify_b64_payload(&b64, 1_700_310_000).is_err());
    }
}
