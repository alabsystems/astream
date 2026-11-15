// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Strict RFC 8259 JSON `\uXXXX` / control-byte validator & `curl --config` API-key injection guard
//! (`docs/AUDIT-2026-09.md` line 51; `Astream.Live.TlaLiveJsonStrictEscapeCurlKeyGuard`).
//!
//! Enforces both `astream-live` parser & capture-config security invariants from `AUDIT-2026-09.md`:
//! 1. **RFC 8259 §7 strictness**: raw control bytes (`0x00..=0x1F`) inside JSON strings are
//!    rejected, and `\uXXXX` escapes require 4 strict ASCII hex digits (refusing `\u+041` / `\u-041`
//!    which `u16::from_str_radix` would otherwise accept!).
//! 2. **`curl --config` header-injection defense**: API keys written into `curl`'s stdin config
//!    must be non-empty, `<= MAX_API_KEY_LEN` (`512` B), and contain only printable token ASCII
//!    without quotes, backslashes, whitespace, or CR/LF directive breaks!

#[cfg(clean_islands)]
#[path = "live_json_strict_escape_curl_key_guard_island.rs"]
mod live_json_strict_escape_curl_key_guard_island;
#[cfg(clean_islands)]
pub use live_json_strict_escape_curl_key_guard_island::{
    api_key_len_clamp_b142, json_scan_pos_advance_b142,
};

/// Maximum API key length admitted into `capture_live`'s `curl --config` (`512` bytes).
pub const MAX_API_KEY_LEN: u64 = 512;

#[cfg(not(clean_islands))]
/// Clamp API key byte length to `max_key_len`.
#[must_use]
pub const fn api_key_len_clamp_b142(cand_len: u64, max_key_len: u64) -> u64 {
    if cand_len < max_key_len {
        cand_len
    } else {
        max_key_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the JSON string byte-scanner cursor.
#[must_use]
pub const fn json_scan_pos_advance_b142(cur_pos: u64, cand_pos: u64) -> u64 {
    if cur_pos < cand_pos {
        cand_pos
    } else {
        cur_pos
    }
}

contract_fn! {
    /// True iff `0 < key_len <= max_key_len` and `!has_unsafe_byte`.
    #[must_use]
    pub const fn curl_header_key_safe_b142(
        key_len: u64,
        max_key_len: u64,
        has_unsafe_byte: bool,
    ) -> bool
    clauses [ensures result == (key_len > 0 && key_len <= max_key_len && !has_unsafe_byte)]
    {
        key_len > 0 && key_len <= max_key_len && !has_unsafe_byte
    }
}

const fn is_strict_hex_digit(b: u8) -> bool {
    b.is_ascii_digit() || (b >= b'a' && b <= b'f') || (b >= b'A' && b <= b'F')
}

/// Validate a 4-byte `\uXXXX` escape quad strictly per RFC 8259 (rejects `+`/`-` signs!).
#[must_use]
pub const fn valid_rfc8259_unicode_quad(quad: [u8; 4]) -> bool {
    is_strict_hex_digit(quad[0])
        && is_strict_hex_digit(quad[1])
        && is_strict_hex_digit(quad[2])
        && is_strict_hex_digit(quad[3])
}

/// True iff an unescaped JSON string byte is permitted by RFC 8259 §7 (`>= 0x20`).
#[must_use]
pub const fn valid_unescaped_json_string_byte(b: u8) -> bool {
    b >= 0x20 && b != b'"' && b != b'\\'
}

/// True iff `b` is safe inside an unescaped `curl --config` `header = "x-api-key: ..."` value.
#[must_use]
pub const fn is_safe_curl_key_byte(b: u8) -> bool {
    b >= 0x21 && b <= 0x7E && b != b'"' && b != b'\\'
}

/// Verdict for `capture_live` API key validation and JSON token checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveInputGuardVerdict {
    AdmittedCurlApiKey { bounded_len: u64 },
    RefusedEmptyOrOversizedApiKey { raw_len: u64 },
    RefusedUnsafeCurlConfigByte,
    RefusedControlByteInJsonString { at_pos: u64 },
    RefusedInvalidUnicodeHexQuad { at_pos: u64 },
    AdmittedJsonChunk { scan_pos: u64 },
}

/// Stateful JSON-scan & `curl --config` guard for `astream-live`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveJsonCurlGuard {
    scan_pos: u64,
}

impl LiveJsonCurlGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { scan_pos: 0 }
    }

    #[must_use]
    pub const fn validate_curl_api_key(
        raw_len: u64,
        has_unsafe_byte: bool,
    ) -> LiveInputGuardVerdict {
        if raw_len == 0 || raw_len > MAX_API_KEY_LEN {
            return LiveInputGuardVerdict::RefusedEmptyOrOversizedApiKey { raw_len };
        }
        if !curl_header_key_safe_b142(raw_len, MAX_API_KEY_LEN, has_unsafe_byte) {
            return LiveInputGuardVerdict::RefusedUnsafeCurlConfigByte;
        }
        LiveInputGuardVerdict::AdmittedCurlApiKey {
            bounded_len: api_key_len_clamp_b142(raw_len, MAX_API_KEY_LEN),
        }
    }

    pub fn check_unescaped_byte(&mut self, b: u8, cand_pos: u64) -> LiveInputGuardVerdict {
        self.scan_pos = json_scan_pos_advance_b142(self.scan_pos, cand_pos);
        if !valid_unescaped_json_string_byte(b) {
            LiveInputGuardVerdict::RefusedControlByteInJsonString {
                at_pos: self.scan_pos,
            }
        } else {
            LiveInputGuardVerdict::AdmittedJsonChunk {
                scan_pos: self.scan_pos,
            }
        }
    }

    pub fn check_unicode_quad(&mut self, quad: [u8; 4], cand_pos: u64) -> LiveInputGuardVerdict {
        self.scan_pos = json_scan_pos_advance_b142(self.scan_pos, cand_pos);
        if !valid_rfc8259_unicode_quad(quad) {
            LiveInputGuardVerdict::RefusedInvalidUnicodeHexQuad {
                at_pos: self.scan_pos,
            }
        } else {
            LiveInputGuardVerdict::AdmittedJsonChunk {
                scan_pos: self.scan_pos,
            }
        }
    }
}

impl Default for LiveJsonCurlGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_signed_unicode_quad_raw_control_bytes_and_curl_newline_injection() {
        let mut g = LiveJsonCurlGuard::new();
        // `\u+041` rejected!
        assert_eq!(
            g.check_unicode_quad(*b"+041", 4),
            LiveInputGuardVerdict::RefusedInvalidUnicodeHexQuad { at_pos: 4 }
        );
        assert_eq!(
            g.check_unicode_quad(*b"0041", 8),
            LiveInputGuardVerdict::AdmittedJsonChunk { scan_pos: 8 }
        );
        // Raw `\n` (`0x0A`) inside JSON string rejected!
        assert_eq!(
            g.check_unescaped_byte(b'\n', 9),
            LiveInputGuardVerdict::RefusedControlByteInJsonString { at_pos: 9 }
        );
        // Newline or quote in API key (`!is_safe_curl_key_byte`) rejected!
        assert!(!is_safe_curl_key_byte(b'\n'));
        assert!(!is_safe_curl_key_byte(b'"'));
        assert_eq!(
            LiveJsonCurlGuard::validate_curl_api_key(48, true),
            LiveInputGuardVerdict::RefusedUnsafeCurlConfigByte
        );
        assert_eq!(
            LiveJsonCurlGuard::validate_curl_api_key(48, false),
            LiveInputGuardVerdict::AdmittedCurlApiKey { bounded_len: 48 }
        );
    }
}
