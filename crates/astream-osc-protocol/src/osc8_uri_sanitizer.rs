// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Terminal `OSC 8` clickable hyperlink URI sanitizer enforcing an explicit safe-scheme allowlist
//! (`https://`, `http://`, `file://`, `conversation://`) and rejecting control characters
//! (`Astream.OscProto.TlaOsc8UriSanitizer`).

#[cfg(clean_islands)]
#[path = "osc8_uri_sanitizer_island.rs"]
mod osc8_uri_sanitizer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_uri_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_link_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use osc8_uri_sanitizer_island::{osc_link_advance, osc_uri_clamp};

/// Maximum `OSC 8` URI byte length (`2_048`).
pub const MAX_OSC8_URI_BYTES: u64 = 2_048;

contract_fn! {
    /// Verified URI safety gate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `osc_uri_safe_isl`.
    #[must_use]
    pub const fn osc_uri_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct Osc8UriSanitizer {
    links_validated: u64,
}

impl Osc8UriSanitizer {
    #[must_use]
    pub const fn new() -> Self {
        Self { links_validated: 0 }
    }

    pub fn validate_uri(&mut self, uri: &str) -> bool {
        self.links_validated =
            osc_link_advance(self.links_validated, self.links_validated.saturating_add(1));
        let raw_len = uri.len() as u64;
        if raw_len == 0 || raw_len > MAX_OSC8_URI_BYTES {
            return false;
        }
        let _ = osc_uri_clamp(raw_len, MAX_OSC8_URI_BYTES);
        let tail = if let Some(t) = uri.strip_prefix("https://") {
            Some(t)
        } else if let Some(t) = uri.strip_prefix("http://") {
            Some(t)
        } else if let Some(t) = uri.strip_prefix("file:///") {
            Some(t)
        } else {
            uri.strip_prefix("conversation://")
        };
        let scheme_ok = match tail {
            Some(t) => !t.is_empty(),
            None => false,
        };
        let bytes = uri.as_bytes();
        let mut ctrl_count = 0u64;
        let mut idx = 0usize;
        while idx < bytes.len() {
            if let Some(&b) = bytes.get(idx) {
                let c1 =
                    b == 0xC2 && matches!(bytes.get(idx.saturating_add(1)), Some(&(0x80..=0x9F)));
                if b <= 0x20 || b == 0x7F || c1 {
                    ctrl_count = ctrl_count.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        let score = if scheme_ok && ctrl_count == 0 {
            1u64
        } else {
            0u64
        };
        osc_uri_safe(score, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allows_file_and_https_uris_and_blocks_javascript_or_control_bytes() {
        let mut s = Osc8UriSanitizer::new();
        assert!(s.validate_uri("file:///fixture-home/astream/Cargo.toml"));
        assert!(s.validate_uri("https://example.com/docs"));
        assert!(!s.validate_uri("javascript:alert(1)"));
        assert!(!s.validate_uri("https://example.com/\x1b]52;c;bad"));
    }
}
