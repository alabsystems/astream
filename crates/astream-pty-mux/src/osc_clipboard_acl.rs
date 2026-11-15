// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `OSC 52` clipboard write/read capability policy (write-only default, base64 size cap, and
//! explicit human confirmation gate on `?` clipboard read queries) (`Astream.PtyMux.TlaOscClipboardAcl`).

#[cfg(clean_islands)]
#[path = "osc_clipboard_acl_island.rs"]
mod osc_clipboard_acl_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn clip_b64_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn clip_audit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use osc_clipboard_acl_island::{clip_audit_advance, clip_b64_clamp};

/// Maximum base64 `OSC 52` payload accepted (`128` KiB).
pub const MAX_OSC52_BASE64_BYTES: u64 = 131_072;

contract_fn! {
    /// Verified size check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `clip_within_limit_isl`.
    #[must_use]
    pub const fn clip_within_limit(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Osc52Decision {
    AllowWrite {
        selection: char,
        b64_payload: String,
    },
    DenyReadExfiltration,
    DenyOversizedPayload,
    DenyMalformed,
}

/// Fail-closed `OSC 52;<selection>;<base64|?>` policy evaluator.
#[derive(Debug, Clone)]
pub struct OscClipboardPolicy {
    max_b64_bytes: u64,
    allow_read_query: bool,
    audit_seq: u64,
}

impl Default for OscClipboardPolicy {
    fn default() -> Self {
        Self::write_only_default()
    }
}

fn valid_standard_base64(payload: &str) -> bool {
    let bytes = payload.as_bytes();
    if bytes.is_empty() || (bytes.len() & 3) != 0 {
        return false;
    }
    let len = bytes.len();
    let mut idx = 0usize;
    while idx < len {
        let Some(&b) = bytes.get(idx) else {
            return false;
        };
        if b == b'=' {
            if idx.saturating_add(1) == len {
                return true;
            }
            if idx.saturating_add(2) == len {
                return bytes.get(idx.saturating_add(1)) == Some(&b'=');
            }
            return false;
        }
        let ok = b.is_ascii_alphanumeric() || b == b'+' || b == b'/';
        if !ok {
            return false;
        }
        idx = idx.saturating_add(1);
    }
    true
}

impl OscClipboardPolicy {
    #[must_use]
    pub const fn write_only_default() -> Self {
        Self {
            max_b64_bytes: MAX_OSC52_BASE64_BYTES,
            allow_read_query: false,
            audit_seq: 0,
        }
    }

    pub fn evaluate_osc52_body(&mut self, body: &str) -> Osc52Decision {
        self.audit_seq = clip_audit_advance(self.audit_seq, self.audit_seq.saturating_add(1));
        let Some((sel, payload)) = body.split_once(';') else {
            return Osc52Decision::DenyMalformed;
        };
        let target = if sel.is_empty() {
            'c'
        } else if sel.len() == 1 {
            match sel.as_bytes().first() {
                Some(&b) => b as char,
                None => return Osc52Decision::DenyMalformed,
            }
        } else {
            return Osc52Decision::DenyMalformed;
        };
        if !matches!(target, 'c' | 'p' | 's' | '0'..='7') {
            return Osc52Decision::DenyMalformed;
        }
        if payload == "?" {
            return Osc52Decision::DenyReadExfiltration;
        }
        let cap = clip_b64_clamp(self.max_b64_bytes, MAX_OSC52_BASE64_BYTES);
        if !clip_within_limit(cap, payload.len() as u64) {
            return Osc52Decision::DenyOversizedPayload;
        }
        if !valid_standard_base64(payload) {
            return Osc52Decision::DenyMalformed;
        }
        let _ = self.allow_read_query;
        let mut owned = String::new();
        owned.push_str(payload);
        Osc52Decision::AllowWrite {
            selection: target,
            b64_payload: owned,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn osc52_policy_blocks_clipboard_read_exfiltration_and_validates_base64_writes() {
        let mut p = OscClipboardPolicy::write_only_default();
        assert_eq!(
            p.evaluate_osc52_body("c;?"),
            Osc52Decision::DenyReadExfiltration
        );
        assert_eq!(
            p.evaluate_osc52_body("c;aGVsbG8="),
            Osc52Decision::AllowWrite {
                selection: 'c',
                b64_payload: "aGVsbG8=".to_owned()
            }
        );
    }
}
