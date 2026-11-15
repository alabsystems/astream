// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Terminal `OSC 52` base64 clipboard write budget enforcing maximum payload bytes and explicit
//! clipboard-write enablement (`Astream.OscProto.TlaOsc52ClipboardBudget`).

#[cfg(clean_islands)]
#[path = "osc52_clipboard_budget_island.rs"]
mod osc52_clipboard_budget_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_b64_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_clip_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use osc52_clipboard_budget_island::{osc_b64_clamp, osc_clip_advance};

/// Default `OSC 52` base64 payload ceiling (`131_072` bytes = ~96 KiB decoded).
pub const MAX_OSC52_BASE64_BYTES: u64 = 131_072;

contract_fn! {
    /// Verified clipboard size check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `osc_clip_within_cap_isl`.
    #[must_use]
    pub const fn osc_clip_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct Osc52Policy {
    allow_write: bool,
    max_b64_bytes: u64,
    accepted_writes: u64,
}

fn valid_rfc4648_base64(bytes: &[u8]) -> bool {
    let len = bytes.len();
    if len == 0 || (len & 3) != 0 {
        return false;
    }
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

impl Osc52Policy {
    #[must_use]
    pub const fn new(allow_write: bool, max_b64_bytes: u64) -> Self {
        Self {
            allow_write,
            max_b64_bytes: osc_b64_clamp(max_b64_bytes, MAX_OSC52_BASE64_BYTES),
            accepted_writes: 0,
        }
    }

    pub fn admit_osc52(&mut self, b64_payload: &[u8]) -> bool {
        if !self.allow_write || !valid_rfc4648_base64(b64_payload) {
            return false;
        }
        let len = b64_payload.len() as u64;
        if !osc_clip_within_cap(self.max_b64_bytes, len) {
            return false;
        }
        self.accepted_writes =
            osc_clip_advance(self.accepted_writes, self.accepted_writes.saturating_add(1));
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_write_toggle_and_base64_byte_ceiling() {
        let mut p = Osc52Policy::new(true, 16);
        assert!(p.admit_osc52(b"aGVsbG8="));
        assert!(!p.admit_osc52(b"0123456789abcdefX"));
        let mut disabled = Osc52Policy::new(false, 16);
        assert!(!disabled.admit_osc52(b"aGVsbG8="));
    }
}
