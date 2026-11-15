// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?2004` bracketed-paste armor detecting and rejecting pasted buffers containing embedded
//! `ESC [ 201 ~` end-paste breakout sequences or raw `NUL`/`ESC` command-injection payloads
//! (`Astream.OscProto.TlaBracketedPasteArmor`).

#[cfg(clean_islands)]
#[path = "bracketed_paste_armor_island.rs"]
mod bracketed_paste_armor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_paste_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc_scrub_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bracketed_paste_armor_island::{osc_paste_clamp, osc_scrub_advance};

/// Maximum single bracketed paste inspection window (`1_048_576` bytes).
pub const MAX_PASTE_BYTES: u64 = 1_048_576;

contract_fn! {
    /// Verified breakout-free paste predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `osc_paste_clean_isl`.
    #[must_use]
    pub const fn osc_paste_clean(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct BracketedPasteArmor {
    pastes_checked: u64,
}

impl BracketedPasteArmor {
    #[must_use]
    pub const fn new() -> Self {
        Self { pastes_checked: 0 }
    }

    pub fn is_safe_paste(&mut self, payload: &[u8]) -> bool {
        self.pastes_checked =
            osc_scrub_advance(self.pastes_checked, self.pastes_checked.saturating_add(1));
        let len = payload.len() as u64;
        if len > MAX_PASTE_BYTES {
            return false;
        }
        let _ = osc_paste_clamp(len, MAX_PASTE_BYTES);
        let mut bad_bytes = 0u64;
        let mut idx = 0usize;
        while idx < payload.len() {
            if let Some(&b) = payload.get(idx) {
                let c0_bad = (b < 0x20 && b != b'\t' && b != b'\n') || b == 0x7F;
                let c1_utf8 =
                    b == 0xC2 && matches!(payload.get(idx.saturating_add(1)), Some(&(0x80..=0x9F)));
                if c0_bad || c1_utf8 {
                    bad_bytes = bad_bytes.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        osc_paste_clean(0, bad_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_embedded_escape_breakout_in_bracketed_paste() {
        let mut a = BracketedPasteArmor::new();
        assert!(a.is_safe_paste(b"echo hello\nworld"));
        assert!(!a.is_safe_paste(b"safe\x1b[201~; rm -rf /\x1b[200~"));
    }
}
