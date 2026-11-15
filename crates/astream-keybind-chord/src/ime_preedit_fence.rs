// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `NSTextInputClient` IME `markedText` composition fence preventing terminal keybind/PTY
//! shortcuts from intercepting `Enter`, `Escape`, or arrow keys while CJK/dead-key preedit text is
//! active (`Astream.KeyChord.TlaImePreeditFence`).

#[cfg(clean_islands)]
#[path = "ime_preedit_fence_island.rs"]
mod ime_preedit_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_ime_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_comp_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ime_preedit_fence_island::{kc_comp_advance, kc_ime_clamp};

/// Maximum UTF-8 bytes in an active IME `markedText` preedit buffer (`512`).
pub const MAX_PREEDIT_BYTES: u64 = 512;

contract_fn! {
    /// Verified non-composing passthrough predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `kc_passthrough_ready_isl`.
    #[must_use]
    pub const fn kc_passthrough_ready(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ImePreeditFence {
    marked_bytes: u64,
    commits: u64,
}

impl ImePreeditFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            marked_bytes: 0,
            commits: 0,
        }
    }

    pub fn set_marked_len(&mut self, utf8_len: u64) {
        self.marked_bytes = kc_ime_clamp(utf8_len, MAX_PREEDIT_BYTES);
    }

    pub fn commit_composition(&mut self) {
        self.marked_bytes = 0;
        self.commits = kc_comp_advance(self.commits, self.commits.saturating_add(1));
    }

    #[must_use]
    pub const fn allow_keybind_intercept(&self) -> bool {
        kc_passthrough_ready(0, self.marked_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_keybind_interception_during_active_ime_marked_text() {
        let mut f = ImePreeditFence::new();
        assert!(f.allow_keybind_intercept());
        f.set_marked_len(6);
        assert!(!f.allow_keybind_intercept());
        f.commit_composition();
        assert!(f.allow_keybind_intercept());
    }
}
