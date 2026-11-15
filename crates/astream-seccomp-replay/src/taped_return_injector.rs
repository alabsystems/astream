// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Taped syscall buffer & return-value cursor (`EffectRecord` / `EffectsLog`,
//! `Astream.SecReplay.TlaTapedReturnInjector`) verifying kind match and bounded output slice
//! length before writing into tracee memory.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "taped_return_injector_island.rs"]
mod taped_return_injector_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_buf_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_idx_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use taped_return_injector_island::{sec_buf_clamp, sec_idx_advance};

/// Maximum single injected syscall buffer (`1_048_576` bytes).
pub const MAX_INJECT_BUF_BYTES: u64 = 1_048_576;

contract_fn! {
    /// Verified tracee destination capacity (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sec_entry_matched_isl`.
    #[must_use]
    pub const fn sec_entry_matched(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct TapedSyscallEntry {
    pub kind_tag: u8,
    pub ret_val: i64,
    pub payload: Vec<u8>,
}

#[derive(Debug, Clone, Default)]
pub struct TapedInjector {
    entries: Vec<TapedSyscallEntry>,
    cursor: u64,
}

impl TapedInjector {
    #[must_use]
    pub fn new(entries: Vec<TapedSyscallEntry>) -> Self {
        Self { entries, cursor: 0 }
    }

    pub fn next_injection(
        &mut self,
        expected_kind: u8,
        tracee_buf_cap: u64,
    ) -> Option<(i64, &[u8])> {
        let Ok(idx) = usize::try_from(self.cursor) else {
            return None;
        };
        let Some(entry) = self.entries.get(idx) else {
            return None;
        };
        if entry.kind_tag != expected_kind {
            return None;
        }
        if entry.ret_val < 0 && !entry.payload.is_empty() {
            return None;
        }
        let len = sec_buf_clamp(entry.payload.len() as u64, MAX_INJECT_BUF_BYTES);
        if len != entry.payload.len() as u64 || !sec_entry_matched(tracee_buf_cap, len) {
            return None;
        }
        let Some(next_cursor) = self.cursor.checked_add(1) else {
            return None;
        };
        self.cursor = sec_idx_advance(self.cursor, next_cursor);
        Some((entry.ret_val, &entry.payload))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_kind_and_tracee_buffer_capacity_before_injecting() {
        let mut inj = TapedInjector::new(vec![TapedSyscallEntry {
            kind_tag: 2,
            ret_val: 4,
            payload: vec![1, 2, 3, 4],
        }]);
        assert!(inj.next_injection(1, 16).is_none());
        assert!(inj.next_injection(2, 2).is_none());
        assert_eq!(inj.next_injection(2, 16).unwrap().0, 4);
    }
}
