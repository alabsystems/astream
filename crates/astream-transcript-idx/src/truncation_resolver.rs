// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Selective `truncated_fields` (`["content"]`, `["thinking"]`, `["tool_calls"]`) hydration planner
//! reading only truncated lines from `transcript_full.jsonl` (`Astream.Transcript.TlaTruncationResolver`).

#[cfg(clean_islands)]
#[path = "truncation_resolver_island.rs"]
mod truncation_resolver_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_fields_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_hydrated_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use truncation_resolver_island::{tr_fields_clamp, tr_hydrated_advance};

/// Maximum truncated field tags per JSONL step (`content`, `thinking`, `tool_calls`).
pub const MAX_TRUNCATED_FIELDS_PER_STEP: u64 = 8;

contract_fn! {
    /// Verified hydration line-match check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tr_hydrated_ok_isl`.
    #[must_use]
    pub const fn tr_hydrated_ok(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Decides whether a compact `transcript.jsonl` line requires a targeted `transcript_full.jsonl` read.
#[derive(Debug, Clone, Default)]
pub struct TruncationHydrator {
    hydrated_steps: u64,
}

impl TruncationHydrator {
    #[must_use]
    pub const fn new() -> Self {
        Self { hydrated_steps: 0 }
    }

    pub fn needs_full_line(
        &mut self,
        line_number_1based: u64,
        truncated_fields: &[&str],
    ) -> Option<u64> {
        let lim =
            tr_fields_clamp(truncated_fields.len() as u64, MAX_TRUNCATED_FIELDS_PER_STEP) as usize;
        let mut non_empty = 0u64;
        let mut idx = 0usize;
        while idx < lim {
            if let Some(&f) = truncated_fields.get(idx) {
                if !f.trim().is_empty() {
                    non_empty = non_empty.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        if non_empty == 0 || !tr_hydrated_ok(line_number_1based, 1) {
            return None;
        }
        self.hydrated_steps =
            tr_hydrated_advance(self.hydrated_steps, self.hydrated_steps.saturating_add(1));
        Some(line_number_1based)
    }

    #[must_use]
    pub const fn hydrated_steps(&self) -> u64 {
        self.hydrated_steps
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hydrator_requests_full_transcript_line_only_when_truncated_fields_present() {
        let mut h = TruncationHydrator::new();
        assert_eq!(h.needs_full_line(42, &[]), None);
        assert_eq!(h.needs_full_line(43, &["content", "tool_calls"]), Some(43));
        assert_eq!(h.hydrated_steps(), 1);
    }
}
