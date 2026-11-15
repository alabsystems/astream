// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual Compact/Full Transcript JSONL Byte-Offset Index & UTF-8 Field Projector
//! (`Astream.Agent.TlaDualTranscriptIndex`).
//!
//! Agent conversation trajectories maintain a compact `transcript.jsonl` alongside a complete
//! `transcript_full.jsonl`: oversized `content`, `thinking`, or `tool_calls` fields are truncated
//! in `transcript.jsonl` with an explicit `truncated_fields` marker so initial scans stay fast,
//! while full step payloads can be retrieved on demand.
//!
//! [`DualTranscriptIndex`] projects each step's fields onto valid UTF-8 boundaries bounded by
//! Clean-origin [`transcript_field_clamp`], records which fields were truncated, and indexes each
//! monotonic `step_index` (`transcript_step_advance`) to its exact `(full_byte_offset, full_len)`
//! span inside `transcript_full.jsonl` for `O(1)` random-access seek/pread.

#![allow(
    clippy::assign_op_pattern,
    clippy::manual_map,
    clippy::manual_unwrap_or_default
)]

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "transcript_index_island.rs"]
mod transcript_index_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn transcript_field_clamp(cand_len: u64, preview_cap: u64) -> u64 {
    if cand_len < preview_cap {
        cand_len
    } else {
        preview_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn transcript_step_advance(cur_step: u64, cand_step: u64) -> u64 {
    if cur_step < cand_step {
        cand_step
    } else {
        cur_step
    }
}
#[cfg(clean_islands)]
pub use transcript_index_island::{transcript_field_clamp, transcript_step_advance};

/// Default preview cap per field in `transcript.jsonl` (`2048` bytes).
pub const DEFAULT_TRANSCRIPT_PREVIEW_CAP: usize = 2048;

/// Bitmask bit indicating `content` was truncated in `transcript.jsonl`.
pub const TRUNCATED_CONTENT_BIT: u8 = 0b001;
/// Bitmask bit indicating `thinking` was truncated in `transcript.jsonl`.
pub const TRUNCATED_THINKING_BIT: u8 = 0b010;
/// Bitmask bit indicating `tool_calls` was truncated in `transcript.jsonl`.
pub const TRUNCATED_TOOL_CALLS_BIT: u8 = 0b100;

contract_fn! {
    /// Kernel-certified check that `preview_len <= preview_cap`, linked via
    /// `clean-kernel-defeq` to `transcript_preview_within_cap_isl`.
    #[must_use]
    pub const fn transcript_preview_within_cap(preview_len: u64, preview_cap: u64) -> bool
    clauses [ensures result == (preview_len <= preview_cap)]
    {
        preview_len <= preview_cap
    }
}

/// Byte span of one full JSONL line inside `transcript_full.jsonl`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FullTranscriptSpan {
    pub step_index: u64,
    pub byte_offset: u64,
    pub byte_len: u64,
    pub truncated_mask: u8,
}

/// Compact projected step fields plus truncation metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedStepPreview<'a> {
    pub content_preview: &'a str,
    pub thinking_preview: &'a str,
    pub tool_calls_preview: &'a str,
    pub truncated_mask: u8,
}

impl ProjectedStepPreview<'_> {
    /// Ordered field names matching `<conversation_transcript>` `truncated_fields`.
    #[must_use]
    pub fn truncated_field_names(&self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if (self.truncated_mask & TRUNCATED_CONTENT_BIT) != 0 {
            names.push("content");
        }
        if (self.truncated_mask & TRUNCATED_THINKING_BIT) != 0 {
            names.push("thinking");
        }
        if (self.truncated_mask & TRUNCATED_TOOL_CALLS_BIT) != 0 {
            names.push("tool_calls");
        }
        names
    }
}

fn truncate_str_utf8_boundary(s: &str, max_bytes: usize) -> (&str, bool) {
    if s.len() <= max_bytes {
        return (s, false);
    }
    let bytes = s.as_bytes();
    let mut end = max_bytes;
    while end > 0 {
        let is_cont = match bytes.get(end) {
            Some(&b) => (b & 0b1100_0000) == 0b1000_0000,
            None => false,
        };
        if !is_cont {
            break;
        }
        end = end.saturating_sub(1);
    }
    (
        match s.get(..end) {
            Some(p) => p,
            None => "",
        },
        true,
    )
}

/// Stateful dual-transcript projector and `O(1)` byte-span index backed by
/// `Astream.Agent.TlaDualTranscriptIndex`.
#[derive(Debug, Clone)]
pub struct DualTranscriptIndex {
    spans: BTreeMap<u64, FullTranscriptSpan>,
    preview_cap: usize,
    last_preview_bytes: u64,
    highest_step: u64,
    has_steps: bool,
    full_file_cursor: u64,
}

impl DualTranscriptIndex {
    /// Construct an index with `preview_cap` (`>= 1` byte per field).
    #[must_use]
    pub fn new(preview_cap: usize) -> Self {
        let cap = if preview_cap == 0 { 1 } else { preview_cap };
        Self {
            spans: BTreeMap::new(),
            preview_cap: cap,
            last_preview_bytes: 0,
            highest_step: 0,
            has_steps: false,
            full_file_cursor: 0,
        }
    }

    /// Construct an index with [`DEFAULT_TRANSCRIPT_PREVIEW_CAP`].
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_TRANSCRIPT_PREVIEW_CAP)
    }

    /// Lookup the exact `(byte_offset, byte_len)` span of `step_index` in `transcript_full.jsonl`.
    #[must_use]
    pub fn lookup_step(&self, step_index: u64) -> Option<FullTranscriptSpan> {
        match self.spans.get(&step_index) {
            Some(&sp) => Some(sp),
            None => None,
        }
    }

    /// Monotone highest `step_index` indexed so far.
    #[must_use]
    pub const fn highest_step(&self) -> u64 {
        self.highest_step
    }

    /// Project a step's three text fields onto `<= preview_cap` UTF-8 boundaries and record its
    /// `full_jsonl_line_len` in the sequential `transcript_full.jsonl` offset map.
    pub fn record_and_project<'a>(
        &mut self,
        cand_step_index: u64,
        content: &'a str,
        thinking: &'a str,
        tool_calls: &'a str,
        full_jsonl_line_len: u64,
    ) -> Result<(ProjectedStepPreview<'a>, FullTranscriptSpan), &'static str> {
        if self.has_steps && cand_step_index <= self.highest_step {
            return Err("non-monotone transcript step_index");
        }
        let next_step = if self.has_steps {
            transcript_step_advance(self.highest_step, cand_step_index)
        } else {
            cand_step_index
        };

        let clamped_cap =
            transcript_field_clamp(self.preview_cap as u64, self.preview_cap as u64) as usize;
        let (c_prev, c_trunc) = truncate_str_utf8_boundary(content, clamped_cap);
        let (t_prev, t_trunc) = truncate_str_utf8_boundary(thinking, clamped_cap);
        let (tc_prev, tc_trunc) = truncate_str_utf8_boundary(tool_calls, clamped_cap);

        let mut mask = 0u8;
        if c_trunc {
            mask = mask | (TRUNCATED_CONTENT_BIT);
        }
        if t_trunc {
            mask = mask | (TRUNCATED_THINKING_BIT);
        }
        if tc_trunc {
            mask = mask | (TRUNCATED_TOOL_CALLS_BIT);
        }

        self.last_preview_bytes =
            transcript_field_clamp(c_prev.len() as u64, self.preview_cap as u64);
        let span = FullTranscriptSpan {
            step_index: next_step,
            byte_offset: self.full_file_cursor,
            byte_len: full_jsonl_line_len,
            truncated_mask: mask,
        };
        self.full_file_cursor = self.full_file_cursor.saturating_add(full_jsonl_line_len);
        self.highest_step = next_step;
        self.has_steps = true;
        self.spans.insert(next_step, span);

        Ok((
            ProjectedStepPreview {
                content_preview: c_prev,
                thinking_preview: t_prev,
                tool_calls_preview: tc_prev,
                truncated_mask: mask,
            },
            span,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncates_multibyte_utf8_cleanly_and_indexes_exact_full_file_offsets() {
        let mut idx = DualTranscriptIndex::new(5);
        // "a🦀b" is 1 + 4 + 1 = 6 bytes; cap 5 keeps "a🦀" (5 bytes), never splitting 🦀!
        let (prev0, span0) = idx
            .record_and_project(0, "a🦀b", "ok", "[]", 120)
            .expect("step 0");
        assert_eq!(prev0.content_preview, "a🦀");
        assert_eq!(prev0.truncated_field_names(), vec!["content"]);
        assert!(transcript_preview_within_cap(
            prev0.content_preview.len() as u64,
            5
        ));
        assert_eq!(span0.byte_offset, 0);

        // Cap 3 on "a🦀b" steps back cleanly to "a" (1 byte) so 4-byte 🦀 is not torn!
        let mut idx3 = DualTranscriptIndex::new(3);
        let (p3, _) = idx3.record_and_project(0, "a🦀b", "", "", 50).unwrap();
        assert_eq!(p3.content_preview, "a");

        let (_prev1, span1) = idx
            .record_and_project(1, "hi", "long-thinking", "[1,2,3,4]", 300)
            .expect("step 1");
        assert_eq!(span1.byte_offset, 120);
        assert_eq!(span1.byte_len, 300);
        assert_eq!(idx.lookup_step(1), Some(span1));
    }
}
