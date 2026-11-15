//! A hand-authored example turn, shared by the selftest example and the tests so
//! they can never drift: an agent builds, sees `BUILD FAILED`, and recovers.

use crate::cog::{CogRecord, StopReason, ToolUse};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "fixtures_island.rs"]
mod fixtures_island;
#[cfg(not(clean_islands))]
pub use crate::twins::fixture_clamp_transcript_len;
#[cfg(clean_islands)]
pub use fixtures_island::fixture_clamp_transcript_len;

contract_fn! {
    /// Verified check that a fixture transcript has the expected record count (`len == expected`),
    /// linked via `clean-kernel-defeq` to `fixture_has_expected_len_isl`.
    #[must_use]
    pub const fn fixture_has_expected_len(len: usize, expected: usize) -> bool
    clauses [ensures result == (len == expected)]
    {
        len == expected
    }
}

/// The 5-record transcript: build → FAILED → recover-call → recover-result → done.
#[expect(
    clippy::vec_init_then_push,
    reason = "the verified lane cannot discharge the `vec![..]` macro's obligations; \
              pushing into a sized Vec keeps this function at 0 runtime-checked (1d191af)"
)]
pub fn build_then_recover() -> Vec<CogRecord> {
    let clamped = fixture_clamp_transcript_len(5, 5) as usize;
    let cap = if clamped <= 5 { clamped } else { 5 };
    let mut out = Vec::with_capacity(cap);
    let mut calls1 = Vec::with_capacity(1);
    calls1.push(ToolUse {
        id: "t1".into(),
        name: "bash".into(),
        input: b"make build".to_vec(),
    });
    out.push(CogRecord::Completion {
        text: "let me build".into(),
        calls: calls1,
        stop: StopReason::ToolUse,
    });
    out.push(CogRecord::ToolResult {
        tool_use_id: "t1".into(),
        content: b"BUILD FAILED: 2 errors".to_vec(),
        is_error: true,
    });
    let mut calls2 = Vec::with_capacity(1);
    calls2.push(ToolUse {
        id: "t2".into(),
        name: "bash".into(),
        input: b"echo recover".to_vec(),
    });
    out.push(CogRecord::Completion {
        text: "let me recover".into(),
        calls: calls2,
        stop: StopReason::ToolUse,
    });
    out.push(CogRecord::ToolResult {
        tool_use_id: "t2".into(),
        content: b"recover".to_vec(),
        is_error: false,
    });
    out.push(CogRecord::Completion {
        text: "done".into(),
        calls: Vec::new(),
        stop: StopReason::EndTurn,
    });
    out
}

/// The counterfactual: the `BUILD FAILED` result swapped for `BUILD OK`.
pub fn build_ok_result() -> CogRecord {
    CogRecord::ToolResult {
        tool_use_id: "t1".into(),
        content: b"BUILD OK: 0 errors".to_vec(),
        is_error: false,
    }
}
