//! A hand-authored example turn, shared by the selftest example and the tests so
//! they can never drift: an agent builds, sees `BUILD FAILED`, and recovers.

use crate::cog::{CogRecord, StopReason, ToolUse};

/// The 5-record transcript: build → FAILED → recover-call → recover-result → done.
pub fn build_then_recover() -> Vec<CogRecord> {
    vec![
        CogRecord::Completion {
            text: "let me build".into(),
            calls: vec![ToolUse {
                id: "t1".into(),
                name: "bash".into(),
                input: b"make build".to_vec(),
            }],
            stop: StopReason::ToolUse,
        },
        CogRecord::ToolResult {
            tool_use_id: "t1".into(),
            content: b"BUILD FAILED: 2 errors".to_vec(),
            is_error: true,
        },
        CogRecord::Completion {
            text: "let me recover".into(),
            calls: vec![ToolUse {
                id: "t2".into(),
                name: "bash".into(),
                input: b"echo recover".to_vec(),
            }],
            stop: StopReason::ToolUse,
        },
        CogRecord::ToolResult {
            tool_use_id: "t2".into(),
            content: b"recover".to_vec(),
            is_error: false,
        },
        CogRecord::Completion {
            text: "done".into(),
            calls: vec![],
            stop: StopReason::EndTurn,
        },
    ]
}

/// The counterfactual: the `BUILD FAILED` result swapped for `BUILD OK`.
pub fn build_ok_result() -> CogRecord {
    CogRecord::ToolResult {
        tool_use_id: "t1".into(),
        content: b"BUILD OK: 0 errors".to_vec(),
        is_error: false,
    }
}
