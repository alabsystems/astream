//! The cognition record model: what an agent turn is made of.
//!
//! A turn is an ordered sequence of [`CogRecord`]s — the model's **completions**
//! (its words + the tools it decided to call) and the **tool results** the world
//! returned. Inputs are opaque bytes, never parsed as live JSON, so the model is
//! deterministic in replay.

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "cog_island.rs"]
mod cog_island;
#[cfg(not(clean_islands))]
pub use crate::twins::cog_clamp_call_count;
#[cfg(clean_islands)]
pub use cog_island::cog_clamp_call_count;

contract_fn! {
    /// Verified check that a stop reason code represents [`StopReason::EndTurn`] (`stop_code == 1`),
    /// linked via `clean-kernel-defeq` to `cog_is_end_turn_isl`.
    #[must_use]
    pub const fn cog_is_end_turn(stop_code: u8) -> bool
    clauses [ensures result == (stop_code == 1)]
    {
        stop_code == 1
    }
}

/// Why a completion stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    /// The model wants to call one or more tools and awaits their results.
    ToolUse,
    /// The model ended its turn.
    EndTurn,
}

impl StopReason {
    /// Wire byte code for this stop reason (`0` = `ToolUse`, `1` = `EndTurn`).
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            StopReason::ToolUse => 0,
            StopReason::EndTurn => 1,
        }
    }

    /// Whether this stop reason ends the turn.
    #[must_use]
    pub const fn is_end_turn(self) -> bool {
        cog_is_end_turn(self.code())
    }
}

/// One tool call the model emitted.
#[derive(Debug, Clone, Eq)]
pub struct ToolUse {
    /// The tool-call id the result will reference.
    pub id: String,
    /// The tool name.
    pub name: String,
    /// The opaque tool input (never parsed as live JSON in replay).
    pub input: Vec<u8>,
}

impl PartialEq for ToolUse {
    fn eq(&self, other: &Self) -> bool {
        self.id.as_bytes() == other.id.as_bytes()
            && self.name.as_bytes() == other.name.as_bytes()
            && self.input.as_slice() == other.input.as_slice()
    }
}

/// One recorded cognition event.
#[derive(Debug, Clone, Eq)]
pub enum CogRecord {
    /// A model completion: its text, the tools it called, and why it stopped.
    Completion {
        /// The assistant text.
        text: String,
        /// The tool calls in this completion.
        calls: Vec<ToolUse>,
        /// Why the completion stopped.
        stop: StopReason,
    },
    /// A tool result fed back to the model.
    ToolResult {
        /// The `ToolUse::id` this answers.
        tool_use_id: String,
        /// The tool's output bytes.
        content: Vec<u8>,
        /// Whether the tool reported an error.
        is_error: bool,
    },
}

impl PartialEq for CogRecord {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                CogRecord::Completion {
                    text: t0,
                    calls: c0,
                    stop: s0,
                },
                CogRecord::Completion {
                    text: t1,
                    calls: c1,
                    stop: s1,
                },
            ) => {
                t0.as_bytes() == t1.as_bytes()
                    && c0.as_slice() == c1.as_slice()
                    && s0.code() == s1.code()
            }
            (
                CogRecord::ToolResult {
                    tool_use_id: id0,
                    content: b0,
                    is_error: e0,
                },
                CogRecord::ToolResult {
                    tool_use_id: id1,
                    content: b1,
                    is_error: e1,
                },
            ) => id0.as_bytes() == id1.as_bytes() && b0.as_slice() == b1.as_slice() && *e0 == *e1,
            _ => false,
        }
    }
}

impl CogRecord {
    /// The bytes this record paints on the agent's screen (its observable surface).
    pub fn display(&self) -> &[u8] {
        match self {
            CogRecord::Completion { text, .. } => text.as_bytes(),
            CogRecord::ToolResult { content, .. } => content.as_slice(),
        }
    }
}
