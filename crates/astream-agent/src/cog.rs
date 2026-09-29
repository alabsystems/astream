//! The cognition record model: what an agent turn is made of.
//!
//! A turn is an ordered sequence of [`CogRecord`]s — the model's **completions**
//! (its words + the tools it decided to call) and the **tool results** the world
//! returned. Inputs are opaque bytes, never parsed as live JSON, so the model is
//! deterministic in replay.

/// Why a completion stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    /// The model wants to call one or more tools and awaits their results.
    ToolUse,
    /// The model ended its turn.
    EndTurn,
}

/// One tool call the model emitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolUse {
    /// The tool-call id the result will reference.
    pub id: String,
    /// The tool name.
    pub name: String,
    /// The opaque tool input (never parsed as live JSON in replay).
    pub input: Vec<u8>,
}

/// One recorded cognition event.
#[derive(Debug, Clone, PartialEq, Eq)]
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

impl CogRecord {
    /// The bytes this record paints on the agent's screen (its observable surface).
    pub fn display(&self) -> &[u8] {
        match self {
            CogRecord::Completion { text, .. } => text.as_bytes(),
            CogRecord::ToolResult { content, .. } => content,
        }
    }
}
