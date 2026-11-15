// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic, bounded Server-Sent Events (`text/event-stream`) Anthropic Messages
//! streaming completion assembler (`Astream.Live.TlaSseStreamAssembler`).
//!
//! Live agent turns in `aterm` (`Claude Code`, `agy`, `capture_live`) stream incrementally
//! as chunked SSE frames (`message_start`, `content_block_start`, `content_block_delta`
//! carrying `text_delta` or `input_json_delta`, `content_block_stop`, `message_delta`, and
//! `message_stop`) split arbitrarily across TCP read boundaries.
//!
//! [`SseCompletionAssembler`] reassembles chunked bytes fail-closed under Clean-clamped
//! byte and block budgets (`sse_accum_clamp_bytes`, `sse_block_count_clamp`) and validates
//! every reconstructed `tool_use` `input_json_delta` buffer through `crate::json::parse`
//! and `crate::render_input` so streaming captures replay bit-identically to non-streaming
//! `crate::parse_completion` turns.

use astream_agent::cog::{CogRecord, StopReason, ToolUse};

use crate::json::{self, Json};

#[cfg(clean_islands)]
#[path = "sse_stream_island.rs"]
mod sse_stream_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sse_accum_clamp_bytes(cur: u64, cap: u64) -> u64 {
    if cur < cap {
        cur
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sse_block_count_clamp(blocks: u64, max_blocks: u64) -> u64 {
    if blocks < max_blocks {
        blocks
    } else {
        max_blocks
    }
}
#[cfg(clean_islands)]
pub use sse_stream_island::{sse_accum_clamp_bytes, sse_block_count_clamp};

/// Hard ceiling on total accumulated payload + pending line bytes (`4 MiB`).
pub const MAX_SSE_ACCUM_BYTES: usize = 4 * 1024 * 1024;

/// Hard ceiling on content blocks in one streamed Messages turn.
pub const MAX_SSE_CONTENT_BLOCKS: usize = 128;

contract_fn! {
    /// Kernel-certified check that accumulated SSE byte footprint `cur` stays within `cap`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `sse_accum_within_cap_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn sse_accum_within_cap(cur: u64, cap: u64) -> bool
    clauses [ensures result == (cur <= cap)]
    {
        cur <= cap
    }
}

/// Fail-closed error returned when an SSE stream violates framing, ordering, JSON validity,
/// or resource caps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SseStreamError {
    /// Accumulated line/delta bytes exceeded the configured cap.
    BudgetExceeded,
    /// Content block index or count exceeded `max_blocks`.
    TooManyBlocks,
    /// Invalid UTF-8 in SSE line framing.
    InvalidUtf8,
    /// Invalid JSON inside an SSE `data:` payload or reconstructed `input_json_delta`.
    InvalidJson(String),
    /// Out-of-order SSE lifecycle event (e.g. delta before `message_start`, unclosed block).
    ProtocolOrder(&'static str),
    /// Upstream `event: error` frame received from the API.
    RemoteError(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BlockSlot {
    Text {
        buf: String,
        closed: bool,
    },
    ToolUse {
        id: String,
        name: String,
        initial_input: Option<Vec<u8>>,
        partial_json: String,
        closed: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Lifecycle {
    AwaitingStart,
    Streaming,
    Finished,
}

/// Stateful, chunk-boundary-agnostic SSE Messages turn assembler.
#[derive(Debug, Clone)]
pub struct SseCompletionAssembler {
    max_accum_bytes: usize,
    max_blocks: usize,
    accum_bytes: usize,
    line_buf: Vec<u8>,
    cur_event: String,
    cur_data: String,
    has_data_line: bool,
    blocks: Vec<Option<BlockSlot>>,
    stop_reason: StopReason,
    lifecycle: Lifecycle,
}

impl Default for SseCompletionAssembler {
    fn default() -> Self {
        Self::new(MAX_SSE_ACCUM_BYTES, MAX_SSE_CONTENT_BLOCKS)
    }
}

impl SseCompletionAssembler {
    /// Create a new assembler bounded by `max_accum_bytes` and `max_blocks` (both clamped
    /// to hard ceilings [`MAX_SSE_ACCUM_BYTES`] and [`MAX_SSE_CONTENT_BLOCKS`]).
    #[must_use]
    pub fn new(max_accum_bytes: usize, max_blocks: usize) -> Self {
        let clamped_bytes =
            sse_accum_clamp_bytes(max_accum_bytes as u64, MAX_SSE_ACCUM_BYTES as u64) as usize;
        let clamped_blocks =
            sse_block_count_clamp(max_blocks as u64, MAX_SSE_CONTENT_BLOCKS as u64) as usize;
        Self {
            max_accum_bytes: if clamped_bytes == 0 { 1 } else { clamped_bytes },
            max_blocks: if clamped_blocks == 0 {
                1
            } else {
                clamped_blocks
            },
            accum_bytes: 0,
            line_buf: Vec::new(),
            cur_event: String::new(),
            cur_data: String::new(),
            has_data_line: false,
            blocks: Vec::new(),
            stop_reason: StopReason::EndTurn,
            lifecycle: Lifecycle::AwaitingStart,
        }
    }

    /// True once `message_stop` (or `[DONE]` after `message_start`) has been processed.
    #[must_use]
    pub const fn is_finished(&self) -> bool {
        matches!(self.lifecycle, Lifecycle::Finished)
    }

    /// Total bytes charged against the accumulator budget so far.
    #[must_use]
    pub const fn accumulated_bytes(&self) -> usize {
        self.accum_bytes
    }

    fn charge_bytes(&mut self, add: usize) -> Result<(), SseStreamError> {
        let Some(next) = self.accum_bytes.checked_add(add) else {
            return Err(SseStreamError::BudgetExceeded);
        };
        if !sse_accum_within_cap(next as u64, self.max_accum_bytes as u64) {
            return Err(SseStreamError::BudgetExceeded);
        }
        self.accum_bytes = next;
        Ok(())
    }

    /// Feed an arbitrary byte chunk of an SSE response body.
    pub fn push_chunk(&mut self, chunk: &[u8]) -> Result<(), SseStreamError> {
        let mut idx = 0usize;
        while idx < chunk.len() {
            let Some(&b) = chunk.get(idx) else {
                break;
            };
            idx = idx.saturating_add(1);
            if b == b'\n' {
                self.process_completed_line()?;
            } else {
                self.charge_bytes(1)?;
                self.line_buf.push(b);
            }
        }
        Ok(())
    }

    fn process_completed_line(&mut self) -> Result<(), SseStreamError> {
        let mut raw_line = core::mem::take(&mut self.line_buf);
        if raw_line.last() == Some(&b'\r') {
            let _ = raw_line.pop();
        }
        if raw_line.is_empty() {
            return self.dispatch_frame();
        }
        let line = match core::str::from_utf8(&raw_line) {
            Ok(s) => s,
            Err(_) => {
                return Err(SseStreamError::InvalidUtf8);
            }
        };
        if line.starts_with(':') {
            return Ok(());
        }
        if let Some(rest) = line.strip_prefix("event:") {
            let trimmed = trim_single_leading_space(rest);
            self.cur_event.clear();
            self.cur_event.push_str(trimmed);
        } else if let Some(rest) = line.strip_prefix("data:") {
            let payload = trim_single_leading_space(rest);
            if self.has_data_line {
                self.charge_bytes(1)?;
                self.cur_data.push('\n');
            }
            self.cur_data.push_str(payload);
            self.has_data_line = true;
        }
        Ok(())
    }

    fn dispatch_frame(&mut self) -> Result<(), SseStreamError> {
        if !self.has_data_line && self.cur_event.is_empty() {
            return Ok(());
        }
        let ev = self.cur_event.clone();
        let data = self.cur_data.clone();
        self.cur_event.clear();
        self.cur_data.clear();
        self.has_data_line = false;

        if data.trim() == "[DONE]" {
            match self.lifecycle {
                Lifecycle::AwaitingStart => {
                    return Err(SseStreamError::ProtocolOrder("[DONE] before message_start"));
                }
                Lifecycle::Streaming => {
                    self.lifecycle = Lifecycle::Finished;
                }
                Lifecycle::Finished => {}
            }
            return Ok(());
        }
        if ev == "ping" {
            return Ok(());
        }
        if data.is_empty() {
            return Ok(());
        }

        let parsed = match json::parse(&data) {
            Ok(v) => v,
            Err(e) => {
                if self.lifecycle == Lifecycle::Finished {
                    return Err(SseStreamError::ProtocolOrder("frame after message_stop"));
                }
                return Err(SseStreamError::InvalidJson(e));
            }
        };

        let kind = match parsed.get("type").and_then(Json::as_str) {
            Some(t) => t,
            None => ev.as_str(),
        };

        if kind == "ping" {
            return Ok(());
        }
        if self.lifecycle == Lifecycle::Finished {
            return Err(SseStreamError::ProtocolOrder("frame after message_stop"));
        }

        match kind {
            "error" => {
                let err_msg = match parsed.get("error") {
                    Some(err_obj) => err_obj.get("message").and_then(Json::as_str),
                    None => None,
                };
                let msg = err_msg.unwrap_or("remote SSE error").to_string();
                Err(SseStreamError::RemoteError(msg))
            }
            "message_start" => {
                if self.lifecycle != Lifecycle::AwaitingStart {
                    return Err(SseStreamError::ProtocolOrder("duplicate message_start"));
                }
                self.lifecycle = Lifecycle::Streaming;
                Ok(())
            }
            "content_block_start" => {
                if self.lifecycle != Lifecycle::Streaming {
                    return Err(SseStreamError::ProtocolOrder(
                        "content_block_start outside active message",
                    ));
                }
                let block_idx = parse_index(&parsed)?;
                if block_idx >= self.max_blocks {
                    return Err(SseStreamError::TooManyBlocks);
                }
                if block_idx != self.blocks.len() {
                    return Err(SseStreamError::ProtocolOrder(
                        "non-contiguous or duplicate content_block_start index",
                    ));
                }
                let Some(cb) = parsed.get("content_block") else {
                    return Err(SseStreamError::ProtocolOrder("missing content_block"));
                };
                let cb_type = cb.get("type").and_then(Json::as_str).unwrap_or("");
                let slot = match cb_type {
                    "text" => {
                        let init_text = cb.get("text").and_then(Json::as_str).unwrap_or("");
                        BlockSlot::Text {
                            buf: init_text.to_string(),
                            closed: false,
                        }
                    }
                    "tool_use" => {
                        let id = cb
                            .get("id")
                            .and_then(Json::as_str)
                            .unwrap_or("")
                            .to_string();
                        let name = cb
                            .get("name")
                            .and_then(Json::as_str)
                            .unwrap_or("")
                            .to_string();
                        let initial_input = match cb.get("input") {
                            Some(Json::Obj(entries)) if entries.is_empty() => None,
                            Some(other) => Some(crate::render_input(Some(other))),
                            None => None,
                        };
                        BlockSlot::ToolUse {
                            id,
                            name,
                            initial_input,
                            partial_json: String::new(),
                            closed: false,
                        }
                    }
                    _ => {
                        return Err(SseStreamError::ProtocolOrder(
                            "unsupported content_block type",
                        ));
                    }
                };
                self.blocks.push(Some(slot));
                Ok(())
            }
            "content_block_delta" => {
                if self.lifecycle != Lifecycle::Streaming {
                    return Err(SseStreamError::ProtocolOrder(
                        "content_block_delta outside active message",
                    ));
                }
                let block_idx = parse_index(&parsed)?;
                let Some(delta) = parsed.get("delta") else {
                    return Err(SseStreamError::ProtocolOrder("missing delta object"));
                };
                let delta_type = delta.get("type").and_then(Json::as_str).unwrap_or("");
                let Some(Some(slot)) = self.blocks.get_mut(block_idx) else {
                    return Err(SseStreamError::ProtocolOrder(
                        "delta references unopened block index",
                    ));
                };
                match (slot, delta_type) {
                    (BlockSlot::Text { buf, closed }, "text_delta") => {
                        if *closed {
                            return Err(SseStreamError::ProtocolOrder(
                                "text_delta after content_block_stop",
                            ));
                        }
                        let piece = delta.get("text").and_then(Json::as_str).unwrap_or("");
                        buf.push_str(piece);
                        Ok(())
                    }
                    (
                        BlockSlot::ToolUse {
                            partial_json,
                            closed,
                            ..
                        },
                        "input_json_delta",
                    ) => {
                        if *closed {
                            return Err(SseStreamError::ProtocolOrder(
                                "input_json_delta after content_block_stop",
                            ));
                        }
                        let piece = delta
                            .get("partial_json")
                            .and_then(Json::as_str)
                            .unwrap_or("");
                        partial_json.push_str(piece);
                        Ok(())
                    }
                    _ => Err(SseStreamError::ProtocolOrder(
                        "delta type mismatches open block kind",
                    )),
                }
            }
            "content_block_stop" => {
                if self.lifecycle != Lifecycle::Streaming {
                    return Err(SseStreamError::ProtocolOrder(
                        "content_block_stop outside active message",
                    ));
                }
                let block_idx = parse_index(&parsed)?;
                let Some(Some(slot)) = self.blocks.get_mut(block_idx) else {
                    return Err(SseStreamError::ProtocolOrder(
                        "content_block_stop references unopened block",
                    ));
                };
                match slot {
                    BlockSlot::Text { closed, .. } | BlockSlot::ToolUse { closed, .. } => {
                        if *closed {
                            return Err(SseStreamError::ProtocolOrder(
                                "duplicate content_block_stop",
                            ));
                        }
                        *closed = true;
                    }
                }
                Ok(())
            }
            "message_delta" => {
                if self.lifecycle != Lifecycle::Streaming {
                    return Err(SseStreamError::ProtocolOrder(
                        "message_delta outside active message",
                    ));
                }
                let stop_str = match parsed.get("delta") {
                    Some(delta_obj) => delta_obj.get("stop_reason").and_then(Json::as_str),
                    None => None,
                };
                if let Some(sr) = stop_str {
                    self.stop_reason = if sr == "tool_use" {
                        StopReason::ToolUse
                    } else {
                        StopReason::EndTurn
                    };
                }
                Ok(())
            }
            "message_stop" => {
                if self.lifecycle != Lifecycle::Streaming {
                    return Err(SseStreamError::ProtocolOrder(
                        "message_stop before message_start",
                    ));
                }
                self.lifecycle = Lifecycle::Finished;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Finalize the stream into a [`CogRecord::Completion`], verifying that `message_stop`
    /// arrived, no trailing partial line remains, every opened block received
    /// `content_block_stop`, and every `input_json_delta` parses as valid JSON.
    pub fn finish(mut self) -> Result<CogRecord, SseStreamError> {
        if !self.line_buf.is_empty() {
            self.process_completed_line()?;
        }
        if self.has_data_line || !self.cur_event.is_empty() {
            self.dispatch_frame()?;
        }
        if self.lifecycle != Lifecycle::Finished {
            return Err(SseStreamError::ProtocolOrder(
                "SSE stream ended before message_stop",
            ));
        }

        let mut text = String::new();
        let mut calls = Vec::new();
        let mut idx = 0usize;
        while idx < self.blocks.len() {
            if let Some(Some(slot)) = self.blocks.get(idx) {
                match slot {
                    BlockSlot::Text { buf, closed } => {
                        if !*closed {
                            return Err(SseStreamError::ProtocolOrder(
                                "unclosed text block at message_stop",
                            ));
                        }
                        text.push_str(buf);
                    }
                    BlockSlot::ToolUse {
                        id,
                        name,
                        initial_input,
                        partial_json,
                        closed,
                    } => {
                        if !*closed {
                            return Err(SseStreamError::ProtocolOrder(
                                "unclosed tool_use block at message_stop",
                            ));
                        }
                        let input = if partial_json.is_empty() {
                            match initial_input {
                                Some(bytes) => bytes.clone(),
                                None => b"{}".to_vec(),
                            }
                        } else {
                            let v = match json::parse(partial_json) {
                                Ok(parsed) => parsed,
                                Err(e) => return Err(SseStreamError::InvalidJson(e)),
                            };
                            crate::render_input(Some(&v))
                        };
                        calls.push(ToolUse {
                            id: id.clone(),
                            name: name.clone(),
                            input,
                        });
                    }
                }
            }
            idx = idx.saturating_add(1);
        }

        Ok(CogRecord::Completion {
            text,
            calls,
            stop: self.stop_reason,
        })
    }
}

fn trim_single_leading_space(s: &str) -> &str {
    match s.strip_prefix(' ') {
        Some(rest) => rest,
        None => s,
    }
}

fn parse_index(v: &Json) -> Result<usize, SseStreamError> {
    let Some(Json::Num(raw)) = v.get("index") else {
        return Err(SseStreamError::ProtocolOrder("missing numeric block index"));
    };
    let s = raw.as_str();
    if s.is_empty() {
        return Err(SseStreamError::ProtocolOrder("empty block index"));
    }
    let mut val = 0usize;
    let bytes = s.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        let Some(&b) = bytes.get(i) else {
            break;
        };
        if !b.is_ascii_digit() {
            return Err(SseStreamError::ProtocolOrder("non-integer block index"));
        }
        let Some(mul) = val.checked_mul(10) else {
            return Err(SseStreamError::TooManyBlocks);
        };
        let Some(next) = mul.checked_add(b.saturating_sub(b'0') as usize) else {
            return Err(SseStreamError::TooManyBlocks);
        };
        val = next;
        i = i.saturating_add(1);
    }
    Ok(val)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE_SSE: &str = "\
: keepalive comment\r\n\
event: message_start\r\n\
data: {\"type\":\"message_start\",\"message\":{\"id\":\"msg_01\"}}\r\n\
\r\n\
event: ping\r\n\
data: {\"type\":\"ping\"}\r\n\
\r\n\
event: content_block_start\r\n\
data: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\r\n\
\r\n\
event: content_block_delta\r\n\
data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"Checking \"}}\r\n\
\r\n\
event: content_block_delta\r\n\
data: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"files.\"}}\r\n\
\r\n\
event: content_block_stop\r\n\
data: {\"type\":\"content_block_stop\",\"index\":0}\r\n\
\r\n\
event: content_block_start\r\n\
data: {\"type\":\"content_block_start\",\"index\":1,\"content_block\":{\"type\":\"tool_use\",\"id\":\"toolu_01\",\"name\":\"bash\",\"input\":{}}}\r\n\
\r\n\
event: content_block_delta\r\n\
data: {\"type\":\"content_block_delta\",\"index\":1,\"delta\":{\"type\":\"input_json_delta\",\"partial_json\":\"{\\\"cmd\\\": \"}}\r\n\
\r\n\
event: content_block_delta\r\n\
data: {\"type\":\"content_block_delta\",\"index\":1,\"delta\":{\"type\":\"input_json_delta\",\"partial_json\":\"\\\"ls -la\\\"}\"}}\r\n\
\r\n\
event: content_block_stop\r\n\
data: {\"type\":\"content_block_stop\",\"index\":1}\r\n\
\r\n\
event: message_delta\r\n\
data: {\"type\":\"message_delta\",\"delta\":{\"stop_reason\":\"tool_use\"}}\r\n\
\r\n\
event: message_stop\r\n\
data: {\"type\":\"message_stop\"}\r\n\
\r\n";

    #[test]
    fn single_byte_chunking_matches_batch_parse_completion_bit_for_bit() {
        let batch_json = r#"{
            "content": [
                {"type": "text", "text": "Checking files."},
                {"type": "tool_use", "id": "toolu_01", "name": "bash", "input": {"cmd": "ls -la"}}
            ],
            "stop_reason": "tool_use"
        }"#;
        let expected = crate::parse_completion(batch_json).unwrap();

        let mut asm = SseCompletionAssembler::default();
        for b in SAMPLE_SSE.as_bytes().chunks(1) {
            asm.push_chunk(b).unwrap();
        }
        assert!(asm.is_finished());
        let actual = asm.finish().unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn rejects_truncated_tool_json_unclosed_blocks_and_budget_overflow() {
        // 1. Truncated stream without message_stop fails closed.
        let mut trunc = SseCompletionAssembler::default();
        trunc
            .push_chunk(b"event: message_start\ndata: {\"type\":\"message_start\"}\n\n")
            .unwrap();
        assert_eq!(
            trunc.finish(),
            Err(SseStreamError::ProtocolOrder(
                "SSE stream ended before message_stop"
            ))
        );

        // 2. Malformed partial_json at finish fails closed.
        let bad_json_sse = "\
event: message_start\ndata: {\"type\":\"message_start\"}\n\n\
event: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"tool_use\",\"id\":\"t1\",\"name\":\"sh\",\"input\":{}}}\n\n\
event: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"input_json_delta\",\"partial_json\":\"{\\\"unterminated\"}}\n\n\
event: content_block_stop\ndata: {\"type\":\"content_block_stop\",\"index\":0}\n\n\
event: message_stop\ndata: {\"type\":\"message_stop\"}\n\n";
        let mut bad = SseCompletionAssembler::default();
        bad.push_chunk(bad_json_sse.as_bytes()).unwrap();
        assert!(matches!(bad.finish(), Err(SseStreamError::InvalidJson(_))));

        // 3. Budget cap enforced strictly.
        let mut tiny = SseCompletionAssembler::new(16, 4);
        assert_eq!(
            tiny.push_chunk(b"event: message_start_way_beyond_sixteen_bytes\n"),
            Err(SseStreamError::BudgetExceeded)
        );

        // 4. Multi-line `data:` newline joins charge against budget.
        let mut nl_budget = SseCompletionAssembler::new(12, 4);
        nl_budget.push_chunk(b"data:\n").unwrap(); // 5 bytes
        nl_budget.push_chunk(b"data:\n").unwrap(); // 5 + 1('\n') = 11 bytes
        assert_eq!(
            nl_budget.push_chunk(b"data:\n"),
            Err(SseStreamError::BudgetExceeded)
        );

        // 5. Premature `[DONE]`, trailing frames after `message_stop`, and sparse block indices fail closed.
        let mut early_done = SseCompletionAssembler::default();
        assert_eq!(
            early_done.push_chunk(b"data: [DONE]\n\n"),
            Err(SseStreamError::ProtocolOrder("[DONE] before message_start"))
        );

        let mut sparse = SseCompletionAssembler::default();
        sparse
            .push_chunk(b"event: message_start\ndata: {\"type\":\"message_start\"}\n\n")
            .unwrap();
        assert_eq!(
            sparse.push_chunk(b"event: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":2,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n\n"),
            Err(SseStreamError::ProtocolOrder(
                "non-contiguous or duplicate content_block_start index"
            ))
        );

        let mut after_stop = SseCompletionAssembler::default();
        after_stop
            .push_chunk(b"event: message_start\ndata: {\"type\":\"message_start\"}\n\nevent: message_stop\ndata: {\"type\":\"message_stop\"}\n\n")
            .unwrap();
        assert_eq!(
            after_stop.push_chunk(b"event: custom\ndata: {\"type\":\"custom\"}\n\n"),
            Err(SseStreamError::ProtocolOrder("frame after message_stop"))
        );
    }
}
