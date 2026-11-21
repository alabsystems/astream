// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Agent wake-hook formatters, socket dispatchers, and broker task-queue adapters
//! (`DESIGN-drive-pipe.md` §5 step 4, `Astream.Pump.TlaWakeDispatch`).
//!
//! Bridges [`crate::Pump`] / `aspump` wake boundaries (`PROMPT_READY`, `COMMAND_START`,
//! `COMMAND_END`, `QUIESCED`) into turn-based drivers that stop between turns:
//!
//! 1. **Broker task-queue adapter ([`WakeTaskQueue`]):** posts compact [`WakeTaskItem`]
//!    envelopes onto a durable broker task subject (`/a/stream/tasks/<queue>` via
//!    [`task_subject`] or any `--task-subject`) keyed by `(producer_id, wake_seq)` so
//!    retransmitted wakes deduplicate on the broker, and drains all ready tasks up to the
//!    broker's caught-up `Mark` at the top of each driver turn ([`drain_wake_tasks`]).
//! 2. **Vendor & sidecar wake hooks ([`WakeHookFormat`], [`deliver_hook_tcp`],
//!    `deliver_hook_unix`):** formats each wake as a raw wake line, a Claude Code
//!    `Notification` / `Stop` JSON hook payload, or a Codex `turn.wake` JSON envelope, and
//!    delivers it over a local Unix control socket or TCP listener before advancing the
//!    pump's durable consumer-group commit cursor ([`wake_commit_after_ack`]).

#![allow(clippy::question_mark)]

use astream_broker::{Client, Event};
use std::io::{self, Read, Write};
use std::net::TcpStream;
use std::time::Duration;

#[cfg(clean_islands)]
#[path = "wake_dispatch_island.rs"]
mod wake_dispatch_island;

#[cfg(not(clean_islands))]
pub use crate::twins::{wake_dispatch_seq_advance, wake_task_payload_clamp};
#[cfg(clean_islands)]
pub use wake_dispatch_island::{wake_dispatch_seq_advance, wake_task_payload_clamp};

/// Maximum encoded byte length of a [`WakeTaskItem`] wire payload.
pub const MAX_WAKE_TASK_PAYLOAD: u64 = 4096;

/// Canonical prefix for an encoded [`WakeTaskItem`] wire record.
pub const WAKE_TASK_PREFIX: &str = "WAKE_TASK v1 ";

contract_fn! {
    /// Kernel-verified commit-after-ack ordering guard (`commit_seq <= acked_seq`),
    /// linked via `clean-kernel-defeq` to `wake_commit_after_ack_isl`.
    #[must_use]
    pub const fn wake_commit_after_ack(acked_seq: u64, commit_seq: u64) -> bool
    clauses [ensures result == (commit_seq <= acked_seq)]
    {
        commit_seq <= acked_seq
    }
}

/// Built task-queue subject `/a/stream/tasks/<queue>` for a named driver queue.
#[must_use]
pub fn task_subject(queue: &str) -> String {
    format!("/a/stream/tasks/{queue}")
}

/// Compact wake task envelope posted onto a broker task queue or delivered to an agent hook.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WakeTaskItem {
    /// Monotone 1-based dispatch sequence (`producer_seq` for broker deduplication).
    pub wake_seq: u64,
    /// Broker offset on the watched `/out` stream where the driver folds the target screen.
    pub boffset: u64,
    /// Watched `/out` subject (e.g. `"/a/stream/term/s1/out"`).
    pub subject: String,
    /// Formatted semantic wake line (e.g. `"PROMPT_READY boffset=42"`).
    pub wake_line: String,
}

fn hex_upper(nibble: u8) -> u8 {
    if nibble < 10 {
        b'0'.saturating_add(nibble)
    } else {
        b'A'.saturating_add(nibble.saturating_sub(10))
    }
}

fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a').saturating_add(10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A').saturating_add(10)),
        _ => None,
    }
}

fn pct_encode(raw: &str) -> String {
    let raw_bytes = raw.as_bytes();
    let cap = raw_bytes.len();
    let mut out = if cap <= 8192 {
        Vec::with_capacity(cap)
    } else {
        Vec::new()
    };
    for &b in raw_bytes {
        let safe = b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'/');
        if safe {
            out.push(b);
        } else {
            out.push(b'%');
            out.push(hex_upper((b >> 4) & 0x0F));
            out.push(hex_upper(b & 0x0F));
        }
    }
    String::from_utf8(out).unwrap_or_default()
}

fn pct_decode(enc: &str) -> Option<String> {
    let bytes = enc.as_bytes();
    let cap = bytes.len();
    let mut out = if cap <= 8192 {
        Vec::with_capacity(cap)
    } else {
        Vec::new()
    };
    let mut idx = 0usize;
    while idx < bytes.len() {
        let &b = bytes.get(idx)?;
        if b == b'%' {
            let &hi_b = bytes.get(idx.saturating_add(1))?;
            let &lo_b = bytes.get(idx.saturating_add(2))?;
            let hi = hex_val(hi_b)?;
            let lo = hex_val(lo_b)?;
            out.push((hi << 4) | lo);
            idx = idx.saturating_add(3);
        } else {
            out.push(b);
            idx = idx.saturating_add(1);
        }
    }
    String::from_utf8(out).ok()
}

fn parse_u64_strict(s: &str) -> Option<u64> {
    if s.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in s.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = acc
            .checked_mul(10)?
            .checked_add(u64::from(b.saturating_sub(b'0')))?;
    }
    Some(acc)
}

fn push_json_escaped(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let code = c as u8;
                out.push_str("\\u00");
                out.push(char::from(hex_upper((code >> 4) & 0x0F)));
                out.push(char::from(hex_upper(code & 0x0F)));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

impl WakeTaskItem {
    /// Encode this wake task into its bounded single-line `WAKE_TASK v1 ...` wire payload.
    ///
    /// Clamps the output check through Clean-origin [`wake_task_payload_clamp`] and fails
    /// closed with `ErrorKind::InvalidInput` if the encoded line would exceed
    /// [`MAX_WAKE_TASK_PAYLOAD`].
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let subj_enc = pct_encode(&self.subject);
        let line_enc = pct_encode(&self.wake_line);
        let formatted = format!(
            "{WAKE_TASK_PREFIX}seq={} boffset={} subject={subj_enc} line={line_enc}",
            self.wake_seq, self.boffset
        );
        let raw_len = formatted.len() as u64;
        let clamped = wake_task_payload_clamp(raw_len, MAX_WAKE_TASK_PAYLOAD);
        if clamped < raw_len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "wake task payload exceeds MAX_WAKE_TASK_PAYLOAD",
            ));
        }
        Ok(formatted.into_bytes())
    }

    /// Decode a `WAKE_TASK v1 ...` wire payload back into [`WakeTaskItem`].
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if (bytes.len() as u64) > MAX_WAKE_TASK_PAYLOAD {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "wake task payload exceeds MAX_WAKE_TASK_PAYLOAD",
            ));
        }
        let Ok(text) = core::str::from_utf8(bytes) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "wake task payload is not UTF-8",
            ));
        };
        let trimmed = text.trim_end_matches(['\r', '\n']);
        let Some(rest) = trimmed.strip_prefix(WAKE_TASK_PREFIX) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "missing WAKE_TASK v1 prefix",
            ));
        };
        let mut wake_seq: Option<u64> = None;
        let mut boffset: Option<u64> = None;
        let mut subject: Option<String> = None;
        let mut wake_line: Option<String> = None;

        for tok in rest.split(' ') {
            if tok.is_empty() {
                continue;
            }
            let Some((k, v)) = tok.split_once('=') else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed wake task token",
                ));
            };
            match k {
                "seq" => {
                    if wake_seq.is_some() {
                        return Err(io::Error::new(io::ErrorKind::InvalidData, "duplicate seq"));
                    }
                    let Some(n) = parse_u64_strict(v) else {
                        return Err(io::Error::new(io::ErrorKind::InvalidData, "invalid seq"));
                    };
                    wake_seq = Some(n);
                }
                "boffset" => {
                    if boffset.is_some() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "duplicate boffset",
                        ));
                    }
                    let Some(n) = parse_u64_strict(v) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "invalid boffset",
                        ));
                    };
                    boffset = Some(n);
                }
                "subject" => {
                    if subject.is_some() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "duplicate subject",
                        ));
                    }
                    let Some(dec) = pct_decode(v) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "invalid percent-encoded subject",
                        ));
                    };
                    subject = Some(dec);
                }
                "line" => {
                    if wake_line.is_some() {
                        return Err(io::Error::new(io::ErrorKind::InvalidData, "duplicate line"));
                    }
                    let Some(dec) = pct_decode(v) else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "invalid percent-encoded line",
                        ));
                    };
                    wake_line = Some(dec);
                }
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "unknown wake task field",
                    ));
                }
            }
        }

        let (Some(seq), Some(off), Some(subj), Some(line)) =
            (wake_seq, boffset, subject, wake_line)
        else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "incomplete wake task fields",
            ));
        };
        if seq == 0 || subj.is_empty() || line.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "wake task seq/subject/line must be non-empty",
            ));
        }
        Ok(Self {
            wake_seq: seq,
            boffset: off,
            subject: subj,
            wake_line: line,
        })
    }
}

/// Wire format for agent wake-hook socket notifications (`--hook-format`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeHookFormat {
    /// Plain `<WAKE_LINE>\n` text line.
    Line,
    /// Claude Code `Notification`-class JSON hook event (`{"hook_event_name":"Notification",...}\n`).
    ClaudeNotificationJson,
    /// Claude Code `Stop`-class JSON hook event (`{"hook_event_name":"Stop",...}\n`).
    ClaudeStopJson,
    /// Codex turn-resume JSON event (`{"type":"turn.wake",...}\n`).
    CodexTurnJson,
}

impl WakeHookFormat {
    /// Parse `line | claude-notification | claude-stop | codex-turn`.
    #[must_use]
    pub fn by_name(name: &str) -> Option<Self> {
        match name {
            "line" => Some(Self::Line),
            "claude-notification" => Some(Self::ClaudeNotificationJson),
            "claude-stop" => Some(Self::ClaudeStopJson),
            "codex-turn" => Some(Self::CodexTurnJson),
            _ => None,
        }
    }

    /// Render `item` into a newline-terminated payload for this hook format.
    #[must_use]
    pub fn render(self, item: &WakeTaskItem) -> String {
        match self {
            Self::Line => {
                let mut s = String::with_capacity(128);
                s.push_str(&item.wake_line);
                s.push('\n');
                s
            }
            Self::ClaudeNotificationJson | Self::ClaudeStopJson => {
                let event_name = if matches!(self, Self::ClaudeNotificationJson) {
                    "Notification"
                } else {
                    "Stop"
                };
                let mut out = String::with_capacity(160);
                out.push_str("{\"hook_event_name\":");
                push_json_escaped(&mut out, event_name);
                out.push_str(",\"wake_seq\":");
                out.push_str(&item.wake_seq.to_string());
                out.push_str(",\"boffset\":");
                out.push_str(&item.boffset.to_string());
                out.push_str(",\"subject\":");
                push_json_escaped(&mut out, &item.subject);
                out.push_str(",\"wake\":");
                push_json_escaped(&mut out, &item.wake_line);
                out.push_str("}\n");
                out
            }
            Self::CodexTurnJson => {
                let mut out = String::with_capacity(160);
                out.push_str("{\"type\":\"turn.wake\",\"wake_seq\":");
                out.push_str(&item.wake_seq.to_string());
                out.push_str(",\"boffset\":");
                out.push_str(&item.boffset.to_string());
                out.push_str(",\"subject\":");
                push_json_escaped(&mut out, &item.subject);
                out.push_str(",\"wake\":");
                push_json_escaped(&mut out, &item.wake_line);
                out.push_str("}\n");
                out
            }
        }
    }
}

/// Deliver a formatted [`WakeTaskItem`] to any `Write` sink and flush it.
pub fn write_hook_payload<W: Write>(
    sink: &mut W,
    fmt: WakeHookFormat,
    item: &WakeTaskItem,
) -> io::Result<()> {
    let payload = fmt.render(item);
    sink.write_all(payload.as_bytes())?;
    sink.flush()
}

/// Deliver one formatted wake hook over a Unix domain control socket (`--hook-unix`).
#[cfg(unix)]
pub fn deliver_hook_unix(
    sock_path: &std::path::Path,
    fmt: WakeHookFormat,
    item: &WakeTaskItem,
) -> io::Result<()> {
    let mut stream = std::os::unix::net::UnixStream::connect(sock_path)?;
    let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
    write_hook_payload(&mut stream, fmt, item)?;
    let _ = stream.shutdown(std::net::Shutdown::Write);
    Ok(())
}

/// Deliver one formatted wake hook over a TCP listener (`--hook-tcp`).
pub fn deliver_hook_tcp(addr: &str, fmt: WakeHookFormat, item: &WakeTaskItem) -> io::Result<()> {
    let mut stream = TcpStream::connect(addr)?;
    stream.set_nodelay(true)?;
    stream.set_write_timeout(Some(Duration::from_secs(5)))?;
    write_hook_payload(&mut stream, fmt, item)?;
    let _ = stream.shutdown(std::net::Shutdown::Write);
    Ok(())
}

/// Stateful broker task-queue publisher with Clean-verified monotone dispatch sequencing
/// (`Astream.Pump.TlaWakeDispatch`) and commit-after-ack tracking.
#[derive(Debug, Clone)]
pub struct WakeTaskQueue {
    task_subject: String,
    producer_id: u64,
    dispatched_seq: u64,
    acked_seq: u64,
}

impl WakeTaskQueue {
    /// Construct a task-queue adapter publishing onto `task_subject` under `producer_id`,
    /// starting after `initial_seq` (`0` for a fresh producer, or the highest previously
    /// published sequence on resume).
    #[must_use]
    pub fn new(task_subject: impl Into<String>, producer_id: u64, initial_seq: u64) -> Self {
        Self {
            task_subject: task_subject.into(),
            producer_id,
            dispatched_seq: initial_seq,
            acked_seq: initial_seq,
        }
    }

    /// Target broker subject where wake tasks are published.
    #[must_use]
    pub fn subject(&self) -> &str {
        &self.task_subject
    }

    /// Producer ID used for broker-side `(producer_id, wake_seq)` deduplication.
    #[must_use]
    pub const fn producer_id(&self) -> u64 {
        self.producer_id
    }

    /// Highest wake sequence allocated on this adapter.
    #[must_use]
    pub const fn dispatched_seq(&self) -> u64 {
        self.dispatched_seq
    }

    /// Highest wake sequence durably acknowledged by the broker task queue.
    #[must_use]
    pub const fn acked_seq(&self) -> u64 {
        self.acked_seq
    }

    /// Whether `commit_seq` may safely commit under the Clean-verified
    /// [`wake_commit_after_ack`] invariant (`commit_seq <= self.acked_seq`).
    #[must_use]
    pub const fn can_commit_seq(&self, commit_seq: u64) -> bool {
        wake_commit_after_ack(self.acked_seq, commit_seq)
    }

    /// Allocate the next monotone `WakeTaskItem`, without publishing it (used when only a
    /// socket hook is configured without a broker task queue).
    #[must_use]
    pub fn next_item(&mut self, boffset: u64, subject: &str, wake_line: &str) -> WakeTaskItem {
        let cand = self.dispatched_seq.saturating_add(1);
        let next_seq = wake_dispatch_seq_advance(self.dispatched_seq, cand);
        self.dispatched_seq = next_seq;
        WakeTaskItem {
            wake_seq: next_seq,
            boffset,
            subject: subject.to_owned(),
            wake_line: wake_line.to_owned(),
        }
    }

    /// Record that `seq` completed external hook delivery.
    pub fn mark_acked(&mut self, seq: u64) {
        self.acked_seq = wake_dispatch_seq_advance(self.acked_seq, seq);
    }

    /// Publish one wake onto `self.task_subject` via `client`, returning
    /// `(item, task_log_offset, was_duplicate)` and advancing `acked_seq` only once the
    /// broker acknowledges the task append.
    pub fn publish_wake<S: Read + Write>(
        &mut self,
        client: &mut Client<S>,
        boffset: u64,
        subject: &str,
        wake_line: &str,
    ) -> io::Result<(WakeTaskItem, u64, bool)> {
        let item = self.next_item(boffset, subject, wake_line);
        let payload = item.encode()?;
        let (task_off, dup) = client.publish(
            self.producer_id,
            item.wake_seq,
            &self.task_subject,
            &payload,
        )?;
        self.acked_seq = wake_dispatch_seq_advance(self.acked_seq, item.wake_seq);
        Ok((item, task_off, dup))
    }

    /// Type-erased [`astream_broker::AnyClient`] specialization of [`Self::publish_wake`].
    pub fn publish_wake_any(
        &mut self,
        client: &mut astream_broker::AnyClient,
        boffset: u64,
        subject: &str,
        wake_line: &str,
    ) -> io::Result<(WakeTaskItem, u64, bool)> {
        let item = self.next_item(boffset, subject, wake_line);
        let payload = item.encode()?;
        let (task_off, dup) = client.publish(
            self.producer_id,
            item.wake_seq,
            &self.task_subject,
            &payload,
        )?;
        self.acked_seq = wake_dispatch_seq_advance(self.acked_seq, item.wake_seq);
        Ok((item, task_off, dup))
    }
}

/// Drain all currently queued [`WakeTaskItem`]s matching `filter` for consumer `group`
/// without blocking past the broker's caught-up `Mark` (up to `max_items`).
///
/// A turn-based driver calls this at the top of its turn, acts on the returned
/// `(task_log_offset, WakeTaskItem)` entries, and commits the highest `task_log_offset`
/// via `commit_client.commit(group, last_task_offset)` so an interrupted turn re-drains
/// unacted tasks on the next turn.
pub fn drain_wake_tasks<S: Read + Write>(
    mut sub_client: Client<S>,
    group: &str,
    filter: &str,
    max_items: usize,
) -> io::Result<Vec<(u64, WakeTaskItem)>> {
    if max_items == 0 {
        return Ok(Vec::new());
    }
    let _ = sub_client.burst_marks()?;
    let mut sub = sub_client.subscribe_group(group, filter)?;
    let mut out = Vec::new();
    while out.len() < max_items {
        match sub.recv_event()? {
            None | Some(Event::Mark { .. }) => break,
            Some(Event::Gap(_)) => {}
            Some(Event::Delivery { offset, body, .. }) => {
                let item = WakeTaskItem::decode(&body)?;
                out.push((offset, item));
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wake_task_item_roundtrips_and_hook_formats_escape_cleanly() {
        let mut q = WakeTaskQueue::new(task_subject("claude-main"), 77, 0);
        assert_eq!(q.subject(), "/a/stream/tasks/claude-main");
        assert_eq!(q.producer_id(), 77);

        let item = q.next_item(
            42,
            "/a/stream/term/s 1/out",
            "PROMPT_READY boffset=42 title=hello%20\"world\"",
        );
        assert_eq!(item.wake_seq, 1);
        assert!(!q.can_commit_seq(1));
        q.mark_acked(1);
        assert!(q.can_commit_seq(1));

        let bytes = item.encode().unwrap();
        let decoded = WakeTaskItem::decode(&bytes).unwrap();
        assert_eq!(decoded, item);

        let claude_notif = WakeHookFormat::ClaudeNotificationJson.render(&item);
        assert!(claude_notif.starts_with("{\"hook_event_name\":\"Notification\","));
        assert!(claude_notif.contains("\"boffset\":42"));
        assert!(claude_notif.ends_with("}\n"));

        let claude_stop = WakeHookFormat::ClaudeStopJson.render(&item);
        assert!(claude_stop.starts_with("{\"hook_event_name\":\"Stop\","));

        let codex = WakeHookFormat::CodexTurnJson.render(&item);
        assert!(codex.starts_with("{\"type\":\"turn.wake\","));
    }
}
