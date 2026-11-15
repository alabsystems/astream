// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Closed-vocabulary agent hook-event normalizer and lease-fenced task-queue adapter
//! (`docs/ROADMAP.md` "vendor-specific agent hooks / task-queue adapters";
//! `docs/DESIGN-drive-pipe.md` §5; `docs/DESIGN-aterm-fabric.md` §8.4).
//!
//! Rebuilds every untrusted vendor hook payload (`ClaudeCode`, `Codex`, `Agy`, `Generic`)
//! from a strict closed vocabulary ([`AgentVendor`], [`HookPhase`], [`TurnDisposition`]) so
//! arbitrary vendor JSON strings never flow unvalidated onto the bus, and coordinates
//! lease-fenced task dispatch ([`TaskQueueAdapter`]) with Clean-origin monotone epoch
//! advancement ([`task_lease_epoch_advance`]) and bounded retry clamping
//! ([`task_retry_clamp`]; `Astream.Agent.TlaTaskAdapter`).

#![allow(clippy::question_mark)]

use astream_wire::{Offset, ReceiptVerdict, V1Receipt};
use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "adapter_island.rs"]
mod adapter_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn task_lease_epoch_advance(cur_epoch: u64, proposed_epoch: u64) -> u64 {
    if cur_epoch < proposed_epoch {
        proposed_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn task_retry_clamp(attempts: u64, max_attempts: u64) -> u64 {
    if attempts < max_attempts {
        attempts
    } else {
        max_attempts
    }
}
#[cfg(clean_islands)]
pub use adapter_island::{task_lease_epoch_advance, task_retry_clamp};

contract_fn! {
    /// Verified check that a worker's presented lease epoch matches the task's active
    /// `cur_epoch` (`req_epoch == cur_epoch`), linked via `clean-kernel-defeq` to
    /// `task_lease_matches_epoch_isl`.
    #[must_use]
    pub const fn task_lease_matches_epoch(req_epoch: u64, cur_epoch: u64) -> bool
    clauses [ensures result == (req_epoch == cur_epoch)]
    {
        req_epoch == cur_epoch
    }
}

/// Hard cap on tasks held in one [`TaskQueueAdapter`].
pub const MAX_ADAPTER_TASKS: usize = 1024;

/// Hard cap on retry attempts per task (`1..=16`).
pub const MAX_TASK_ATTEMPTS: u32 = 16;

/// Closed vocabulary of agent harness vendors (`DESIGN-drive-pipe.md` §5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgentVendor {
    ClaudeCode,
    Codex,
    Agy,
    Generic,
}

impl AgentVendor {
    /// Canonical lowercase wire token for this vendor.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ClaudeCode => "claude",
            Self::Codex => "codex",
            Self::Agy => "agy",
            Self::Generic => "generic",
        }
    }

    /// Parse a closed-vocabulary vendor token.
    pub fn parse(raw: &str) -> Option<Self> {
        if raw == "claude" || raw == "claude-code" {
            Some(Self::ClaudeCode)
        } else if raw == "codex" || raw == "codex-alab" {
            Some(Self::Codex)
        } else if raw == "agy" || raw == "antigravity" {
            Some(Self::Agy)
        } else if raw == "generic" {
            Some(Self::Generic)
        } else {
            None
        }
    }
}

/// Closed vocabulary of normalized agent lifecycle phases (`DESIGN-aterm-fabric.md` §8.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HookPhase {
    SessionStart,
    UserPromptSubmit,
    PreToolUse,
    PostToolUse,
    TurnStop,
    NeedsHuman,
}

impl HookPhase {
    /// Canonical wire word for this lifecycle phase.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SessionStart => "session_start",
            Self::UserPromptSubmit => "prompt_submit",
            Self::PreToolUse => "pre_tool_use",
            Self::PostToolUse => "post_tool_use",
            Self::TurnStop => "turn_stop",
            Self::NeedsHuman => "needs_human",
        }
    }

    /// Map vendor-specific hook names (`PreToolUse`, `Stop`, `agent-turn-complete`, etc.)
    /// onto the closed [`HookPhase`] vocabulary.
    pub fn from_vendor_event(raw: &str) -> Option<Self> {
        if raw == "SessionStart" || raw == "session_start" || raw == "session-start" {
            Some(Self::SessionStart)
        } else if raw == "UserPromptSubmit" || raw == "prompt_submit" || raw == "user-prompt" {
            Some(Self::UserPromptSubmit)
        } else if raw == "PreToolUse" || raw == "pre_tool_use" || raw == "before_tool" {
            Some(Self::PreToolUse)
        } else if raw == "PostToolUse" || raw == "post_tool_use" || raw == "after_tool" {
            Some(Self::PostToolUse)
        } else if raw == "Stop"
            || raw == "turn_stop"
            || raw == "agent-turn-complete"
            || raw == "turn-complete"
        {
            Some(Self::TurnStop)
        } else if raw == "Notification" || raw == "needs_human" || raw == "permission-prompt" {
            Some(Self::NeedsHuman)
        } else {
            None
        }
    }
}

/// Closed-vocabulary tool category extracted without forwarding untrusted arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToolCategory {
    None,
    Shell,
    FileRead,
    FileWrite,
    Search,
    Subagent,
    Web,
    Other,
}

impl ToolCategory {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Shell => "shell",
            Self::FileRead => "file_read",
            Self::FileWrite => "file_write",
            Self::Search => "search",
            Self::Subagent => "subagent",
            Self::Web => "web",
            Self::Other => "other",
        }
    }

    #[must_use]
    pub fn classify(tool_name: &str) -> Self {
        if tool_name.is_empty() || tool_name == "none" {
            Self::None
        } else if tool_name == "Bash" || tool_name == "run_command" || tool_name == "shell" {
            Self::Shell
        } else if tool_name == "Read" || tool_name == "read_file" || tool_name == "view_file" {
            Self::FileRead
        } else if tool_name == "Edit"
            || tool_name == "Write"
            || tool_name == "edit_file"
            || tool_name == "write_file"
        {
            Self::FileWrite
        } else if tool_name == "Grep" || tool_name == "Glob" || tool_name == "grep_search" {
            Self::Search
        } else if tool_name == "Task" || tool_name == "invoke_subagent" {
            Self::Subagent
        } else if tool_name == "WebSearch" || tool_name == "WebFetch" || tool_name == "search_web" {
            Self::Web
        } else {
            Self::Other
        }
    }
}

/// Sanitized, closed-vocabulary agent lifecycle event (`DESIGN-aterm-fabric.md` §8.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentHookEvent {
    pub vendor: AgentVendor,
    pub phase: HookPhase,
    pub tool: ToolCategory,
    pub timestamp_ms: u64,
}

fn is_hook_delim(b: u8) -> bool {
    b.is_ascii_whitespace() || b == b',' || b == b'{' || b == b'}'
}

fn trim_hook_atom(s: &str) -> &str {
    s.trim_ascii()
        .trim_matches('"')
        .trim_matches('\'')
        .trim_ascii()
}

impl AgentHookEvent {
    /// Normalize a flat `key=value` or minimal JSON-like vendor hook snippet into a
    /// closed-vocabulary [`AgentHookEvent`], discarding all unrecognized fields.
    pub fn normalize_kv(vendor: AgentVendor, raw: &str, timestamp_ms: u64) -> Option<Self> {
        if raw.len() > 16_384 {
            return None;
        }
        let mut phase: Option<HookPhase> = None;
        let mut tool = ToolCategory::None;

        let bytes = raw.as_bytes();
        let mut idx = 0usize;
        while idx < bytes.len() {
            while let Some(&b) = bytes.get(idx) {
                if !is_hook_delim(b) {
                    break;
                }
                idx = idx.saturating_add(1);
            }
            let start = idx;
            while let Some(&b) = bytes.get(idx) {
                if is_hook_delim(b) {
                    break;
                }
                idx = idx.saturating_add(1);
            }
            if start == idx {
                break;
            }
            let Some(tok_bytes) = bytes.get(start..idx) else {
                break;
            };
            let Ok(tok) = core::str::from_utf8(tok_bytes) else {
                continue;
            };
            let split_kv = match tok.split_once('=') {
                Some(pair) => Some(pair),
                None => tok.split_once(':'),
            };
            if let Some((k, v)) = split_kv {
                let k_trim = trim_hook_atom(k);
                let v_trim = trim_hook_atom(v);
                if k_trim == "event"
                    || k_trim == "hook_event_name"
                    || k_trim == "type"
                    || k_trim == "phase"
                {
                    if let Some(p) = HookPhase::from_vendor_event(v_trim) {
                        phase = Some(p);
                    }
                } else if k_trim == "tool" || k_trim == "tool_name" {
                    tool = ToolCategory::classify(v_trim);
                }
            } else if phase.is_none() {
                if let Some(p) = HookPhase::from_vendor_event(trim_hook_atom(tok)) {
                    phase = Some(p);
                }
            }
        }

        let Some(resolved_phase) = phase else {
            return None;
        };
        Some(Self {
            vendor,
            phase: resolved_phase,
            tool,
            timestamp_ms,
        })
    }

    /// Render the normalized event as a fixed-vocabulary `v=1` bus line.
    #[must_use]
    pub fn encode_v1(&self) -> String {
        format!(
            "v=1 t={} vendor={} phase={} tool={}",
            self.timestamp_ms,
            self.vendor.as_str(),
            self.phase.as_str(),
            self.tool.as_str()
        )
    }
}

/// Terminal disposition of a leased task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TurnDisposition {
    Handled,
    Refused,
    Deferred,
}

impl TurnDisposition {
    #[must_use]
    pub const fn to_receipt_verdict(self) -> ReceiptVerdict {
        match self {
            Self::Handled => ReceiptVerdict::Handled,
            Self::Refused => ReceiptVerdict::Refused,
            Self::Deferred => ReceiptVerdict::Deferred,
        }
    }
}

/// Lifecycle state of one task managed by [`TaskQueueAdapter`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TaskLeaseState {
    Pending,
    Leased {
        worker_id: String,
        lease_epoch: u64,
        deadline_ms: u64,
    },
    Settled {
        worker_id: String,
        lease_epoch: u64,
        disposition: TurnDisposition,
    },
    Exhausted {
        last_epoch: u64,
    },
}

/// One queued agent task indexed by its durable bus `task_offset`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaskQueueItem {
    pub task_offset: u64,
    pub prompt: String,
    pub attempts: u32,
    pub max_attempts: u32,
    pub state: TaskLeaseState,
}

/// Deterministic, lease-fenced agent task-queue adapter (`Astream.Agent.TlaTaskAdapter`).
#[derive(Clone, Debug)]
pub struct TaskQueueAdapter {
    next_epoch: u64,
    tasks: BTreeMap<u64, TaskQueueItem>,
}

fn valid_worker_id(worker_id: &str) -> bool {
    if worker_id.is_empty() || worker_id.len() > 64 {
        return false;
    }
    let mut rest = worker_id.as_bytes();
    while let &[b, ref tail @ ..] = rest {
        let ok = b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b':';
        if !ok {
            return false;
        }
        rest = tail;
    }
    true
}

impl Default for TaskQueueAdapter {
    fn default() -> Self {
        Self::new()
    }
}

impl TaskQueueAdapter {
    /// Construct an empty task-queue adapter starting at epoch `0`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_epoch: 0,
            tasks: BTreeMap::new(),
        }
    }

    /// Number of tracked tasks.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tasks.len()
    }

    /// Whether no tasks are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// Inspect a task by `task_offset`.
    #[must_use]
    pub fn get(&self, task_offset: u64) -> Option<&TaskQueueItem> {
        self.tasks.get(&task_offset)
    }

    /// Enqueue a new task at `task_offset` with bounded `max_attempts` (`1..=MAX_TASK_ATTEMPTS`).
    /// Idempotent if `task_offset` is already present (`false` returned).
    pub fn enqueue(
        &mut self,
        task_offset: u64,
        prompt: &str,
        max_attempts: u32,
    ) -> Result<bool, String> {
        if self.tasks.contains_key(&task_offset) {
            return Ok(false);
        }
        if self.tasks.len() >= MAX_ADAPTER_TASKS {
            return Err("TaskQueueAdapter full (MAX_ADAPTER_TASKS)".to_string());
        }
        if prompt.len() > 65_536 {
            return Err("task prompt exceeds 64 KiB".to_string());
        }
        let ma_floor = if max_attempts > 1 { max_attempts } else { 1 };
        let cap = task_retry_clamp(u64::from(ma_floor), u64::from(MAX_TASK_ATTEMPTS)) as u32;
        self.tasks.insert(
            task_offset,
            TaskQueueItem {
                task_offset,
                prompt: prompt.to_string(),
                attempts: 0,
                max_attempts: cap,
                state: TaskLeaseState::Pending,
            },
        );
        Ok(true)
    }

    /// Lease the lowest-offset `Pending` task to `worker_id` with `lease_ttl_ms` from `now_ms`.
    /// Advances `next_epoch` strictly monotonically via [`task_lease_epoch_advance`].
    pub fn claim_next(
        &mut self,
        worker_id: &str,
        now_ms: u64,
        lease_ttl_ms: u64,
    ) -> Result<Option<(u64, u64, String)>, String> {
        if !valid_worker_id(worker_id) {
            return Err(format!("invalid worker_id {worker_id:?}"));
        }
        let mut target_off: Option<u64> = None;
        for (&off, item) in &self.tasks {
            if item.state == TaskLeaseState::Pending {
                target_off = Some(off);
                break;
            }
        }
        let Some(off) = target_off else {
            return Ok(None);
        };
        if self.next_epoch == u64::MAX {
            return Err("lease epoch exhausted".to_string());
        }
        let proposed = self.next_epoch.saturating_add(1);
        let epoch = task_lease_epoch_advance(self.next_epoch, proposed);
        self.next_epoch = epoch;

        let Some(item) = self.tasks.get_mut(&off) else {
            return Ok(None);
        };
        let next_att = task_retry_clamp(
            u64::from(item.attempts).saturating_add(1),
            u64::from(item.max_attempts),
        ) as u32;
        item.attempts = next_att;
        let eff_ttl = if lease_ttl_ms == 0 { 1 } else { lease_ttl_ms };
        item.state = TaskLeaseState::Leased {
            worker_id: worker_id.to_string(),
            lease_epoch: epoch,
            deadline_ms: now_ms.saturating_add(eff_ttl),
        };
        Ok(Some((off, epoch, item.prompt.clone())))
    }

    /// Complete a leased task at `(task_offset, lease_epoch)` and emit a canonical
    /// [`V1Receipt`] `ack` body (`v=1 t=<now_ms> re=<task_offset> verdict=<word>`).
    /// Stale or mismatched `lease_epoch` completions are fenced fail-closed.
    pub fn complete_lease(
        &mut self,
        task_offset: u64,
        lease_epoch: u64,
        disposition: TurnDisposition,
        now_ms: u64,
    ) -> Result<String, String> {
        let Some(item) = self.tasks.get_mut(&task_offset) else {
            return Err(format!("unknown task_offset {task_offset}"));
        };
        let (worker_id, cur_epoch) = match &item.state {
            TaskLeaseState::Leased {
                worker_id,
                lease_epoch: cur,
                ..
            } => (worker_id.clone(), *cur),
            _ => {
                return Err(format!(
                    "task {task_offset} is not currently leased (state={:?})",
                    item.state
                ))
            }
        };
        if !task_lease_matches_epoch(lease_epoch, cur_epoch) {
            return Err(format!(
                "stale lease_epoch {lease_epoch} fenced by active epoch {cur_epoch}"
            ));
        }
        item.state = TaskLeaseState::Settled {
            worker_id,
            lease_epoch: cur_epoch,
            disposition,
        };
        let receipt = V1Receipt::Ack {
            re: Offset(task_offset),
            verdict: Some(disposition.to_receipt_verdict()),
            sender_t_ms: Some(now_ms),
        };
        Ok(receipt.encode())
    }

    /// Sweep expired leases (`deadline_ms <= now_ms`), returning tasks with remaining retry
    /// budget (`attempts < max_attempts`) to `Pending` and marking exhausted tasks `Exhausted`.
    pub fn expire_overdue(&mut self, now_ms: u64) -> Vec<u64> {
        let mut expired = Vec::new();
        for (&off, item) in &mut self.tasks {
            let overdue_epoch = match &item.state {
                TaskLeaseState::Leased {
                    lease_epoch,
                    deadline_ms,
                    ..
                } if *deadline_ms <= now_ms => Some(*lease_epoch),
                _ => None,
            };
            if let Some(ep) = overdue_epoch {
                expired.push(off);
                if item.attempts < item.max_attempts {
                    item.state = TaskLeaseState::Pending;
                } else {
                    item.state = TaskLeaseState::Exhausted { last_epoch: ep };
                }
            }
        }
        expired
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closed_vocabulary_hook_strips_untrusted_payloads_and_fences_stale_leases() {
        let raw_json =
            r#"{"hook_event_name":"PreToolUse","tool_name":"Bash","tool_input":"rm -rf / ; evil"}"#;
        let ev = AgentHookEvent::normalize_kv(AgentVendor::ClaudeCode, raw_json, 1_700_000_000)
            .expect("normalize");
        assert_eq!(ev.vendor, AgentVendor::ClaudeCode);
        assert_eq!(ev.phase, HookPhase::PreToolUse);
        assert_eq!(ev.tool, ToolCategory::Shell);
        let line = ev.encode_v1();
        assert_eq!(
            line,
            "v=1 t=1700000000 vendor=claude phase=pre_tool_use tool=shell"
        );
        assert!(!line.contains("evil"));

        let mut q = TaskQueueAdapter::new();
        assert!(q.enqueue(42, "fix bug", 2).expect("enqueue"));
        let (off1, ep1, _) = q
            .claim_next("worker-1", 1000, 500)
            .expect("claim 1")
            .expect("some");
        assert_eq!((off1, ep1), (42, 1));

        // Lease expires at t=1500 -> requeued because attempts (1) < max_attempts (2).
        assert_eq!(q.expire_overdue(1500), vec![42]);
        let (off2, ep2, _) = q
            .claim_next("worker-2", 1600, 500)
            .expect("claim 2")
            .expect("some");
        assert_eq!((off2, ep2), (42, 2));

        // Worker-1 presenting stale epoch 1 is fenced!
        assert!(q
            .complete_lease(42, ep1, TurnDisposition::Handled, 1700)
            .is_err());

        // Worker-2 presenting current epoch 2 succeeds and emits valid V1Receipt!
        let ack_line = q
            .complete_lease(42, ep2, TurnDisposition::Handled, 1700)
            .expect("complete");
        let parsed = V1Receipt::decode("ack", ack_line.as_bytes()).expect("v1 decode");
        assert_eq!(
            parsed,
            V1Receipt::Ack {
                re: Offset(42),
                verdict: Some(ReceiptVerdict::Handled),
                sender_t_ms: Some(1700),
            }
        );
    }

    #[test]
    fn zero_ttl_clamps_to_one_ms_and_exhausted_epoch_fails_closed() {
        let mut q = TaskQueueAdapter::new();
        assert!(q.enqueue(7, "task", 2).unwrap());
        let (_off, ep, _) = q.claim_next("worker-1", 1000, 0).unwrap().unwrap();
        assert_eq!(ep, 1);
        // Zero TTL clamps to 1ms, so lease is still active at t=1000 and expires at t=1001.
        assert!(q.expire_overdue(1000).is_empty());
        assert_eq!(q.expire_overdue(1001), vec![7]);

        q.next_epoch = u64::MAX;
        assert!(q.claim_next("worker-1", 1002, 500).is_err());
    }
}
