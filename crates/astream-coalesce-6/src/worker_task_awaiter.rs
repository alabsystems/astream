// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-worker `@<sid>:<rev>` revision cursor & terminal-wakeup tracker
//! (`Astream.Agent.TlaWorkerTaskAwaiter`).
//!
//! Models `aterm ctl @self spawn agent=<kind> -` and
//! `aterm ctl await task @<sid>:<rev>,…` across Claude Code, `codex-alab`, `agy`, and
//! Muse Code worker tabs:
//! - Tracks monotone per-worker `since_rev <= observed_rev` watermarks so transitions that
//!   occurred between background `await task` invocations are never missed.
//! - Triggers wakeups on actionable worker states (`DoneLanded`, `Exited`, `Stalled`,
//!   `NeedsPerson`) strictly when `worker_has_new_revision(since_rev, incoming_rev)`.
//! - Formats exact `@<sid>:<rev>` wait tokens for follow-up `await task` calls.

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
#[path = "worker_task_awaiter_island.rs"]
mod worker_task_awaiter_island;
#[cfg(clean_islands)]
pub use worker_task_awaiter_island::{awaiter_rev_advance, worker_delivery_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn awaiter_rev_advance(cur_rev: u64, incoming_rev: u64) -> u64 {
    if cur_rev < incoming_rev {
        incoming_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn worker_delivery_clamp(delivered: u64, observed_rev: u64) -> u64 {
    if delivered < observed_rev {
        delivered
    } else {
        observed_rev
    }
}

contract_fn! {
    /// Verified check that `observed_rev` strictly exceeds the consumer's `since_rev` cursor,
    /// linked via `clean-kernel-defeq` to `worker_has_new_revision_isl`.
    #[must_use]
    pub const fn worker_has_new_revision(since_rev: u64, observed_rev: u64) -> bool
    clauses [ensures result == (since_rev < observed_rev)]
    {
        since_rev < observed_rev
    }
}

/// Supported `aterm` worker harness agent families.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerAgentKind {
    /// `agent=claude` (Claude Code).
    Claude,
    /// `agent=codex` (`codex-alab`).
    CodexAlab,
    /// `agent=agy` (Antigravity CLI).
    Agy,
    /// `agent=muse` (Muse Code).
    MuseCode,
}

/// Lifecycle state observed for a spawned worker session `@<sid>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskStatus {
    /// Actively working under Autopilot; do not wake parent yet.
    Running,
    /// Work landed cleanly on remote `main` (`Nothing left:`).
    DoneLanded,
    /// Worker process exited before landing.
    Exited,
    /// Worker stopped making progress (`sys jobs` / stall detector).
    Stalled,
    /// Worker raised a `NEEDS YOU:` item requiring a human decision/credential.
    NeedsPerson,
}

impl WorkerTaskStatus {
    /// Returns `true` when `aterm ctl await task` exits to notify the coordinator.
    #[must_use]
    pub const fn is_wakeup_state(self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Tracked revision cursor and latest status for a single worker session `@<sid>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkerCursor {
    session_id: String,
    kind: WorkerAgentKind,
    since_rev: u64,
    observed_rev: u64,
    delivered_count: u64,
    status: WorkerTaskStatus,
}

impl WorkerCursor {
    /// Register a newly spawned worker tab starting at `since=0`.
    #[must_use]
    pub fn new(session_id: impl Into<String>, kind: WorkerAgentKind) -> Self {
        Self {
            session_id: session_id.into(),
            kind,
            since_rev: 0,
            observed_rev: 0,
            delivered_count: 0,
            status: WorkerTaskStatus::Running,
        }
    }

    /// Worker session identifier (without leading `@`).
    #[must_use]
    pub fn session_id(&self) -> &str {
        &self.session_id
    }

    /// Worker agent family.
    #[must_use]
    pub const fn kind(&self) -> WorkerAgentKind {
        self.kind
    }

    /// Last acknowledged revision (`<= observed_rev`).
    #[must_use]
    pub const fn since_rev(&self) -> u64 {
        self.since_rev
    }

    /// Highest revision observed from `aterm ctl` (`>= since_rev`).
    #[must_use]
    pub const fn observed_rev(&self) -> u64 {
        self.observed_rev
    }

    /// Clamped count of delivered wakeups (`<= observed_rev`).
    #[must_use]
    pub const fn delivered_count(&self) -> u64 {
        self.delivered_count
    }

    /// Latest observed [`WorkerTaskStatus`].
    #[must_use]
    pub const fn status(&self) -> WorkerTaskStatus {
        self.status
    }

    /// Format the exact `aterm ctl await task` target token (`@<sid>` at rev 0 or `@<sid>:<rev>`).
    #[must_use]
    pub fn await_token(&self) -> String {
        let mut out = String::new();
        out.push('@');
        out.push_str(&self.session_id);
        if self.observed_rev != 0 {
            out.push(':');
            push_u64_dec(&mut out, self.observed_rev);
        }
        out
    }

    /// Ingest an observed `(incoming_rev, status)` snapshot and return `true` iff a fresh
    /// wakeup should be delivered to the parent agent.
    pub fn observe(&mut self, incoming_rev: u64, status: WorkerTaskStatus) -> bool {
        let next_obs = awaiter_rev_advance(self.observed_rev, incoming_rev);
        let is_new = worker_has_new_revision(self.observed_rev, next_obs);
        if incoming_rev >= self.observed_rev {
            self.since_rev = self.observed_rev;
            self.status = status;
        }
        self.observed_rev = next_obs;
        if is_new && status.is_wakeup_state() {
            let raw_del = self.delivered_count.saturating_add(1);
            self.delivered_count = worker_delivery_clamp(raw_del, self.observed_rev);
            true
        } else {
            self.delivered_count = worker_delivery_clamp(self.delivered_count, self.observed_rev);
            false
        }
    }
}

/// Format a comma-separated `@<sid>:<rev>,...` selector list for `aterm ctl await task`.
#[must_use]
pub fn format_await_task_spec(workers: &[WorkerCursor]) -> String {
    let mut out = String::new();
    let mut rest = workers;
    let mut first = true;
    while let [w, tail @ ..] = rest {
        if !first {
            out.push(',');
        }
        first = false;
        out.push_str(&w.await_token());
        rest = tail;
    }
    out
}

fn push_u64_dec(out: &mut String, mut val: u64) {
    if val == 0 {
        out.push('0');
        return;
    }
    let mut digits = [b'0'; 20];
    let mut len = 0usize;
    while val > 0 && len < digits.len() {
        let rem = (val % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add(rem);
        }
        val /= 10;
        len = len.saturating_add(1);
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&d) = digits.get(len) {
            out.push(d as char);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn monotone_revisions_wake_once_per_actionable_transition_and_format_tokens() {
        let mut w1 = WorkerCursor::new("s41", WorkerAgentKind::Claude);
        let mut w2 = WorkerCursor::new("s42", WorkerAgentKind::Agy);
        assert_eq!(
            format_await_task_spec(&[w1.clone(), w2.clone()]),
            "@s41,@s42"
        );

        // Running progress advances revision without premature wakeup.
        assert!(!w1.observe(3, WorkerTaskStatus::Running));
        assert_eq!(w1.await_token(), "@s41:3");

        // Stale or duplicate revision 3 does not re-fire even if status says Stalled.
        assert!(!w1.observe(3, WorkerTaskStatus::Stalled));

        // Revision 4 with NeedsPerson wakes once and advances token to `@s41:4`!
        assert!(w1.observe(4, WorkerTaskStatus::NeedsPerson));
        assert_eq!(w1.delivered_count(), 1);
        assert_eq!(w1.since_rev(), 3);
        assert_eq!(w1.observed_rev(), 4);

        // Second worker lands at rev 7.
        assert!(w2.observe(7, WorkerTaskStatus::DoneLanded));
        assert_eq!(
            format_await_task_spec(&[w1.clone(), w2.clone()]),
            "@s41:4,@s42:7"
        );
        assert!(w1.since_rev() <= w1.observed_rev());
        assert!(w1.delivered_count() <= w1.observed_rev());
    }
}
