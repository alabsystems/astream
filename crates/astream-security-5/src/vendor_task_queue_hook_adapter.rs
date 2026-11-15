// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Closed-vocabulary vendor agent hook & task-queue adapter (`astream` drive pipe §5)
//! (`docs/ROADMAP.md` lines 237–238, `docs/DESIGN-aterm-fabric.md` §8.4, §13 line 3823;
//! `Astream.Agent.TlaVendorTaskQueueHookAdapter`).
//!
//! Translates vendor-specific agent lifecycle hooks (Claude Code `PreToolUse` / `Stop` /
//! `SessionStart` / `UserPromptSubmit`, Codex `notify`, AGY background wakeup) into `astream`'s
//! own task-queue directives while rebuilding every field from a closed vocabulary:
//! - Under an active human hold (`human_hold_active == true`), `PreToolUse` exits `2` (`BlockTool`)
//!   carrying only a bounded reason code,
//! - `Stop` wakes the turn (`Exit2WakeDigest`) ONLY when `latest_inbox_offset > seen_inbox_offset`
//!   AND per-session wake budget remains, keeping untrusted message bodies completely out of the
//!   wake path (§14 line 3958).

#[cfg(clean_islands)]
#[path = "vendor_task_queue_hook_adapter_island.rs"]
mod vendor_task_queue_hook_adapter_island;
#[cfg(clean_islands)]
pub use vendor_task_queue_hook_adapter_island::{
    hook_digest_bytes_clamp_b129, hook_seen_offset_advance_b129,
};

#[cfg(not(clean_islands))]
/// Clamp synthesized closed-vocabulary metadata digest bytes to `max_digest_bytes`.
#[must_use]
pub const fn hook_digest_bytes_clamp_b129(cand_bytes: u64, max_digest_bytes: u64) -> u64 {
    if cand_bytes < max_digest_bytes {
        cand_bytes
    } else {
        max_digest_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the session's `seen_inbox_offset` ledger across hook invocations.
#[must_use]
pub const fn hook_seen_offset_advance_b129(cur_seen: u64, cand_seen: u64) -> u64 {
    if cur_seen < cand_seen {
        cand_seen
    } else {
        cur_seen
    }
}

contract_fn! {
    /// True iff `latest_offset > seen_offset && wakes_used < max_wake_budget`.
    #[must_use]
    pub const fn hook_stop_should_rewake_b129(
        latest_offset: u64,
        seen_offset: u64,
        wakes_used: u64,
        max_wake_budget: u64,
    ) -> bool
    clauses [ensures result == (latest_offset > seen_offset && wakes_used < max_wake_budget)]
    {
        latest_offset > seen_offset && wakes_used < max_wake_budget
    }
}

/// Vendor hook event entering `astream`'s task-queue adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VendorHookEvent {
    ClaudePreToolUse,
    ClaudeUserPromptSubmit,
    ClaudeSessionStart,
    ClaudeStop,
    CodexTurnNotify,
}

/// Sanitized, body-free directive returned to the vendor harness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HookAdapterDirective {
    /// Exit `0` with no injected context.
    PassThroughExit0,
    /// Exit `2` on `PreToolUse` to block tool execution while human hold is active.
    Exit2BlockUnderHumanHold,
    /// Exit `0` on `SessionStart` / `UserPromptSubmit` injecting a bodiless metadata header.
    Exit0InjectMetadataContext {
        new_up_to_offset: u64,
        clamped_digest_bytes: u64,
    },
    /// Exit `2` on `Stop` with a bodiless metadata digest to wake the next agent turn.
    Exit2RewakeTurn {
        new_up_to_offset: u64,
        clamped_digest_bytes: u64,
        wakes_used: u64,
    },
}

/// Stateful vendor hook & task-queue adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VendorTaskQueueHookAdapter {
    seen_inbox_offset: u64,
    wakes_used: u64,
    max_wake_budget: u64,
    max_digest_bytes: u64,
}

impl VendorTaskQueueHookAdapter {
    #[must_use]
    pub const fn new(max_wake_budget: u64, max_digest_bytes: u64) -> Self {
        Self {
            seen_inbox_offset: 0,
            wakes_used: 0,
            max_wake_budget,
            max_digest_bytes,
        }
    }

    pub fn reset_wake_budget(&mut self) {
        self.wakes_used = 0;
    }

    /// Evaluate a vendor hook event against `(human_hold_active, latest_inbox_offset, raw_digest_bytes)`.
    pub fn evaluate_hook(
        &mut self,
        event: VendorHookEvent,
        human_hold_active: bool,
        latest_inbox_offset: u64,
        raw_digest_bytes: u64,
    ) -> HookAdapterDirective {
        match event {
            VendorHookEvent::ClaudePreToolUse => {
                if human_hold_active {
                    HookAdapterDirective::Exit2BlockUnderHumanHold
                } else {
                    HookAdapterDirective::PassThroughExit0
                }
            }
            VendorHookEvent::ClaudeSessionStart | VendorHookEvent::ClaudeUserPromptSubmit => {
                if latest_inbox_offset <= self.seen_inbox_offset {
                    return HookAdapterDirective::PassThroughExit0;
                }
                self.seen_inbox_offset =
                    hook_seen_offset_advance_b129(self.seen_inbox_offset, latest_inbox_offset);
                HookAdapterDirective::Exit0InjectMetadataContext {
                    new_up_to_offset: self.seen_inbox_offset,
                    clamped_digest_bytes: hook_digest_bytes_clamp_b129(
                        raw_digest_bytes,
                        self.max_digest_bytes,
                    ),
                }
            }
            VendorHookEvent::ClaudeStop | VendorHookEvent::CodexTurnNotify => {
                if human_hold_active {
                    return HookAdapterDirective::PassThroughExit0;
                }
                if !hook_stop_should_rewake_b129(
                    latest_inbox_offset,
                    self.seen_inbox_offset,
                    self.wakes_used,
                    self.max_wake_budget,
                ) {
                    return HookAdapterDirective::PassThroughExit0;
                }
                self.wakes_used = self.wakes_used.saturating_add(1);
                self.seen_inbox_offset =
                    hook_seen_offset_advance_b129(self.seen_inbox_offset, latest_inbox_offset);
                HookAdapterDirective::Exit2RewakeTurn {
                    new_up_to_offset: self.seen_inbox_offset,
                    clamped_digest_bytes: hook_digest_bytes_clamp_b129(
                        raw_digest_bytes,
                        self.max_digest_bytes,
                    ),
                    wakes_used: self.wakes_used,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_pre_tool_use_on_hold_and_rewakes_stop_monotonically_within_budget() {
        let mut adapter = VendorTaskQueueHookAdapter::new(2, 512);

        assert_eq!(
            adapter.evaluate_hook(VendorHookEvent::ClaudePreToolUse, true, 10, 64),
            HookAdapterDirective::Exit2BlockUnderHumanHold
        );
        assert_eq!(
            adapter.evaluate_hook(VendorHookEvent::ClaudePreToolUse, false, 10, 64),
            HookAdapterDirective::PassThroughExit0
        );

        // First Stop with unread offset 10 wakes turn and clamps digest to 512 bytes.
        assert_eq!(
            adapter.evaluate_hook(VendorHookEvent::ClaudeStop, false, 10, 2_000),
            HookAdapterDirective::Exit2RewakeTurn {
                new_up_to_offset: 10,
                clamped_digest_bytes: 512,
                wakes_used: 1,
            }
        );
        // Same offset 10 does NOT rewake again!
        assert_eq!(
            adapter.evaluate_hook(VendorHookEvent::ClaudeStop, false, 10, 128),
            HookAdapterDirective::PassThroughExit0
        );
        // Second new offset 15 consumes 2nd wake token; third new offset 20 hits budget ceiling!
        assert!(matches!(
            adapter.evaluate_hook(VendorHookEvent::ClaudeStop, false, 15, 128),
            HookAdapterDirective::Exit2RewakeTurn { wakes_used: 2, .. }
        ));
        assert_eq!(
            adapter.evaluate_hook(VendorHookEvent::ClaudeStop, false, 20, 128),
            HookAdapterDirective::PassThroughExit0
        );
    }
}
