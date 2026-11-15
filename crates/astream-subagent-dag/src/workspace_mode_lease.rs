// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Subagent `Workspace` mode (`inherit` | `branch` | `share`) write-isolation validator preventing
//! two write-enabled `inherit` subagents from clobbering the parent working tree simultaneously!
//! (`Astream.Subagent.TlaWorkspaceModeLease`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "workspace_mode_lease_island.rs"]
mod workspace_mode_lease_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_leases_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use workspace_mode_lease_island::{sub_epoch_advance, sub_leases_clamp};

/// Maximum concurrent isolated `branch` / `share` workspaces per parent session.
pub const MAX_ISOLATED_WORKTREES: u64 = 32;

contract_fn! {
    /// Verified exclusive `inherit` writer check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sub_inherit_free_isl`.
    #[must_use]
    pub const fn sub_inherit_free(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubagentWorkspaceMode {
    Inherit,
    Branch,
    Share,
}

/// Coordinates read-only vs write-enabled subagent workspace modes.
#[derive(Debug, Clone, Default)]
pub struct WorkspaceIsolationGuard {
    active_inherit_writer: Option<String>,
    active_isolated: BTreeMap<String, SubagentWorkspaceMode>,
    isolated_count: u64,
    epoch: u64,
}

impl WorkspaceIsolationGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active_inherit_writer: None,
            active_isolated: BTreeMap::new(),
            isolated_count: 0,
            epoch: 0,
        }
    }

    pub fn acquire_subagent_workspace(
        &mut self,
        conv_id: &str,
        mode: SubagentWorkspaceMode,
        write_enabled: bool,
    ) -> Result<(), &'static str> {
        if conv_id.trim().is_empty() {
            return Err("empty subagent conversation id");
        }
        if !write_enabled {
            return Ok(());
        }
        if self.active_inherit_writer.as_deref() == Some(conv_id)
            || self.active_isolated.contains_key(conv_id)
        {
            return Err("subagent already holds an active write workspace lease");
        }
        match mode {
            SubagentWorkspaceMode::Inherit => {
                let busy = if self.active_inherit_writer.is_some() {
                    1u64
                } else {
                    0u64
                };
                if !sub_inherit_free(0, busy) {
                    return Err("another write-enabled subagent already holds Inherit workspace; use Branch or Share");
                }
                let mut owned = String::new();
                owned.push_str(conv_id);
                self.active_inherit_writer = Some(owned);
            }
            SubagentWorkspaceMode::Branch | SubagentWorkspaceMode::Share => {
                let cap = sub_leases_clamp(MAX_ISOLATED_WORKTREES, MAX_ISOLATED_WORKTREES);
                if self.isolated_count >= cap {
                    return Err("isolated branch/share worktree cap reached");
                }
                let mut owned = String::new();
                owned.push_str(conv_id);
                self.active_isolated.insert(owned, mode);
                self.isolated_count = self.active_isolated.len() as u64;
            }
        }
        self.epoch = sub_epoch_advance(self.epoch, self.epoch.saturating_add(1));
        Ok(())
    }

    pub fn release(&mut self, conv_id: &str, mode: SubagentWorkspaceMode, write_enabled: bool) {
        if !write_enabled {
            return;
        }
        if matches!(mode, SubagentWorkspaceMode::Inherit) {
            if self.active_inherit_writer.as_deref() == Some(conv_id) {
                self.active_inherit_writer = None;
            }
        } else if self.active_isolated.get(conv_id) == Some(&mode) {
            self.active_isolated.remove(conv_id);
            self.isolated_count = self.active_isolated.len() as u64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn isolation_guard_blocks_concurrent_inherit_writers_while_allowing_parallel_share_or_readonly()
    {
        let mut g = WorkspaceIsolationGuard::new();
        g.acquire_subagent_workspace("c1", SubagentWorkspaceMode::Inherit, true)
            .unwrap();
        assert!(g
            .acquire_subagent_workspace("c2", SubagentWorkspaceMode::Inherit, true)
            .is_err());
        g.acquire_subagent_workspace("c2", SubagentWorkspaceMode::Inherit, false)
            .unwrap();
        g.acquire_subagent_workspace("c3", SubagentWorkspaceMode::Share, true)
            .unwrap();
    }
}
