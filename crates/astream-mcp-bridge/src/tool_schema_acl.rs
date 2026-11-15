// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Least-privilege MCP tool allowlist and JSON argument byte-size guard (`EnableMCPTools`,
//! `Astream.Mcp.TlaToolSchemaAcl`).

use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "tool_schema_acl_island.rs"]
mod tool_schema_acl_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_args_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_calls_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use tool_schema_acl_island::{mcp_args_clamp, mcp_calls_advance};

/// Maximum serialized JSON arguments payload for a single MCP tool call (`256` KiB).
pub const MAX_MCP_TOOL_ARGS_BYTES: u64 = 262_144;

contract_fn! {
    /// Verified argument budget check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mcp_args_within_cap_isl`.
    #[must_use]
    pub const fn mcp_args_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Per-subagent MCP tool allowlist.
#[derive(Debug, Clone)]
pub struct McpToolAcl {
    mcp_enabled: bool,
    max_args_bytes: u64,
    allowed_tools: BTreeSet<String>,
    admitted_calls: u64,
}

impl McpToolAcl {
    #[must_use]
    pub fn new(mcp_enabled: bool, tools: &[&str], max_args_bytes: u64) -> Self {
        let mut allowed_tools = BTreeSet::new();
        for &t in tools {
            if !t.is_empty() {
                let mut owned = String::new();
                owned.push_str(t);
                allowed_tools.insert(owned);
            }
        }
        Self {
            mcp_enabled,
            max_args_bytes: mcp_args_clamp(max_args_bytes, MAX_MCP_TOOL_ARGS_BYTES),
            allowed_tools,
            admitted_calls: 0,
        }
    }

    pub fn authorize_call(&mut self, tool: &str, args_json: &[u8]) -> Result<u64, &'static str> {
        if !self.mcp_enabled {
            return Err("EnableMCPTools is false for this agent");
        }
        if tool.is_empty() || !self.allowed_tools.contains(tool) {
            return Err("MCP tool not in allowlist");
        }
        if !mcp_args_within_cap(self.max_args_bytes, args_json.len() as u64) {
            return Err("MCP tool arguments exceed byte cap");
        }
        self.admitted_calls =
            mcp_calls_advance(self.admitted_calls, self.admitted_calls.saturating_add(1));
        Ok(self.admitted_calls)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mcp_acl_enforces_enable_flag_allowlist_and_arg_size() {
        let mut acl = McpToolAcl::new(true, &["read_issue"], 64);
        assert_eq!(acl.authorize_call("read_issue", b"{\"id\":1}").unwrap(), 1);
        assert!(acl.authorize_call("delete_repo", b"{}").is_err());
        assert!(acl.authorize_call("read_issue", &[b'x'; 80]).is_err());
    }
}
