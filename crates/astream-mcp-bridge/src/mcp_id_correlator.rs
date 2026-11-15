// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded in-flight JSON-RPC `id` correlator preventing response spoofing or duplicate settlement
//! (`Astream.Mcp.TlaMcpIdCorrelator`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "mcp_id_correlator_island.rs"]
mod mcp_id_correlator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_inflight_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_next_id_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use mcp_id_correlator_island::{mcp_inflight_clamp, mcp_next_id_advance};

/// Maximum concurrent unresolved MCP tool invocations per server.
pub const MAX_MCP_INFLIGHT: u64 = 128;

contract_fn! {
    /// Verified settlement check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mcp_id_settled_isl`.
    #[must_use]
    pub const fn mcp_id_settled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Tracks pending `(request_id -> tool_name)` calls and rejects unsolicited or duplicate replies.
#[derive(Debug, Clone, Default)]
pub struct McpRequestCorrelator {
    next_id: u64,
    pending: BTreeMap<u64, String>,
}

impl McpRequestCorrelator {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_id: 1,
            pending: BTreeMap::new(),
        }
    }

    pub fn issue_request(&mut self, tool_name: &str) -> Result<u64, &'static str> {
        if tool_name.trim().is_empty() {
            return Err("empty MCP tool name");
        }
        let cap = mcp_inflight_clamp(MAX_MCP_INFLIGHT, MAX_MCP_INFLIGHT) as usize;
        if self.pending.len() >= cap {
            return Err("MCP in-flight request window full");
        }
        let id = self.next_id;
        let Some(cand) = id.checked_add(1) else {
            return Err("MCP request id space exhausted");
        };
        self.next_id = mcp_next_id_advance(self.next_id, cand);
        let mut owned = String::new();
        owned.push_str(tool_name);
        self.pending.insert(id, owned);
        Ok(id)
    }

    pub fn settle_response(&mut self, id: u64) -> Result<String, &'static str> {
        if id == 0 {
            return Err("zero MCP request id invalid");
        }
        let Some(req_bound) = id.checked_add(1) else {
            return Err("invalid MCP request id");
        };
        if !mcp_id_settled(self.next_id, req_bound) {
            return Err("future request id never issued");
        }
        match self.pending.remove(&id) {
            Some(tool) => Ok(tool),
            None => Err("unknown or duplicate MCP response id"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correlator_settles_exact_once_and_rejects_spoofed_or_replayed_ids() {
        let mut c = McpRequestCorrelator::new();
        let id = c.issue_request("search_docs").unwrap();
        assert!(c.settle_response(999).is_err());
        assert_eq!(c.settle_response(id).unwrap(), "search_docs");
        assert!(c.settle_response(id).is_err());
    }
}
