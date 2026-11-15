// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic SHA-256 `(server, tool, args)` replay tape for hermetic shadow MCP turns
//! (`Astream.Mcp.TlaMcpTapeDedup`).

use astream_digest::Sha256;
use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "mcp_tape_dedup_island.rs"]
mod mcp_tape_dedup_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_cache_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_hit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use mcp_tape_dedup_island::{mcp_cache_clamp, mcp_hit_advance};

/// Maximum taped MCP responses indexed per shadow session.
pub const MAX_MCP_TAPE_ENTRIES: u64 = 1_024;

contract_fn! {
    /// Verified hit predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mcp_tape_recorded_isl`.
    #[must_use]
    pub const fn mcp_tape_recorded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn call_digest(server: &str, tool: &str, args: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-MCP-TAPE-V1\0");
    h.update_slice(&(server.len() as u64).to_le_bytes());
    h.update_slice(server.as_bytes());
    h.update_slice(&(tool.len() as u64).to_le_bytes());
    h.update_slice(tool.as_bytes());
    h.update_slice(&(args.len() as u64).to_le_bytes());
    h.update_slice(args);
    h.finalize()
}

/// Keyed replay store answering recorded MCP calls without live network side effects.
#[derive(Debug, Clone, Default)]
pub struct McpShadowTape {
    hits: u64,
    entries: BTreeMap<[u8; 32], Vec<u8>>,
}

impl McpShadowTape {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            hits: 0,
            entries: BTreeMap::new(),
        }
    }

    pub fn record(&mut self, server: &str, tool: &str, args: &[u8], response: Vec<u8>) -> bool {
        if server.is_empty() || tool.is_empty() {
            return false;
        }
        let cap = mcp_cache_clamp(MAX_MCP_TAPE_ENTRIES, MAX_MCP_TAPE_ENTRIES) as usize;
        let key = call_digest(server, tool, args);
        if !self.entries.contains_key(&key) && self.entries.len() >= cap {
            return false;
        }
        self.entries.insert(key, response);
        true
    }

    pub fn replay(&mut self, server: &str, tool: &str, args: &[u8]) -> Option<&[u8]> {
        if server.is_empty() || tool.is_empty() {
            return None;
        }
        let key = call_digest(server, tool, args);
        if let Some(resp) = self.entries.get(&key) {
            self.hits = mcp_hit_advance(self.hits, self.hits.saturating_add(1));
            if mcp_tape_recorded(self.hits, 1) {
                return Some(resp.as_slice());
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mcp_shadow_tape_answers_exact_recorded_call_and_misses_altered_args() {
        let mut t = McpShadowTape::new();
        assert!(t.record("git-mcp", "diff", b"{\"rev\":\"HEAD\"}", b"ok".to_vec()));
        assert_eq!(
            t.replay("git-mcp", "diff", b"{\"rev\":\"HEAD\"}"),
            Some(b"ok".as_slice())
        );
        assert!(t.replay("git-mcp", "diff", b"{\"rev\":\"main\"}").is_none());
    }
}
