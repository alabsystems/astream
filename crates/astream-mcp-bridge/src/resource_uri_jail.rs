// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Canonical `file://` URI sandbox rejecting `..` path traversal, `%2e%2e` encoded escapes,
//! NUL bytes, and out-of-workspace roots (`Astream.Mcp.TlaResourceUriJail`).

#[cfg(clean_islands)]
#[path = "resource_uri_jail_island.rs"]
mod resource_uri_jail_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_uri_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_checks_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use resource_uri_jail_island::{mcp_checks_advance, mcp_uri_clamp};

/// Maximum URI byte length accepted (`4096` bytes).
pub const MAX_RESOURCE_URI_LEN: u64 = 4_096;

contract_fn! {
    /// Verified depth safety (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mcp_uri_depth_safe_isl`.
    #[must_use]
    pub const fn mcp_uri_depth_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Workspace-rooted `file://` URI sandbox.
#[derive(Debug, Clone)]
pub struct ResourceUriJail {
    workspace_root: String,
    checks: u64,
}

fn strip_trailing_slashes(mut s: &str) -> &str {
    while let Some(rest) = s.strip_suffix('/') {
        s = rest;
    }
    s
}

impl ResourceUriJail {
    #[must_use]
    pub fn new(workspace_root: &str) -> Self {
        let trimmed = strip_trailing_slashes(workspace_root);
        let mut owned = String::new();
        owned.push_str(trimmed);
        Self {
            workspace_root: owned,
            checks: 0,
        }
    }

    pub fn resolve_jailed(&mut self, uri: &str) -> Result<String, &'static str> {
        if self.workspace_root.is_empty()
            || !self.workspace_root.starts_with('/')
            || self.workspace_root.contains('\0')
        {
            return Err("invalid workspace root");
        }
        let cap = mcp_uri_clamp(MAX_RESOURCE_URI_LEN, MAX_RESOURCE_URI_LEN) as usize;
        if uri.len() > cap || uri.contains('\0') || uri.contains('%') || uri.contains('\\') {
            return Err("oversized, NUL-bearing, backslash, or percent-encoded URI refused");
        }
        self.checks = mcp_checks_advance(self.checks, self.checks.saturating_add(1));
        let Some(path) = uri.strip_prefix("file://") else {
            return Err("only file:// scheme allowed");
        };
        for seg in path.split('/') {
            if seg == ".." || seg == "." {
                return Err("dot-segment traversal refused");
            }
        }
        let inside_root = if path == self.workspace_root.as_str() {
            true
        } else if let Some(rem) = path.strip_prefix(self.workspace_root.as_str()) {
            rem.starts_with('/')
        } else {
            false
        };
        if !inside_root {
            return Err("URI escapes jailed workspace root");
        }
        if !mcp_uri_depth_safe(path.len() as u64, self.workspace_root.len() as u64) {
            return Err("invalid path length");
        }
        let mut out = String::new();
        out.push_str(path);
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uri_jail_admits_clean_workspace_files_and_blocks_traversal_and_sibling_prefix() {
        let mut j = ResourceUriJail::new("/fixture-home/astream");
        assert_eq!(
            j.resolve_jailed("file:///fixture-home/astream/Cargo.toml")
                .unwrap(),
            "/fixture-home/astream/Cargo.toml"
        );
        assert!(j
            .resolve_jailed("file:///fixture-home/astream/../secret")
            .is_err());
        assert!(j
            .resolve_jailed("file:///fixture-home/astream-evil/x")
            .is_err());
    }
}
