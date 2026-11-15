// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Exact 13-prefix agent environment sanitizer for spawned shells
//! (`Astream.Host.TlaEnvPrefixStripper`).
//!
//! Enforces `aterm`'s shell-isolation rule: strips `CLAUDE*`, `ANTHROPIC_*`,
//! `COPILOT_*`, `CODEX_*`, `ANTIGRAVITY_*`, `GEMINI_*`, `CURSOR_*`, `GROK_*`,
//! `XAI_*`, `KIMI_*`, `MOONSHOT_*`, `AI_*`, and `_DEVTOOL_*` environment variables
//! when spawning fresh shells so nested agents never inherit stale session tokens
//! or recursion sentinels.

#[cfg(clean_islands)]
#[path = "env_prefix_stripper_island.rs"]
mod env_prefix_stripper_island;
#[cfg(clean_islands)]
pub use env_prefix_stripper_island::{env_spawn_epoch_advance, env_stripped_clamp};

/// Default maximum environment variables passed through to a spawned shell.
pub const DEFAULT_MAX_SPAWN_ENV_VARS: u64 = 1_024;

/// Exact 13 vendor prefixes stripped by `aterm` on shell spawn (`CLAUDE` matches `CLAUDE*`).
pub const STRIPPED_ENV_PREFIXES: [&[u8]; 13] = [
    b"CLAUDE",
    b"ANTHROPIC_",
    b"COPILOT_",
    b"CODEX_",
    b"ANTIGRAVITY_",
    b"GEMINI_",
    b"CURSOR_",
    b"GROK_",
    b"XAI_",
    b"KIMI_",
    b"MOONSHOT_",
    b"AI_",
    b"_DEVTOOL_",
];

#[cfg(not(clean_islands))]
/// Monotonically advance the shell-environment sanitization epoch.
#[must_use]
pub const fn env_spawn_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp stripped environment variable count to `max_vars`.
#[must_use]
pub const fn env_stripped_clamp(cand_stripped: u64, max_vars: u64) -> u64 {
    if cand_stripped < max_vars {
        cand_stripped
    } else {
        max_vars
    }
}

contract_fn! {
    /// True iff `retained_vars <= max_vars`.
    #[must_use]
    pub const fn env_retained_within_cap(retained_vars: u64, max_vars: u64) -> bool
    clauses [ensures result == (retained_vars <= max_vars)]
    {
        retained_vars <= max_vars
    }
}

/// True iff `key` matches any of `aterm`'s 13 stripped agent/vendor prefixes.
#[must_use]
pub fn should_strip_env_key(key: &[u8]) -> bool {
    let mut rest = STRIPPED_ENV_PREFIXES.as_slice();
    while let &[prefix, ref tail @ ..] = rest {
        if key.starts_with(prefix) {
            return true;
        }
        rest = tail;
    }
    false
}

/// Summary of filtering an environment block for a spawned child shell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FilteredEnvIndices {
    pub retained_indices: Vec<usize>,
    pub stripped_count: u64,
    pub spawn_epoch: u64,
}

/// Stateful environment-sanitization gate for `astream-host` child spawns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnvPrefixStripper {
    spawn_epoch: u64,
    last_stripped: u64,
    max_vars: u64,
}

impl Default for EnvPrefixStripper {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_SPAWN_ENV_VARS)
    }
}

impl EnvPrefixStripper {
    #[must_use]
    pub const fn new(max_vars: u64) -> Self {
        let cap = if max_vars == 0 {
            DEFAULT_MAX_SPAWN_ENV_VARS
        } else {
            max_vars
        };
        Self {
            spawn_epoch: 0,
            last_stripped: 0,
            max_vars: cap,
        }
    }

    #[must_use]
    pub const fn spawn_epoch(&self) -> u64 {
        self.spawn_epoch
    }

    #[must_use]
    pub const fn last_stripped(&self) -> u64 {
        self.last_stripped
    }

    /// Filter `env_keys`, returning the indices of safe non-vendor keys up to `max_vars`.
    pub fn filter_keys(&mut self, env_keys: &[&[u8]]) -> FilteredEnvIndices {
        let cand_ep = self.spawn_epoch.saturating_add(1);
        self.spawn_epoch = env_spawn_epoch_advance(self.spawn_epoch, cand_ep);

        let mut retained: Vec<usize> = Vec::new();
        let mut stripped = 0u64;
        let mut idx = 0usize;
        let mut rest = env_keys;
        while let &[key, ref tail @ ..] = rest {
            if should_strip_env_key(key) {
                stripped = stripped.saturating_add(1);
            } else {
                let next_ret = (retained.len() as u64).saturating_add(1);
                if env_retained_within_cap(next_ret, self.max_vars) {
                    retained.push(idx);
                }
            }
            idx = idx.saturating_add(1);
            rest = tail;
        }

        self.last_stripped = env_stripped_clamp(stripped, self.max_vars);
        FilteredEnvIndices {
            retained_indices: retained,
            stripped_count: self.last_stripped,
            spawn_epoch: self.spawn_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_all_thirteen_vendor_prefixes_and_preserves_aterm_and_path() {
        let mut stripper = EnvPrefixStripper::new(64);
        let keys: &[&[u8]] = &[
            b"PATH",
            b"ATERM_SESSION_ID",
            b"CLAUDECODE",
            b"CLAUDE_API_KEY",
            b"ANTHROPIC_API_KEY",
            b"COPILOT_TOKEN",
            b"CODEX_HOME",
            b"ANTIGRAVITY_CLI",
            b"GEMINI_API_KEY",
            b"CURSOR_TRACE_ID",
            b"GROK_KEY",
            b"XAI_API_KEY",
            b"KIMI_TOKEN",
            b"MOONSHOT_KEY",
            b"AI_GATEWAY",
            b"_DEVTOOL_PORT",
            b"ATPKG_BIN",
        ];

        let out = stripper.filter_keys(keys);
        assert_eq!(out.retained_indices, vec![0, 1, 16]);
        assert_eq!(out.stripped_count, 14);
        assert_eq!(out.spawn_epoch, 1);
    }
}
