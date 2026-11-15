// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` spawned-shell AI/devtool environment prefix scrubber
//! (`Astream.Host.TlaSpawnEnvStripFence`).
//!
//! Enforces `aterm`'s 13-prefix environment isolation policy when spawning child shells:
//! strips `CLAUDE*`, `ANTHROPIC_*`, `COPILOT_*`, `CODEX_*`, `ANTIGRAVITY_*`, `GEMINI_*`,
//! `CURSOR_*`, `GROK_*`, `XAI_*`, `KIMI_*`, `MOONSHOT_*`, `AI_*`, and `_DEVTOOL_*`.

#[cfg(clean_islands)]
#[path = "spawn_env_strip_fence_island.rs"]
mod spawn_env_strip_fence_island;
#[cfg(clean_islands)]
pub use spawn_env_strip_fence_island::{env_sanitize_epoch_advance_b112, stripped_env_clamp_b112};

#[cfg(not(clean_islands))]
/// Clamp stripped environment key count per spawn to `max_keys`.
#[must_use]
pub const fn stripped_env_clamp_b112(cand_stripped: u64, max_keys: u64) -> u64 {
    if cand_stripped < max_keys {
        cand_stripped
    } else {
        max_keys
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the environment-scrubbing pass epoch.
#[must_use]
pub const fn env_sanitize_epoch_advance_b112(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `stripped_count` remains strictly below `max_keys`.
    #[must_use]
    pub const fn env_strip_below_cap_b112(stripped_count: u64, max_keys: u64) -> bool
    clauses [ensures result == (stripped_count < max_keys)]
    {
        stripped_count < max_keys
    }
}

const STRIPPED_PREFIXES: [&[u8]; 13] = [
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

fn starts_with_bytes(mut haystack: &[u8], mut prefix: &[u8]) -> bool {
    while let [pb, p_tail @ ..] = prefix {
        let [hb, h_tail @ ..] = haystack else {
            return false;
        };
        if *hb != *pb {
            return false;
        }
        prefix = p_tail;
        haystack = h_tail;
    }
    prefix.is_empty()
}

/// True iff `env_key` matches one of `aterm`'s stripped agent/harness prefixes.
#[must_use]
pub fn should_strip_env_key(env_key: &[u8]) -> bool {
    let mut rest: &[&[u8]] = &STRIPPED_PREFIXES;
    while let [pref, tail @ ..] = rest {
        if starts_with_bytes(env_key, pref) {
            return true;
        }
        rest = tail;
    }
    false
}

/// Stateful scrubber accounting for child-shell environment sanitization passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpawnEnvStripFence {
    max_keys_cap: u64,
    stripped_in_pass: u64,
    sanitize_epoch: u64,
}

impl SpawnEnvStripFence {
    #[must_use]
    pub const fn new(max_keys_cap: u64) -> Self {
        let cap = if max_keys_cap == 0 {
            4096
        } else {
            max_keys_cap
        };
        Self {
            max_keys_cap: cap,
            stripped_in_pass: 0,
            sanitize_epoch: 0,
        }
    }

    #[must_use]
    pub const fn stripped_in_pass(&self) -> u64 {
        self.stripped_in_pass
    }

    #[must_use]
    pub const fn sanitize_epoch(&self) -> u64 {
        self.sanitize_epoch
    }

    pub fn begin_spawn_pass(&mut self) {
        let next_ep = self.sanitize_epoch.saturating_add(1);
        self.sanitize_epoch = env_sanitize_epoch_advance_b112(self.sanitize_epoch, next_ep);
        self.stripped_in_pass = 0;
    }

    /// Returns `true` iff `env_key` is permitted through to the child shell (`false` if stripped).
    pub fn filter_key(&mut self, env_key: &[u8]) -> bool {
        if should_strip_env_key(env_key) {
            if env_strip_below_cap_b112(self.stripped_in_pass, self.max_keys_cap) {
                let cand = self.stripped_in_pass.saturating_add(1);
                self.stripped_in_pass = stripped_env_clamp_b112(cand, self.max_keys_cap);
            }
            false
        } else {
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_all_agent_prefixes_while_preserving_normal_env_vars() {
        let mut f = SpawnEnvStripFence::new(64);
        f.begin_spawn_pass();
        assert!(!f.filter_key(b"CLAUDECODE"));
        assert!(!f.filter_key(b"ANTIGRAVITY_CLI_TOKEN"));
        assert!(!f.filter_key(b"GEMINI_API_KEY"));
        assert!(!f.filter_key(b"_DEVTOOL_SOCK"));
        assert!(f.filter_key(b"ATERM_SESSION_ID"));
        assert!(f.filter_key(b"PATH"));
        assert_eq!(f.stripped_in_pass(), 4);
    }
}
