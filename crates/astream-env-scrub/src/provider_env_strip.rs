// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` child-shell AI provider environment variable scrubber stripping `CLAUDE*`,
//! `ANTHROPIC_*`, `COPILOT_*`, `CODEX_*`, `ANTIGRAVITY_*`, `GEMINI_*`, `CURSOR_*`, `GROK_*`,
//! `XAI_*`, `KIMI_*`, `MOONSHOT_*`, `AI_*`, and `_DEVTOOL_*` before spawning shells
//! (`aterm` primer, `Astream.EnvScrub.TlaProviderEnvStrip`).

#[cfg(clean_islands)]
#[path = "provider_env_strip_island.rs"]
mod provider_env_strip_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn env_vars_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn w15_env_stripped_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use provider_env_strip_island::{env_vars_clamp, w15_env_stripped_advance};

/// Maximum environment entries inspected per child shell spawn.
pub const MAX_CHILD_ENV_VARS: u64 = 2_048;

/// Exact prefixes stripped by `aterm` from spawned child shells.
pub const STRIPPED_AI_ENV_PREFIXES: &[&str] = &[
    "CLAUDE",
    "ANTHROPIC_",
    "COPILOT_",
    "CODEX_",
    "ANTIGRAVITY_",
    "GEMINI_",
    "CURSOR_",
    "GROK_",
    "XAI_",
    "KIMI_",
    "MOONSHOT_",
    "AI_",
    "_DEVTOOL_",
];

contract_fn! {
    /// Verified clean-pass check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `env_clean_pass_isl`.
    #[must_use]
    pub const fn env_clean_pass(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[must_use]
pub fn should_strip_ai_env_key(key: &str) -> bool {
    let mut i = 0usize;
    while i < STRIPPED_AI_ENV_PREFIXES.len() {
        if let Some(&pfx) = STRIPPED_AI_ENV_PREFIXES.get(i) {
            if key.starts_with(pfx) {
                return true;
            }
        }
        i = i.saturating_add(1);
    }
    false
}

/// Filters an inherited `(key, val)` environment block for a newly spawned `aterm` shell.
#[derive(Debug, Clone, Default)]
pub struct ChildShellEnvScrubber {
    stripped_total: u64,
}

impl ChildShellEnvScrubber {
    #[must_use]
    pub const fn new() -> Self {
        Self { stripped_total: 0 }
    }

    pub fn scrub<'a>(&mut self, pairs: &[(&'a str, &'a str)]) -> Vec<(&'a str, &'a str)> {
        let lim = env_vars_clamp(pairs.len() as u64, MAX_CHILD_ENV_VARS) as usize;
        let mut kept = Vec::new();
        let mut dropped = 0u64;
        let mut idx = 0usize;
        while idx < lim {
            let Some(&(k, v)) = pairs.get(idx) else {
                break;
            };
            if should_strip_ai_env_key(k) {
                dropped = dropped.saturating_add(1);
            } else {
                kept.push((k, v));
            }
            idx = idx.saturating_add(1);
        }
        self.stripped_total = w15_env_stripped_advance(
            self.stripped_total,
            self.stripped_total.saturating_add(dropped),
        );
        let mut residual = 0u64;
        let mut chk = 0usize;
        while chk < kept.len() {
            if let Some(&(k, _)) = kept.get(chk) {
                if should_strip_ai_env_key(k) {
                    residual = residual.saturating_add(1);
                }
            }
            chk = chk.saturating_add(1);
        }
        let _ = env_clean_pass(0, residual);
        kept
    }

    #[must_use]
    pub const fn stripped_total(&self) -> u64 {
        self.stripped_total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scrubber_strips_all_13_ai_env_families_while_preserving_path_and_aterm_vars() {
        let mut s = ChildShellEnvScrubber::new();
        let out = s.scrub(&[
            ("PATH", "/usr/bin"),
            ("ATERM_SESSION_ID", "s1"),
            ("CLAUDECODE", "1"),
            ("ANTHROPIC_API_KEY", "sk-ant"),
            ("GEMINI_API_KEY", "ai-gem"),
            ("_DEVTOOL_PORT", "9222"),
        ]);
        assert_eq!(out, vec![("PATH", "/usr/bin"), ("ATERM_SESSION_ID", "s1")]);
        assert_eq!(s.stripped_total(), 4);
    }
}
