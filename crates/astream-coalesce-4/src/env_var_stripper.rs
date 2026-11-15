// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` Child-Shell AI Environment Variable Sanitizer.
//!
//! Enforces the exact `aterm` shell-spawn environment hygiene contract:
//! strips `CLAUDE*`, `ANTHROPIC_*`, `COPILOT_*`, `CODEX_*`, `ANTIGRAVITY_*`, `GEMINI_*`,
//! `CURSOR_*`, `GROK_*`, `XAI_*`, `KIMI_*`, `MOONSHOT_*`, `AI_*`, and `_DEVTOOL_*`
//! environment variables from spawned shells and PTY sessions so parent agent tokens,
//! internal IPC sockets, and recursive harness flags never leak into child shells.
//!
//! Backed by Clean TLA+ Island `Astream.Host.TlaAgentEnvSanitizer`
//! (`env_var_stripper_island.rs`), proving `retainedVars <= inputVars` and
//! `inputVars <= maxEnvCap`.

#[cfg(clean_islands)]
#[path = "env_var_stripper_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{env_input_clamp, env_retained_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn env_retained_clamp(retained: u64, input_vars: u64) -> u64 {
    if retained < input_vars {
        retained
    } else {
        input_vars
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn env_input_clamp(input_vars: u64, max_cap: u64) -> u64 {
    if input_vars < max_cap {
        input_vars
    } else {
        max_cap
    }
}

contract_fn! {
    /// Kernel-certified check that retained variable count never exceeds input variable count.
    #[must_use]
    #[inline]
    pub const fn env_retained_within_input(retained: u64, input_vars: u64) -> bool
    clauses [ensures result == (retained <= input_vars)]
    {
        retained <= input_vars
    }
}

/// Default maximum environment variables processed per PTY spawn (`4096`).
pub const DEFAULT_MAX_ENV_VARS: usize = 4096;

/// Underscore-suffixed agent prefixes stripped from spawned shells (`CLAUDE*` is checked
/// separately because `aterm` strips `CLAUDE*` with or without a trailing underscore, e.g.
/// `CLAUDECODE=1`).
const STRIPPED_UNDERSCORE_PREFIXES: [&[u8]; 12] = [
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

const fn has_byte_prefix(mut name: &[u8], mut prefix: &[u8]) -> bool {
    if name.len() < prefix.len() {
        return false;
    }
    while let &[pb, ref ptail @ ..] = prefix {
        let &[nb, ref ntail @ ..] = name else {
            return false;
        };
        if nb != pb {
            return false;
        }
        prefix = ptail;
        name = ntail;
    }
    true
}

/// Returns `true` if environment variable `key` matches any of the 13 `aterm` stripped
/// agent/harness prefixes (`CLAUDE*` plus the 12 `*_` prefixes).
#[must_use]
pub const fn should_strip_agent_env_key(key: &str) -> bool {
    let raw = key.as_bytes();
    if has_byte_prefix(raw, b"CLAUDE") {
        return true;
    }
    let mut rest: &[&[u8]] = &STRIPPED_UNDERSCORE_PREFIXES;
    while let &[pfx, ref tail @ ..] = rest {
        if has_byte_prefix(raw, pfx) {
            return true;
        }
        rest = tail;
    }
    false
}

/// Summary telemetry of a sanitized PTY environment pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SanitizeEnvSummary {
    pub input_vars: u64,
    pub retained_vars: u64,
    pub stripped_vars: u64,
    pub truncated_by_cap: bool,
}

/// Filters `(key, value)` environment pairs into `out` up to `max_env_cap`, stripping all
/// `aterm`-prohibited agent/harness variables while preserving `ATERM_*` and user variables.
pub fn sanitize_env_pairs<'a>(
    pairs: &[(&'a str, &'a str)],
    max_env_cap: usize,
    out: &mut Vec<(&'a str, &'a str)>,
) -> SanitizeEnvSummary {
    let cap_u64 = max_env_cap as u64;
    let bounded_in = env_input_clamp(pairs.len() as u64, cap_u64);
    let limit = bounded_in as usize;
    let truncated_by_cap = pairs.len() > limit;

    let mut raw_retained: u64 = 0;
    let mut raw_stripped: u64 = 0;
    let mut rest = match pairs.get(..limit) {
        Some(slice) => slice,
        None => pairs,
    };
    while let &[(k, v), ref tail @ ..] = rest {
        if should_strip_agent_env_key(k) {
            raw_stripped = raw_stripped.saturating_add(1);
        } else {
            out.push((k, v));
            raw_retained = raw_retained.saturating_add(1);
        }
        rest = tail;
    }

    let retained_vars = env_retained_clamp(raw_retained, bounded_in);
    SanitizeEnvSummary {
        input_vars: bounded_in,
        retained_vars,
        stripped_vars: raw_stripped,
        truncated_by_cap,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_all_thirteen_aterm_agent_prefixes_and_preserves_aterm_and_posix_vars() {
        let env_in = [
            ("PATH", "/usr/bin:/bin"),
            ("ATERM_SESSION_ID", "s-101"),
            ("TERM_PROGRAM", "aterm"),
            ("CLAUDECODE", "1"),
            ("CLAUDE_API_KEY", "sk-1"),
            ("ANTHROPIC_API_KEY", "sk-2"),
            ("COPILOT_TOKEN", "ghu_1"),
            ("CODEX_HOME", "/tmp/codex"),
            ("ANTIGRAVITY_CLI_SOCK", "/tmp/agy.sock"),
            ("GEMINI_API_KEY", "gm-1"),
            ("CURSOR_TRACE_ID", "cur-1"),
            ("GROK_API_KEY", "gr-1"),
            ("XAI_API_KEY", "xai-1"),
            ("KIMI_API_KEY", "km-1"),
            ("MOONSHOT_API_KEY", "ms-1"),
            ("AI_GATEWAY_KEY", "ai-1"),
            ("_DEVTOOL_IPC", "fd:9"),
            ("AIRPORT_CODE", "SFO"), // `AIRPORT_` does NOT start with `AI_`!
        ];

        let mut clean = Vec::new();
        let sum = sanitize_env_pairs(&env_in, DEFAULT_MAX_ENV_VARS, &mut clean);
        assert!(!sum.truncated_by_cap);
        assert_eq!(sum.input_vars, 18);
        assert_eq!(sum.stripped_vars, 14);
        assert_eq!(sum.retained_vars, 4);
        assert!(env_retained_within_input(sum.retained_vars, sum.input_vars));
        assert_eq!(
            clean,
            vec![
                ("PATH", "/usr/bin:/bin"),
                ("ATERM_SESSION_ID", "s-101"),
                ("TERM_PROGRAM", "aterm"),
                ("AIRPORT_CODE", "SFO"),
            ]
        );
    }
}
