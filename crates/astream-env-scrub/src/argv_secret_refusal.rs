// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Process `argv` secret-leak refusal blocking inline `--token=sk-...`, `Authorization: Bearer`,
//! or `api_key=` credentials that would become world-visible via `ps` / `aterm ctl survey`
//! (`Astream.EnvScrub.TlaArgvSecretRefusal`).

#[cfg(clean_islands)]
#[path = "argv_secret_refusal_island.rs"]
mod argv_secret_refusal_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn argv_count_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn argv_audit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use argv_secret_refusal_island::{argv_audit_advance, argv_count_clamp};

/// Maximum `argv` elements scanned per process launch.
pub const MAX_SCANNED_ARGV: u64 = 512;

contract_fn! {
    /// Verified zero-inline-secret check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `argv_no_inline_secret_isl`.
    #[must_use]
    pub const fn argv_no_inline_secret(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn starts_with_ignore_ascii_case(haystack: &[u8], needle: &[u8]) -> bool {
    let Some(prefix) = haystack.get(..needle.len()) else {
        return false;
    };
    prefix.eq_ignore_ascii_case(needle)
}

fn contains_ignore_ascii_case(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    let mut i = 0usize;
    while i.saturating_add(needle.len()) <= haystack.len() {
        if let Some(sub) = haystack.get(i..i.saturating_add(needle.len())) {
            if sub.eq_ignore_ascii_case(needle) {
                return true;
            }
        }
        i = i.saturating_add(1);
    }
    false
}

fn looks_like_inline_secret(arg: &str) -> bool {
    let b = arg.as_bytes();
    contains_ignore_ascii_case(b, b"authorization: bearer ")
        || starts_with_ignore_ascii_case(b, b"--api-key=")
        || starts_with_ignore_ascii_case(b, b"--token=")
        || starts_with_ignore_ascii_case(b, b"api_key=")
        || contains_ignore_ascii_case(b, b"sk-ant-")
        || contains_ignore_ascii_case(b, b"ghp_")
}

/// Audits `argv` slices before `execve` so secrets pass via fd/stdin rather than `ps`.
#[derive(Debug, Clone, Default)]
pub struct ArgvSecretAuditor {
    audited: u64,
}

impl ArgvSecretAuditor {
    #[must_use]
    pub const fn new() -> Self {
        Self { audited: 0 }
    }

    pub fn check_argv(&mut self, argv: &[&str]) -> Result<(), &'static str> {
        let max_args = argv_count_clamp(MAX_SCANNED_ARGV, MAX_SCANNED_ARGV) as usize;
        if argv.len() > max_args {
            return Err("argv length exceeds MAX_SCANNED_ARGV");
        }
        let lim = argv_count_clamp(argv.len() as u64, MAX_SCANNED_ARGV) as usize;
        self.audited = argv_audit_advance(self.audited, self.audited.saturating_add(1));
        let mut leaks = 0u64;
        let mut idx = 0usize;
        while idx < lim {
            let Some(&a) = argv.get(idx) else {
                break;
            };
            if looks_like_inline_secret(a) {
                leaks = leaks.saturating_add(1);
            }
            idx = idx.saturating_add(1);
        }
        if !argv_no_inline_secret(0, leaks) {
            return Err("inline credential in process argv refused; pass secret via stdin or fd");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn argv_auditor_blocks_bearer_and_api_key_flags_while_passing_stdin_flag() {
        let mut a = ArgvSecretAuditor::new();
        assert!(a
            .check_argv(&["curl", "-H", "Authorization: Bearer secret123"])
            .is_err());
        assert!(a
            .check_argv(&["gh", "auth", "login", "--with-token"])
            .is_ok());
    }
}
