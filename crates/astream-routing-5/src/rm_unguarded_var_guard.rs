// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-safe `${VAR:?}` `rm` operand guard (`Astream.Agent.TlaRmUnguardedVarGuard`).
//!
//! Under `aterm` Autopilot in Claude Code, the harness answers `Yes` to confirmation
//! prompts raised by unguarded `$VAR` in an `rm` operand; if `$VAR` is empty,
//! `rm -rf "$VAR/..."` expands to `rm -rf "/..."`! Requiring `"${VAR:?}/..."`
//! aborts the shell before `rm` executes when `VAR` is unset or empty.

#![allow(clippy::manual_is_ascii_check, clippy::match_ref_pats)]

#[cfg(clean_islands)]
#[path = "rm_unguarded_var_guard_island.rs"]
mod rm_unguarded_var_guard_island;
#[cfg(clean_islands)]
pub use rm_unguarded_var_guard_island::{rm_audit_epoch_advance, rm_blocked_clamp};

/// Hard upper bound on counted blocked `rm` commands.
pub const MAX_TRACKED_RM_BLOCKS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Monotonically advance the shell `rm` audit epoch.
#[must_use]
pub const fn rm_audit_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp blocked command counter to `max_blocked`.
#[must_use]
pub const fn rm_blocked_clamp(cand_blocked: u64, max_blocked: u64) -> u64 {
    if cand_blocked < max_blocked {
        cand_blocked
    } else {
        max_blocked
    }
}

contract_fn! {
    /// True iff `unguarded_count == zero_expected` (`0`).
    #[must_use]
    pub const fn rm_zero_unguarded(unguarded_count: u64, zero_expected: u64) -> bool
    clauses [ensures result == (unguarded_count == zero_expected)]
    {
        unguarded_count == zero_expected
    }
}

const fn is_ident_start(b: u8) -> bool {
    matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'_')
}

const fn is_ident_cont(b: u8) -> bool {
    is_ident_start(b) || matches!(b, b'0'..=b'9')
}

/// Count unguarded `$VAR` or `${VAR}` expansions inside a single `rm` operand token.
/// `${VAR:?...}` is accepted as fail-safe; bare `$VAR` or `${VAR}` / `${VAR:-...}` is flagged.
#[must_use]
pub fn count_unguarded_vars_in_operand(token: &[u8]) -> u64 {
    let mut unguarded = 0u64;
    let mut in_single_quotes = false;
    let mut rest = token;

    while let &[b, ref tail @ ..] = rest {
        if b == b'\\' && !in_single_quotes {
            let &[_, ref after_esc @ ..] = tail else {
                break;
            };
            rest = after_esc;
            continue;
        }
        if b == b'\'' {
            in_single_quotes = !in_single_quotes;
            rest = tail;
            continue;
        }
        if !in_single_quotes && b == b'$' {
            match tail {
                &[b'{', ref brace_body @ ..] => {
                    // Expect IDENT followed immediately by ":?"
                    let mut scan = brace_body;
                    let mut saw_ident = false;
                    while let &[c, ref c_tail @ ..] = scan {
                        if (!saw_ident && is_ident_start(c)) || (saw_ident && is_ident_cont(c)) {
                            saw_ident = true;
                            scan = c_tail;
                        } else {
                            break;
                        }
                    }
                    let guarded = saw_ident && matches!(scan, [b':', b'?', ..]);
                    if !guarded {
                        unguarded = unguarded.saturating_add(1);
                    }
                }
                &[c, ..] if is_ident_start(c) || matches!(c, b'0'..=b'9' | b'@' | b'*') => {
                    unguarded = unguarded.saturating_add(1);
                }
                _ => {}
            }
        }
        rest = tail;
    }
    unguarded
}

/// Stateful pre-exec shell `rm` operand validator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RmUnguardedVarGuard {
    audit_epoch: u64,
    blocked_count: u64,
}

impl Default for RmUnguardedVarGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl RmUnguardedVarGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            audit_epoch: 0,
            blocked_count: 0,
        }
    }

    #[must_use]
    pub const fn audit_epoch(&self) -> u64 {
        self.audit_epoch
    }

    #[must_use]
    pub const fn blocked_count(&self) -> u64 {
        self.blocked_count
    }

    /// Audit tokenized `argv` of a shell command; returns `Err(unguarded_count)` if `argv[0] == "rm"`
    /// has any non-flag operand with an unguarded `$VAR` expansion.
    pub fn audit_rm_argv(&mut self, argv: &[&[u8]]) -> Result<(), u64> {
        let cand_ep = self.audit_epoch.saturating_add(1);
        self.audit_epoch = rm_audit_epoch_advance(self.audit_epoch, cand_ep);

        let &[prog, ref args @ ..] = argv else {
            return Ok(());
        };
        if prog != b"rm" && !prog.ends_with(b"/rm") {
            return Ok(());
        }

        let mut end_of_flags = false;
        let mut unguarded_total = 0u64;
        let mut rest = args;
        while let &[arg, ref tail @ ..] = rest {
            if !end_of_flags && arg == b"--" {
                end_of_flags = true;
                rest = tail;
                continue;
            }
            if !end_of_flags && arg.starts_with(b"-") && arg.len() > 1 {
                rest = tail;
                continue;
            }
            unguarded_total = unguarded_total.saturating_add(count_unguarded_vars_in_operand(arg));
            rest = tail;
        }

        if rm_zero_unguarded(unguarded_total, 0) {
            Ok(())
        } else {
            let cand_blk = self.blocked_count.saturating_add(1);
            self.blocked_count = rm_blocked_clamp(cand_blk, MAX_TRACKED_RM_BLOCKS);
            Err(unguarded_total)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_bare_dollar_var_in_rm_and_accepts_colon_question_guard() {
        let mut guard = RmUnguardedVarGuard::new();

        // Bare $OUT or ${OUT} in rm -rf is refused!
        assert_eq!(
            guard.audit_rm_argv(&[b"rm", b"-rf", b"$OUT/report"]),
            Err(1)
        );
        assert_eq!(
            guard.audit_rm_argv(&[b"rm", b"-rf", b"${OUT}/report"]),
            Err(1)
        );
        assert_eq!(guard.blocked_count(), 2);

        // Fail-safe "${OUT:?}/report" is accepted!
        assert_eq!(
            guard.audit_rm_argv(&[b"rm", b"-rf", b"${OUT:?}/report"]),
            Ok(())
        );
        // Non-rm commands are unaffected
        assert_eq!(guard.audit_rm_argv(&[b"echo", b"$OUT"]), Ok(()));
    }
}
