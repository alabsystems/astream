// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-safe `${VAR:?}` parameter-expansion guard for `rm` operands
//! (`Astream.Host.TlaClaudeRmVarGuard`).
//!
//! Enforces the `aterm` Claude Code / Autopilot `rm` safety rule:
//! in Claude Code under `aterm`, Autopilot answers `Yes` to the confirmation dialog that an
//! unguarded `$VAR` in an `rm` operand raises; if `$VAR` is empty or unset, `"$VAR/foo"`
//! expands to `"/foo"` and `"$VAR/*"` expands to `"/*"`. Writing `"${VAR:?}/…"` fails closed
//! inside zsh/bash BEFORE `rm` executes (`unguarded_permitted == 0`).

#![allow(
    clippy::match_ref_pats,
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "claude_rm_var_guard_island.rs"]
mod claude_rm_var_guard_island;
#[cfg(clean_islands)]
pub use claude_rm_var_guard_island::{rm_intercept_clamp, rm_zero_unguarded};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn rm_intercept_clamp(intercepted: u64, scanned: u64) -> u64 {
    if intercepted < scanned {
        intercepted
    } else {
        scanned
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn rm_zero_unguarded(_flag: u64) -> u64 {
    0
}

contract_fn! {
    /// Verified check that at least one unguarded `$VAR` `rm` operand was found
    /// (`0 < unguarded_count`), linked via `clean-kernel-defeq` to
    /// `rm_has_unguarded_operands_isl`.
    #[must_use]
    pub const fn rm_has_unguarded_operands(unguarded_count: u64) -> bool
    clauses [ensures result == (0 < unguarded_count)]
    {
        0 < unguarded_count
    }
}

/// Verdict returned when inspecting a shell `rm` argv slice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RmOperandVerdict {
    /// Command is either not `rm` or all variable-expanded operands use `${VAR:?}` / `${VAR?}`.
    SafeToRun,
    /// Refused because one or more `rm` operands contain an unguarded `$VAR` / `${VAR}`
    /// or target `/` directly.
    RefuseUnsafeRmOperand {
        /// First unsafe operand detected.
        offending_operand: String,
        /// Suggested `${VAR:?}` fail-safe rewrite hint.
        remediation: &'static str,
    },
}

/// Stateful `rm` operand static guard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClaudeRmVarGuard {
    unguarded_permitted: u64,
    intercepted_count: u64,
    scanned_commands: u64,
}

impl Default for ClaudeRmVarGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl ClaudeRmVarGuard {
    /// Create a fresh `rm` operand guard.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            unguarded_permitted: 0,
            intercepted_count: 0,
            scanned_commands: 0,
        }
    }

    /// Count of unguarded `$VAR` `rm` commands permitted (invariant: always `0`).
    #[must_use]
    pub const fn unguarded_permitted(&self) -> u64 {
        self.unguarded_permitted
    }

    /// Clamped count of intercepted unsafe `rm` invocations (`<= scanned_commands`).
    #[must_use]
    pub const fn intercepted_count(&self) -> u64 {
        self.intercepted_count
    }

    /// Total shell invocations inspected.
    #[must_use]
    pub const fn scanned_commands(&self) -> u64 {
        self.scanned_commands
    }

    /// Check whether a single `rm` path operand is safe (`true`) or contains an unguarded
    /// `$VAR` / `${VAR}` / root `/` (`false`).
    #[must_use]
    pub fn operand_is_fail_safe(operand: &str) -> bool {
        let trimmed = operand.trim_matches('"').trim_matches('\'');
        if trimmed.is_empty() || trimmed == "/" || trimmed == "/*" {
            return false;
        }
        let mut rest = operand.as_bytes();
        while let &[b, ref tail @ ..] = rest {
            if b == b'$' {
                match tail {
                    &[b'{', ref after_open @ ..] => {
                        let &[first_inner, ref inner_tail @ ..] = after_open else {
                            return false;
                        };
                        if first_inner == b'}' || first_inner == b':' || first_inner == b'?' {
                            return false;
                        }
                        let mut saw_qmark = false;
                        let mut found_close: Option<&[u8]> = None;
                        let mut scan = inner_tail;
                        while let &[ib, ref itail @ ..] = scan {
                            if ib == b'}' {
                                found_close = Some(itail);
                                break;
                            }
                            if ib == b'?' {
                                saw_qmark = true;
                            }
                            scan = itail;
                        }
                        let Some(after_close) = found_close else {
                            return false;
                        };
                        if !saw_qmark {
                            return false;
                        }
                        rest = after_close;
                        continue;
                    }
                    &[b'$', ref after_pid @ ..] => {
                        rest = after_pid;
                        continue;
                    }
                    _ => return false,
                }
            }
            rest = tail;
        }
        true
    }

    /// Inspect an argv token list (`tokens[0]` is the command name, e.g. `"rm"` or `"/bin/rm"`).
    pub fn inspect_argv(&mut self, tokens: &[&str]) -> RmOperandVerdict {
        let next_scanned = self.scanned_commands.saturating_add(1);
        let &[prog, ref arg_tokens @ ..] = tokens else {
            self.unguarded_permitted = rm_zero_unguarded(self.intercepted_count);
            self.intercepted_count = rm_intercept_clamp(self.intercepted_count, next_scanned);
            self.scanned_commands = next_scanned;
            return RmOperandVerdict::SafeToRun;
        };
        let base = match prog.rsplit_once('/') {
            Some((_, tail)) => tail,
            None => prog,
        };
        if base != "rm" && base != "grm" {
            self.unguarded_permitted = rm_zero_unguarded(self.intercepted_count);
            self.intercepted_count = rm_intercept_clamp(self.intercepted_count, next_scanned);
            self.scanned_commands = next_scanned;
            return RmOperandVerdict::SafeToRun;
        }

        let mut end_of_flags = false;
        let mut unguarded = 0u64;
        let mut first_bad: Option<&str> = None;
        let mut rest = arg_tokens;
        while let &[tok, ref tail @ ..] = rest {
            rest = tail;
            if !end_of_flags {
                if tok == "--" {
                    end_of_flags = true;
                    continue;
                }
                if tok.starts_with('-') && tok.len() > 1 && !contains_dollar(tok.as_bytes()) {
                    continue;
                }
            }
            if !Self::operand_is_fail_safe(tok) {
                unguarded = unguarded.saturating_add(1);
                if first_bad.is_none() {
                    first_bad = Some(tok);
                }
            }
        }

        if rm_has_unguarded_operands(unguarded) {
            let next_int = self.intercepted_count.saturating_add(1);
            self.unguarded_permitted = rm_zero_unguarded(next_int);
            self.intercepted_count = rm_intercept_clamp(next_int, next_scanned);
            self.scanned_commands = next_scanned;
            RmOperandVerdict::RefuseUnsafeRmOperand {
                offending_operand: match first_bad {
                    Some(s) => {
                        let mut out = String::new();
                        out.push_str(s);
                        out
                    }
                    None => String::new(),
                },
                remediation: "guard every variable in rm operands with \"${VAR:?}/...\" so unset/empty variables abort before rm runs",
            }
        } else {
            self.unguarded_permitted = rm_zero_unguarded(self.intercepted_count);
            self.intercepted_count = rm_intercept_clamp(self.intercepted_count, next_scanned);
            self.scanned_commands = next_scanned;
            RmOperandVerdict::SafeToRun
        }
    }
}

fn contains_dollar(bytes: &[u8]) -> bool {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b == b'$' {
            return true;
        }
        rest = tail;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_unguarded_dollar_var_and_accepts_colon_question_fail_safe_rm_operands() {
        let mut guard = ClaudeRmVarGuard::new();

        // Unguarded `$OUT/label` and `${OUT}/label` and `${OUT:-}/label` are all rejected!
        assert!(matches!(
            guard.inspect_argv(&["rm", "-rf", "$OUT/astream-term"]),
            RmOperandVerdict::RefuseUnsafeRmOperand { .. }
        ));
        assert!(matches!(
            guard.inspect_argv(&["/bin/rm", "-rf", "${OUT}/astream-term"]),
            RmOperandVerdict::RefuseUnsafeRmOperand { .. }
        ));
        assert!(matches!(
            guard.inspect_argv(&["rm", "-rf", "${OUT:-}/astream-term"]),
            RmOperandVerdict::RefuseUnsafeRmOperand { .. }
        ));
        assert!(matches!(
            guard.inspect_argv(&["rm", "-rf", "/*"]),
            RmOperandVerdict::RefuseUnsafeRmOperand { .. }
        ));

        // Fail-safe `"${OUT:?}/$label"`? Wait: `$label` inside is ALSO checked if unguarded —
        // `"${OUT:?}/${label:?}"` or `"${OUT:?}/astream-term"` passes cleanly!
        assert_eq!(
            guard.inspect_argv(&["rm", "-rf", "\"${OUT:?}/astream-term\""]),
            RmOperandVerdict::SafeToRun
        );
        assert_eq!(
            guard.inspect_argv(&["rm", "-rf", "\"${OUT:?}/${label:?}\""]),
            RmOperandVerdict::SafeToRun
        );
        assert_eq!(guard.unguarded_permitted(), 0);
        assert_eq!(guard.intercepted_count(), 4);
        assert_eq!(guard.scanned_commands(), 6);
    }
}
