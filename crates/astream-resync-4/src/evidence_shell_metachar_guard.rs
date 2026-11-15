// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence claim exit-masking shell-operator refusal & per-claim timeout classifier
//! (`docs/AUDIT-2026-09.md` lines 36, 51, 90; `Astream.Evidence.TlaEvidenceShellMetacharGuard`).
//!
//! Enforces the falsifiability rule from `AUDIT-2026-09.md` line 36:
//! - A claim command containing shell exit-masking or chaining operators (`||`, `&&`, `;`, `|`,
//!   `&`, leading `!`, command substitution, or shell interpreter flags `-c`) MUST be refused by
//!   both `gate` and `run` so a failing command (`... || true`) can never silently pass,
//! - Tracks monotone elapsed execution time against an optional per-claim timeout budget (`ms`).

#[cfg(clean_islands)]
#[path = "evidence_shell_metachar_guard_island.rs"]
mod evidence_shell_metachar_guard_island;
#[cfg(clean_islands)]
pub use evidence_shell_metachar_guard_island::{claim_argc_clamp_b140, claim_elapsed_advance_b140};

/// Upper bound on tokenized claim argument count (`256`).
pub const MAX_CLAIM_ARGC: u64 = 256;

#[cfg(not(clean_islands))]
/// Clamp tokenized claim argument count to `max_argc`.
#[must_use]
pub const fn claim_argc_clamp_b140(cand_argc: u64, max_argc: u64) -> u64 {
    if cand_argc < max_argc {
        cand_argc
    } else {
        max_argc
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance observed per-claim elapsed wall time (`ms`).
#[must_use]
pub const fn claim_elapsed_advance_b140(cur_ms: u64, cand_ms: u64) -> u64 {
    if cur_ms < cand_ms {
        cand_ms
    } else {
        cur_ms
    }
}

contract_fn! {
    /// True iff the claim command is non-empty and contains neither a shell chaining/masking
    /// operator (`||`, `&&`, `;`, `|`, `&`, subshell) nor a leading `!` exit-code negation.
    #[must_use]
    pub const fn claim_command_unmasked_b140(
        argc: u64,
        has_shell_operator: bool,
        leading_bang: bool,
    ) -> bool
    clauses [ensures result == (argc > 0 && !has_shell_operator && !leading_bang)]
    {
        argc > 0 && !has_shell_operator && !leading_bang
    }
}

/// Gate verdict for a manifest claim command string and its execution budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimGuardVerdict {
    AdmittedDirectExec { bounded_argc: u64 },
    RefusedEmptyCommand,
    RefusedLeadingBangInversion,
    RefusedShellMaskingOperator,
    ClaimTimedOut { elapsed_ms: u64, budget_ms: u64 },
}

/// Inspect pre-extracted command metadata and per-claim execution timing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimExecutionGuard {
    bounded_argc: u64,
    elapsed_ms: u64,
    timeout_budget_ms: u64,
}

impl ClaimExecutionGuard {
    #[must_use]
    pub const fn new(raw_argc: u64, timeout_budget_ms: u64) -> Self {
        Self {
            bounded_argc: claim_argc_clamp_b140(raw_argc, MAX_CLAIM_ARGC),
            elapsed_ms: 0,
            timeout_budget_ms,
        }
    }

    #[must_use]
    pub const fn check_syntax(
        &self,
        has_shell_operator: bool,
        leading_bang: bool,
    ) -> ClaimGuardVerdict {
        if self.bounded_argc == 0 {
            return ClaimGuardVerdict::RefusedEmptyCommand;
        }
        if leading_bang {
            return ClaimGuardVerdict::RefusedLeadingBangInversion;
        }
        if !claim_command_unmasked_b140(self.bounded_argc, has_shell_operator, false) {
            return ClaimGuardVerdict::RefusedShellMaskingOperator;
        }
        ClaimGuardVerdict::AdmittedDirectExec {
            bounded_argc: claim_argc_clamp_b140(self.bounded_argc, MAX_CLAIM_ARGC),
        }
    }

    pub fn poll_elapsed(&mut self, cand_elapsed_ms: u64) -> ClaimGuardVerdict {
        self.elapsed_ms = claim_elapsed_advance_b140(self.elapsed_ms, cand_elapsed_ms);
        if self.timeout_budget_ms > 0 && self.elapsed_ms >= self.timeout_budget_ms {
            ClaimGuardVerdict::ClaimTimedOut {
                elapsed_ms: self.elapsed_ms,
                budget_ms: self.timeout_budget_ms,
            }
        } else {
            ClaimGuardVerdict::AdmittedDirectExec {
                bounded_argc: claim_argc_clamp_b140(self.bounded_argc, MAX_CLAIM_ARGC),
            }
        }
    }
}

/// Pure non-loop classifier for a single claim token (`||`, `&&`, `|`, `;`, `&`, `!`).
#[must_use]
pub const fn is_shell_control_token(tok: &[u8]) -> bool {
    matches!(tok, b"||" | b"&&" | b"|" | b";" | b"&" | b"|&")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_exit_masking_operators_and_leading_bang_and_enforces_timeout() {
        assert!(is_shell_control_token(b"||"));
        assert!(is_shell_control_token(b";"));
        assert!(!is_shell_control_token(b"--locked"));

        let g = ClaimExecutionGuard::new(5, 30_000);
        assert_eq!(
            g.check_syntax(true, false),
            ClaimGuardVerdict::RefusedShellMaskingOperator
        );
        assert_eq!(
            g.check_syntax(false, true),
            ClaimGuardVerdict::RefusedLeadingBangInversion
        );
        assert_eq!(
            g.check_syntax(false, false),
            ClaimGuardVerdict::AdmittedDirectExec { bounded_argc: 5 }
        );

        let mut timed = ClaimExecutionGuard::new(3, 10_000);
        assert_eq!(
            timed.poll_elapsed(9_999),
            ClaimGuardVerdict::AdmittedDirectExec { bounded_argc: 3 }
        );
        assert_eq!(
            timed.poll_elapsed(10_000),
            ClaimGuardVerdict::ClaimTimedOut {
                elapsed_ms: 10_000,
                budget_ms: 10_000
            }
        );
    }
}
