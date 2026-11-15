// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-safe `"${VAR:?}/..."` shell `rm` operand validator (`Astream.Host.TlaShellRmVarExpansionFence`).
//!
//! Prevents catastrophic `rm -rf "$UNSET_VAR/..."` expansions under automated `aterm` harnesses:
//! requires any `$` variable expansion inside an `rm` operand to use `${NAME:?...}` non-empty
//! fail-safe parameter expansion.

#[cfg(clean_islands)]
#[path = "shell_rm_var_expansion_fence_island.rs"]
mod shell_rm_var_expansion_fence_island;
#[cfg(clean_islands)]
pub use shell_rm_var_expansion_fence_island::{
    rm_scan_epoch_advance_b111, rm_unguarded_clamp_b111,
};

#[cfg(not(clean_islands))]
/// Clamp rejected unguarded-`$VAR` `rm` command count to `max_rejected`.
#[must_use]
pub const fn rm_unguarded_clamp_b111(cand_rejected: u64, max_rejected: u64) -> u64 {
    if cand_rejected < max_rejected {
        cand_rejected
    } else {
        max_rejected
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the shell `rm` operand scan epoch.
#[must_use]
pub const fn rm_scan_epoch_advance_b111(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `rejected` remains strictly below `max_rejected`.
    #[must_use]
    pub const fn rm_reject_below_cap_b111(rejected: u64, max_rejected: u64) -> bool
    clauses [ensures result == (rejected < max_rejected)]
    {
        rejected < max_rejected
    }
}

/// Verdict of checking an `rm` operand byte slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RmOperandVerdict {
    SafeLiteralOrFailSafeVar {
        scan_epoch: u64,
    },
    RejectedUnguardedDollarVar {
        offset: usize,
        rejected_total: u64,
        scan_epoch: u64,
    },
}

fn has_guarded_colon_qmark(mut after_open_brace: &[u8]) -> bool {
    // Look for ":?" before matching '}'
    while let [b, rest @ ..] = after_open_brace {
        if *b == b'}' {
            return false;
        }
        if *b == b':' {
            if let [b'?', tail_start @ ..] = rest {
                let mut tail = tail_start;
                while let [c, c_tail @ ..] = tail {
                    if *c == b'}' {
                        return true;
                    }
                    tail = c_tail;
                }
                return false;
            }
        }
        after_open_brace = rest;
    }
    false
}

/// Validator requiring `${VAR:?}` fail-safe expansion on `rm` operands containing `$`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShellRmVarExpansionFence {
    rejected_total: u64,
    max_rejected_cap: u64,
    scan_epoch: u64,
}

impl ShellRmVarExpansionFence {
    #[must_use]
    pub const fn new(max_rejected_cap: u64) -> Self {
        let cap = if max_rejected_cap == 0 {
            1024
        } else {
            max_rejected_cap
        };
        Self {
            rejected_total: 0,
            max_rejected_cap: cap,
            scan_epoch: 0,
        }
    }

    #[must_use]
    pub const fn rejected_total(&self) -> u64 {
        self.rejected_total
    }

    /// Check a single `rm` path operand for unguarded `$VAR` or `${VAR}` expansions.
    pub fn check_rm_operand(&mut self, operand: &[u8]) -> RmOperandVerdict {
        let next_ep = self.scan_epoch.saturating_add(1);
        self.scan_epoch = rm_scan_epoch_advance_b111(self.scan_epoch, next_ep);

        let mut i = 0usize;
        let mut scan = operand;
        while let [b, tail @ ..] = scan {
            if *b == b'$' {
                let ok = if let [b'{', after_brace @ ..] = tail {
                    has_guarded_colon_qmark(after_brace)
                } else {
                    false
                };
                if !ok {
                    if rm_reject_below_cap_b111(self.rejected_total, self.max_rejected_cap) {
                        let cand = self.rejected_total.saturating_add(1);
                        self.rejected_total = rm_unguarded_clamp_b111(cand, self.max_rejected_cap);
                    }
                    return RmOperandVerdict::RejectedUnguardedDollarVar {
                        offset: i,
                        rejected_total: self.rejected_total,
                        scan_epoch: self.scan_epoch,
                    };
                }
            }
            scan = tail;
            i = i.saturating_add(1);
        }
        RmOperandVerdict::SafeLiteralOrFailSafeVar {
            scan_epoch: self.scan_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_bare_dollar_var_and_accepts_colon_qmark_guard() {
        let mut f = ShellRmVarExpansionFence::new(16);
        assert!(matches!(
            f.check_rm_operand(b"$OUT/report"),
            RmOperandVerdict::RejectedUnguardedDollarVar { offset: 0, .. }
        ));
        assert!(matches!(
            f.check_rm_operand(b"${OUT}/report"),
            RmOperandVerdict::RejectedUnguardedDollarVar { offset: 0, .. }
        ));
        assert_eq!(
            f.check_rm_operand(b"${OUT:?}/report"),
            RmOperandVerdict::SafeLiteralOrFailSafeVar { scan_epoch: 3 }
        );
    }
}
