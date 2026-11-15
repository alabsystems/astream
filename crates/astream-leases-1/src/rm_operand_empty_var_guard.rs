// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `rm` operand unguarded `$VAR` fail-safe verifier
//! (`Astream.Agent.TlaRmOperandEmptyVarGuard`, Island #282).

#![allow(clippy::absurd_extreme_comparisons)]

#[cfg(clean_islands)]
#[path = "rm_operand_empty_var_guard_island.rs"]
mod rm_operand_empty_var_guard_island;
#[cfg(clean_islands)]
pub use rm_operand_empty_var_guard_island::{rm_operand_count_clamp, rm_unguarded_hits_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn rm_operand_count_clamp(operands: u64, max_operands: u64) -> u64 {
    if operands < max_operands {
        operands
    } else {
        max_operands
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn rm_unguarded_hits_advance(prev_hits: u64, next_hits: u64) -> u64 {
    if prev_hits < next_hits {
        next_hits
    } else {
        prev_hits
    }
}

/// Maximum `rm` operands inspected in one command (`256`).
pub const MAX_RM_OPERANDS: u64 = 256;

contract_fn! {
    /// Verified check `unguarded_count <= 0`, linked via `clean-kernel-defeq` to
    /// `rm_zero_unguarded_count_isl`.
    #[must_use]
    pub const fn rm_zero_unguarded_count(unguarded_count: u64) -> bool
    clauses [ensures result == (unguarded_count <= 0)]
    {
        unguarded_count <= 0
    }
}

/// Check `unguarded_count == 0 && operands_checked != 0`.
#[inline]
#[must_use]
pub const fn rm_operands_all_safe(unguarded_count: u64, operands_checked: u64) -> bool {
    rm_zero_unguarded_count(unguarded_count) && operands_checked != 0
}

#[inline]
const fn is_var_ident_char(b: u8) -> bool {
    (b >= b'a' && b <= b'z') || (b >= b'A' && b <= b'Z') || (b >= b'0' && b <= b'9') || b == b'_'
}

const fn is_quote_or_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C | b'"' | b'\'')
}

const fn trim_quotes_and_ws(mut s: &[u8]) -> &[u8] {
    while let [head, rest @ ..] = s {
        if is_quote_or_ws(*head) {
            s = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = s {
        if is_quote_or_ws(*last) {
            s = rest;
        } else {
            break;
        }
    }
    s
}

/// Inspect a single `rm` path operand for catastrophic roots or unguarded `$VAR` expansions.
#[must_use]
pub const fn is_safe_rm_operand(raw: &str) -> bool {
    let trimmed = trim_quotes_and_ws(raw.as_bytes());
    if matches!(trimmed, b"" | b"/" | b"/*" | b"." | b".." | b"~" | b"~/") {
        return false;
    }

    let mut cur = trimmed;
    while let [b, rest @ ..] = cur {
        if *b == b'$' {
            let Some((&open_br, inner_start)) = rest.split_first() else {
                return false;
            };
            if open_br != b'{' {
                // Bare `$VAR` or trailing `$` without `${VAR:?}` fail-safe guard!
                return false;
            }
            let mut inner = inner_start;
            let mut has_ident = false;
            while let [ch, next_inner @ ..] = inner {
                if is_var_ident_char(*ch) {
                    has_ident = true;
                    inner = next_inner;
                } else {
                    break;
                }
            }
            if !has_ident {
                return false;
            }
            let Some((&colon, after_colon)) = inner.split_first() else {
                return false;
            };
            let Some((&qmark, after_start)) = after_colon.split_first() else {
                return false;
            };
            if colon != b':' || qmark != b'?' {
                return false;
            }
            let mut after_op = after_start;
            let mut found_close = false;
            while let [ch, tail @ ..] = after_op {
                after_op = tail;
                if *ch == b'}' {
                    found_close = true;
                    break;
                }
            }
            if !found_close {
                return false;
            }
            cur = after_op;
            continue;
        }
        cur = rest;
    }
    true
}

/// Verdict returned by [`check_rm_operands`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RmGuardVerdict {
    /// Every non-flag operand is safe (no root wildcard and every `$VAR` uses `${VAR:?}`).
    Safe { operands_checked: u64 },
    /// Command had zero path operands or contained `unguarded_count` unsafe operands.
    Refused {
        unguarded_count: u64,
        operands_checked: u64,
    },
}

/// Evaluate the arguments of an `rm` invocation (after the `rm` token itself).
#[must_use]
pub fn check_rm_operands(args: &[&str]) -> RmGuardVerdict {
    let mut after_double_dash = false;
    let mut checked = 0u64;
    let mut unguarded = 0u64;
    let mut rest = args;
    while let [tok, tail @ ..] = rest {
        rest = tail;
        let tb = tok.as_bytes();
        if !after_double_dash && matches!(tb, b"--") {
            after_double_dash = true;
            continue;
        }
        if !after_double_dash && matches!(tb, [b'-', _, ..]) {
            continue;
        }
        checked = rm_operand_count_clamp(checked.saturating_add(1), MAX_RM_OPERANDS);
        if !is_safe_rm_operand(tok) {
            unguarded = rm_unguarded_hits_advance(unguarded, unguarded.saturating_add(1));
        }
    }
    if rm_operands_all_safe(unguarded, checked) {
        RmGuardVerdict::Safe {
            operands_checked: checked,
        }
    } else {
        RmGuardVerdict::Refused {
            unguarded_count: unguarded,
            operands_checked: checked,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_unguarded_dollar_var_and_accepts_colon_question_failsafe() {
        assert_eq!(
            check_rm_operands(&["-rf", "\"$OUT/astream-broker\""]),
            RmGuardVerdict::Refused {
                unguarded_count: 1,
                operands_checked: 1,
            }
        );
        assert_eq!(
            check_rm_operands(&["-rf", "\"${OUT}/astream-broker\""]),
            RmGuardVerdict::Refused {
                unguarded_count: 1,
                operands_checked: 1,
            }
        );
        assert_eq!(
            check_rm_operands(&["-rf", "/"]),
            RmGuardVerdict::Refused {
                unguarded_count: 1,
                operands_checked: 1,
            }
        );

        assert_eq!(
            check_rm_operands(&[
                "-rf",
                "\"${OUT:?}/astream-broker\"",
                "target/trust-ready/tmp"
            ]),
            RmGuardVerdict::Safe {
                operands_checked: 2,
            }
        );
    }
}
