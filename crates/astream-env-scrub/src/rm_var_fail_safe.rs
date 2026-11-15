// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-safe `${VAR:?}` `rm` operand guard (`aterm` primer: an unguarded `$VAR/…` in an `rm`
//! operand can expand to `/` if unset under automated Yes approval; `"${VAR:?}/…"` fails safe;
//! `Astream.EnvScrub.TlaRmVarFailSafe`).

#[cfg(clean_islands)]
#[path = "rm_var_fail_safe_island.rs"]
mod rm_var_fail_safe_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rm_tokens_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rm_checked_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use rm_var_fail_safe_island::{rm_checked_advance, rm_tokens_clamp};

/// Maximum shell words audited per `rm` command line.
pub const MAX_RM_OPERAND_TOKENS: u64 = 128;

contract_fn! {
    /// Verified guard completeness (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `rm_all_guarded_isl`.
    #[must_use]
    pub const fn rm_all_guarded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn operand_has_unguarded_dollar_var(tok: &str) -> bool {
    let bytes = tok.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        let Some(&b) = bytes.get(i) else {
            break;
        };
        if b == b'`' {
            return true;
        }
        if b == b'$' {
            match bytes.get(i.saturating_add(1)) {
                Some(&b'{') => {
                    // Require non-empty var name followed by `:?` before closing `}`
                    let start = i.saturating_add(2);
                    let mut scan = start;
                    let mut close_idx: Option<usize> = None;
                    let mut colon_q_ok = false;
                    while scan < bytes.len() {
                        let Some(&ch) = bytes.get(scan) else {
                            break;
                        };
                        if ch == b'$' || ch == b'`' {
                            return true;
                        }
                        if ch == b'}' {
                            close_idx = Some(scan);
                            break;
                        }
                        if ch == b':'
                            && scan > start
                            && bytes.get(scan.saturating_add(1)) == Some(&b'?')
                        {
                            colon_q_ok = true;
                        }
                        scan = scan.saturating_add(1);
                    }
                    let Some(close) = close_idx else {
                        return true;
                    };
                    if !colon_q_ok {
                        return true;
                    }
                    i = close.saturating_add(1);
                    continue;
                }
                Some(&b'(') => return true,
                Some(&c)
                    if c.is_ascii_alphanumeric()
                        || c == b'_'
                        || c == b'@'
                        || c == b'*'
                        || c == b'?'
                        || c == b'!'
                        || c == b'#'
                        || c == b'-' =>
                {
                    return true;
                }
                _ => {}
            }
        }
        i = i.saturating_add(1);
    }
    false
}

/// Rejects `rm` invocations whose path operands contain bare `$VAR` or `${VAR}` without `:?`.
#[derive(Debug, Clone, Default)]
pub struct RmOperandSafetyGuard {
    commands_checked: u64,
}

impl RmOperandSafetyGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            commands_checked: 0,
        }
    }

    pub fn validate_rm_words(&mut self, words: &[&str]) -> Result<(), &'static str> {
        let max_toks = rm_tokens_clamp(MAX_RM_OPERAND_TOKENS, MAX_RM_OPERAND_TOKENS) as usize;
        if words.len() > max_toks {
            return Err("rm word count exceeds MAX_RM_OPERAND_TOKENS");
        }
        let lim = rm_tokens_clamp(words.len() as u64, MAX_RM_OPERAND_TOKENS) as usize;
        self.commands_checked = rm_checked_advance(
            self.commands_checked,
            self.commands_checked.saturating_add(1),
        );
        let mut unguarded = 0u64;
        let mut opts_ended = false;
        let mut idx = 1usize;
        while idx < lim {
            let Some(&w) = words.get(idx) else {
                break;
            };
            if !opts_ended {
                if w == "--" {
                    opts_ended = true;
                    idx = idx.saturating_add(1);
                    continue;
                }
                if w.starts_with('-') && w != "-" {
                    idx = idx.saturating_add(1);
                    continue;
                }
            }
            if operand_has_unguarded_dollar_var(w) {
                unguarded = unguarded.saturating_add(1);
            }
            idx = idx.saturating_add(1);
        }
        if !rm_all_guarded(0, unguarded) {
            return Err("unguarded $VAR in rm operand refused; use \"${VAR:?}/...\" to fail safe");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rm_guard_refuses_bare_var_and_accepts_colon_question_fail_safe_expansion() {
        let mut g = RmOperandSafetyGuard::new();
        assert!(g.validate_rm_words(&["rm", "-rf", "$TMP_DIR/out"]).is_err());
        assert!(g
            .validate_rm_words(&["rm", "-rf", "${TMP_DIR}/out"])
            .is_err());
        assert!(g
            .validate_rm_words(&["rm", "-rf", "${TMP_DIR:?}/out"])
            .is_ok());
    }
}
