// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WAN speculative-echo password/mode suppression fence & unconfirmed keystroke budget.
//!
//! Prevents Mosh-style client-side speculative echo (`Cell::FAINT` in `predict.rs`) from
//! leaking characters or painting false echoes when:
//! 1. The terminal enters `altscreen`, `bracketed_paste`, or `synchronized_output` (`?2026`).
//! 2. The cursor row displays an interactive secret prompt (`Password:`, `passphrase`,
//!    `[sudo]`, `PIN:`, `verification code`, `secret key`).
//! 3. Unconfirmed speculative keystrokes reach `max_unconfirmed` on a high-loss WAN link
//!    (`!echo_has_key_budget`).
//!
//! Zero closures (`0 mandated`), backed by Clean TLA+ island `Astream.Term.TlaMoshPasswordFence`.

#[cfg(clean_islands)]
#[path = "speculative_echo_fence_island.rs"]
mod speculative_echo_fence_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn echo_unconfirmed_clamp(proposed_keys: u64, max_keys: u64) -> u64 {
    if proposed_keys < max_keys {
        proposed_keys
    } else {
        max_keys
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn echo_epoch_advance(cur_epoch: u64, proposed_epoch: u64) -> u64 {
    if cur_epoch < proposed_epoch {
        proposed_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use speculative_echo_fence_island::{echo_epoch_advance, echo_unconfirmed_clamp};

contract_fn! {
    /// Kernel-certified check that `unconfirmed` speculative keystrokes remain strictly
    /// below `max_keys` (`unconfirmed < max_keys`), linked via `clean-kernel-defeq` to
    /// `echo_has_key_budget_isl`.
    #[must_use]
    pub const fn echo_has_key_budget(unconfirmed: u64, max_keys: u64) -> bool
    clauses [ensures result == (unconfirmed < max_keys)]
    {
        unconfirmed < max_keys
    }
}

/// Default cap on unconfirmed speculative keystrokes painted ahead of PTY echo (`32`).
pub const DEFAULT_MAX_UNCONFIRMED_KEYS: u64 = 32;

/// Reason local speculative keystroke echo was suppressed or allowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EchoAdmission {
    /// Keystroke admitted for speculative local echo at `epoch`.
    Allow { epoch: u64, unconfirmed_keys: u64 },
    /// Suppressed because `altscreen`, `bracketed_paste`, or `?2026` sync mode is active.
    SuppressedTerminalMode,
    /// Suppressed because the active prompt line looks like a no-echo password/PIN prompt.
    SuppressedSecretPrompt,
    /// Suppressed because `ch` is a non-printable control character (e.g. `\r`, `\n`, Ctrl-C).
    SuppressedControlChar,
    /// Suppressed because unconfirmed keystrokes reached `max_unconfirmed`.
    SuppressedBudgetFull,
}

const fn to_ascii_lower(b: u8) -> u8 {
    match b {
        b'A'..=b'Z' => b.saturating_add(32),
        _ => b,
    }
}

fn contains_ascii_case_insensitive(haystack: &[u8], needle_lower: &[u8]) -> bool {
    if needle_lower.is_empty() {
        return true;
    }
    let mut cur = haystack;
    while cur.len() >= needle_lower.len() {
        let mut hc = cur;
        let mut nc = needle_lower;
        let mut matched = true;
        while let (&[hb, ref hrest @ ..], &[nb, ref nrest @ ..]) = (hc, nc) {
            if to_ascii_lower(hb) != nb {
                matched = false;
                break;
            }
            hc = hrest;
            nc = nrest;
        }
        if matched {
            return true;
        }
        let &[_, ref rest @ ..] = cur else {
            break;
        };
        cur = rest;
    }
    false
}

/// Pure lexical detector for common POSIX / SSH / sudo / GPG / 2FA secret prompts.
#[must_use]
pub fn line_looks_like_secret_prompt(cursor_row_text: &str) -> bool {
    let trimmed = cursor_row_text.trim();
    if trimmed.is_empty() {
        return false;
    }
    let raw = trimmed.as_bytes();
    contains_ascii_case_insensitive(raw, b"password")
        || contains_ascii_case_insensitive(raw, b"passphrase")
        || contains_ascii_case_insensitive(raw, b"[sudo]")
        || contains_ascii_case_insensitive(raw, b"enter pin")
        || contains_ascii_case_insensitive(raw, b"pin:")
        || contains_ascii_case_insensitive(raw, b"verification code")
        || contains_ascii_case_insensitive(raw, b"one-time code")
        || contains_ascii_case_insensitive(raw, b"secret key")
}

/// Stateful WAN speculative-echo safety fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpeculativeEchoFence {
    unconfirmed_keys: u64,
    max_unconfirmed: u64,
    confirmed_epoch: u64,
    issued_epoch: u64,
    secret_latched: bool,
}

impl SpeculativeEchoFence {
    /// Construct a new [`SpeculativeEchoFence`] with `max_unconfirmed` keystroke cap.
    #[must_use]
    pub const fn new(max_unconfirmed: u64) -> Self {
        let cap = if max_unconfirmed == 0 {
            1
        } else {
            max_unconfirmed
        };
        Self {
            unconfirmed_keys: 0,
            max_unconfirmed: cap,
            confirmed_epoch: 0,
            issued_epoch: 0,
            secret_latched: false,
        }
    }

    /// Current count of unconfirmed speculative keystrokes (`<= max_unconfirmed`).
    #[must_use]
    pub const fn unconfirmed_keys(&self) -> u64 {
        self.unconfirmed_keys
    }

    /// Highest confirmed input epoch echoed by the remote PTY (`<= issued_epoch`).
    #[must_use]
    pub const fn confirmed_epoch(&self) -> u64 {
        self.confirmed_epoch
    }

    /// Highest speculative input epoch issued locally.
    #[must_use]
    pub const fn issued_epoch(&self) -> u64 {
        self.issued_epoch
    }

    /// Evaluate whether keystroke `ch` may be speculatively echoed given current screen state.
    pub fn evaluate_keystroke(
        &mut self,
        ch: char,
        altscreen: bool,
        bracketed_paste: bool,
        synchronized_output: bool,
        cursor_row_text: &str,
    ) -> EchoAdmission {
        if altscreen || bracketed_paste || synchronized_output {
            self.reset_to_confirmed();
            return EchoAdmission::SuppressedTerminalMode;
        }
        if ch == '\r' || ch == '\n' {
            self.secret_latched = false;
            self.reset_to_confirmed();
            return EchoAdmission::SuppressedControlChar;
        }
        if self.secret_latched || line_looks_like_secret_prompt(cursor_row_text) {
            self.secret_latched = true;
            self.reset_to_confirmed();
            return EchoAdmission::SuppressedSecretPrompt;
        }
        if ch.is_control() {
            return EchoAdmission::SuppressedControlChar;
        }
        if !echo_has_key_budget(self.unconfirmed_keys, self.max_unconfirmed) {
            return EchoAdmission::SuppressedBudgetFull;
        }
        let next_epoch = echo_epoch_advance(self.issued_epoch, self.issued_epoch.saturating_add(1));
        let next_keys = echo_unconfirmed_clamp(
            self.unconfirmed_keys.saturating_add(1),
            self.max_unconfirmed,
        );
        self.issued_epoch = next_epoch;
        self.unconfirmed_keys = next_keys;
        EchoAdmission::Allow {
            epoch: self.issued_epoch,
            unconfirmed_keys: self.unconfirmed_keys,
        }
    }

    /// Acknowledge remote PTY confirmation through `remote_acked_epoch`.
    pub fn on_remote_ack(&mut self, remote_acked_epoch: u64) {
        let clamped_ack = if remote_acked_epoch > self.issued_epoch {
            self.issued_epoch
        } else {
            remote_acked_epoch
        };
        if clamped_ack > self.confirmed_epoch {
            let delta = clamped_ack - self.confirmed_epoch;
            self.confirmed_epoch = clamped_ack;
            self.unconfirmed_keys = self.unconfirmed_keys.saturating_sub(delta);
        }
    }

    /// Discard all unconfirmed predictions and align `confirmed_epoch = issued_epoch`.
    pub fn reset_to_confirmed(&mut self) {
        self.unconfirmed_keys = 0;
        self.confirmed_epoch = self.issued_epoch;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_password_prompts_and_altscreen_while_bounding_wan_key_budget() {
        let mut fence = SpeculativeEchoFence::new(2);
        assert_eq!(
            fence.evaluate_keystroke('l', false, false, false, "$ "),
            EchoAdmission::Allow {
                epoch: 1,
                unconfirmed_keys: 1,
            }
        );
        assert_eq!(
            fence.evaluate_keystroke('s', false, false, false, "$ l"),
            EchoAdmission::Allow {
                epoch: 2,
                unconfirmed_keys: 2,
            }
        );
        assert_eq!(
            fence.evaluate_keystroke('!', false, false, false, "$ ls"),
            EchoAdmission::SuppressedBudgetFull
        );

        fence.on_remote_ack(2);
        assert_eq!(fence.unconfirmed_keys(), 0);

        // Password prompt latches suppression until Enter (`\n`)!
        assert_eq!(
            fence.evaluate_keystroke('x', false, false, false, "[sudo] password for user: "),
            EchoAdmission::SuppressedSecretPrompt
        );
        assert_eq!(
            fence.evaluate_keystroke('y', false, false, false, ""),
            EchoAdmission::SuppressedSecretPrompt
        );
        assert_eq!(
            fence.evaluate_keystroke('\n', false, false, false, ""),
            EchoAdmission::SuppressedControlChar
        );
        assert_eq!(
            fence.evaluate_keystroke('a', false, false, false, "$ "),
            EchoAdmission::Allow {
                epoch: 3,
                unconfirmed_keys: 1,
            }
        );
    }
}
