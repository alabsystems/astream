// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! POSIX `termios` `ECHO | ECHOE | ECHOCTL | ONLCR` expected echo byte-length calculator
//! (`term.echo.overlap-attribution`: `^X` -> `2`, `\n` -> `2` `\r\n`, `DEL` -> `3` `\x08 \x08`,
//! `ESC` -> `0`; `Astream.SpecEcho.TlaCaretCtrlExpander`).

#[cfg(clean_islands)]
#[path = "caret_ctrl_expander_island.rs"]
mod caret_ctrl_expander_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_exp_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_attr_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use caret_ctrl_expander_island::{se_attr_advance, se_exp_clamp};

/// Maximum expected echo bytes for one 4 KiB write chunk (`16_384`).
pub const MAX_EXPECTED_ECHO_BYTES: u64 = 16_384;

contract_fn! {
    /// Verified complete echo attribution (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `se_echo_attributed_isl`.
    #[must_use]
    pub const fn se_echo_attributed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct EchoLengthAttributor {
    retired_in_offset: u64,
}

impl EchoLengthAttributor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            retired_in_offset: 0,
        }
    }

    #[must_use]
    pub fn expected_echo_len(input: &[u8]) -> u64 {
        let mut total = 0u64;
        for &b in input {
            let add = match b {
                0x1B => 0,          // ESC suppressed under ECHOCTL
                b'\n' | b'\r' => 2, // ONLCR `\r\n`
                0x7F | 0x08 => 3,   // ECHOE `\x08 \x08`
                0x00..=0x1F => 2,   // ECHOCTL `^X`
                _ => 1,
            };
            total = total.saturating_add(add);
        }
        se_exp_clamp(total, MAX_EXPECTED_ECHO_BYTES)
    }

    pub fn try_retire_write(
        &mut self,
        in_offset: u64,
        input: &[u8],
        observed_out_len: u64,
    ) -> bool {
        let expected = Self::expected_echo_len(input);
        if se_echo_attributed(observed_out_len, expected) {
            self.retired_in_offset = se_attr_advance(self.retired_in_offset, in_offset);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computes_exact_echoctl_and_echoe_byte_expansions() {
        assert_eq!(
            EchoLengthAttributor::expected_echo_len(b"ls\x7f\n"),
            2 + 3 + 2
        );
        assert_eq!(EchoLengthAttributor::expected_echo_len(b"\x03\x1b"), 2);
        let mut a = EchoLengthAttributor::new();
        assert!(a.try_retire_write(42, b"hi\n", 4));
    }
}
