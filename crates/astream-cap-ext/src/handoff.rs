// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Supervised agent self-restart handoff envelope (`aterm ctl @self restart pid=<agent-pid>`,
//! `Astream.Agent.TlaRestartHandoff`).
//!
//! Encodes and validates a deterministic, newline-free `v=1` restart handoff record carrying
//! `sid`, `conv`, `pid`, monotone `epoch` (`handoff_epoch_advance`), `cursor`, percent-encoded
//! `cwd`, and bounded `summary` (`handoff_summary_clamp`), with kernel-certified foreground
//! PID supervision verification (`handoff_pid_matches`), `0 mandated`, and `0 runtime_checked`
//! obligations.

#![allow(clippy::manual_is_ascii_check, clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "handoff_island.rs"]
mod handoff_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn handoff_epoch_advance(prev_epoch: u64, cand_epoch: u64) -> u64 {
    if prev_epoch < cand_epoch {
        cand_epoch
    } else {
        prev_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn handoff_summary_clamp(len: u64, max_len: u64) -> u64 {
    if len < max_len {
        len
    } else {
        max_len
    }
}
#[cfg(clean_islands)]
pub use handoff_island::{handoff_epoch_advance, handoff_summary_clamp};

/// Maximum UTF-8 byte length of the handoff summary (`512` bytes).
pub const MAX_HANDOFF_SUMMARY_BYTES: usize = 512;

/// Maximum UTF-8 byte length of `sid`, `conv`, or `cwd` fields (`256` bytes).
pub const MAX_HANDOFF_FIELD_BYTES: usize = 256;

/// Maximum wire byte length of an encoded `V1RestartHandoff` line.
pub const MAX_HANDOFF_LINE_BYTES: usize = 4096;

contract_fn! {
    /// Kernel-certified foreground process equality (`expected_pid == observed_pid`).
    #[must_use]
    pub const fn handoff_pid_eq(expected_pid: u32, observed_pid: u32) -> bool
    clauses [ensures result == (expected_pid == observed_pid)]
    {
        expected_pid == observed_pid
    }
}

/// Foreground process validation (`expected_pid == observed_pid && observed_pid > 0`).
#[inline]
#[must_use]
pub const fn handoff_pid_matches(expected_pid: u32, observed_pid: u32) -> bool {
    0 < observed_pid && handoff_pid_eq(expected_pid, observed_pid)
}

/// Errors returned when decoding or validating a [`V1RestartHandoff`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandoffError {
    /// Line exceeds [`MAX_HANDOFF_LINE_BYTES`] or is empty.
    LengthOutOfBounds,
    /// Missing `v=1` header, unknown key, or malformed token.
    MalformedToken,
    /// Duplicate key or missing required field.
    InvalidFields,
    /// Invalid percent-encoding or UTF-8 sequence.
    InvalidEncoding,
    /// Foreground process PID mismatch or zero PID (`aterm ctl @self restart` refusal).
    PidMismatch { expected: u32, observed: u32 },
    /// Non-monotone restart epoch relative to prior handoff.
    StaleEpoch { prior: u64, candidate: u64 },
}

/// Canonical `v=1` supervised self-restart handoff envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V1RestartHandoff {
    /// `aterm` session identifier (`ATERM_SESSION_ID`).
    pub sid: String,
    /// Agent conversation/thread identifier to resume with the same recorded args/env.
    pub conversation_id: String,
    /// Agent foreground PID (`> 0`).
    pub agent_pid: u32,
    /// Monotone restart epoch (`>= 1`).
    pub epoch: u64,
    /// Durable log cursor offset saved at handoff time.
    pub log_cursor: u64,
    /// Working directory to preserve across restart.
    pub cwd: String,
    /// Bounded handoff note for the resumed turn (`<= MAX_HANDOFF_SUMMARY_BYTES`).
    pub summary: String,
}

impl V1RestartHandoff {
    /// Advance from `prior_epoch` to `prior_epoch + 1` via Clean-origin [`handoff_epoch_advance`].
    #[must_use]
    pub fn next_epoch(prior_epoch: u64) -> u64 {
        let cand = prior_epoch.saturating_add(1);
        handoff_epoch_advance(prior_epoch, cand)
    }

    /// Validate that the supervised foreground process `observed_fg_pid` matches `self.agent_pid`
    /// and that `self.epoch` strictly advances past `prior_epoch`.
    pub fn validate_for_restart(
        &self,
        observed_fg_pid: u32,
        prior_epoch: u64,
    ) -> Result<(), HandoffError> {
        if !handoff_pid_matches(self.agent_pid, observed_fg_pid) {
            return Err(HandoffError::PidMismatch {
                expected: self.agent_pid,
                observed: observed_fg_pid,
            });
        }
        if self.epoch <= prior_epoch {
            return Err(HandoffError::StaleEpoch {
                prior: prior_epoch,
                candidate: self.epoch,
            });
        }
        Ok(())
    }

    /// Encode this handoff into a single canonical `v=1` ASCII line.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"v=1 sid=");
        push_pct_clamped(&mut out, &self.sid, MAX_HANDOFF_FIELD_BYTES as u64);
        out.extend_from_slice(b" conv=");
        push_pct_clamped(
            &mut out,
            &self.conversation_id,
            MAX_HANDOFF_FIELD_BYTES as u64,
        );
        out.extend_from_slice(b" pid=");
        push_dec_u64(&mut out, self.agent_pid as u64);
        out.extend_from_slice(b" epoch=");
        push_dec_u64(&mut out, self.epoch);
        out.extend_from_slice(b" cursor=");
        push_dec_u64(&mut out, self.log_cursor);
        out.extend_from_slice(b" cwd=");
        push_pct_clamped(&mut out, &self.cwd, MAX_HANDOFF_FIELD_BYTES as u64);
        out.extend_from_slice(b" summary=");
        push_pct_clamped(&mut out, &self.summary, MAX_HANDOFF_SUMMARY_BYTES as u64);
        out
    }

    /// Decode a canonical `v=1` restart handoff line.
    pub fn decode(raw: &[u8]) -> Result<Self, HandoffError> {
        if raw.is_empty() || raw.len() > MAX_HANDOFF_LINE_BYTES {
            return Err(HandoffError::LengthOutOfBounds);
        }
        if core::str::from_utf8(raw).is_err() {
            return Err(HandoffError::InvalidEncoding);
        }
        let (first, mut rem_tokens) = next_handoff_token(raw);
        if first != b"v=1" {
            return Err(HandoffError::MalformedToken);
        }

        let mut sid: Option<String> = None;
        let mut conv: Option<String> = None;
        let mut pid: Option<u32> = None;
        let mut epoch: Option<u64> = None;
        let mut cursor: Option<u64> = None;
        let mut cwd: Option<String> = None;
        let mut summary: Option<String> = None;

        while !rem_tokens.is_empty() {
            let (tok, next_rem) = next_handoff_token(rem_tokens);
            rem_tokens = next_rem;
            if tok.is_empty() {
                continue;
            }
            let Some((k, v)) = split_handoff_byte_once(tok, b'=') else {
                return Err(HandoffError::MalformedToken);
            };
            if k == b"sid" {
                if sid.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let s = match pct_decode_bounded(v, MAX_HANDOFF_FIELD_BYTES) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                if s.is_empty() {
                    return Err(HandoffError::InvalidFields);
                }
                sid = Some(s);
            } else if k == b"conv" {
                if conv.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let s = match pct_decode_bounded(v, MAX_HANDOFF_FIELD_BYTES) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                if s.is_empty() {
                    return Err(HandoffError::InvalidFields);
                }
                conv = Some(s);
            } else if k == b"pid" {
                if pid.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let n = match parse_u64_digits(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                if n == 0 || n > (u32::MAX as u64) {
                    return Err(HandoffError::InvalidFields);
                }
                pid = Some(n as u32);
            } else if k == b"epoch" {
                if epoch.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let ep = match parse_u64_digits(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                epoch = Some(ep);
            } else if k == b"cursor" {
                if cursor.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let cur = match parse_u64_digits(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                cursor = Some(cur);
            } else if k == b"cwd" {
                if cwd.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let c = match pct_decode_bounded(v, MAX_HANDOFF_FIELD_BYTES) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                cwd = Some(c);
            } else if k == b"summary" {
                if summary.is_some() {
                    return Err(HandoffError::InvalidFields);
                }
                let sum = match pct_decode_bounded(v, MAX_HANDOFF_SUMMARY_BYTES) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
                summary = Some(sum);
            } else {
                return Err(HandoffError::MalformedToken);
            }
        }

        let (
            Some(s_sid),
            Some(s_conv),
            Some(n_pid),
            Some(n_epoch),
            Some(n_cursor),
            Some(s_cwd),
            Some(s_sum),
        ) = (sid, conv, pid, epoch, cursor, cwd, summary)
        else {
            return Err(HandoffError::InvalidFields);
        };
        Ok(Self {
            sid: s_sid,
            conversation_id: s_conv,
            agent_pid: n_pid,
            epoch: n_epoch,
            log_cursor: n_cursor,
            cwd: s_cwd,
            summary: s_sum,
        })
    }
}

const fn find_handoff_byte(mut rest: &[u8], needle: u8) -> Option<usize> {
    let mut idx = 0usize;
    while let &[b, ref tail @ ..] = rest {
        if b == needle {
            return Some(idx);
        }
        idx = idx.saturating_add(1);
        rest = tail;
    }
    None
}

fn split_handoff_byte_once(bytes: &[u8], delim: u8) -> Option<(&[u8], &[u8])> {
    let Some(i) = find_handoff_byte(bytes, delim) else {
        return None;
    };
    let Some(next) = i.checked_add(1) else {
        return None;
    };
    let Some(head) = bytes.get(..i) else {
        return None;
    };
    let Some(tail) = bytes.get(next..) else {
        return None;
    };
    Some((head, tail))
}

fn next_handoff_token(bytes: &[u8]) -> (&[u8], &[u8]) {
    let mut trimmed = bytes;
    while let &[b' ', ref tail @ ..] = trimmed {
        trimmed = tail;
    }
    match split_handoff_byte_once(trimmed, b' ') {
        Some((tok, rest)) => (tok, rest),
        None => (trimmed, &[]),
    }
}

fn push_pct_clamped(out: &mut Vec<u8>, s: &str, max_raw: u64) {
    let bytes = s.as_bytes();
    let limit = handoff_summary_clamp(bytes.len() as u64, max_raw) as usize;
    let mut cut = if limit < bytes.len() {
        limit
    } else {
        bytes.len()
    };
    while cut > 0 {
        match bytes.get(cut) {
            Some(&b) if (b & 0xC0) == 0x80 => {
                cut = cut.saturating_sub(1);
            }
            _ => break,
        }
    }
    let Some(mut rest) = bytes.get(..cut) else {
        return;
    };
    while let &[b, ref tail @ ..] = rest {
        let safe = matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'/');
        if safe {
            out.push(b);
        } else {
            out.push(b'%');
            out.push(hex_upper(b >> 4));
            out.push(hex_upper(b & 0x0F));
        }
        rest = tail;
    }
}

fn hex_upper(nib: u8) -> u8 {
    if nib < 10 {
        b'0'.wrapping_add(nib)
    } else {
        b'A'.wrapping_add(nib.saturating_sub(10))
    }
}

fn decode_hex_nibble(b: u8) -> Result<u8, HandoffError> {
    if matches!(b, b'0'..=b'9') {
        Ok(b.saturating_sub(b'0'))
    } else if matches!(b, b'a'..=b'f') {
        Ok(b.saturating_sub(b'a').wrapping_add(10))
    } else if matches!(b, b'A'..=b'F') {
        Ok(b.saturating_sub(b'A').wrapping_add(10))
    } else {
        Err(HandoffError::InvalidEncoding)
    }
}

fn pct_decode_bounded(bytes: &[u8], max_bytes: usize) -> Result<String, HandoffError> {
    let mut out = Vec::new();
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        let decoded = if b == b'%' {
            let &[hi, lo, ref after_hex @ ..] = tail else {
                return Err(HandoffError::InvalidEncoding);
            };
            rest = after_hex;
            let h_val = match decode_hex_nibble(hi) {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            let l_val = match decode_hex_nibble(lo) {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            (h_val << 4) | l_val
        } else {
            rest = tail;
            b
        };
        if out.len() >= max_bytes {
            return Err(HandoffError::LengthOutOfBounds);
        }
        out.push(decoded);
    }
    match String::from_utf8(out) {
        Ok(text) => Ok(text),
        Err(_) => Err(HandoffError::InvalidEncoding),
    }
}

fn push_dec_u64(out: &mut Vec<u8>, mut val: u64) {
    if val == 0 {
        out.push(b'0');
        return;
    }
    let mut rev = Vec::new();
    while val > 0 {
        let d = (val % 10) as u8;
        rev.push(b'0'.wrapping_add(d));
        val /= 10;
    }
    while let Some(b) = rev.pop() {
        out.push(b);
    }
}

fn parse_u64_digits(bytes: &[u8]) -> Result<u64, HandoffError> {
    if bytes.is_empty() || bytes.len() > 20 {
        return Err(HandoffError::MalformedToken);
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !matches!(b, b'0'..=b'9') {
            return Err(HandoffError::MalformedToken);
        }
        let Some(m) = acc.checked_mul(10) else {
            return Err(HandoffError::MalformedToken);
        };
        let Some(next) = m.checked_add(b.saturating_sub(b'0') as u64) else {
            return Err(HandoffError::MalformedToken);
        };
        acc = next;
        rest = tail;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_decodes_and_validates_supervised_pid_and_monotone_epoch() {
        let ep = V1RestartHandoff::next_epoch(0);
        assert_eq!(ep, 1);

        let h = V1RestartHandoff {
            sid: "s-tab-8".to_string(),
            conversation_id: "31bdcf2b-4697-4d9a".to_string(),
            agent_pid: 47485,
            epoch: ep,
            log_cursor: 12_345,
            cwd: "/fixture-home/astream".to_string(),
            summary: "Batch 8 verified; resume at Batch 9".to_string(),
        };
        let wire = h.encode();
        assert!(!wire.contains(&b'\n'));
        let decoded = V1RestartHandoff::decode(&wire).unwrap();
        assert_eq!(decoded, h);

        // Matching foreground PID and newer epoch succeeds.
        assert!(decoded.validate_for_restart(47485, 0).is_ok());

        // Supervisor host PID != agent PID refuses!
        assert_eq!(
            decoded.validate_for_restart(99999, 0),
            Err(HandoffError::PidMismatch {
                expected: 47485,
                observed: 99999
            })
        );

        // Stale epoch replay refuses!
        assert_eq!(
            decoded.validate_for_restart(47485, 1),
            Err(HandoffError::StaleEpoch {
                prior: 1,
                candidate: 1
            })
        );
    }
}
