// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `OSC 52` clipboard write decoder & read-exfiltration blocker (`aterm` SSH/fabric safety).
//!
//! `OSC 52 ; <Pc> ; <Pd> ST` lets terminal editors (Neovim, Helix, tmux) copy text into the
//! host clipboard across remote `aterm-link` sessions, **but** `OSC 52 ; c ; ? ST` asks the
//! terminal to *echo the user's current clipboard back into PTY stdin*—a classic secret
//! exfiltration vector when viewing untrusted logs or running untrusted binaries.
//!
//! `Osc52ClipboardGuard` unconditionally blocks every `OSC 52` read query (`?`), validates
//! RFC 4648 base64 write payloads without closures, clamps decoded byte size via Clean-origin
//! `osc52_payload_clamp`, and advances `copy_epoch` monotonically.
//!
//! Clean specification: `osc52_clipboard_guard_island.rs` (`Astream.Term.TlaOsc52ClipboardGuard`).

#![allow(clippy::manual_is_multiple_of)]

#[cfg(clean_islands)]
#[path = "osc52_clipboard_guard_island.rs"]
mod osc52_clipboard_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc52_payload_clamp(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc52_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use osc52_clipboard_guard_island::{osc52_epoch_advance, osc52_payload_clamp};

/// Default maximum decoded clipboard write size (`65_536` bytes = `64 KiB`).
pub const DEFAULT_MAX_OSC52_DECODED_BYTES: usize = 65_536;

contract_fn! {
    /// Kernel-certified check that `copied <= max_bytes`, linked via
    /// `clean-kernel-defeq` to `osc52_payload_within_max_isl`.
    #[must_use]
    pub const fn osc52_payload_within_max(copied: u64, max_bytes: u64) -> bool
    clauses [ensures result == (copied <= max_bytes)]
    {
        copied <= max_bytes
    }
}

/// Target clipboard register selected by `OSC 52 ; <Pc> ; ...`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClipboardTarget {
    SystemClipboard,
    PrimarySelection,
}

/// Verdict returned when evaluating the body of an `OSC 52` sequence (`after "52;"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Osc52Verdict {
    /// Safe decoded write to host clipboard.
    AllowWrite {
        target: ClipboardTarget,
        decoded: Vec<u8>,
        copy_epoch: u64,
    },
    /// Clear the target clipboard (`OSC 52 ; c ; ST`).
    ClearClipboard {
        target: ClipboardTarget,
        copy_epoch: u64,
    },
    /// Blocked clipboard read exfiltration attempt (`OSC 52 ; ... ; ?`).
    ReadQueryBlocked,
    /// Rejected becausewrite policy is disabled on this tab.
    WriteDisabled,
    /// Rejected because payload exceeded `max_decoded_bytes`.
    PayloadTooLarge { max_decoded_bytes: usize },
    /// Rejected malformed `OSC 52` syntax or invalid base64.
    MalformedSequence,
}

const fn b64_val(b: u8) -> Option<u8> {
    match b {
        b'A'..=b'Z' => Some(b.saturating_sub(b'A')),
        b'a'..=b'z' => Some(b.saturating_sub(b'a').saturating_add(26)),
        b'0'..=b'9' => Some(b.saturating_sub(b'0').saturating_add(52)),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

fn slice_has_byte(mut s: &[u8], needle: u8) -> bool {
    while let &[b, ref rest @ ..] = s {
        s = rest;
        if b == needle {
            return true;
        }
    }
    false
}

fn decode_base64_bounded(b64: &[u8], max_out: usize) -> Result<Vec<u8>, bool> {
    // Returns Err(true) on oversize, Err(false) on invalid base64.
    let mut clean_len = 0usize;
    let mut scan = b64;
    while let &[b, ref rest @ ..] = scan {
        scan = rest;
        if b != b'\r' && b != b'\n' && b != b' ' {
            clean_len = clean_len.saturating_add(1);
        }
    }
    if clean_len % 4 != 0 {
        return Err(false);
    }
    let mut out = Vec::new();
    let mut quad = [0u8; 4];
    let mut q_idx = 0usize;
    let mut seen_pad = false;
    let mut cur = b64;
    while let &[b, ref rest @ ..] = cur {
        cur = rest;
        if b == b'\r' || b == b'\n' || b == b' ' {
            continue;
        }
        if let Some(slot) = quad.get_mut(q_idx) {
            *slot = b;
        }
        q_idx = q_idx.saturating_add(1);
        if q_idx == 4 {
            q_idx = 0;
            if seen_pad {
                return Err(false);
            }
            let [q0, q1, q2, q3] = quad;
            let Some(v0) = b64_val(q0) else {
                return Err(false);
            };
            let Some(v1) = b64_val(q1) else {
                return Err(false);
            };
            let b0 = (v0 << 2) | (v1 >> 4);
            if out.len() >= max_out {
                return Err(true);
            }
            out.push(b0);

            if q2 == b'=' {
                if q3 != b'=' || (v1 & 0x0f) != 0 {
                    return Err(false);
                }
                seen_pad = true;
            } else {
                let Some(v2) = b64_val(q2) else {
                    return Err(false);
                };
                let b1 = ((v1 & 0x0f) << 4) | (v2 >> 2);
                if out.len() >= max_out {
                    return Err(true);
                }
                out.push(b1);

                if q3 == b'=' {
                    if (v2 & 0x03) != 0 {
                        return Err(false);
                    }
                    seen_pad = true;
                } else {
                    let Some(v3) = b64_val(q3) else {
                        return Err(false);
                    };
                    let b2 = ((v2 & 0x03) << 6) | v3;
                    if out.len() >= max_out {
                        return Err(true);
                    }
                    out.push(b2);
                }
            }
        }
    }
    Ok(out)
}

/// Stateful `OSC 52` clipboard security gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Osc52ClipboardGuard {
    allow_writes: bool,
    max_decoded_bytes: usize,
    copy_epoch: u64,
    blocked_read_queries: u64,
}

impl Osc52ClipboardGuard {
    #[must_use]
    pub fn new(allow_writes: bool, max_decoded_bytes: usize) -> Self {
        let cap = if max_decoded_bytes == 0 {
            DEFAULT_MAX_OSC52_DECODED_BYTES
        } else {
            max_decoded_bytes
        };
        Self {
            allow_writes,
            max_decoded_bytes: cap,
            copy_epoch: 0,
            blocked_read_queries: 0,
        }
    }

    #[must_use]
    pub const fn copy_epoch(&self) -> u64 {
        self.copy_epoch
    }

    #[must_use]
    pub const fn blocked_read_queries(&self) -> u64 {
        self.blocked_read_queries
    }

    /// Evaluate an `OSC` payload body (e.g. `b"52;c;SGVsbG8="`).
    pub fn evaluate_osc_body(&mut self, osc_body: &[u8]) -> Osc52Verdict {
        let Some(after_52) = osc_body.strip_prefix(b"52;") else {
            return Osc52Verdict::MalformedSequence;
        };
        let mut semi_pos = None;
        let mut i = 0usize;
        let mut scan = after_52;
        while let &[b, ref rest @ ..] = scan {
            if b == b';' {
                semi_pos = Some(i);
                break;
            }
            scan = rest;
            i = i.saturating_add(1);
        }
        let Some(pos) = semi_pos else {
            return Osc52Verdict::MalformedSequence;
        };
        let (Some(sel), Some(pd)) = (after_52.get(..pos), after_52.get(pos.saturating_add(1)..))
        else {
            return Osc52Verdict::MalformedSequence;
        };

        if pd == b"?" {
            self.blocked_read_queries = self.blocked_read_queries.saturating_add(1);
            return Osc52Verdict::ReadQueryBlocked;
        }
        if !self.allow_writes {
            return Osc52Verdict::WriteDisabled;
        }

        let target = if slice_has_byte(sel, b'p') && !slice_has_byte(sel, b'c') {
            ClipboardTarget::PrimarySelection
        } else {
            ClipboardTarget::SystemClipboard
        };

        if pd.is_empty() {
            let next_epoch =
                osc52_epoch_advance(self.copy_epoch, self.copy_epoch.saturating_add(1));
            self.copy_epoch = next_epoch;
            return Osc52Verdict::ClearClipboard {
                target,
                copy_epoch: next_epoch,
            };
        }

        match decode_base64_bounded(pd, self.max_decoded_bytes) {
            Ok(mut decoded) => {
                let clamped =
                    osc52_payload_clamp(decoded.len() as u64, self.max_decoded_bytes as u64);
                let _ = osc52_payload_within_max(clamped, self.max_decoded_bytes as u64);
                decoded.truncate(clamped as usize);
                let next_epoch =
                    osc52_epoch_advance(self.copy_epoch, self.copy_epoch.saturating_add(1));
                self.copy_epoch = next_epoch;
                Osc52Verdict::AllowWrite {
                    target,
                    decoded,
                    copy_epoch: next_epoch,
                }
            }
            Err(true) => Osc52Verdict::PayloadTooLarge {
                max_decoded_bytes: self.max_decoded_bytes,
            },
            Err(false) => Osc52Verdict::MalformedSequence,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_read_exfiltration_decodes_valid_base64_and_enforces_size_cap() {
        let mut guard = Osc52ClipboardGuard::new(true, 8);
        assert_eq!(
            guard.evaluate_osc_body(b"52;c;?"),
            Osc52Verdict::ReadQueryBlocked
        );
        assert_eq!(guard.blocked_read_queries(), 1);

        assert_eq!(
            guard.evaluate_osc_body(b"52;c;SGVsbG8="),
            Osc52Verdict::AllowWrite {
                target: ClipboardTarget::SystemClipboard,
                decoded: b"Hello".to_vec(),
                copy_epoch: 1,
            }
        );

        // "HelloWorld" = 10 bytes > 8 byte cap -> PayloadTooLarge.
        assert_eq!(
            guard.evaluate_osc_body(b"52;p;SGVsbG9Xb3JsZA=="),
            Osc52Verdict::PayloadTooLarge {
                max_decoded_bytes: 8
            }
        );
    }
}
