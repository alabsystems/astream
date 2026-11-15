// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `OSC 52` Clipboard Write-Only Filter & Bounded RFC 4648 Base64 Decoder.
//!
//! Terminal programs (`tmux`, `neovim`, `amacs`, remote SSH/fabric tools) copy text to the
//! operator's pasteboard via `OSC 52 ; <targets> ; <base64-payload> ST`. Two hazards arise
//! when bridging sessions across `asb`:
//! 1. **Clipboard Exfiltration (`OSC 52 ; c ; ?`)**: a query payload `?` asks the terminal to
//!    echo the user's current clipboard back into the PTY input stream! Under write-only policy
//!    (default), `?` queries are unconditionally blocked.
//! 2. **Unbounded Wire Bloat**: multi-megabyte `OSC 52` payloads stall low-bandwidth WAN links;
//!    both encoded wire bytes (`max_wire_bytes`) and decoded UTF-8/raw bytes
//!    (`max_clipboard_bytes`) are strictly bounded.
//!
//! Backed by Clean TLA+ Island `Astream.Term.TlaOsc52ClipboardBudget`
//! (`osc52_clipboard_budget_island.rs`), proving `decodedBytes <= maxClipboardBytes` and
//! `encodedBytes <= maxWireBytes`.

#[cfg(clean_islands)]
#[path = "osc52_clipboard_budget_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{osc52_decoded_clamp, osc52_wire_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn osc52_decoded_clamp(decoded_bytes: u64, max_decoded: u64) -> u64 {
    if decoded_bytes < max_decoded {
        decoded_bytes
    } else {
        max_decoded
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn osc52_wire_clamp(encoded_bytes: u64, max_wire: u64) -> u64 {
    if encoded_bytes < max_wire {
        encoded_bytes
    } else {
        max_wire
    }
}

contract_fn! {
    /// Kernel-certified byte-budget check (`byte_len <= budget`).
    #[must_use]
    #[inline]
    pub const fn osc52_within_budget(byte_len: u64, budget: u64) -> bool
    clauses [ensures result == (byte_len <= budget)]
    {
        byte_len <= budget
    }
}

/// Default decoded clipboard cap (`65_536` bytes = 64 KiB).
pub const DEFAULT_MAX_CLIPBOARD_BYTES: usize = 65_536;

/// Default Base64 wire payload cap (`90_112` bytes).
pub const DEFAULT_MAX_OSC52_WIRE_BYTES: usize = 90_112;

/// Parsed & validated `OSC 52` action.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Osc52Decision {
    /// Validated clipboard write (`decoded.len() <= max_clipboard_bytes`).
    WriteClipboard {
        target_clipboard: bool,
        target_primary: bool,
        decoded: Vec<u8>,
    },
    /// Explicit clipboard clear (`OSC 52 ; c ; ST` with empty payload).
    ClearClipboard {
        target_clipboard: bool,
        target_primary: bool,
    },
    /// Blocked `OSC 52 ; ... ; ?` clipboard read query (anti-exfiltration).
    BlockedReadQuery,
    /// Rejected malformed `OSC 52` syntax or invalid Base64.
    MalformedSyntax,
    /// Rejected because encoded or decoded length exceeded configured budget.
    RejectedOverBudget,
}

#[inline]
const fn decode_b64_sextet(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' {
        b.saturating_sub(b'A')
    } else if b >= b'a' && b <= b'z' {
        b.saturating_sub(b'a').wrapping_add(26)
    } else if b >= b'0' && b <= b'9' {
        b.saturating_sub(b'0').wrapping_add(52)
    } else if b == b'+' {
        62
    } else if b == b'/' {
        63
    } else {
        0xFF
    }
}

/// Evaluates an `OSC 52` body after the `"52;"` prefix (`<targets>;<payload>`), enforcing
/// write-only security and certified wire/decoded byte budgets without closures.
#[must_use]
pub fn evaluate_osc52_body(
    body_after_52_semi: &[u8],
    max_clipboard_bytes: usize,
    max_wire_bytes: usize,
) -> Osc52Decision {
    let mut semi_pos: Option<usize> = None;
    let mut idx = 0usize;
    let mut scan = body_after_52_semi;
    while let &[b, ref tail @ ..] = scan {
        if b == b';' {
            semi_pos = Some(idx);
            break;
        }
        idx = idx.saturating_add(1);
        scan = tail;
    }
    let Some(split) = semi_pos else {
        return Osc52Decision::MalformedSyntax;
    };
    let (Some(targets), Some(b64)) = (
        body_after_52_semi.get(..split),
        body_after_52_semi.get(split.saturating_add(1)..),
    ) else {
        return Osc52Decision::MalformedSyntax;
    };

    // Default target per xterm spec when `targets` is empty is `c` (system clipboard).
    let mut target_clipboard = targets.is_empty();
    let mut target_primary = false;
    let mut t_rest = targets;
    while let &[tb, ref tail @ ..] = t_rest {
        match tb {
            b'c' | b'0' => target_clipboard = true,
            b'p' | b's' => target_primary = true,
            b'q' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' => {}
            _ => return Osc52Decision::MalformedSyntax,
        }
        t_rest = tail;
    }

    if b64 == b"?" {
        return Osc52Decision::BlockedReadQuery;
    }
    if b64.is_empty() {
        return Osc52Decision::ClearClipboard {
            target_clipboard,
            target_primary,
        };
    }

    let wire_cap = max_wire_bytes as u64;
    let enc_len = b64.len() as u64;
    if !osc52_within_budget(enc_len, wire_cap) || osc52_wire_clamp(enc_len, wire_cap) < enc_len {
        return Osc52Decision::RejectedOverBudget;
    }

    // Strip ASCII whitespace inside Base64 if any, validating quartets.
    let mut q0 = 0u8;
    let mut q1 = 0u8;
    let mut q2 = 0u8;
    let mut q3 = 0u8;
    let mut q_len = 0u8;
    let mut pad_seen = false;
    let mut out = Vec::new();
    let dec_cap = max_clipboard_bytes as u64;

    let mut b64_rest = b64;
    while let &[ch, ref tail @ ..] = b64_rest {
        b64_rest = tail;
        if ch == b' ' || ch == b'\n' || ch == b'\r' || ch == b'\t' {
            continue;
        }
        match q_len {
            0 => {
                q0 = ch;
                q_len = 1;
            }
            1 => {
                q1 = ch;
                q_len = 2;
            }
            2 => {
                q2 = ch;
                q_len = 3;
            }
            _ => {
                q3 = ch;
                q_len = 4;
            }
        }
        if q_len == 4 {
            if pad_seen {
                return Osc52Decision::MalformedSyntax;
            }
            let s0 = decode_b64_sextet(q0);
            let s1 = decode_b64_sextet(q1);
            if s0 == 0xFF || s1 == 0xFF {
                return Osc52Decision::MalformedSyntax;
            }
            let b0 = (s0 << 2) | (s1 >> 4);
            let add_count: u64;
            let mut b1 = 0u8;
            let mut b2 = 0u8;

            if q2 == b'=' {
                if q3 != b'=' {
                    return Osc52Decision::MalformedSyntax;
                }
                pad_seen = true;
                add_count = 1;
            } else if q3 == b'=' {
                let s2 = decode_b64_sextet(q2);
                if s2 == 0xFF {
                    return Osc52Decision::MalformedSyntax;
                }
                b1 = ((s1 & 0x0F) << 4) | (s2 >> 2);
                pad_seen = true;
                add_count = 2;
            } else {
                let s2 = decode_b64_sextet(q2);
                let s3 = decode_b64_sextet(q3);
                if s2 == 0xFF || s3 == 0xFF {
                    return Osc52Decision::MalformedSyntax;
                }
                b1 = ((s1 & 0x0F) << 4) | (s2 >> 2);
                b2 = ((s2 & 0x03) << 6) | s3;
                add_count = 3;
            }

            let proposed_dec = (out.len() as u64).saturating_add(add_count);
            let clamped_dec = osc52_decoded_clamp(proposed_dec, dec_cap);
            if clamped_dec < proposed_dec || !osc52_within_budget(proposed_dec, dec_cap) {
                return Osc52Decision::RejectedOverBudget;
            }
            out.push(b0);
            if add_count >= 2 {
                out.push(b1);
            }
            if add_count == 3 {
                out.push(b2);
            }
            q_len = 0;
        }
    }

    if q_len != 0 {
        return Osc52Decision::MalformedSyntax;
    }

    Osc52Decision::WriteClipboard {
        target_clipboard,
        target_primary,
        decoded: out,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_read_queries_decodes_valid_base64_and_enforces_byte_caps() {
        // Exfiltration attempt `c;?` -> blocked!
        assert_eq!(
            evaluate_osc52_body(b"c;?", 64, 128),
            Osc52Decision::BlockedReadQuery
        );

        // Valid write `c;aGVsbG8gYXRlcm0=` ("hello aterm") -> decoded!
        assert_eq!(
            evaluate_osc52_body(b"c;aGVsbG8gYXRlcm0=", 64, 128),
            Osc52Decision::WriteClipboard {
                target_clipboard: true,
                target_primary: false,
                decoded: b"hello aterm".to_vec(),
            }
        );

        // Decoded budget exceeded (max 5 bytes < 11 bytes) -> rejected!
        assert_eq!(
            evaluate_osc52_body(b"cp;aGVsbG8gYXRlcm0=", 5, 128),
            Osc52Decision::RejectedOverBudget
        );

        // Empty payload clears clipboard.
        assert_eq!(
            evaluate_osc52_body(b";", 64, 128),
            Osc52Decision::ClearClipboard {
                target_clipboard: true,
                target_primary: false,
            }
        );
    }
}
