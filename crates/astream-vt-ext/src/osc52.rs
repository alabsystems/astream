// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! ECMA-48 / xterm OSC 52 (`\x1b]52;<targets>;<base64-or-?>\x07`) clipboard set/clear/query
//! parser, zero-exfiltration policy gate, and RFC 4648 Base64 codec (`Astream.Term.TlaClipboardOsc52`).
//!
//! Protects `aterm` and remote terminal sessions against clipboard readback exfiltration (`?`
//! queries denied by default) and bracketed-paste / escape-sequence injection while supporting
//! bounded clipboard writes up to `MAX_OSC52_DECODED_BYTES` (`64 KiB`) with `0 mandated` obligations.

#![allow(
    clippy::assign_op_pattern,
    clippy::manual_is_ascii_check,
    clippy::manual_range_contains,
    clippy::question_mark
)]

#[cfg(clean_islands)]
#[path = "osc52_island.rs"]
mod osc52_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc52_bytes_clamp(decoded_len: u64, max_bytes: u64) -> u64 {
    if decoded_len < max_bytes {
        decoded_len
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc52_target_mask_clamp(mask: u64, max_mask: u64) -> u64 {
    if mask < max_mask {
        mask
    } else {
        max_mask
    }
}
#[cfg(clean_islands)]
pub use osc52_island::{osc52_bytes_clamp, osc52_target_mask_clamp};

/// Maximum decoded clipboard payload size accepted by OSC 52 (`64 KiB`).
pub const MAX_OSC52_DECODED_BYTES: usize = 65_536;

/// Maximum encoded OSC 52 body length (`52;<targets>;<base64>`).
pub const MAX_OSC52_RAW_BYTES: usize = 90_000;

/// Bitmask ceiling covering xterm clipboard targets (`c`, `p`, `q`, `s`, `0..=7` -> 12 bits = `0x0FFF`).
pub const MAX_OSC52_TARGET_MASK: u64 = 0x0FFF;

/// Target bit for system clipboard (`c`).
pub const OSC52_TARGET_CLIPBOARD: u64 = 1 << 0;
/// Target bit for X11 primary selection (`p`).
pub const OSC52_TARGET_PRIMARY: u64 = 1 << 1;
/// Target bit for secondary selection (`q`).
pub const OSC52_TARGET_SECONDARY: u64 = 1 << 2;
/// Target bit for select (`s`).
pub const OSC52_TARGET_SELECT: u64 = 1 << 3;

contract_fn! {
    /// Verified check that a decoded OSC 52 clipboard payload is within `max_len`
    /// (`len <= max_len`), linked via `clean-kernel-defeq` to `osc52_payload_within_cap_isl`.
    #[must_use]
    pub const fn osc52_payload_within_cap(len: usize, max_len: usize) -> bool
    clauses [ensures result == (len <= max_len)]
    {
        len <= max_len
    }
}

/// Security policy governing OSC 52 clipboard operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc52Policy {
    /// Allow `?` clipboard readback queries (DEFAULT: `false` — prevents clipboard exfiltration!).
    pub allow_query: bool,
    /// Maximum decoded clipboard payload bytes (`<= MAX_OSC52_DECODED_BYTES`).
    pub max_decoded_bytes: usize,
    /// Strip dangerous C0/C1 terminal control bytes (except `\t` and `\n`) from decoded text.
    pub strip_unsafe_controls: bool,
}

impl Default for Osc52Policy {
    fn default() -> Self {
        Self {
            allow_query: false,
            max_decoded_bytes: MAX_OSC52_DECODED_BYTES,
            strip_unsafe_controls: true,
        }
    }
}

/// Parsed and policy-checked OSC 52 clipboard action.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Osc52Action {
    /// Set clipboard selection(s) in `target_mask` to `bytes`.
    SetClipboard { target_mask: u64, bytes: Vec<u8> },
    /// Explicitly clear clipboard selection(s) in `target_mask` (`52;<targets>;`).
    ClearClipboard { target_mask: u64 },
    /// Clipboard `?` readback permitted by policy.
    QueryClipboard { target_mask: u64 },
    /// Clipboard `?` readback blocked by zero-exfiltration policy (`allow_query == false`).
    QueryDenied { target_mask: u64 },
}

/// Parse an OSC payload body (after stripping leading `\x1b]` and trailing BEL `\x07` or ST `\x1b\\`),
/// returning `Ok(Some(Osc52Action))` when it is a valid `52;...` sequence, `Ok(None)` when it is
/// a different OSC number, or `Err(...)` when malformed or oversized.
pub fn parse_osc52_body(
    raw: &[u8],
    policy: Osc52Policy,
) -> Result<Option<Osc52Action>, &'static str> {
    let Some(after_52) = raw.strip_prefix(b"52;") else {
        return Ok(None);
    };
    if raw.len() > MAX_OSC52_RAW_BYTES {
        return Err("OSC 52 sequence exceeds MAX_OSC52_RAW_BYTES");
    }
    let mut semi_pos: Option<usize> = None;
    let mut i = 0usize;
    while let Some(&b) = after_52.get(i) {
        if b == b';' {
            semi_pos = Some(i);
            break;
        }
        i = i.saturating_add(1);
    }
    let Some(split_idx) = semi_pos else {
        return Err("OSC 52 missing payload separator ';'");
    };
    let Some(targets_raw) = after_52.get(..split_idx) else {
        return Err("OSC 52 invalid target slice");
    };
    let Some(b64_raw) = after_52.get(split_idx.saturating_add(1)..) else {
        return Err("OSC 52 invalid payload slice");
    };
    let target_mask = parse_target_mask(targets_raw);

    if b64_raw.is_empty() {
        return Ok(Some(Osc52Action::ClearClipboard { target_mask }));
    }
    if b64_raw == b"?" {
        if policy.allow_query {
            return Ok(Some(Osc52Action::QueryClipboard { target_mask }));
        }
        return Ok(Some(Osc52Action::QueryDenied { target_mask }));
    }

    let cap = osc52_bytes_clamp(
        policy.max_decoded_bytes as u64,
        MAX_OSC52_DECODED_BYTES as u64,
    ) as usize;
    let mut decoded = match base64_decode_bounded(b64_raw, cap) {
        Ok(d) => d,
        Err(e) => return Err(e),
    };
    if !osc52_payload_within_cap(decoded.len(), cap) {
        return Err("decoded OSC 52 payload exceeds policy cap");
    }
    if policy.strip_unsafe_controls {
        decoded = sanitize_clipboard_bytes(&decoded);
    }
    Ok(Some(Osc52Action::SetClipboard {
        target_mask,
        bytes: decoded,
    }))
}

/// Format a complete `\x1b]52;<targets>;<base64>\x07` sequence for `payload`.
pub fn encode_osc52_set(targets: &[u8], payload: &[u8]) -> Result<Vec<u8>, &'static str> {
    if !osc52_payload_within_cap(payload.len(), MAX_OSC52_DECODED_BYTES) {
        return Err("payload exceeds MAX_OSC52_DECODED_BYTES");
    }
    let tgt = if targets.is_empty() {
        b"c".as_slice()
    } else {
        let mut check = targets;
        while let &[b, ref tail @ ..] = check {
            let valid =
                b == b'c' || b == b'p' || b == b'q' || b == b's' || (b >= b'0' && b <= b'7');
            if !valid {
                return Err("invalid OSC 52 target character");
            }
            check = tail;
        }
        targets
    };
    let b64 = base64_encode(payload);
    let raw_cap = b64.len().saturating_add(tgt.len()).saturating_add(6);
    let cap = if raw_cap < MAX_OSC52_RAW_BYTES {
        raw_cap
    } else {
        MAX_OSC52_RAW_BYTES
    };
    let mut out = {
        let _ = cap;
        Vec::new()
    };
    out.extend_from_slice(b"\x1b]52;");
    out.extend_from_slice(tgt);
    out.push(b';');
    out.extend_from_slice(&b64);
    out.push(0x07);
    Ok(out)
}

fn parse_target_mask(raw: &[u8]) -> u64 {
    if raw.is_empty() {
        return OSC52_TARGET_CLIPBOARD;
    }
    let mut mask = 0u64;
    let mut rest = raw;
    while let &[b, ref tail @ ..] = rest {
        let bit = match b {
            b'c' => OSC52_TARGET_CLIPBOARD,
            b'p' => OSC52_TARGET_PRIMARY,
            b'q' => OSC52_TARGET_SECONDARY,
            b's' => OSC52_TARGET_SELECT,
            b'0' => 1u64 << 4,
            b'1' => 1u64 << 5,
            b'2' => 1u64 << 6,
            b'3' => 1u64 << 7,
            b'4' => 1u64 << 8,
            b'5' => 1u64 << 9,
            b'6' => 1u64 << 10,
            b'7' => 1u64 << 11,
            _ => 0,
        };
        mask = mask | (bit);
        rest = tail;
    }
    if mask == 0 {
        mask = OSC52_TARGET_CLIPBOARD;
    }
    osc52_target_mask_clamp(mask, MAX_OSC52_TARGET_MASK)
}

fn sanitize_clipboard_bytes(src: &[u8]) -> Vec<u8> {
    let cap = if src.len() < MAX_OSC52_DECODED_BYTES {
        src.len()
    } else {
        MAX_OSC52_DECODED_BYTES
    };
    let mut out = {
        let _ = cap;
        Vec::new()
    };
    let mut i = 0usize;
    while let Some(&b) = src.get(i) {
        if b == b'\t' || b == b'\n' || (b >= 0x20 && b <= 0x7E) {
            out.push(b);
            i = i.saturating_add(1);
            continue;
        }
        if b < 0x80 {
            i = i.saturating_add(1);
            continue;
        }
        if b == 0xC2 {
            if let Some(&b2) = src.get(i.saturating_add(1)) {
                if b2 >= 0x80 && b2 <= 0x9F {
                    // Strip UTF-8 C1 control (`U+0080..=U+009F`).
                    i = i.saturating_add(2);
                    continue;
                }
                if b2 >= 0xA0 && b2 <= 0xBF {
                    out.push(b);
                    out.push(b2);
                    i = i.saturating_add(2);
                    continue;
                }
            }
            i = i.saturating_add(1);
            continue;
        }
        let width = if b >= 0xC3 && b <= 0xDF {
            2usize
        } else if b >= 0xE0 && b <= 0xEF {
            3usize
        } else if b >= 0xF0 && b <= 0xF4 {
            4usize
        } else {
            0usize
        };
        if width >= 2 {
            if let Some(seq) = src.get(i..i.saturating_add(width)) {
                if core::str::from_utf8(seq).is_ok() {
                    out.extend_from_slice(seq);
                    i = i.saturating_add(width);
                    continue;
                }
            }
        }
        i = i.saturating_add(1);
    }
    out
}

fn b64_val(b: u8) -> Result<u8, &'static str> {
    if b >= b'A' && b <= b'Z' {
        Ok(b.saturating_sub(b'A'))
    } else if b >= b'a' && b <= b'z' {
        Ok(b.saturating_sub(b'a').saturating_add(26))
    } else if b >= b'0' && b <= b'9' {
        Ok(b.saturating_sub(b'0').saturating_add(52))
    } else if b == b'+' {
        Ok(62)
    } else if b == b'/' {
        Ok(63)
    } else {
        Err("invalid base64 character")
    }
}

fn base64_decode_bounded(raw: &[u8], max_out: usize) -> Result<Vec<u8>, &'static str> {
    // Strip optional ASCII whitespace inside base64 (xterm permits folded base64).
    let clean_cap = if raw.len() < MAX_OSC52_RAW_BYTES {
        raw.len()
    } else {
        MAX_OSC52_RAW_BYTES
    };
    let mut clean = {
        let _ = clean_cap;
        Vec::new()
    };
    let mut raw_rest = raw;
    while let &[b, ref tail @ ..] = raw_rest {
        if b != b' ' && b != b'\n' && b != b'\r' && b != b'\t' {
            clean.push(b);
        }
        raw_rest = tail;
    }
    if clean.is_empty() {
        return Ok(Vec::new());
    }
    if clean.len() % 4 != 0 {
        return Err("base64 length must be a multiple of 4");
    }
    let mut out = Vec::new();
    let mut rest = clean.as_slice();
    while let &[c0, c1, c2, c3, ref tail @ ..] = rest {
        let is_last = tail.is_empty();

        let v0 = match b64_val(c0) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let v1 = match b64_val(c1) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        if out.len() >= max_out {
            return Err("decoded OSC 52 payload exceeds cap");
        }
        out.push((v0 << 2) | (v1 >> 4));

        if c2 == b'=' {
            if !is_last || c3 != b'=' || (v1 & 0x0F) != 0 {
                return Err("invalid base64 padding");
            }
        } else {
            let v2 = match b64_val(c2) {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            if out.len() >= max_out {
                return Err("decoded OSC 52 payload exceeds cap");
            }
            out.push((v1 << 4) | (v2 >> 2));
            if c3 == b'=' {
                if !is_last || (v2 & 0x03) != 0 {
                    return Err("invalid base64 padding");
                }
            } else {
                let v3 = match b64_val(c3) {
                    Ok(v) => v,
                    Err(e) => return Err(e),
                };
                if out.len() >= max_out {
                    return Err("decoded OSC 52 payload exceeds cap");
                }
                out.push((v2 << 6) | v3);
            }
        }
        rest = tail;
    }
    Ok(out)
}

const fn b64_char(idx6: u8) -> u8 {
    match idx6 & 0x3F {
        x @ 0..=25 => b'A'.saturating_add(x),
        x @ 26..=51 => b'a'.saturating_add(x.saturating_sub(26)),
        x @ 52..=61 => b'0'.saturating_add(x.saturating_sub(52)),
        62 => b'+',
        _ => b'/',
    }
}

fn base64_encode(src: &[u8]) -> Vec<u8> {
    let out_cap = ((src.len().saturating_add(2)) / 3).saturating_mul(4);
    let bounded_cap = if out_cap < MAX_OSC52_RAW_BYTES {
        out_cap
    } else {
        MAX_OSC52_RAW_BYTES
    };
    let mut out = {
        let _ = bounded_cap;
        Vec::new()
    };
    let mut rest = src;
    while let &[b0, b1, b2, ref tail @ ..] = rest {
        out.push(b64_char(b0 >> 2));
        out.push(b64_char(((b0 & 0x03) << 4) | (b1 >> 4)));
        out.push(b64_char(((b1 & 0x0F) << 2) | (b2 >> 6)));
        out.push(b64_char(b2 & 0x3F));
        rest = tail;
    }
    if let &[b0] = rest {
        out.push(b64_char(b0 >> 2));
        out.push(b64_char((b0 & 0x03) << 4));
        out.push(b'=');
        out.push(b'=');
    } else if let &[b0, b1] = rest {
        out.push(b64_char(b0 >> 2));
        out.push(b64_char(((b0 & 0x03) << 4) | (b1 >> 4)));
        out.push(b64_char((b1 & 0x0F) << 2));
        out.push(b'=');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn denies_query_by_default_strips_escape_injection_and_round_trips_base64() {
        let policy = Osc52Policy::default();

        // `?` readback probe is denied by default!
        assert_eq!(
            parse_osc52_body(b"52;c;?", policy).unwrap(),
            Some(Osc52Action::QueryDenied {
                target_mask: OSC52_TARGET_CLIPBOARD
            })
        );

        // Encode & decode round-trip with escape injection sanitized.
        let encoded = encode_osc52_set(b"cp", b"hello\x1b[2J\nworld").unwrap();
        // Strip `\x1b]` and `\x07` as the VT OSC parser hands it over.
        let body = &encoded[2..encoded.len() - 1];
        assert_eq!(
            parse_osc52_body(body, policy).unwrap(),
            Some(Osc52Action::SetClipboard {
                target_mask: OSC52_TARGET_CLIPBOARD | OSC52_TARGET_PRIMARY,
                bytes: b"hello[2J\nworld".to_vec(),
            })
        );

        // Clear clipboard (`52;c;`).
        assert_eq!(
            parse_osc52_body(b"52;c;", policy).unwrap(),
            Some(Osc52Action::ClearClipboard {
                target_mask: OSC52_TARGET_CLIPBOARD
            })
        );
    }

    #[test]
    fn rejects_invalid_targets_noncanonical_base64_and_c1_injections() {
        let policy = Osc52Policy::default();
        assert!(encode_osc52_set(b"c;evil", b"hi").is_err());
        // Non-zero pad bits in `QUJ=` (`v2 = 9`, `v2 & 0x03 != 0`) and `AB==` (`v1 = 1`, `v1 & 0x0F != 0`).
        assert!(parse_osc52_body(b"52;c;QUJ=", policy).is_err());
        assert!(parse_osc52_body(b"52;c;AB==", policy).is_err());

        // UTF-8 C1 (`0xC2 0x9B`) and bare 8-bit C1 (`0x9B`) are stripped while valid UTF-8 (`€`) stays intact.
        let raw_payload = b"ok\xc2\x9b2J\x9b!\xe2\x82\xac";
        let enc = encode_osc52_set(b"c", raw_payload).unwrap();
        let body = &enc[2..enc.len() - 1];
        assert_eq!(
            parse_osc52_body(body, policy).unwrap(),
            Some(Osc52Action::SetClipboard {
                target_mask: OSC52_TARGET_CLIPBOARD,
                bytes: b"ok2J!\xe2\x82\xac".to_vec(),
            })
        );
    }
}
