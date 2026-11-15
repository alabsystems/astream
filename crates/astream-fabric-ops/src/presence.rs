// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Canonical `DESIGN-aterm-fabric.md` §4.2 session & node presence row codec (`V1PresenceRow`)
//! with Clean-verified field & watcher count clamping (`Astream.Broker.TlaPresenceRow`).
//!
//! Completes the `DESIGNED` §4.2 / §15 presence schema (`role`, `detail`, `phase`, `title`,
//! `driving`, `watchers`, `parent`, `host`, `pid`) in a zero-dependency, `0 runtime_checked`
//! `key=value` wire format compatible with `aterm-link`'s token grammar.

#![allow(clippy::manual_is_ascii_check, clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "presence_island.rs"]
mod presence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn presence_watchers_clamp(count: u64, max_watchers: u64) -> u64 {
    if count < max_watchers {
        count
    } else {
        max_watchers
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn presence_field_clamp(field_len: u64, max_len: u64) -> u64 {
    if field_len < max_len {
        field_len
    } else {
        max_len
    }
}
#[cfg(clean_islands)]
pub use presence_island::{presence_field_clamp, presence_watchers_clamp};

/// Maximum encoded byte length of a single §4.2 `V1PresenceRow` line.
pub const MAX_PRESENCE_ROW_BYTES: usize = 1024;

/// Maximum UTF-8 byte length of any single text field (`role`, `detail`, `phase`, `title`, `driving`, `parent`, `host`).
pub const MAX_PRESENCE_FIELD_BYTES: usize = 128;

/// Maximum reported watcher count on a session presence row.
pub const MAX_PRESENCE_WATCHERS: u64 = 4096;

contract_fn! {
    /// Kernel-certified row byte-budget check (`len <= max_len`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `presence_row_within_cap_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn presence_row_within_cap(len: usize, max_len: usize) -> bool
    clauses [ensures result == (len <= max_len)]
    {
        len <= max_len
    }
}

/// Errors returned when decoding or validating a [`V1PresenceRow`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PresenceError {
    /// Row exceeds [`MAX_PRESENCE_ROW_BYTES`] or is empty.
    LengthOutOfBounds,
    /// Missing `v=1` header token or malformed `key=value` token.
    MalformedToken,
    /// Repeated key in the same presence row.
    DuplicateField,
    /// Invalid percent-escape or non-UTF-8 decoded value.
    InvalidEncoding,
}

/// Canonical `DESIGN-aterm-fabric.md` §4.2 session/node presence row (`v=1`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct V1PresenceRow {
    /// Session role (e.g. `"worker"`, `"reviewer"`, `"shell"`).
    pub role: Option<String>,
    /// Short task/role detail.
    pub detail: Option<String>,
    /// Execution phase (e.g. `"running"`, `"idle"`, `"blocked"`, `"exited"`).
    pub phase: Option<String>,
    /// Sanitized terminal window/tab title.
    pub title: Option<String>,
    /// Principal or session currently driving this session (`driving=<id>` or `None` for `-`).
    pub driving: Option<String>,
    /// Clamped count of active live watchers (`<= MAX_PRESENCE_WATCHERS`).
    pub watchers: u64,
    /// Optional parent session/supervisor identifier (`parent=<sid>`).
    pub parent: Option<String>,
    /// Node hostname (`host=<name>` on node/session rows).
    pub host: Option<String>,
    /// OS process identifier (`pid=<u32>`).
    pub pid: Option<u32>,
}

impl V1PresenceRow {
    /// Construct an empty `v=1` presence row.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Encode this row into canonical space-separated `v=1 key=pct_encoded_val ...` bytes,
    /// clamping text fields via [`presence_field_clamp`] and `watchers` via
    /// [`presence_watchers_clamp`].
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let init_cap = if MAX_PRESENCE_ROW_BYTES < 256 {
            MAX_PRESENCE_ROW_BYTES
        } else {
            256
        };
        let mut out = {
            let _ = init_cap;
            Vec::new()
        };
        out.extend_from_slice(b"v=1");
        append_opt_str(&mut out, b"role", self.role.as_deref());
        append_opt_str(&mut out, b"detail", self.detail.as_deref());
        append_opt_str(&mut out, b"phase", self.phase.as_deref());
        append_opt_str(&mut out, b"title", self.title.as_deref());
        append_opt_str(&mut out, b"driving", self.driving.as_deref());
        let clamped_w = presence_watchers_clamp(self.watchers, MAX_PRESENCE_WATCHERS);
        out.extend_from_slice(b" watchers=");
        append_decimal_u64(&mut out, clamped_w);
        append_opt_str(&mut out, b"parent", self.parent.as_deref());
        append_opt_str(&mut out, b"host", self.host.as_deref());
        if let Some(p) = self.pid {
            out.extend_from_slice(b" pid=");
            append_decimal_u64(&mut out, p as u64);
        }
        out
    }

    /// Decode and validate a `v=1` §4.2 presence row from `raw`.
    pub fn decode(raw: &[u8]) -> Result<Self, PresenceError> {
        if raw.is_empty() || !presence_row_within_cap(raw.len(), MAX_PRESENCE_ROW_BYTES) {
            return Err(PresenceError::LengthOutOfBounds);
        }
        if core::str::from_utf8(raw).is_err() {
            return Err(PresenceError::InvalidEncoding);
        }
        let (first, mut rem) = split_first_space(raw);
        if first != b"v=1" {
            return Err(PresenceError::MalformedToken);
        }

        let mut row = Self::new();
        let mut saw_watchers = false;
        let mut saw_pid = false;

        while let Some(after_sp) = rem {
            if after_sp.is_empty() {
                return Err(PresenceError::MalformedToken);
            }
            let (tok, next_rem) = split_first_space(after_sp);
            rem = next_rem;
            if tok.is_empty() {
                return Err(PresenceError::MalformedToken);
            }
            let Some((k, v)) = split_eq_once(tok) else {
                return Err(PresenceError::MalformedToken);
            };
            if k == b"role" {
                if row.role.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.role = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"detail" {
                if row.detail.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.detail = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"phase" {
                if row.phase.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.phase = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"title" {
                if row.title.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.title = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"driving" {
                if row.driving.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.driving = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"watchers" {
                if saw_watchers {
                    return Err(PresenceError::DuplicateField);
                }
                saw_watchers = true;
                let Some(w) = parse_u64_digits(v) else {
                    return Err(PresenceError::MalformedToken);
                };
                row.watchers = presence_watchers_clamp(w, MAX_PRESENCE_WATCHERS);
            } else if k == b"parent" {
                if row.parent.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.parent = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"host" {
                if row.host.is_some() {
                    return Err(PresenceError::DuplicateField);
                }
                row.host = match decode_opt_field_bytes(v) {
                    Ok(val) => val,
                    Err(e) => return Err(e),
                };
            } else if k == b"pid" {
                if saw_pid {
                    return Err(PresenceError::DuplicateField);
                }
                saw_pid = true;
                let Some(p64) = parse_u64_digits(v) else {
                    return Err(PresenceError::MalformedToken);
                };
                if p64 > u32::MAX as u64 {
                    return Err(PresenceError::MalformedToken);
                }
                row.pid = Some(p64 as u32);
            } else {
                return Err(PresenceError::MalformedToken);
            }
        }
        Ok(row)
    }
}

const fn find_byte_pos(mut rest: &[u8], needle: u8) -> Option<usize> {
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

fn split_first_space(bytes: &[u8]) -> (&[u8], Option<&[u8]>) {
    let Some(i) = find_byte_pos(bytes, b' ') else {
        return (bytes, None);
    };
    let Some(next) = i.checked_add(1) else {
        return (bytes, None);
    };
    let head = match bytes.get(..i) {
        Some(h) => h,
        None => bytes,
    };
    let tail = bytes.get(next..);
    (head, tail)
}

fn split_eq_once(bytes: &[u8]) -> Option<(&[u8], &[u8])> {
    let Some(i) = find_byte_pos(bytes, b'=') else {
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

fn truncate_utf8_clamped(s: &str) -> &[u8] {
    let bytes = s.as_bytes();
    let cap = presence_field_clamp(bytes.len() as u64, MAX_PRESENCE_FIELD_BYTES as u64) as usize;
    let mut end = if cap < bytes.len() { cap } else { bytes.len() };
    while end > 0 {
        let is_cont = match bytes.get(end) {
            Some(&b) => (b & 0xC0) == 0x80,
            None => false,
        };
        if !is_cont {
            break;
        }
        end = end.saturating_sub(1);
    }
    match bytes.get(..end) {
        Some(sub) => sub,
        None => &[],
    }
}

fn append_opt_str(out: &mut Vec<u8>, key: &[u8], val: Option<&str>) {
    let Some(v) = val else {
        return;
    };
    let clamped = truncate_utf8_clamped(v);
    if clamped.is_empty() {
        return;
    }
    out.push(b' ');
    out.extend_from_slice(key);
    out.push(b'=');
    if clamped == b"-" {
        out.extend_from_slice(b"%2d");
        return;
    }
    let mut rest = clamped;
    while let &[b, ref tail @ ..] = rest {
        if is_safe_token_byte(b) {
            out.push(b);
        } else {
            out.push(b'%');
            out.push(hex_lower(b >> 4));
            out.push(hex_lower(b & 0x0f));
        }
        rest = tail;
    }
}

const fn is_safe_token_byte(b: u8) -> bool {
    matches!(b, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'/')
}

const fn hex_lower(nib: u8) -> u8 {
    match nib & 0x0f {
        0 => b'0',
        1 => b'1',
        2 => b'2',
        3 => b'3',
        4 => b'4',
        5 => b'5',
        6 => b'6',
        7 => b'7',
        8 => b'8',
        9 => b'9',
        10 => b'a',
        11 => b'b',
        12 => b'c',
        13 => b'd',
        14 => b'e',
        _ => b'f',
    }
}

const fn unhex(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a').saturating_add(10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A').saturating_add(10)),
        _ => None,
    }
}

fn decode_opt_field_bytes(mut bytes: &[u8]) -> Result<Option<String>, PresenceError> {
    if bytes == b"-" || bytes.is_empty() {
        return Ok(None);
    }
    let dec_cap = if bytes.len() < MAX_PRESENCE_FIELD_BYTES {
        bytes.len()
    } else {
        MAX_PRESENCE_FIELD_BYTES
    };
    let mut decoded = {
        let _ = dec_cap;
        Vec::new()
    };
    while let [b, rest @ ..] = bytes {
        if *b == b'%' {
            let [h, l, after @ ..] = rest else {
                return Err(PresenceError::InvalidEncoding);
            };
            let Some(hi) = unhex(*h) else {
                return Err(PresenceError::InvalidEncoding);
            };
            let Some(lo) = unhex(*l) else {
                return Err(PresenceError::InvalidEncoding);
            };
            decoded.push((hi << 4) | lo);
            bytes = after;
        } else {
            decoded.push(*b);
            bytes = rest;
        }
        if decoded.len() > MAX_PRESENCE_FIELD_BYTES {
            return Err(PresenceError::LengthOutOfBounds);
        }
    }
    let Ok(text) = core::str::from_utf8(&decoded) else {
        return Err(PresenceError::InvalidEncoding);
    };
    let mut out = String::new();
    out.push_str(text);
    Ok(Some(out))
}

fn append_decimal_u64(out: &mut Vec<u8>, mut n: u64) {
    if n == 0 {
        out.push(b'0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while n > 0 {
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add((n % 10) as u8);
            len = len.saturating_add(1);
        }
        n /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&d) = digits.get(len) {
            out.push(d);
        }
    }
}

const fn parse_u64_digits(mut bytes: &[u8]) -> Option<u64> {
    if bytes.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    while let [b, rest @ ..] = bytes {
        if !matches!(*b, b'0'..=b'9') {
            return None;
        }
        let Some(m) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = m.checked_add(b.saturating_sub(b'0') as u64) else {
            return None;
        };
        acc = next;
        bytes = rest;
    }
    Some(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_and_cap_predicate_hold() {
        assert_eq!(presence_watchers_clamp(12, MAX_PRESENCE_WATCHERS), 12);
        assert_eq!(
            presence_watchers_clamp(99_999, MAX_PRESENCE_WATCHERS),
            MAX_PRESENCE_WATCHERS
        );
        assert_eq!(presence_field_clamp(40, 128), 40);
        assert_eq!(presence_field_clamp(500, 128), 128);
        assert!(presence_row_within_cap(1024, MAX_PRESENCE_ROW_BYTES));
        assert!(!presence_row_within_cap(1025, MAX_PRESENCE_ROW_BYTES));
    }

    #[test]
    fn roundtrips_all_section_4_2_fields_including_driving_watchers_and_parent() {
        let row = V1PresenceRow {
            role: Some("worker".to_string()),
            detail: Some("auditing astream-broker".to_string()),
            phase: Some("running".to_string()),
            title: Some("claude: batch 19 = green".to_string()),
            driving: Some("a-supervisor".to_string()),
            watchers: 3,
            parent: Some("s-root01".to_string()),
            host: Some("mac-studio.local".to_string()),
            pid: Some(47298),
        };
        let wire = row.encode();
        let decoded = V1PresenceRow::decode(&wire).unwrap();
        assert_eq!(decoded, row);
    }

    #[test]
    fn clamps_watchers_and_rejects_duplicate_or_unknown_fields() {
        let mut row = V1PresenceRow::new();
        row.watchers = 999_999;
        row.driving = Some("-".to_string());
        let wire = row.encode();
        let decoded = V1PresenceRow::decode(&wire).unwrap();
        assert_eq!(decoded.watchers, MAX_PRESENCE_WATCHERS);
        // Literal `"-"` survives roundtrip without turning into `None`!
        assert_eq!(decoded.driving.as_deref(), Some("-"));

        // Explicit `driving=-` on wire decodes as `None`.
        let dash = V1PresenceRow::decode(b"v=1 driving=- watchers=2").unwrap();
        assert_eq!(dash.driving, None);
        assert_eq!(dash.watchers, 2);

        assert_eq!(
            V1PresenceRow::decode(b"v=1 role=a role=b"),
            Err(PresenceError::DuplicateField)
        );
        assert_eq!(
            V1PresenceRow::decode(b"v=1 unknown=1"),
            Err(PresenceError::MalformedToken)
        );
    }
}
