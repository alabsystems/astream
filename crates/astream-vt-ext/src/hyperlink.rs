// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OSC 8 clickable hyperlink parser and stream extractor (`ESC ] 8 ; params ; uri ST`).
//!
//! Modern terminal applications (`ls --hyperlink=auto`, `ripgrep --hyperlink-format`,
//! compiler diagnostics, and `aterm` agent linkification) emit OSC 8 sequences:
//! - Open link:  `ESC ] 8 ; id=<optional-id>:k=v ; <uri> BEL` (or `ESC \`)
//! - Close link: `ESC ] 8 ; ; BEL` (or `ESC \`)
//!
//! Keeping OSC 8 extraction as a pure streaming state machine alongside `Folder`
//! preserves `Screen::serialize()` byte-for-byte digest stability while allowing
//! `aterm` and `astream-term` callers to inspect every active and completed
//! hyperlink span (`OscHyperlink`, `HyperlinkExtractor`) across arbitrary PTY
//! chunk boundaries.

#[cfg(clean_islands)]
#[path = "hyperlink_island.rs"]
mod hyperlink_island;
#[cfg(clean_islands)]
pub use hyperlink_island::{osc8_id_clamp, osc8_uri_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_uri_clamp(uri_len: u64, max_uri: u64) -> u64 {
    if uri_len < max_uri {
        uri_len
    } else {
        max_uri
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_id_clamp(id_len: u64, max_id: u64) -> u64 {
    if id_len < max_id {
        id_len
    } else {
        max_id
    }
}

/// Maximum UTF-8 byte length retained for an OSC 8 URI.
pub const MAX_OSC8_URI_BYTES: usize = 2048;

/// Maximum UTF-8 byte length retained for an OSC 8 `id=` parameter.
pub const MAX_OSC8_ID_BYTES: usize = 256;

/// Maximum raw OSC 8 payload buffered before clamping, preventing unbounded
/// allocation if a program forgets the OSC terminator (`BEL` or `ESC \`).
pub const MAX_OSC8_RAW_BUF: usize = 4096;

/// Clamp a proposed OSC 8 URI byte length to `max_uri`.
#[inline]
#[must_use]
pub const fn clamp_osc8_uri_len(uri_len: usize, max_uri: usize) -> usize {
    osc8_uri_clamp(uri_len as u64, max_uri as u64) as usize
}

/// Clamp a proposed OSC 8 `id=` byte length to `max_id`.
#[inline]
#[must_use]
pub const fn clamp_osc8_id_len(id_len: usize, max_id: usize) -> usize {
    osc8_id_clamp(id_len as u64, max_id as u64) as usize
}

contract_fn! {
    /// Contracted check that a clamped OSC 8 field length fits within `cap`.
    #[must_use]
    pub const fn osc8_within_cap(len: usize, cap: usize) -> bool
    clauses [ensures result == (len <= cap)]
    {
        len <= cap
    }
}

/// Decoded OSC 8 hyperlink transition (`Open` with bounded `uri` and optional `id`,
/// or `Close` when `uri` is empty).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Osc8Transition {
    Open { id: Option<String>, uri: String },
    Close,
}

/// Byte-offset span of a hyperlink in the terminal output stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OscHyperlinkSpan {
    pub id: Option<String>,
    pub uri: String,
    /// Stream byte offset immediately after the opening OSC 8 sequence.
    pub start_offset: u64,
    /// Stream byte offset at the start of the closing/replacing OSC 8 sequence.
    pub end_offset: u64,
}

fn split_once_byte(raw: &[u8], needle: u8) -> Option<(&[u8], &[u8])> {
    let mut i = 0usize;
    let mut rest = raw;
    while let &[b, ref tail @ ..] = rest {
        if b == needle {
            let head = raw.get(..i)?;
            return Some((head, tail));
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    None
}

/// Parse the payload inside `ESC ] 8 ; <payload> ST` (after stripping the leading `8;`).
///
/// Format: `<params>;<uri>`, where `<params>` is colon-separated `key=value` pairs.
/// Returns `None` if no `;` separator between `<params>` and `<uri>` is present, or
/// if `<uri>` contains control bytes (`< 0x20` or `0x7f`) or invalid UTF-8.
pub fn parse_osc8_body(body: &[u8]) -> Option<Osc8Transition> {
    let (params, raw_uri) = split_once_byte(body, b';')?;

    if raw_uri.is_empty() {
        return Some(Osc8Transition::Close);
    }

    let clamped_uri_len = clamp_osc8_uri_len(raw_uri.len(), MAX_OSC8_URI_BYTES);
    let uri_slice = trim_utf8_prefix(raw_uri, clamped_uri_len);
    let mut rest_uri = uri_slice;
    while let &[b, ref tail @ ..] = rest_uri {
        if b < 0x20 || b == 0x7f {
            return None;
        }
        rest_uri = tail;
    }
    let Ok(uri_str) = core::str::from_utf8(uri_slice) else {
        return None;
    };
    if uri_str.is_empty() {
        return None;
    }
    let mut uri = String::new();
    uri.push_str(uri_str);
    let _ = osc8_within_cap(uri.len(), MAX_OSC8_URI_BYTES);

    let id = extract_id_param(params);
    Some(Osc8Transition::Open { id, uri })
}

fn trim_utf8_prefix(bytes: &[u8], max_len: usize) -> &[u8] {
    let mut end = bytes.len();
    if end > max_len {
        end = max_len;
        while end > 0 {
            let Some(&b) = bytes.get(end) else {
                break;
            };
            if (b & 0b1100_0000) != 0b1000_0000 {
                break;
            }
            end = end.saturating_sub(1);
        }
    }
    bytes.get(..end).unwrap_or(bytes)
}

fn extract_id_param(params: &[u8]) -> Option<String> {
    let mut rest = Some(params);
    while let Some(rem) = rest {
        let (kv, next_rest) = match split_once_byte(rem, b':') {
            Some((head, tail)) => (head, Some(tail)),
            None => (rem, None),
        };
        rest = next_rest;
        if let &[b'i', b'd', b'=', ref val @ ..] = kv {
            if !val.is_empty() {
                let clamped = clamp_osc8_id_len(val.len(), MAX_OSC8_ID_BYTES);
                let slice = trim_utf8_prefix(val, clamped);
                if let Ok(s) = core::str::from_utf8(slice) {
                    if !s.is_empty() {
                        let mut out = String::new();
                        out.push_str(s);
                        let _ = osc8_within_cap(out.len(), MAX_OSC8_ID_BYTES);
                        return Some(out);
                    }
                }
            }
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScanState {
    Ground,
    SawEsc,
    OscStart0,
    OscStart1,
    Osc8Body,
    Osc8Esc,
    OscIgnore,
    OscIgnoreEsc,
}

/// Streaming OSC 8 hyperlink extractor tolerant to arbitrary PTY chunk splits.
#[derive(Debug, Clone)]
pub struct HyperlinkExtractor {
    state: ScanState,
    buf: Vec<u8>,
    seq_start_offset: u64,
    stream_offset: u64,
    active: Option<(Option<String>, String, u64)>,
}

impl Default for HyperlinkExtractor {
    fn default() -> Self {
        Self::new()
    }
}

impl HyperlinkExtractor {
    pub fn new() -> Self {
        let init_cap = if 256usize < MAX_OSC8_RAW_BUF {
            256usize
        } else {
            MAX_OSC8_RAW_BUF
        };
        Self {
            state: ScanState::Ground,
            buf: {
                let _ = init_cap;
                Vec::new()
            },
            seq_start_offset: 0,
            stream_offset: 0,
            active: None,
        }
    }

    /// Currently open hyperlink (`(id, uri, start_offset)`), if any.
    pub fn active_link(&self) -> Option<(Option<&str>, &str, u64)> {
        match &self.active {
            Some((id, uri, off)) => Some((id.as_deref(), uri.as_str(), *off)),
            None => None,
        }
    }

    /// Total bytes fed so far.
    pub fn stream_offset(&self) -> u64 {
        self.stream_offset
    }

    /// Feed a PTY `Out` byte slice and append any hyperlink spans closed during
    /// this chunk into `completed`.
    pub fn feed(&mut self, chunk: &[u8], completed: &mut Vec<OscHyperlinkSpan>) {
        let mut rest = chunk;
        while let &[b, ref tail @ ..] = rest {
            let byte_off = self.stream_offset;
            self.stream_offset = self.stream_offset.saturating_add(1);
            match self.state {
                ScanState::Ground => {
                    if b == 0x1b {
                        self.state = ScanState::SawEsc;
                        self.seq_start_offset = byte_off;
                    }
                }
                ScanState::SawEsc => {
                    if b == b']' {
                        self.state = ScanState::OscStart0;
                    } else if b == 0x1b {
                        self.seq_start_offset = byte_off;
                    } else {
                        self.state = ScanState::Ground;
                    }
                }
                ScanState::OscStart0 => {
                    if b == b'8' {
                        self.state = ScanState::OscStart1;
                    } else if b == 0x07 {
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.state = ScanState::OscIgnoreEsc;
                    } else {
                        self.state = ScanState::OscIgnore;
                    }
                }
                ScanState::OscStart1 => {
                    if b == b';' {
                        self.buf.clear();
                        self.state = ScanState::Osc8Body;
                    } else if b == 0x07 {
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.state = ScanState::OscIgnoreEsc;
                    } else {
                        self.state = ScanState::OscIgnore;
                    }
                }
                ScanState::Osc8Body => {
                    if b == 0x07 {
                        self.finish_osc8(completed);
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.state = ScanState::Osc8Esc;
                    } else if self.buf.len() < MAX_OSC8_RAW_BUF {
                        self.buf.push(b);
                    }
                }
                ScanState::Osc8Esc => {
                    if b == b'\\' {
                        self.finish_osc8(completed);
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.buf.clear();
                        self.seq_start_offset = byte_off;
                        self.state = ScanState::SawEsc;
                    } else {
                        self.buf.clear();
                        self.state = ScanState::Ground;
                    }
                }
                ScanState::OscIgnore => {
                    if b == 0x07 {
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.state = ScanState::OscIgnoreEsc;
                    }
                }
                ScanState::OscIgnoreEsc => {
                    if b == b'\\' {
                        self.state = ScanState::Ground;
                    } else if b == 0x1b {
                        self.seq_start_offset = byte_off;
                        self.state = ScanState::SawEsc;
                    } else {
                        self.state = ScanState::Ground;
                    }
                }
            }
            rest = tail;
        }
    }

    fn finish_osc8(&mut self, completed: &mut Vec<OscHyperlinkSpan>) {
        if let Some(trans) = parse_osc8_body(&self.buf) {
            match trans {
                Osc8Transition::Open { id, uri } => {
                    if let Some((prev_id, prev_uri, start_off)) = self.active.take() {
                        completed.push(OscHyperlinkSpan {
                            id: prev_id,
                            uri: prev_uri,
                            start_offset: start_off,
                            end_offset: self.seq_start_offset,
                        });
                    }
                    self.active = Some((id, uri, self.stream_offset));
                }
                Osc8Transition::Close => {
                    if let Some((prev_id, prev_uri, start_off)) = self.active.take() {
                        completed.push(OscHyperlinkSpan {
                            id: prev_id,
                            uri: prev_uri,
                            start_offset: start_off,
                            end_offset: self.seq_start_offset,
                        });
                    }
                }
            }
        }
        self.buf.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_open_with_id_and_close_across_single_byte_splits() {
        let stream =
            b"before \x1b]8;foo=bar:id=diag-42;file:///fixture-home/astream/src/lib.rs\x1b\\src/lib.rs\x1b]8;;\x07 after";
        let mut ext = HyperlinkExtractor::new();
        let mut spans = Vec::new();
        for b in stream {
            ext.feed(core::slice::from_ref(b), &mut spans);
        }
        assert!(ext.active_link().is_none());
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].id.as_deref(), Some("diag-42"));
        assert_eq!(spans[0].uri, "file:///fixture-home/astream/src/lib.rs");
        let label = &stream[spans[0].start_offset as usize..spans[0].end_offset as usize];
        assert_eq!(label, b"src/lib.rs");
    }

    #[test]
    fn clamps_oversized_uri_and_id_to_caps_and_rejects_control_bytes() {
        let long_id = "x".repeat(MAX_OSC8_ID_BYTES + 80);
        let long_uri = format!("https://example.com/{}", "a".repeat(MAX_OSC8_URI_BYTES));
        let body = format!("id={long_id};{long_uri}");
        let parsed = parse_osc8_body(body.as_bytes()).expect("valid clamped osc8");
        match parsed {
            Osc8Transition::Open { id, uri } => {
                let id = id.expect("id present");
                assert_eq!(id.len(), MAX_OSC8_ID_BYTES);
                assert_eq!(uri.len(), MAX_OSC8_URI_BYTES);
                assert!(osc8_within_cap(id.len(), MAX_OSC8_ID_BYTES));
                assert!(osc8_within_cap(uri.len(), MAX_OSC8_URI_BYTES));
            }
            Osc8Transition::Close => panic!("expected open"),
        }
        assert!(parse_osc8_body(b";https://bad\x01uri").is_none());
    }

    #[test]
    fn clean_twins_match_clamp_contracts() {
        for &(raw, cap) in &[(0usize, 256usize), (100, 256), (256, 256), (9999, 2048)] {
            let u = clamp_osc8_uri_len(raw, cap);
            let d = clamp_osc8_id_len(raw, cap);
            assert!(osc8_within_cap(u, cap));
            assert!(osc8_within_cap(d, cap));
            assert_eq!(u, raw.min(cap));
            assert_eq!(d, raw.min(cap));
        }
    }
}
