// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! MCP JSON-RPC 2.0 `Content-Length: <N>\r\n\r\n` stdio/pipe frame codec with pre-allocation cap
//! (`Astream.Mcp.TlaJsonrpcFrame`).

#[cfg(clean_islands)]
#[path = "jsonrpc_frame_island.rs"]
mod jsonrpc_frame_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_body_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mcp_rx_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use jsonrpc_frame_island::{mcp_body_clamp, mcp_rx_advance};

/// Hard ceiling on a single MCP JSON-RPC message body (`4` MiB).
pub const MAX_MCP_FRAME_BYTES: u64 = 4 * 1024 * 1024;

contract_fn! {
    /// Verified size check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mcp_frame_within_cap_isl`.
    #[must_use]
    pub const fn mcp_frame_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn push_usize_decimal(out: &mut Vec<u8>, mut n: usize) {
    if n == 0 {
        out.push(b'0');
        return;
    }
    let mut buf = [0u8; 20];
    let mut pos = 20usize;
    while n > 0 && pos > 0 {
        pos = pos.saturating_sub(1);
        if let Some(slot) = buf.get_mut(pos) {
            *slot = b'0'.saturating_add((n % 10) as u8);
        }
        n /= 10;
    }
    if let Some(slice) = buf.get(pos..) {
        out.extend_from_slice(slice);
    }
}

#[allow(clippy::question_mark)]
fn parse_ascii_u64(s: &str) -> Option<u64> {
    let b = s.as_bytes();
    if b.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < b.len() {
        let Some(&ch) = b.get(i) else {
            return None;
        };
        if !ch.is_ascii_digit() {
            return None;
        }
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(ch.saturating_sub(b'0') as u64) else {
            return None;
        };
        acc = next;
        i = i.saturating_add(1);
    }
    Some(acc)
}

#[must_use]
pub fn encode_jsonrpc_frame(json_utf8: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"Content-Length: ");
    push_usize_decimal(&mut out, json_utf8.len());
    out.extend_from_slice(b"\r\n\r\n");
    out.extend_from_slice(json_utf8);
    out
}

/// Incremental MCP `Content-Length` stream framer rejecting oversized declarations before buffering!
#[derive(Debug, Clone, Default)]
pub struct McpStreamFramer {
    max_body: u64,
    frames_decoded: u64,
}

impl McpStreamFramer {
    #[must_use]
    pub const fn new(max_body: u64) -> Self {
        let c = mcp_body_clamp(max_body, MAX_MCP_FRAME_BYTES);
        Self {
            max_body: if c == 0 { 65_536 } else { c },
            frames_decoded: 0,
        }
    }

    /// Returns `Ok(Some((body_slice, total_consumed)))` when a whole frame is available,
    /// `Ok(None)` when truncated, or `Err` on malformed/oversized `Content-Length`.
    pub fn try_decode<'a>(
        &mut self,
        buf: &'a [u8],
    ) -> Result<Option<(&'a [u8], usize)>, &'static str> {
        let mut sep_pos = None;
        let mut i = 0usize;
        while i.saturating_add(4) <= buf.len() {
            if buf.get(i..i.saturating_add(4)) == Some(b"\r\n\r\n") {
                sep_pos = Some(i);
                break;
            }
            i = i.saturating_add(1);
        }
        let Some(hdr_end) = sep_pos else {
            if buf.len() > 1024 {
                return Err("MCP header block exceeds 1024 bytes without CRLFCRLF");
            }
            return Ok(None);
        };
        let Some(hdr_bytes) = buf.get(..hdr_end) else {
            return Err("bad hdr");
        };
        let Ok(hdr_str) = core::str::from_utf8(hdr_bytes) else {
            return Err("non-UTF8 MCP header");
        };
        let mut content_len: Option<u64> = None;
        for line in hdr_str.split("\r\n") {
            if let Some((k, v)) = line.split_once(':') {
                if k.trim().eq_ignore_ascii_case("Content-Length") {
                    if content_len.is_some() {
                        return Err("duplicate Content-Length header");
                    }
                    let Some(parsed) = parse_ascii_u64(v.trim()) else {
                        return Err("bad Content-Length");
                    };
                    content_len = Some(parsed);
                }
            }
        }
        let Some(len) = content_len else {
            return Err("missing Content-Length header");
        };
        if !mcp_frame_within_cap(self.max_body, len) {
            return Err("MCP Content-Length exceeds max_body ceiling");
        }
        let body_start = hdr_end.saturating_add(4);
        let Some(total) = body_start.checked_add(len as usize) else {
            return Err("MCP frame overflow");
        };
        let Some(body) = buf.get(body_start..total) else {
            return Ok(None);
        };
        self.frames_decoded =
            mcp_rx_advance(self.frames_decoded, self.frames_decoded.saturating_add(1));
        Ok(Some((body, total)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mcp_framer_roundtrips_split_frames_and_rejects_oversized_length_headers() {
        let mut f = McpStreamFramer::new(1024);
        let wire = encode_jsonrpc_frame(br#"{"jsonrpc":"2.0","id":1,"method":"tools/list"}"#);
        assert!(f.try_decode(&wire[..10]).unwrap().is_none());
        let (body, used) = f.try_decode(&wire).unwrap().unwrap();
        assert_eq!(used, wire.len());
        assert!(body.starts_with(b"{\"jsonrpc\""));
        assert!(f.try_decode(b"Content-Length: 99999\r\n\r\n{}").is_err());
    }
}
