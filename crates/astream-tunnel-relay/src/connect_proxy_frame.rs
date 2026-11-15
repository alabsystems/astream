// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RFC 9110 §9.3.6 HTTP `CONNECT host:port HTTP/1.1` corporate-proxy tunnel request builder &
//! `200` status response parser (`Astream.Tunnel.TlaConnectProxyFrame`).
#![allow(clippy::question_mark, clippy::manual_range_contains)]

#[cfg(clean_islands)]
#[path = "connect_proxy_frame_island.rs"]
mod connect_proxy_frame_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_hdr_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tun_conn_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use connect_proxy_frame_island::{tun_conn_advance, tun_hdr_clamp};

/// Maximum HTTP `CONNECT` response header block (`8` KiB).
pub const MAX_CONNECT_HEADER_BYTES: u64 = 8_192;

contract_fn! {
    /// Verified `2xx` tunnel establishment (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tun_proxy_established_isl`.
    #[must_use]
    pub const fn tun_proxy_established(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Formats injection-safe `CONNECT` requests and parses `HTTP/1.x 200` replies.
#[derive(Debug, Clone, Default)]
pub struct HttpConnectTunnel {
    established_count: u64,
}

fn valid_connect_authority(authority: &str) -> bool {
    let bytes = authority.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut last_colon: Option<usize> = None;
    let mut idx = 0usize;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if b <= 0x20 || b == 0x7F || b == b'/' || b == b'\\' {
            return false;
        }
        if b == b':' {
            last_colon = Some(idx);
        }
        idx = idx.saturating_add(1);
    }
    let Some(colon_idx) = last_colon else {
        return false;
    };
    if colon_idx == 0 {
        return false;
    }
    let port_start = colon_idx.saturating_add(1);
    let Some(port_bytes) = bytes.get(port_start..) else {
        return false;
    };
    if port_bytes.is_empty() || port_bytes.len() > 5 {
        return false;
    }
    let mut port = 0u64;
    let mut p_idx = 0usize;
    while p_idx < port_bytes.len() {
        let Some(&b) = port_bytes.get(p_idx) else {
            break;
        };
        if !b.is_ascii_digit() {
            return false;
        }
        port = port
            .saturating_mul(10)
            .saturating_add(u64::from(b.saturating_sub(b'0')));
        p_idx = p_idx.saturating_add(1);
    }
    port >= 1 && port <= 65_535
}

fn find_crlfcrlf(buf: &[u8]) -> Option<usize> {
    let mut idx = 0usize;
    while idx.saturating_add(4) <= buf.len() {
        if buf.get(idx..idx.saturating_add(4)) == Some(b"\r\n\r\n") {
            return Some(idx);
        }
        idx = idx.saturating_add(1);
    }
    None
}

fn parse_http_status_code(head_bytes: &[u8]) -> Option<u64> {
    let mut line_end = head_bytes.len();
    let mut idx = 0usize;
    while idx < head_bytes.len() {
        if head_bytes.get(idx) == Some(&b'\n') || head_bytes.get(idx) == Some(&b'\r') {
            line_end = idx;
            break;
        }
        idx = idx.saturating_add(1);
    }
    let Some(line) = head_bytes.get(..line_end) else {
        return None;
    };
    if line.get(0..7) != Some(b"HTTP/1.") {
        return None;
    }
    let mut p = 0usize;
    while p < line.len() && line.get(p) != Some(&b' ') {
        p = p.saturating_add(1);
    }
    while p < line.len() && line.get(p) == Some(&b' ') {
        p = p.saturating_add(1);
    }
    let Some(&d0) = line.get(p) else {
        return None;
    };
    let Some(&d1) = line.get(p.saturating_add(1)) else {
        return None;
    };
    let Some(&d2) = line.get(p.saturating_add(2)) else {
        return None;
    };
    if !d0.is_ascii_digit() || !d1.is_ascii_digit() || !d2.is_ascii_digit() {
        return None;
    }
    let next = line.get(p.saturating_add(3));
    if next.is_some() && next != Some(&b' ') {
        return None;
    }
    let code = u64::from(d0.saturating_sub(b'0'))
        .saturating_mul(100)
        .saturating_add(u64::from(d1.saturating_sub(b'0')).saturating_mul(10))
        .saturating_add(u64::from(d2.saturating_sub(b'0')));
    Some(code)
}

impl HttpConnectTunnel {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            established_count: 0,
        }
    }

    pub fn format_request(authority: &str) -> Result<Vec<u8>, &'static str> {
        if !valid_connect_authority(authority) {
            return Err("invalid host:port authority for HTTP CONNECT");
        }
        let mut out = Vec::new();
        out.extend_from_slice(b"CONNECT ");
        out.extend_from_slice(authority.as_bytes());
        out.extend_from_slice(b" HTTP/1.1\r\nHost: ");
        out.extend_from_slice(authority.as_bytes());
        out.extend_from_slice(b"\r\n\r\n");
        Ok(out)
    }

    pub fn parse_response(&mut self, buf: &[u8]) -> Result<Option<usize>, &'static str> {
        let cap = tun_hdr_clamp(MAX_CONNECT_HEADER_BYTES, MAX_CONNECT_HEADER_BYTES) as usize;
        if buf.len() > cap {
            return Err("proxy CONNECT response header exceeds 8 KiB cap");
        }
        let Some(end_pos) = find_crlfcrlf(buf) else {
            return Ok(None);
        };
        let header_end = end_pos.saturating_add(4);
        let Some(head_bytes) = buf.get(..end_pos) else {
            return Err("short proxy header");
        };
        if core::str::from_utf8(head_bytes).is_err() {
            return Err("non-UTF8 proxy status line");
        }
        let Some(code) = parse_http_status_code(head_bytes) else {
            return Err("malformed proxy HTTP status");
        };
        if !tun_proxy_established(code, 200) || code >= 300 {
            return Err("proxy refused HTTP CONNECT tunnel");
        }
        self.established_count = tun_conn_advance(
            self.established_count,
            self.established_count.saturating_add(1),
        );
        Ok(Some(header_end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn http_connect_formats_clean_authority_and_parses_200_tunnel_reply() {
        let req = HttpConnectTunnel::format_request("broker.example.com:9443").unwrap();
        assert!(req.starts_with(b"CONNECT broker.example.com:9443 HTTP/1.1\r\n"));
        assert!(HttpConnectTunnel::format_request("evil\r\nX-Inj: 1:443").is_err());

        let mut t = HttpConnectTunnel::new();
        let used = t
            .parse_response(b"HTTP/1.1 200 Connection Established\r\n\r\nNEXT")
            .unwrap();
        assert_eq!(used, Some(39));
        assert!(t
            .parse_response(b"HTTP/1.1 407 Proxy Auth Required\r\n\r\n")
            .is_err());
    }
}
