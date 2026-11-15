// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Extended `DESIGN-aterm-fabric.md` §4.2 presence wire codec (`driving`, `watchers`, `parent`,
//! `autopilot`, `needs_you`) (`DESIGN-aterm-fabric.md` line 4041, `Astream.Presence.TlaPresenceV2`).
//!
//! Encodes and parses single-line `v=1` presence records published on
//! `/f/<F>/pub/<node>/<sid>/presence` while remaining backward-compatible with older readers that
//! ignore unknown keys:
//! `v=1 t=<ms> seq=<u64> state=<live|idle|busy|gone> prog=<token> driving=<sid|none> watchers=<csv> parent=<sid|none> autopilot=<off|land|cruise> needs_you=<pct>`

#[cfg(clean_islands)]
#[path = "presence_v2_island.rs"]
mod presence_v2_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pres_watchers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pres_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use presence_v2_island::{pres_seq_advance, pres_watchers_clamp};

/// Maximum read-only watcher session ids advertised on a single presence row.
pub const MAX_PRESENCE_WATCHERS: u64 = 32;

contract_fn! {
    /// Verified liveness check (`threshold <= observed`, i.e. `now_ms <= lease_until_ms`),
    /// linked via `clean-kernel-defeq` to `pres_lease_live_isl`.
    #[must_use]
    pub const fn pres_lease_live(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Session lifecycle state on `/f/<F>/pub/<node>/<sid>/presence`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionState {
    Live,
    Idle,
    Busy,
    Gone,
}

impl SessionState {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Live => "live",
            Self::Idle => "idle",
            Self::Busy => "busy",
            Self::Gone => "gone",
        }
    }

    pub fn parse(s: &str) -> Result<Self, &'static str> {
        match s {
            "live" => Ok(Self::Live),
            "idle" => Ok(Self::Idle),
            "busy" => Ok(Self::Busy),
            "gone" => Ok(Self::Gone),
            _ => Err("unknown presence state"),
        }
    }
}

/// Autopilot mode advertised in `autopilot=` (`aterm ctl @self status`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotMode {
    Off,
    Land,
    Cruise,
}

impl AutopilotMode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Land => "land",
            Self::Cruise => "cruise",
        }
    }

    pub fn parse(s: &str) -> Result<Self, &'static str> {
        match s {
            "off" => Ok(Self::Off),
            "land" => Ok(Self::Land),
            "cruise" => Ok(Self::Cruise),
            _ => Err("unknown autopilot mode"),
        }
    }
}

/// Extended §4.2 presence row with `driving`, `watchers`, `parent`, `autopilot`, and `needs_you`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresenceV2Record {
    pub sender_t_ms: u64,
    pub seq: u64,
    pub state: SessionState,
    pub program: String,
    pub driving: Option<String>,
    pub watchers: Vec<String>,
    pub parent: Option<String>,
    pub autopilot: AutopilotMode,
    pub needs_you: Option<String>,
}

/// Maximum wire length accepted for a single presence v2 line.
pub const MAX_PRESENCE_LINE_BYTES: usize = 4096;

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn push_u64_dec(out: &mut String, mut val: u64) {
    if val == 0 {
        out.push('0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while val > 0 && len < digits.len() {
        let rem = (val % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add(rem);
        }
        len = len.saturating_add(1);
        val /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&b) = digits.get(len) {
            out.push(b as char);
        }
    }
}

#[allow(clippy::question_mark)]
fn parse_u64_dec(s: &str) -> Option<u64> {
    if s.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in s.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = match acc.checked_mul(10) {
            Some(v) => v,
            None => return None,
        };
        acc = match acc.checked_add(b.saturating_sub(b'0') as u64) {
            Some(v) => v,
            None => return None,
        };
    }
    Some(acc)
}

fn pct_encode(s: &str) -> String {
    let hex = b"0123456789ABCDEF";
    let mut out = String::new();
    let escape_leading_n = s == "none";
    let mut first = true;
    for &b in s.as_bytes() {
        let force_escape = first && escape_leading_n;
        first = false;
        if !force_escape && (b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.') {
            out.push(b as char);
        } else {
            out.push('%');
            let hi = match hex.get(((b >> 4) & 0x0F) as usize) {
                Some(&c) => c,
                None => b'0',
            };
            let lo = match hex.get((b & 0x0F) as usize) {
                Some(&c) => c,
                None => b'0',
            };
            out.push(hi as char);
            out.push(lo as char);
        }
    }
    out
}

fn hex_val(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a').saturating_add(10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A').saturating_add(10)),
        _ => None,
    }
}

fn pct_decode(s: &str) -> Result<String, &'static str> {
    let raw = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(&b0) = raw.get(i) {
        if b0 == b'%' {
            let b1 = match raw.get(i.saturating_add(1)) {
                Some(&b) => b,
                None => return Err("truncated percent escape"),
            };
            let b2 = match raw.get(i.saturating_add(2)) {
                Some(&b) => b,
                None => return Err("truncated percent escape"),
            };
            let hi = match hex_val(b1) {
                Some(v) => v,
                None => return Err("bad hex digit"),
            };
            let lo = match hex_val(b2) {
                Some(v) => v,
                None => return Err("bad hex digit"),
            };
            out.push((hi << 4) | lo);
            i = i.saturating_add(3);
        } else {
            out.push(b0);
            i = i.saturating_add(1);
        }
    }
    match core::str::from_utf8(&out) {
        Ok(valid) => Ok(clone_str(valid)),
        Err(_) => Err("invalid utf8 in percent-decoded field"),
    }
}

impl PresenceV2Record {
    /// Serializes the extended `v=1` presence wire line, clamping `watchers` to [`MAX_PRESENCE_WATCHERS`].
    #[must_use]
    pub fn encode_line(&self) -> String {
        let keep = pres_watchers_clamp(self.watchers.len() as u64, MAX_PRESENCE_WATCHERS) as usize;
        let mut watchers_field = String::new();
        if keep == 0 {
            watchers_field.push_str("none");
        } else {
            let mut idx = 0usize;
            while idx < keep {
                if let Some(w) = self.watchers.get(idx) {
                    if idx > 0 {
                        watchers_field.push(',');
                    }
                    watchers_field.push_str(&pct_encode(w));
                }
                idx = idx.saturating_add(1);
            }
        }
        let driving = match &self.driving {
            Some(d) => pct_encode(d),
            None => clone_str("none"),
        };
        let parent = match &self.parent {
            Some(p) => pct_encode(p),
            None => clone_str("none"),
        };
        let needs = match &self.needs_you {
            Some(n) => pct_encode(n),
            None => clone_str("none"),
        };
        let mut out = String::new();
        out.push_str("v=1 t=");
        push_u64_dec(&mut out, self.sender_t_ms);
        out.push_str(" seq=");
        push_u64_dec(&mut out, self.seq);
        out.push_str(" state=");
        out.push_str(self.state.as_str());
        out.push_str(" prog=");
        out.push_str(&pct_encode(&self.program));
        out.push_str(" driving=");
        out.push_str(&driving);
        out.push_str(" watchers=");
        out.push_str(&watchers_field);
        out.push_str(" parent=");
        out.push_str(&parent);
        out.push_str(" autopilot=");
        out.push_str(self.autopilot.as_str());
        out.push_str(" needs_you=");
        out.push_str(&needs);
        out
    }

    /// Parses an extended `v=1` presence wire line fail-closed (stopping at first `\n`,
    /// rejecting duplicate known keys, and skipping unrecognized future keys).
    #[allow(clippy::manual_unwrap_or_default, clippy::manual_unwrap_or)]
    pub fn decode_line(input: &str) -> Result<Self, &'static str> {
        let line = match input.split_once('\n') {
            Some((first, _)) => first,
            None => input,
        };
        if line.len() > MAX_PRESENCE_LINE_BYTES {
            return Err("presence line exceeds MAX_PRESENCE_LINE_BYTES");
        }
        let mut ver_ok = false;
        let mut sender_t_ms: Option<u64> = None;
        let mut seq: Option<u64> = None;
        let mut state: Option<SessionState> = None;
        let mut prog: Option<String> = None;
        let mut driving: Option<Option<String>> = None;
        let mut watchers: Option<Vec<String>> = None;
        let mut parent: Option<Option<String>> = None;
        let mut autopilot: Option<AutopilotMode> = None;
        let mut needs_you: Option<Option<String>> = None;

        for tok in line.split_ascii_whitespace() {
            let (k, v) = match tok.split_once('=') {
                Some(pair) => pair,
                None => return Err("malformed presence token"),
            };
            match k {
                "v" => {
                    if ver_ok || v != "1" {
                        return Err("invalid or duplicate v=");
                    }
                    ver_ok = true;
                }
                "t" => {
                    if sender_t_ms.is_some() {
                        return Err("duplicate t=");
                    }
                    let parsed = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad t="),
                    };
                    sender_t_ms = Some(parsed);
                }
                "seq" => {
                    if seq.is_some() {
                        return Err("duplicate seq=");
                    }
                    let parsed = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad seq="),
                    };
                    seq = Some(parsed);
                }
                "state" => {
                    if state.is_some() {
                        return Err("duplicate state=");
                    }
                    state = Some(SessionState::parse(v)?);
                }
                "prog" => {
                    if prog.is_some() {
                        return Err("duplicate prog=");
                    }
                    prog = Some(pct_decode(v)?);
                }
                "driving" => {
                    if driving.is_some() {
                        return Err("duplicate driving=");
                    }
                    driving = Some(if v == "none" {
                        None
                    } else {
                        Some(pct_decode(v)?)
                    });
                }
                "watchers" => {
                    if watchers.is_some() {
                        return Err("duplicate watchers=");
                    }
                    if v == "none" || v.is_empty() {
                        watchers = Some(Vec::new());
                    } else {
                        let mut list = Vec::new();
                        for item in v.split(',') {
                            if (list.len() as u64) >= MAX_PRESENCE_WATCHERS {
                                return Err("watchers exceed MAX_PRESENCE_WATCHERS");
                            }
                            list.push(pct_decode(item)?);
                        }
                        watchers = Some(list);
                    }
                }
                "parent" => {
                    if parent.is_some() {
                        return Err("duplicate parent=");
                    }
                    parent = Some(if v == "none" {
                        None
                    } else {
                        Some(pct_decode(v)?)
                    });
                }
                "autopilot" => {
                    if autopilot.is_some() {
                        return Err("duplicate autopilot=");
                    }
                    autopilot = Some(AutopilotMode::parse(v)?);
                }
                "needs_you" => {
                    if needs_you.is_some() {
                        return Err("duplicate needs_you=");
                    }
                    needs_you = Some(if v == "none" {
                        None
                    } else {
                        Some(pct_decode(v)?)
                    });
                }
                _ => {}
            }
        }

        if !ver_ok {
            return Err("missing v=1");
        }
        let sender_t_val = match sender_t_ms {
            Some(t) => t,
            None => return Err("missing t="),
        };
        let seq_val = match seq {
            Some(s) => s,
            None => 0,
        };
        let state_val = match state {
            Some(st) => st,
            None => return Err("missing state="),
        };
        let prog_val = match prog {
            Some(p) => p,
            None => clone_str("unknown"),
        };
        let driving_val = match driving {
            Some(d) => d,
            None => None,
        };
        let watchers_val = match watchers {
            Some(w) => w,
            None => Vec::new(),
        };
        let parent_val = match parent {
            Some(p) => p,
            None => None,
        };
        let autopilot_val = match autopilot {
            Some(a) => a,
            None => AutopilotMode::Off,
        };
        let needs_you_val = match needs_you {
            Some(n) => n,
            None => None,
        };
        Ok(Self {
            sender_t_ms: sender_t_val,
            seq: seq_val,
            state: state_val,
            program: prog_val,
            driving: driving_val,
            watchers: watchers_val,
            parent: parent_val,
            autopilot: autopilot_val,
            needs_you: needs_you_val,
        })
    }

    /// Checks whether a presence row stamped at `broker_bt_ms` with `ttl_ms` is still live at `now_ms`.
    #[must_use]
    pub const fn is_lease_live(&self, broker_bt_ms: u64, ttl_ms: u64, now_ms: u64) -> bool {
        if matches!(self.state, SessionState::Gone) {
            return false;
        }
        let expiry = broker_bt_ms.saturating_add(ttl_ms);
        pres_lease_live(expiry, now_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extended_presence_v2_roundtrips_and_enforces_clamps_and_leases() {
        for &a in &[0u64, 1, 32, 40, u64::MAX] {
            for &b in &[0u64, 1, 32, 100, u64::MAX] {
                assert_eq!(pres_watchers_clamp(a, b), if a < b { a } else { b });
                assert_eq!(pres_seq_advance(a, b), if a < b { b } else { a });
                assert_eq!(pres_lease_live(a, b), b <= a);
            }
        }

        let rec = PresenceV2Record {
            sender_t_ms: 1_730_000_000_123,
            seq: pres_seq_advance(4, 5),
            state: SessionState::Busy,
            program: "claude code".to_owned(),
            driving: Some("@s-worker-2".to_owned()),
            watchers: vec!["@s-human".to_owned(), "@s-audit".to_owned()],
            parent: Some("@s-root".to_owned()),
            autopilot: AutopilotMode::Cruise,
            needs_you: Some("grant Full Disk Access".to_owned()),
        };
        let line = rec.encode_line();
        let back = PresenceV2Record::decode_line(&line).unwrap();
        assert_eq!(back, rec);
        assert!(back.is_lease_live(1_000, 500, 1_500));
        assert!(!back.is_lease_live(1_000, 500, 1_501));
    }
}
