// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fabric peer session status & untrusted survey excerpt sanitization
//! (`Astream.Host.TlaPeerStatusExcerpt`; `aterm ctl ls` / `aterm ctl survey`).
//!
//! Each live `aterm` session publishes its current program, `autopilot` mode, execution
//! state, monotone revision `rev`, and an optional bounded excerpt of recent terminal
//! activity. Because `aterm ctl survey` excerpts are untrusted data from peer sessions
//! ("like a mail body"), [`sanitize_survey_excerpt`] strips all C0/C1 control bytes and
//! ANSI/OSC escape sequences while clamping byte length through Clean-origin
//! [`peer_excerpt_clamp`] (`<= MAX_SURVEY_EXCERPT_BYTES`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use core::fmt;

#[cfg(clean_islands)]
#[path = "peer_status_island.rs"]
mod peer_status_island;
#[cfg(clean_islands)]
pub use peer_status_island::{peer_excerpt_clamp, peer_rev_advance};

/// Mirror of Clean's `peer_rev_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn peer_rev_advance(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

/// Mirror of Clean's `peer_excerpt_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn peer_excerpt_clamp(raw_len: u64, max_cap: u64) -> u64 {
    if raw_len < max_cap {
        raw_len
    } else {
        max_cap
    }
}

contract_fn! {
    /// Kernel-certified check that a sanitized survey excerpt fits within `cap`
    /// (`len <= cap`), linked via `clean-kernel-defeq` to `peer_excerpt_within_cap_isl`.
    #[must_use]
    pub const fn peer_excerpt_within_cap(len: usize, cap: usize) -> bool
    clauses [ensures result == (len <= cap)]
    {
        len <= cap
    }
}

/// Maximum byte length of a sanitized peer survey excerpt (`512` bytes).
pub const MAX_SURVEY_EXCERPT_BYTES: usize = 512;

/// Maximum byte length of a peer's foreground program token (`64` bytes).
pub const MAX_PEER_PROGRAM_BYTES: usize = 64;

const fn bytes_eq(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let &[x, ref at @ ..] = a {
        let &[y, ref bt @ ..] = b else {
            return false;
        };
        if x != y {
            return false;
        }
        a = at;
        b = bt;
    }
    true
}

/// Autopilot mode advertised on a peer session's status row (`autopilot=off|cruise|land`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PeerAutopilotMode {
    /// Harness types nothing (`off`).
    Off,
    /// Harness continues every turn end (`cruise`).
    Cruise,
    /// Harness continues until all work lands on remote main (`land`).
    Land,
}

impl PeerAutopilotMode {
    /// Closed vocabulary of autopilot modes.
    pub const ALL: [Self; 3] = [Self::Off, Self::Cruise, Self::Land];

    /// Canonical wire token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Cruise => "cruise",
            Self::Land => "land",
        }
    }

    /// Parse canonical wire bytes.
    #[must_use]
    pub const fn parse_bytes(s: &[u8]) -> Option<Self> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[m, ref tail @ ..] = rest {
            if bytes_eq(s, m.as_str().as_bytes()) {
                return Some(m);
            }
            rest = tail;
        }
        None
    }

    /// Parse canonical wire token.
    #[must_use]
    pub const fn parse(s: &str) -> Option<Self> {
        Self::parse_bytes(s.as_bytes())
    }
}

/// Execution state advertised on a peer session's status row.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PeerRunState {
    /// Prompt idle / awaiting input (`idle`).
    Idle,
    /// Actively executing a turn or foreground command (`running`).
    Running,
    /// Foreground job stopped making progress (`stalled`).
    Stalled,
    /// Blocked on an item only a person can grant (`needs_you`).
    NeedsYou,
    /// Foreground process exited (`exited`).
    Exited,
}

impl PeerRunState {
    /// Closed vocabulary of peer run states.
    pub const ALL: [Self; 5] = [
        Self::Idle,
        Self::Running,
        Self::Stalled,
        Self::NeedsYou,
        Self::Exited,
    ];

    /// Canonical wire token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Idle => "idle",
            Self::Running => "running",
            Self::Stalled => "stalled",
            Self::NeedsYou => "needs_you",
            Self::Exited => "exited",
        }
    }

    /// Whether `aterm ctl await task` treats this state as terminal/attention-worthy.
    #[must_use]
    pub const fn wakes_await_task(self) -> bool {
        matches!(self, Self::Stalled | Self::NeedsYou | Self::Exited)
    }

    /// Parse canonical wire bytes.
    #[must_use]
    pub const fn parse_bytes(s: &[u8]) -> Option<Self> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[st, ref tail @ ..] = rest {
            if bytes_eq(s, st.as_str().as_bytes()) {
                return Some(st);
            }
            rest = tail;
        }
        None
    }

    /// Parse canonical wire token.
    #[must_use]
    pub const fn parse(s: &str) -> Option<Self> {
        Self::parse_bytes(s.as_bytes())
    }
}

#[derive(Clone, Copy)]
enum EscapeScanState {
    Normal,
    AfterEsc,
    InCsi,
    InOsc,
    InOscAfterEsc,
}

/// Sanitize raw peer terminal output into single-line printable UTF-8 safe to embed as
/// untrusted data in `aterm ctl survey` (`<= MAX_SURVEY_EXCERPT_BYTES`), stripping all
/// CSI/OSC escape sequences and collapsing control whitespace to single spaces.
#[must_use]
#[allow(clippy::manual_range_contains)]
pub fn sanitize_survey_excerpt(raw: &[u8], max_bytes: usize) -> String {
    let cap = peer_excerpt_clamp(raw.len() as u64, MAX_SURVEY_EXCERPT_BYTES as u64) as usize;
    let limit = if max_bytes < MAX_SURVEY_EXCERPT_BYTES {
        max_bytes
    } else {
        MAX_SURVEY_EXCERPT_BYTES
    };
    let init_cap = if cap < limit { cap } else { limit };
    let mut out: Vec<u8> = {
        let _ = init_cap;
        Vec::new()
    };
    let mut state = EscapeScanState::Normal;
    let mut last_was_space = true;
    let mut rest = raw;

    while let &[b, ref tail @ ..] = rest {
        rest = tail;
        match state {
            EscapeScanState::Normal => {
                if b == 0x1b {
                    state = EscapeScanState::AfterEsc;
                } else if b == b'\n' || b == b'\r' || b == b'\t' || b == b' ' {
                    if !last_was_space
                        && peer_excerpt_within_cap(out.len().saturating_add(1), limit)
                    {
                        out.push(b' ');
                        last_was_space = true;
                    }
                } else if b >= 0x20 && b < 0x7f {
                    if !peer_excerpt_within_cap(out.len().saturating_add(1), limit) {
                        break;
                    }
                    out.push(b);
                    last_was_space = false;
                }
            }
            EscapeScanState::AfterEsc => {
                state = if b == b'[' {
                    EscapeScanState::InCsi
                } else if b == b']' {
                    EscapeScanState::InOsc
                } else {
                    EscapeScanState::Normal
                };
            }
            EscapeScanState::InCsi => {
                if (b >= 0x40) && (b <= 0x7e) {
                    state = EscapeScanState::Normal;
                }
            }
            EscapeScanState::InOsc => {
                if b == 0x07 {
                    state = EscapeScanState::Normal;
                } else if b == 0x1b {
                    state = EscapeScanState::InOscAfterEsc;
                }
            }
            EscapeScanState::InOscAfterEsc => {
                state = if b == b'\\' {
                    EscapeScanState::Normal
                } else {
                    EscapeScanState::InOsc
                };
            }
        }
    }
    while let Some(&b' ') = out.last() {
        out.pop();
    }
    match core::str::from_utf8(&out) {
        Ok(s) => copy_str(s),
        Err(_) => String::new(),
    }
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

/// Monotone status tracker for a single peer session (`@<sid>:<rev>`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeerSessionStatus {
    /// Foreground program token (`claude`, `codex-alab`, `agy`, `zsh`, etc.).
    pub program: String,
    /// Active harness Autopilot mode.
    pub autopilot: PeerAutopilotMode,
    /// Current run state.
    pub state: PeerRunState,
    /// Monotone session status revision (`rev`), advanced via [`peer_rev_advance`].
    pub rev: u64,
    /// Sanitized single-line excerpt (`<= MAX_SURVEY_EXCERPT_BYTES`).
    pub excerpt: String,
}

impl PeerSessionStatus {
    /// Construct an initial peer status snapshot with sanitized program and excerpt.
    #[must_use]
    pub fn new(
        program: &str,
        autopilot: PeerAutopilotMode,
        state: PeerRunState,
        rev: u64,
        raw_excerpt: &[u8],
    ) -> Self {
        let clean_prog = sanitize_survey_excerpt(program.as_bytes(), MAX_PEER_PROGRAM_BYTES);
        let prog = if clean_prog.is_empty() {
            copy_str("unknown")
        } else {
            clean_prog
        };
        Self {
            program: prog,
            autopilot,
            state,
            rev,
            excerpt: sanitize_survey_excerpt(raw_excerpt, MAX_SURVEY_EXCERPT_BYTES),
        }
    }

    /// Advance this peer status snapshot monotonically to `cand_rev` via [`peer_rev_advance`],
    /// ignoring stale out-of-order status rows (`cand_rev < self.rev`).
    pub fn apply_update(
        &mut self,
        cand_rev: u64,
        autopilot: PeerAutopilotMode,
        state: PeerRunState,
        raw_excerpt: &[u8],
    ) -> bool {
        if cand_rev < self.rev {
            return false;
        }
        self.rev = peer_rev_advance(self.rev, cand_rev);
        self.autopilot = autopilot;
        self.state = state;
        self.excerpt = sanitize_survey_excerpt(raw_excerpt, MAX_SURVEY_EXCERPT_BYTES);
        true
    }
}

impl fmt::Display for PeerSessionStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "prog={} autopilot={} state={} rev={}",
            self.program,
            self.autopilot.as_str(),
            self.state.as_str(),
            self.rev
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitize_survey_excerpt_strips_csi_osc_and_clamps_length() {
        let raw = b"\x1b]0;spoofed-title\x07  \x1b[31mNEEDS YOU:\x1b[0m\r\ncheck   logs\x1b]52;c;YWJj\x1b\\";
        assert_eq!(sanitize_survey_excerpt(raw, 512), "NEEDS YOU: check logs");
        assert_eq!(sanitize_survey_excerpt(b"abcdefghij", 5), "abcde");
    }

    #[test]
    fn peer_session_status_advances_rev_monotonically_and_drops_stale_updates() {
        let mut st = PeerSessionStatus::new(
            "claude",
            PeerAutopilotMode::Land,
            PeerRunState::Running,
            10,
            b"running targo test",
        );
        assert!(!st.state.wakes_await_task());
        assert!(!st.apply_update(9, PeerAutopilotMode::Off, PeerRunState::Idle, b"stale"));
        assert_eq!(st.rev, 10);
        assert_eq!(st.autopilot, PeerAutopilotMode::Land);

        assert!(st.apply_update(
            11,
            PeerAutopilotMode::Land,
            PeerRunState::NeedsYou,
            b"\x1b[1mNEEDS YOU: grant Full Disk Access\x1b[0m"
        ));
        assert_eq!(st.rev, 11);
        assert!(st.state.wakes_await_task());
        assert_eq!(st.excerpt, "NEEDS YOU: grant Full Disk Access");
    }
}
