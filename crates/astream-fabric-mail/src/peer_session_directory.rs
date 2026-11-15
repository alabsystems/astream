// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `aterm ctl ls` peer session directory classifying each tab's foreground program (`claude`,
//! `codex-alab`, `agy`, `muse`, or `shell`) so peers never accidentally type into another live agent's
//! prompt (`Astream.FabMail.TlaPeerSessionDirectory`).

#[cfg(clean_islands)]
#[path = "peer_session_directory_island.rs"]
mod peer_session_directory_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_peers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_dir_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use peer_session_directory_island::{fm_dir_advance, fm_peers_clamp};

/// Maximum tracked sessions in `aterm ctl ls` (`256`).
pub const MAX_TRACKED_SESSIONS: u64 = 256;

contract_fn! {
    /// Verified session-directory capacity bound (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `fm_directory_within_cap_isl`.
    #[must_use]
    pub const fn fm_directory_within_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PeerProgram {
    ClaudeCode,
    CodexAlab,
    Agy,
    MuseCode,
    ShellOrTool,
}

fn contains_ascii_ci(haystack: &str, needle: &[u8]) -> bool {
    let bytes = haystack.as_bytes();
    if needle.is_empty() {
        return true;
    }
    let mut idx = 0usize;
    while idx.saturating_add(needle.len()) <= bytes.len() {
        if let Some(sub) = bytes.get(idx..idx.saturating_add(needle.len())) {
            if sub.eq_ignore_ascii_case(needle) {
                return true;
            }
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl PeerProgram {
    #[must_use]
    pub fn parse(program: &str) -> Self {
        if contains_ascii_ci(program, b"claude") {
            Self::ClaudeCode
        } else if contains_ascii_ci(program, b"codex") {
            Self::CodexAlab
        } else if contains_ascii_ci(program, b"agy") || contains_ascii_ci(program, b"antigravity") {
            Self::Agy
        } else if contains_ascii_ci(program, b"muse") {
            Self::MuseCode
        } else {
            Self::ShellOrTool
        }
    }

    #[must_use]
    pub const fn is_agent_prompt(self) -> bool {
        !matches!(self, Self::ShellOrTool)
    }
}

#[derive(Debug, Clone, Default)]
pub struct PeerDirectory {
    live_count: u64,
    refresh_seq: u64,
}

impl PeerDirectory {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            live_count: 0,
            refresh_seq: 0,
        }
    }

    pub fn record_snapshot(&mut self, sessions_seen: u64) -> bool {
        self.live_count = fm_peers_clamp(sessions_seen, MAX_TRACKED_SESSIONS);
        self.refresh_seq = fm_dir_advance(self.refresh_seq, self.refresh_seq.saturating_add(1));
        fm_directory_within_cap(MAX_TRACKED_SESSIONS, self.live_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifies_agent_programs_whose_stdin_is_a_prompt() {
        assert!(PeerProgram::parse("claude").is_agent_prompt());
        assert!(PeerProgram::parse("codex-alab").is_agent_prompt());
        assert!(PeerProgram::parse("agy").is_agent_prompt());
        assert!(!PeerProgram::parse("zsh").is_agent_prompt());
        let mut dir = PeerDirectory::new();
        assert!(dir.record_snapshot(12));
    }
}
