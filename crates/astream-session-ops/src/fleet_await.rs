// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-session worker task supervision & `since=<rev>` await multiplexer
//! (`aterm ctl await task @<sid>,… since=0` & `aterm ctl survey`, `Astream.Engine.TlaFleetAwait`).
//!
//! Tracks per-session monotone state revisions (`rev`) across worker sessions (`Running`,
//! `LandedDone`, `Exited`, `Stalled`, `NeedsPerson`) together with bounded survey excerpts,
//! waking `await_any` deterministically on the first watched session whose revision exceeds
//! `since_rev` (`await_rev_fresh`) and whose state requires supervisor/operator attention.

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "fleet_await_island.rs"]
mod fleet_await_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn await_rev_advance(prev_rev: u64, cand_rev: u64) -> u64 {
    if prev_rev < cand_rev {
        cand_rev
    } else {
        prev_rev
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn await_targets_clamp(targets: u64, max_targets: u64) -> u64 {
    if targets < max_targets {
        targets
    } else {
        max_targets
    }
}
#[cfg(clean_islands)]
pub use fleet_await_island::{await_rev_advance, await_targets_clamp};

/// Maximum number of concurrent worker targets in one `await_any` query.
pub const MAX_AWAIT_TARGETS: u64 = 128;

/// Maximum UTF-8 byte length of a session's bounded `survey` excerpt.
pub const MAX_SURVEY_EXCERPT_BYTES: usize = 256;

contract_fn! {
    /// Verified check that a session's revision `cur_rev` is strictly newer than a caller's
    /// `since_rev` (`since_rev < cur_rev`), linked via `clean-kernel-defeq` to `await_rev_fresh_isl`.
    #[must_use]
    pub const fn await_rev_fresh(since_rev: u64, cur_rev: u64) -> bool
    clauses [ensures result == (since_rev < cur_rev)]
    {
        since_rev < cur_rev
    }
}

/// Lifecycle state of a supervised worker session (`aterm ctl await task`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkerTaskState {
    /// Worker is actively making progress.
    Running,
    /// Worker completed and landed its work cleanly (`done`).
    LandedDone,
    /// Worker process exited with `exit_code`.
    Exited { exit_code: i32 },
    /// Worker stopped making progress past the stall horizon.
    Stalled,
    /// Worker emitted a `NEEDS YOU:` item requiring a person's decision/credential.
    NeedsPerson { item: String },
}

impl WorkerTaskState {
    /// Returns `true` when this state wakes `aterm ctl await task` (`done`, `exited`,
    /// `stalled`, or `needs a person`).
    #[must_use]
    pub const fn wakes_supervisor(&self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Snapshot of a single session's supervised state (`aterm ctl survey` row).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionSurveyEntry {
    /// Session identifier (e.g. `"s-worker-1"`).
    pub sid: String,
    /// Monotone per-session revision counter (`>= 1` once observed).
    pub rev: u64,
    /// Current lifecycle state.
    pub state: WorkerTaskState,
    /// Sanitized single-line terminal/report excerpt (`<= MAX_SURVEY_EXCERPT_BYTES`).
    pub excerpt: String,
}

/// Target selector `@<sid>:<since_rev>` passed to [`FleetTaskAwaiter::await_any`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwaitSelector {
    /// Watched session identifier.
    pub sid: String,
    /// Revision last acknowledged by caller (`0` for initial wait).
    pub since_rev: u64,
}

impl AwaitSelector {
    /// Parse `@<sid>` (`since_rev = 0`) or `@<sid>:<rev>`.
    pub fn parse(spec: &str) -> Result<Self, &'static str> {
        let stripped = match spec.strip_prefix('@') {
            Some(r) => r,
            None => spec,
        };
        if stripped.is_empty() {
            return Err("empty session selector");
        }
        match stripped.split_once(':') {
            None => Ok(Self {
                sid: str_to_owned_string(stripped),
                since_rev: 0,
            }),
            Some((sid, rev_s)) => {
                if sid.is_empty() {
                    return Err("empty sid before ':'");
                }
                let Ok(rev) = parse_u64_dec_str(rev_s) else {
                    return Err("invalid revision number in selector");
                };
                Ok(Self {
                    sid: str_to_owned_string(sid),
                    since_rev: rev,
                })
            }
        }
    }
}

const fn parse_u64_dec_str(s: &str) -> Result<u64, &'static str> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return Err("empty revision");
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !b.is_ascii_digit() {
            return Err("non-digit in revision");
        }
        let d = b.saturating_sub(b'0') as u64;
        let Some(mul) = acc.checked_mul(10) else {
            return Err("revision overflow");
        };
        let Some(next) = mul.checked_add(d) else {
            return Err("revision overflow");
        };
        acc = next;
        rest = tail;
    }
    Ok(acc)
}

/// Deterministic fleet task supervision table for `aterm ctl survey` and `await task`.
#[derive(Debug, Clone, Default)]
pub struct FleetTaskAwaiter {
    sessions: BTreeMap<String, SessionSurveyEntry>,
}

impl FleetTaskAwaiter {
    /// Create an empty fleet task awaiter.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a state/excerpt update for `sid`, strictly advancing its monotone `rev`
    /// via Clean-origin [`await_rev_advance`].
    pub fn update_session(&mut self, sid: &str, state: WorkerTaskState, raw_excerpt: &str) -> u64 {
        let clean_excerpt = sanitize_excerpt(raw_excerpt);
        if let Some(entry) = self.sessions.get_mut(sid) {
            let cand = entry.rev.saturating_add(1);
            entry.rev = await_rev_advance(entry.rev, cand);
            entry.state = state;
            entry.excerpt = clean_excerpt;
            return entry.rev;
        }
        let rev = await_rev_advance(0, 1);
        self.sessions.insert(
            str_to_owned_string(sid),
            SessionSurveyEntry {
                sid: str_to_owned_string(sid),
                rev,
                state,
                excerpt: clean_excerpt,
            },
        );
        rev
    }

    /// Return all tracked sessions in deterministic `sid` order (`aterm ctl survey`).
    #[must_use]
    pub fn survey(&self) -> Vec<SessionSurveyEntry> {
        let cap = if self.sessions.len() < 256 {
            self.sessions.len()
        } else {
            256
        };
        let mut out = {
            let _ = cap;
            Vec::new()
        };
        for entry in self.sessions.values() {
            out.push(entry.clone());
        }
        out
    }

    /// Evaluate up to [`MAX_AWAIT_TARGETS`] selectors (`@<sid>:<since_rev>`) and return
    /// the first session that has transitioned past `since_rev` (`await_rev_fresh`) into a
    /// supervisor-waking state (`done`, `exited`, `stalled`, or `NEEDS YOU`).
    #[must_use]
    pub fn await_any(&self, selectors: &[AwaitSelector]) -> Option<SessionSurveyEntry> {
        let limit = await_targets_clamp(selectors.len() as u64, MAX_AWAIT_TARGETS) as usize;
        let mut i = 0usize;
        while i < limit {
            let Some(sel) = selectors.get(i) else {
                break;
            };
            if let Some(entry) = self.sessions.get(&sel.sid) {
                if await_rev_fresh(sel.since_rev, entry.rev) && entry.state.wakes_supervisor() {
                    return Some(entry.clone());
                }
            }
            i = i.saturating_add(1);
        }
        None
    }
}

fn str_to_owned_string(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn sanitize_excerpt(raw: &str) -> String {
    let cap = if raw.len() < MAX_SURVEY_EXCERPT_BYTES {
        raw.len()
    } else {
        MAX_SURVEY_EXCERPT_BYTES
    };
    let mut out = {
        let _ = cap;
        String::new()
    };
    for ch in raw.chars() {
        let mapped = if ch == '\n' || ch == '\r' || ch == '\t' {
            ' '
        } else if ch.is_control() {
            continue;
        } else {
            ch
        };
        if out.len().saturating_add(mapped.len_utf8()) > MAX_SURVEY_EXCERPT_BYTES {
            break;
        }
        out.push(mapped);
    }
    str_to_owned_string(out.trim())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn awaits_actionable_worker_transition_and_respects_since_rev() {
        let mut fleet = FleetTaskAwaiter::new();
        let r1 = fleet.update_session("w1", WorkerTaskState::Running, "building crate...");
        let r2 = fleet.update_session("w2", WorkerTaskState::Running, "running tests...");
        assert_eq!(r1, 1);
        assert_eq!(r2, 1);

        let initial = [
            AwaitSelector::parse("@w1:0").unwrap(),
            AwaitSelector::parse("@w2:0").unwrap(),
        ];
        // Both are still `Running`, so `await_any` stays parked (`None`).
        assert_eq!(fleet.await_any(&initial), None);

        // `w2` hits a `NEEDS YOU:` item -> revision advances to 2 and `await_any` wakes!
        let r2_next = fleet.update_session(
            "w2",
            WorkerTaskState::NeedsPerson {
                item: "grant Full Disk Access".to_string(),
            },
            "NEEDS YOU: grant Full Disk Access",
        );
        assert_eq!(r2_next, 2);

        let woke = fleet.await_any(&initial).unwrap();
        assert_eq!(woke.sid, "w2");
        assert_eq!(woke.rev, 2);

        // Subsequent wait naming `@w2:2` does NOT re-fire until rev > 2!
        let next_wait = [
            AwaitSelector::parse("@w1:0").unwrap(),
            AwaitSelector::parse("@w2:2").unwrap(),
        ];
        assert_eq!(fleet.await_any(&next_wait), None);

        // `w1` lands its work -> `await_any` wakes for `w1`!
        fleet.update_session("w1", WorkerTaskState::LandedDone, "Nothing left: pushed");
        let woke_w1 = fleet.await_any(&next_wait).unwrap();
        assert_eq!(woke_w1.sid, "w1");
        assert_eq!(woke_w1.state, WorkerTaskState::LandedDone);
    }
}
