// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `DCS` (`ESC P ... ST`) / `APC` (`ESC _ ... ST`) passthrough watchdog
//! (`Astream.Term.TlaDcsPassthroughBudget`).
//!
//! Guards `aterm` terminal folds against unterminated `DCS`/`APC` strings (such as truncated
//! `tmux` passthrough wrappers or malformed `XTGETTCAP` queries missing `ESC \` / `0x9c` `ST`)
//! that would otherwise swallow subsequent shell output indefinitely.

#[cfg(clean_islands)]
#[path = "dcs_passthrough_budget_island.rs"]
mod dcs_passthrough_budget_island;
#[cfg(clean_islands)]
pub use dcs_passthrough_budget_island::{dcs_bytes_clamp, dcs_depth_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn dcs_bytes_clamp(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn dcs_depth_clamp(cand_depth: u64, max_depth: u64) -> u64 {
    if cand_depth < max_depth {
        cand_depth
    } else {
        max_depth
    }
}

contract_fn! {
    /// Verified check that buffered `DCS`/`APC` payload bytes sit within `max_bytes`,
    /// linked via `clean-kernel-defeq` to `dcs_within_budget_isl`.
    #[must_use]
    pub const fn dcs_within_budget(buffered_bytes: u64, max_bytes: u64) -> bool
    clauses [ensures result == (buffered_bytes <= max_bytes)]
    {
        buffered_bytes <= max_bytes
    }
}

/// Default maximum `DCS`/`APC` payload size before fail-open abort (`64 KiB`).
pub const DEFAULT_MAX_DCS_BYTES: u64 = 64 * 1024;

/// Default maximum nested `tmux` `DCS` passthrough ESC-doubling depth (`4`).
pub const DEFAULT_MAX_DCS_DEPTH: u64 = 4;

/// Step verdict from [`DcsPassthroughGuard::feed_chunk`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DcsStepVerdict {
    /// Not currently inside a `DCS` / `APC` sequence.
    Inactive,
    /// Still accumulating a bounded `DCS` / `APC` payload.
    Buffering { buffered_bytes: u64, depth: u64 },
    /// Cleanly terminated via `ST` (`ESC \` or `0x9c`) or `CAN`/`SUB` (`0x18`/`0x1a`).
    Completed { payload_bytes: u64 },
    /// Exceeded `max_bytes` and aborted fail-open so normal VT output resumes immediately.
    AbortedOverflow { dropped_bytes: u64 },
}

/// Streaming `DCS` / `APC` passthrough byte & nesting budget guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DcsPassthroughGuard {
    active: bool,
    saw_esc: bool,
    buffered_bytes: u64,
    escape_depth: u64,
    max_bytes: u64,
    max_depth: u64,
}

impl DcsPassthroughGuard {
    #[must_use]
    pub const fn new(max_bytes: u64, max_depth: u64) -> Self {
        let cap_b = if max_bytes == 0 {
            DEFAULT_MAX_DCS_BYTES
        } else {
            max_bytes
        };
        let cap_d = if max_depth == 0 {
            DEFAULT_MAX_DCS_DEPTH
        } else {
            max_depth
        };
        Self {
            active: false,
            saw_esc: false,
            buffered_bytes: 0,
            escape_depth: 0,
            max_bytes: cap_b,
            max_depth: cap_d,
        }
    }

    #[must_use]
    pub const fn is_active(&self) -> bool {
        self.active
    }

    #[must_use]
    pub const fn buffered_bytes(&self) -> u64 {
        self.buffered_bytes
    }

    /// Enter a `DCS` or `APC` sequence at nesting `depth` (`1..=max_depth`).
    pub fn enter(&mut self, depth: u64) {
        self.active = true;
        self.saw_esc = false;
        self.buffered_bytes = 0;
        let raw_d = if depth == 0 { 1 } else { depth };
        self.escape_depth = dcs_depth_clamp(raw_d, self.max_depth);
    }

    /// Feed a slice of bytes while inside a `DCS` / `APC` sequence, scanning for `ST` (`ESC \`),
    /// `0x9c`, `CAN` (`0x18`), `SUB` (`0x1a`), or budget overflow.
    pub fn feed_chunk(&mut self, chunk: &[u8]) -> DcsStepVerdict {
        if !self.active {
            return DcsStepVerdict::Inactive;
        }
        let mut rest = chunk;
        while let &[b, ref tail @ ..] = rest {
            if self.saw_esc {
                self.saw_esc = false;
                if b == b'\\' {
                    let done = self.buffered_bytes;
                    self.reset();
                    return DcsStepVerdict::Completed {
                        payload_bytes: done,
                    };
                }
            } else if b == 0x1b {
                self.saw_esc = true;
                rest = tail;
                continue;
            } else if b == 0x9c || b == 0x18 || b == 0x1a {
                let done = self.buffered_bytes;
                self.reset();
                return DcsStepVerdict::Completed {
                    payload_bytes: done,
                };
            }

            let cand = self.buffered_bytes.saturating_add(1);
            if !dcs_within_budget(cand, self.max_bytes) {
                let dropped = dcs_bytes_clamp(cand, self.max_bytes);
                self.reset();
                return DcsStepVerdict::AbortedOverflow {
                    dropped_bytes: dropped,
                };
            }
            self.buffered_bytes = dcs_bytes_clamp(cand, self.max_bytes);
            rest = tail;
        }
        DcsStepVerdict::Buffering {
            buffered_bytes: self.buffered_bytes,
            depth: self.escape_depth,
        }
    }

    fn reset(&mut self) {
        self.active = false;
        self.saw_esc = false;
        self.buffered_bytes = 0;
        self.escape_depth = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn completes_on_st_and_fails_open_when_unterminated_dcs_overflows() {
        let mut g = DcsPassthroughGuard::new(8, 4);
        g.enter(2);
        assert_eq!(
            g.feed_chunk(b"hello"),
            DcsStepVerdict::Buffering {
                buffered_bytes: 5,
                depth: 2
            }
        );
        assert_eq!(
            g.feed_chunk(b"\x1b\\"),
            DcsStepVerdict::Completed { payload_bytes: 5 }
        );
        assert!(!g.is_active());

        // Unterminated DCS exceeding 8 bytes aborts fail-open instead of swallowing forever.
        g.enter(1);
        assert_eq!(
            g.feed_chunk(b"0123456789"),
            DcsStepVerdict::AbortedOverflow { dropped_bytes: 8 }
        );
        assert!(!g.is_active());
        assert_eq!(g.buffered_bytes(), 0);
    }
}
