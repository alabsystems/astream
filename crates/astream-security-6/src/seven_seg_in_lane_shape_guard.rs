// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::manual_is_ascii_check)]

//! Pinned 7-segment `/f/<F>/in/<node>/<sid>/<src>/<kind>` left-to-right parser & suffix-forgery guard
//! (`docs/DESIGN-aterm-fabric.md` §3.3 lines 828–835; `Astream.Wire.TlaSevenSegInLaneShapeGuard`).
//!
//! Because `>` is one-or-more segments, a sender holding an overly broad `>` grant could publish
//! an 8-segment subject whose trailing two segments spoof `<src>/<kind>`. This guard parses `in`
//! subjects strictly from the left and refuses (`ev undeliverable off=<n> reason=malformed`) any
//! subject with `!= 7` segments, a `<src>` lacking a valid `s-|n-|h-|a-` class prefix (`3..=34`
//! `[a-z0-9-]` bytes), or an empty segment.
//!
//! Pure stack `no_std`, slice-pattern destructuring only, zero `Display` (`0` `unknown`, `0` `rtc`).

#[cfg(clean_islands)]
#[path = "seven_seg_in_lane_shape_guard_island.rs"]
mod seven_seg_in_lane_shape_guard_island;
#[cfg(clean_islands)]
pub use seven_seg_in_lane_shape_guard_island::{
    in_shape_src_len_clamp_b131, in_shape_undeliv_advance_b131,
};

/// Required exact segment count of `/f/<F>/in/<node>/<sid>/<src>/<kind>` (`7`).
pub const PINNED_IN_SEGMENT_COUNT: u64 = 7;

/// Maximum byte length of `<class>-<name>` (`2 + 32 = 34` bytes, §3.2).
pub const MAX_PRINCIPAL_SEG_BYTES: usize = 34;

#[cfg(not(clean_islands))]
/// Clamp `<src>` principal segment byte length to `max_principal_bytes`.
#[must_use]
pub const fn in_shape_src_len_clamp_b131(cand_len: u64, max_principal_bytes: u64) -> u64 {
    if cand_len < max_principal_bytes {
        cand_len
    } else {
        max_principal_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of malformed `in`-lane subjects refused as undeliverable.
#[must_use]
pub const fn in_shape_undeliv_advance_b131(cur_count: u64, cand_count: u64) -> u64 {
    if cur_count < cand_count {
        cand_count
    } else {
        cur_count
    }
}

contract_fn! {
    /// True iff `seg_count == 7`.
    #[must_use]
    pub const fn in_shape_exact_seven_b131(seg_count: u64) -> bool
    clauses [ensures result == (seg_count == 7)]
    {
        seg_count == 7
    }
}

const fn split_first_slash(mut s: &[u8]) -> (&[u8], Option<&[u8]>) {
    let mut head_len = 0usize;
    let orig = s;
    while let &[b, ref tail @ ..] = s {
        if b == b'/' {
            return match orig.split_at_checked(head_len) {
                Some((head, _)) => (head, Some(tail)),
                None => (orig, None),
            };
        }
        head_len = head_len.saturating_add(1);
        s = tail;
    }
    (orig, None)
}

/// Whether `seg` is an aterm tab ID, a session's principal: `t` and 10 lower-case Crockford
/// base32 characters (`0-9`, `a-z` without `i`, `l`, `o`, `u`).
const fn is_tab_id(seg: &[u8]) -> bool {
    let &[b't', ref body @ ..] = seg else {
        return false;
    };
    if body.len() != 10 {
        return false;
    }
    let mut rest = body;
    while let &[b, ref tail @ ..] = rest {
        if !(matches!(b, b'0'..=b'9' | b'a'..=b'h' | b'j' | b'k' | b'm' | b'n' | b'p'..=b't')
            || matches!(b, b'v'..=b'z'))
        {
            return false;
        }
        rest = tail;
    }
    true
}

const fn valid_principal_segment(seg: &[u8]) -> bool {
    if is_tab_id(seg) {
        return true;
    }
    if seg.len() < 3 || seg.len() > MAX_PRINCIPAL_SEG_BYTES {
        return false;
    }
    let &[c0, c1, ref body @ ..] = seg else {
        return false;
    };
    if c1 != b'-' || !matches!(c0, b's' | b'n' | b'h' | b'a') {
        return false;
    }
    let mut rest = body;
    while let &[b, ref tail @ ..] = rest {
        if !(matches!(b, b'a'..=b'z') || matches!(b, b'0'..=b'9') || b == b'-') {
            return false;
        }
        rest = tail;
    }
    true
}

/// Refusal reason (`ev undeliverable off=<n> reason=malformed`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum InLaneShapeError {
    MissingLeadingSlash,
    WrongSegmentCount { got: u64 },
    WrongFacePrefix,
    EmptySegment,
    InvalidSourcePrincipal,
}

/// Borrowed 7-segment `in`-lane view parsed left-to-right.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ParsedInSubject<'a> {
    pub fleet: &'a [u8],
    pub node: &'a [u8],
    pub sid: &'a [u8],
    pub src: &'a [u8],
    pub kind: &'a [u8],
}

/// Pure stack `in`-lane shape guard tracking malformed-refusal counters.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SevenSegInLaneShapeGuard {
    undeliverable_count: u64,
    last_src_bytes: u64,
}

impl Default for SevenSegInLaneShapeGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl SevenSegInLaneShapeGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            undeliverable_count: 0,
            last_src_bytes: 0,
        }
    }

    #[must_use]
    pub const fn undeliverable_count(&self) -> u64 {
        self.undeliverable_count
    }

    fn note_undeliverable(&mut self) {
        let cand = self.undeliverable_count.saturating_add(1);
        self.undeliverable_count = in_shape_undeliv_advance_b131(self.undeliverable_count, cand);
    }

    /// Validate `/f/<F>/in/<node>/<sid>/<src>/<kind>` strictly from the left.
    pub fn validate<'a>(
        &mut self,
        subject: &'a [u8],
    ) -> Result<ParsedInSubject<'a>, InLaneShapeError> {
        let &[b'/', ref after_root @ ..] = subject else {
            self.note_undeliverable();
            return Err(InLaneShapeError::MissingLeadingSlash);
        };
        // Count total slash-separated segments first.
        let mut seg_count = 1u64;
        let mut scan = after_root;
        while let &[b, ref tail @ ..] = scan {
            if b == b'/' {
                seg_count = seg_count.saturating_add(1);
            }
            scan = tail;
        }
        if !in_shape_exact_seven_b131(seg_count) {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        }

        let (s1_f, Some(r1)) = split_first_slash(after_root) else {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        };
        let (s2_fleet, Some(r2)) = split_first_slash(r1) else {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        };
        let (s3_in, Some(r3)) = split_first_slash(r2) else {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        };
        let (s4_node, Some(r4)) = split_first_slash(r3) else {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        };
        let (s5_sid, Some(r5)) = split_first_slash(r4) else {
            self.note_undeliverable();
            return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
        };
        let (s6_src, None) = split_first_slash(r5) else {
            // Wait: r5 is `<src>/<kind>`, so it MUST have one slash!
            let (src_seg, Some(s7_kind)) = split_first_slash(r5) else {
                self.note_undeliverable();
                return Err(InLaneShapeError::WrongSegmentCount { got: seg_count });
            };
            if !matches!(s1_f, &[b'f']) || !matches!(s3_in, &[b'i', b'n']) {
                self.note_undeliverable();
                return Err(InLaneShapeError::WrongFacePrefix);
            }
            if s2_fleet.is_empty() || s4_node.is_empty() || s5_sid.is_empty() || s7_kind.is_empty()
            {
                self.note_undeliverable();
                return Err(InLaneShapeError::EmptySegment);
            }
            if !valid_principal_segment(src_seg) {
                self.note_undeliverable();
                return Err(InLaneShapeError::InvalidSourcePrincipal);
            }
            self.last_src_bytes =
                in_shape_src_len_clamp_b131(src_seg.len() as u64, MAX_PRINCIPAL_SEG_BYTES as u64);
            return Ok(ParsedInSubject {
                fleet: s2_fleet,
                node: s4_node,
                sid: s5_sid,
                src: src_seg,
                kind: s7_kind,
            });
        };
        let _ = s6_src;
        self.note_undeliverable();
        Err(InLaneShapeError::WrongSegmentCount { got: seg_count })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_exact_seven_segments_and_defeats_eight_segment_suffix_forgery() {
        let mut g = SevenSegInLaneShapeGuard::new();
        let ok = g
            .validate(b"/f/prod/in/n-0123456789abcdef/s-0123456789abcdef0123/h-alice/task")
            .unwrap();
        assert_eq!(ok.fleet, b"prod");
        assert_eq!(ok.src, b"h-alice");
        assert_eq!(ok.kind, b"task");

        // 8-segment `>` suffix forgery `/f/prod/in/n-1/s-1/s-evil/h-alice/control` MUST fail!
        assert_eq!(
            g.validate(b"/f/prod/in/n-1/s-1/s-evil/h-alice/control"),
            Err(InLaneShapeError::WrongSegmentCount { got: 8 })
        );
        // Unprefixed `<src>` `root` MUST fail!
        assert_eq!(
            g.validate(b"/f/prod/in/n-1/s-1/root/task"),
            Err(InLaneShapeError::InvalidSourcePrincipal)
        );
        assert_eq!(g.undeliverable_count(), 2);
    }

    #[test]
    fn an_aterm_tab_id_is_a_source_principal_and_its_near_misses_are_not() {
        let mut g = SevenSegInLaneShapeGuard::new();
        let ok = g
            .validate(b"/f/prod/in/n-0123456789abcdef/tqn5r6e0148/tqn5r6e0148/task")
            .unwrap();
        assert_eq!(ok.src, b"tqn5r6e0148");
        for near in [
            &b"/f/prod/in/n-1/tqn5r6e0148/tqn5r6e014/task"[..],
            b"/f/prod/in/n-1/tqn5r6e0148/tqn5r6e01488/task",
            b"/f/prod/in/n-1/tqn5r6e0148/tqn5r6e014u/task",
            b"/f/prod/in/n-1/tqn5r6e0148/tQN5R6E0148/task",
        ] {
            assert_eq!(
                g.validate(near),
                Err(InLaneShapeError::InvalidSourcePrincipal)
            );
        }
    }
}
