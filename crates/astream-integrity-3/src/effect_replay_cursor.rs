// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic seam effect replay cursor & strict sequence verifier.
//!
//! When an `aterm` / `astream-effects` session replays a recorded `SeamEffectEntry` tape,
//! non-deterministic code changes (an extra `ClockNow` read, a reordered `EntropyFill`,
//! a mismatched request hash, or trailing unconsumed effects at session end) must fail
//! closed with exact step coordinates instead of silently misaligning subsequent seam
//! responses.
//!
//! Clean specification: `effect_replay_cursor_island.rs` (`Astream.Effects.TlaEffectReplayCursor`).

#[cfg(clean_islands)]
#[path = "effect_replay_cursor_island.rs"]
mod effect_replay_cursor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replay_cursor_clamp(cand_cursor: u64, tape_len: u64) -> u64 {
    if cand_cursor < tape_len {
        cand_cursor
    } else {
        tape_len
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replay_cursor_advance(cur_cursor: u64, cand_cursor: u64) -> u64 {
    if cur_cursor < cand_cursor {
        cand_cursor
    } else {
        cur_cursor
    }
}
#[cfg(clean_islands)]
pub use effect_replay_cursor_island::{replay_cursor_advance, replay_cursor_clamp};

contract_fn! {
    /// Kernel-certified check that `cursor <= tape_len`, linked via
    /// `clean-kernel-defeq` to `replay_cursor_within_tape_isl`.
    #[must_use]
    pub const fn replay_cursor_within_tape(cursor: u64, tape_len: u64) -> bool
    clauses [ensures result == (cursor <= tape_len)]
    {
        cursor <= tape_len
    }
}

fn advance_clamped_cursor(cur_cursor: u64, cand_cursor: u64, tape_len: u64) -> u64 {
    let clamped = replay_cursor_clamp(replay_cursor_advance(cur_cursor, cand_cursor), tape_len);
    let _ = replay_cursor_within_tape(clamped, tape_len);
    clamped
}

/// Kind of recorded host-seam effect on a replay tape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplaySeamKind {
    ClockMonotonic,
    EntropyBytes,
    EnvLookup,
    FsMetadata,
    ToolExec,
    NetRpc,
}

/// Single recorded seam invocation on a deterministic replay tape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordedSeamStep {
    pub seq: u64,
    pub kind: ReplaySeamKind,
    pub request_digest: [u8; 32],
    pub response_bytes: Vec<u8>,
}

/// Exact mismatch reported when replayed execution diverges from the recorded tape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplayCursorError {
    /// Recorded tape itself did not have strictly increasing `seq` numbers.
    NonMonotoneTape {
        index: usize,
        prev_seq: u64,
        got_seq: u64,
    },
    /// Replayed execution attempted a seam call after all recorded entries were consumed.
    TapeExhausted {
        cursor: u64,
        attempted_kind: ReplaySeamKind,
    },
    /// Replayed execution requested a different seam kind at `cursor`.
    KindMismatch {
        cursor: u64,
        seq: u64,
        expected: ReplaySeamKind,
        got: ReplaySeamKind,
    },
    /// Replayed execution passed different request inputs at `cursor`.
    RequestDigestMismatch { cursor: u64, seq: u64 },
    /// Replayed execution finished while `remaining` recorded seam calls were still unconsumed.
    UnconsumedTrailingEffects { cursor: u64, remaining: u64 },
}

/// Strict monotone replay cursor over a validated `RecordedSeamStep` tape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectReplayCursor {
    tape: Vec<RecordedSeamStep>,
    cursor: u64,
}

impl EffectReplayCursor {
    /// Validate that `tape` has strictly increasing `seq` values and initialize cursor at `0`.
    pub fn new(tape: Vec<RecordedSeamStep>) -> Result<Self, ReplayCursorError> {
        let mut idx = 1usize;
        while idx < tape.len() {
            if let (Some(prev), Some(got)) = (tape.get(idx.saturating_sub(1)), tape.get(idx)) {
                let prev_seq = prev.seq;
                let got_seq = got.seq;
                if got_seq <= prev_seq {
                    return Err(ReplayCursorError::NonMonotoneTape {
                        index: idx,
                        prev_seq,
                        got_seq,
                    });
                }
            }
            idx = idx.saturating_add(1);
        }
        Ok(Self { tape, cursor: 0 })
    }

    /// Total number of recorded steps on the tape.
    #[must_use]
    pub fn tape_len(&self) -> u64 {
        self.tape.len() as u64
    }

    /// Current replay cursor position (`0 <= cursor <= tape_len()`).
    #[must_use]
    pub const fn cursor(&self) -> u64 {
        self.cursor
    }

    /// Remaining unconsumed steps on the tape.
    #[must_use]
    pub fn remaining(&self) -> u64 {
        self.tape_len().saturating_sub(self.cursor)
    }

    /// Consume the next recorded step matching `(kind, request_digest)` and return its
    /// recorded response payload, or fail closed on any divergence.
    pub fn consume_step(
        &mut self,
        kind: ReplaySeamKind,
        request_digest: &[u8; 32],
    ) -> Result<&[u8], ReplayCursorError> {
        let len_u64 = self.tape_len();
        if self.cursor >= len_u64 {
            return Err(ReplayCursorError::TapeExhausted {
                cursor: self.cursor,
                attempted_kind: kind,
            });
        }
        let idx = self.cursor as usize;
        let Some(entry) = self.tape.get(idx) else {
            return Err(ReplayCursorError::TapeExhausted {
                cursor: self.cursor,
                attempted_kind: kind,
            });
        };
        let step_seq = entry.seq;
        let step_kind = entry.kind;
        if step_kind != kind {
            return Err(ReplayCursorError::KindMismatch {
                cursor: self.cursor,
                seq: step_seq,
                expected: step_kind,
                got: kind,
            });
        }
        if &entry.request_digest != request_digest {
            return Err(ReplayCursorError::RequestDigestMismatch {
                cursor: self.cursor,
                seq: step_seq,
            });
        }
        self.cursor = advance_clamped_cursor(self.cursor, self.cursor.saturating_add(1), len_u64);
        match self.tape.get(idx) {
            Some(e) => Ok(&e.response_bytes),
            None => Err(ReplayCursorError::TapeExhausted {
                cursor: self.cursor,
                attempted_kind: kind,
            }),
        }
    }

    /// Verify at session completion that every recorded seam call on the tape was consumed.
    pub fn verify_complete(&self) -> Result<(), ReplayCursorError> {
        let rem = self.remaining();
        if rem != 0 {
            return Err(ReplayCursorError::UnconsumedTrailingEffects {
                cursor: self.cursor,
                remaining: rem,
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_step(seq: u64, kind: ReplaySeamKind, tag: u8, out: &[u8]) -> RecordedSeamStep {
        RecordedSeamStep {
            seq,
            kind,
            request_digest: [tag; 32],
            response_bytes: out.to_vec(),
        }
    }

    #[test]
    fn replays_exact_sequence_and_verifies_completion() {
        let tape = vec![
            sample_step(10, ReplaySeamKind::ClockMonotonic, 0x01, b"t=100"),
            sample_step(20, ReplaySeamKind::ToolExec, 0x02, b"exit=0"),
        ];
        let mut cur = EffectReplayCursor::new(tape).expect("monotone tape");
        assert_eq!(cur.remaining(), 2);

        let r1 = cur
            .consume_step(ReplaySeamKind::ClockMonotonic, &[0x01; 32])
            .expect("step 1");
        assert_eq!(r1, b"t=100");
        assert_eq!(cur.cursor(), 1);
        assert!(cur.verify_complete().is_err());

        let r2 = cur
            .consume_step(ReplaySeamKind::ToolExec, &[0x02; 32])
            .expect("step 2");
        assert_eq!(r2, b"exit=0");
        assert_eq!(cur.cursor(), 2);
        cur.verify_complete().expect("all steps consumed");
    }

    #[test]
    fn rejects_non_monotone_tape_kind_mismatch_and_exhaustion() {
        let bad_tape = vec![
            sample_step(5, ReplaySeamKind::EnvLookup, 1, b"a"),
            sample_step(5, ReplaySeamKind::EnvLookup, 2, b"b"),
        ];
        assert_eq!(
            EffectReplayCursor::new(bad_tape),
            Err(ReplayCursorError::NonMonotoneTape {
                index: 1,
                prev_seq: 5,
                got_seq: 5,
            })
        );

        let tape = vec![sample_step(1, ReplaySeamKind::EntropyBytes, 0xAA, b"seed")];
        let mut cur = EffectReplayCursor::new(tape).expect("valid");
        assert_eq!(
            cur.consume_step(ReplaySeamKind::NetRpc, &[0xAA; 32]),
            Err(ReplayCursorError::KindMismatch {
                cursor: 0,
                seq: 1,
                expected: ReplaySeamKind::EntropyBytes,
                got: ReplaySeamKind::NetRpc,
            })
        );
        // Cursor did not advance on mismatch; valid call still succeeds.
        assert_eq!(
            cur.consume_step(ReplaySeamKind::EntropyBytes, &[0xAA; 32])
                .expect("valid"),
            b"seed"
        );
        assert_eq!(
            cur.consume_step(ReplaySeamKind::ClockMonotonic, &[0xBB; 32]),
            Err(ReplayCursorError::TapeExhausted {
                cursor: 1,
                attempted_kind: ReplaySeamKind::ClockMonotonic,
            })
        );
    }
}
