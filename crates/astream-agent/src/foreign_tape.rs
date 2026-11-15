// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::needless_lifetimes)]

//! Foreign-process effects tape framing (`EFFECT_TAPE_VERSION = 1`) and unified
//! session splicing (`Astream.Agent.TlaForeignTape`).
//!
//! Closes the two open boundaries documented in `astream-effects`:
//! 1. **Durable framing & offset-addressing** of a standalone [`EffectsLog`] over
//!    CRC-checked [`astream_wire::Frame`] records (`EffectEnvelope`, `encode_effects_tape`,
//!    `decode_effects_tape_strict`) without adding wire dependencies to `astream-effects`.
//! 2. **Feeding a foreign-process `ptrace` tape into [`crate::unified::replay_session`]**
//!    (`ToolEffectSpan`, `splice_foreign_tape`, `replay_session_with_foreign_tape`), so
//!    syscall effects recorded by `astream-host::foreign` (or a cooperative seam) fold
//!    onto ONE offset axis with `In`, `Out`, and `Cognition` events and diverge coherently
//!    under counterfactual forks (`fork_session`).

use crate::cog::CogRecord;
use crate::envelope::envelope_version_matches;
use crate::unified::{replay_session, Event, Replay};
use astream_effects::{EffectRecord, EffectsLog};
use astream_wire::{Frame, FrameError, Offset};
use std::io::ErrorKind;

#[cfg(clean_islands)]
#[path = "foreign_tape_island.rs"]
mod foreign_tape_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{foreign_tape_clamp_records, foreign_tape_cursor_advance};
#[cfg(clean_islands)]
pub use foreign_tape_island::{foreign_tape_clamp_records, foreign_tape_cursor_advance};

contract_fn! {
    /// Verified check that a foreign-tape splice cursor has consumed every record
    /// (`cursor == total`), linked via `clean-kernel-defeq` to `foreign_tape_exhausted_isl`.
    #[must_use]
    pub const fn foreign_tape_exhausted(cursor: u64, total: u64) -> bool
    clauses [ensures result == (cursor == total)]
    {
        cursor == total
    }
}

/// Wire format version for CRC-framed standalone [`EffectsLog`] tapes.
pub const EFFECT_TAPE_VERSION: u8 = 1;

/// Maximum number of effect records decoded or spliced from a foreign tape (`65_536`).
pub const MAX_FOREIGN_TAPE_RECORDS: usize = 65_536;

/// Maximum byte length of a single string/payload field inside a framed effect record (`4 MiB`).
pub const MAX_EFFECT_FIELD_BYTES: usize = 4 * 1024 * 1024;

/// One offset-addressed effect record framed for durable storage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectEnvelope {
    /// Zero-based monotonic offset of this effect in the tape (`0..N`).
    pub seq: Offset,
    /// The recorded effect event.
    pub record: EffectRecord,
}

/// Error returned when encoding or decoding a framed [`EffectsLog`] tape fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectTapeError {
    /// Buffer ended before a fixed or length-prefixed field completed.
    Short,
    /// Envelope version byte did not match [`EFFECT_TAPE_VERSION`].
    BadVersion(u8),
    /// Unknown `EffectRecord` discriminator tag byte.
    BadTag(u8),
    /// Unknown `std::io::ErrorKind` wire code in a `FileErr` record.
    BadErrorKind(u8),
    /// Declared field length exceeded buffer bounds or [`MAX_EFFECT_FIELD_BYTES`].
    BadLen,
    /// UTF-8 validation failed on a `path` or `door` string.
    BadUtf8,
    /// Outer `astream-wire` CRC frame error.
    Frame(FrameError),
    /// Decoded sequence offset did not match the expected monotonic index.
    NonMonotonicSeq { expected: u64, actual: u64 },
    /// Tape record count exceeded [`MAX_FOREIGN_TAPE_RECORDS`].
    RecordCapExceeded { count: usize, max: usize },
}

/// Error returned when splicing foreign-process effect spans into a unified session fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForeignTapeSpliceError {
    /// `ToolEffectSpan::tool_result_index` values were not strictly increasing.
    SpanOutOfOrder { prev_index: usize, index: usize },
    /// Total foreign effect records across spans exceeded [`MAX_FOREIGN_TAPE_RECORDS`].
    RecordCapExceeded { requested: usize, max: usize },
    /// Session ended before reaching the targeted `CogRecord::ToolResult` ordinal.
    MissingToolResult {
        target_index: usize,
        observed_tool_results: usize,
    },
    /// Not all foreign effect records were spliced onto the unified axis.
    UnconsumedRecords { remaining: usize },
}

/// Associates one tool execution (`tool_result_index`, 0-based ordinal among
/// `Event::Cognition(CogRecord::ToolResult { .. })` events in the session) with
/// the [`EffectsLog`] captured from the foreign child process (e.g. `astream-host::foreign`)
/// or cooperative seam that produced that tool result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolEffectSpan {
    /// Zero-based ordinal of the `CogRecord::ToolResult` this foreign run produced.
    pub tool_result_index: usize,
    /// Recorded syscall/seam effects of that tool run, in causal execution order.
    pub tape: EffectsLog,
}

#[must_use]
const fn error_kind_to_code(kind: ErrorKind) -> u8 {
    match kind {
        ErrorKind::NotFound => 1,
        ErrorKind::PermissionDenied => 2,
        ErrorKind::ConnectionRefused => 3,
        ErrorKind::ConnectionReset => 4,
        ErrorKind::ConnectionAborted => 5,
        ErrorKind::NotConnected => 6,
        ErrorKind::AddrInUse => 7,
        ErrorKind::AddrNotAvailable => 8,
        ErrorKind::BrokenPipe => 9,
        ErrorKind::AlreadyExists => 10,
        ErrorKind::WouldBlock => 11,
        ErrorKind::InvalidInput => 12,
        ErrorKind::InvalidData => 13,
        ErrorKind::TimedOut => 14,
        ErrorKind::WriteZero => 15,
        ErrorKind::Interrupted => 16,
        ErrorKind::Unsupported => 17,
        ErrorKind::UnexpectedEof => 18,
        ErrorKind::OutOfMemory => 19,
        _ => 255,
    }
}

const fn code_to_error_kind(code: u8) -> Result<ErrorKind, EffectTapeError> {
    match code {
        1 => Ok(ErrorKind::NotFound),
        2 => Ok(ErrorKind::PermissionDenied),
        3 => Ok(ErrorKind::ConnectionRefused),
        4 => Ok(ErrorKind::ConnectionReset),
        5 => Ok(ErrorKind::ConnectionAborted),
        6 => Ok(ErrorKind::NotConnected),
        7 => Ok(ErrorKind::AddrInUse),
        8 => Ok(ErrorKind::AddrNotAvailable),
        9 => Ok(ErrorKind::BrokenPipe),
        10 => Ok(ErrorKind::AlreadyExists),
        11 => Ok(ErrorKind::WouldBlock),
        12 => Ok(ErrorKind::InvalidInput),
        13 => Ok(ErrorKind::InvalidData),
        14 => Ok(ErrorKind::TimedOut),
        15 => Ok(ErrorKind::WriteZero),
        16 => Ok(ErrorKind::Interrupted),
        17 => Ok(ErrorKind::Unsupported),
        18 => Ok(ErrorKind::UnexpectedEof),
        19 => Ok(ErrorKind::OutOfMemory),
        255 => Ok(ErrorKind::Other),
        other => Err(EffectTapeError::BadErrorKind(other)),
    }
}

fn put_u32_le(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&[v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]);
}

fn put_u64_le(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&[
        v as u8,
        (v >> 8) as u8,
        (v >> 16) as u8,
        (v >> 24) as u8,
        (v >> 32) as u8,
        (v >> 40) as u8,
        (v >> 48) as u8,
        (v >> 56) as u8,
    ]);
}

fn put_bytes_checked(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), EffectTapeError> {
    if bytes.len() > MAX_EFFECT_FIELD_BYTES {
        return Err(EffectTapeError::BadLen);
    }
    put_u32_le(out, bytes.len() as u32);
    out.extend_from_slice(bytes);
    Ok(())
}

const fn take_u8(buf: &[u8]) -> Result<(u8, &[u8]), EffectTapeError> {
    let &[b, ref rest @ ..] = buf else {
        return Err(EffectTapeError::Short);
    };
    Ok((b, rest))
}

const fn take_u64_le(buf: &[u8]) -> Result<(u64, &[u8]), EffectTapeError> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = buf else {
        return Err(EffectTapeError::Short);
    };
    let val = (b0 as u64)
        | ((b1 as u64) << 8)
        | ((b2 as u64) << 16)
        | ((b3 as u64) << 24)
        | ((b4 as u64) << 32)
        | ((b5 as u64) << 40)
        | ((b6 as u64) << 48)
        | ((b7 as u64) << 56);
    Ok((val, rest))
}

fn take_bytes<'a>(buf: &'a [u8]) -> Result<(&'a [u8], &'a [u8]), EffectTapeError> {
    let &[b0, b1, b2, b3, ref rest @ ..] = buf else {
        return Err(EffectTapeError::Short);
    };
    let len =
        ((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)) as usize;
    if len > MAX_EFFECT_FIELD_BYTES || rest.len() < len {
        return Err(EffectTapeError::BadLen);
    }
    Ok(rest.split_at(len))
}

fn take_str(buf: &[u8]) -> Result<(String, &[u8]), EffectTapeError> {
    let (raw, rest) = take_bytes(buf)?;
    match std::str::from_utf8(raw) {
        Ok(s) => Ok((s.to_owned(), rest)),
        Err(_) => Err(EffectTapeError::BadUtf8),
    }
}

impl EffectEnvelope {
    /// Encode this offset-addressed effect record into a CRC-checked `astream-wire` frame.
    pub fn encode_frame(&self) -> Result<Vec<u8>, EffectTapeError> {
        let mut payload = Vec::new();
        payload.push(EFFECT_TAPE_VERSION);
        payload.push(self.record.tag_byte());
        put_u64_le(&mut payload, self.seq.0);
        match &self.record {
            EffectRecord::Clock(v) | EffectRecord::Rand(v) | EffectRecord::Mono(v) => {
                put_u64_le(&mut payload, *v);
            }
            EffectRecord::File { path, bytes } => {
                put_bytes_checked(&mut payload, path.as_bytes())?;
                put_bytes_checked(&mut payload, bytes.as_slice())?;
            }
            EffectRecord::FileErr { path, kind } => {
                put_bytes_checked(&mut payload, path.as_bytes())?;
                payload.push(error_kind_to_code(*kind));
            }
            EffectRecord::Exchange {
                door,
                request,
                reply,
            } => {
                put_bytes_checked(&mut payload, door.as_bytes())?;
                put_bytes_checked(&mut payload, request.as_slice())?;
                put_bytes_checked(&mut payload, reply.as_slice())?;
            }
            EffectRecord::Emit { door, bytes } => {
                put_bytes_checked(&mut payload, door.as_bytes())?;
                put_bytes_checked(&mut payload, bytes.as_slice())?;
            }
            EffectRecord::Raised { door, false_reads } => {
                put_bytes_checked(&mut payload, door.as_bytes())?;
                put_u64_le(&mut payload, *false_reads);
            }
        }
        match Frame::new(payload).encode() {
            Ok(framed) => Ok(framed),
            Err(e) => Err(EffectTapeError::Frame(e)),
        }
    }

    /// Decode one CRC-checked `astream-wire` frame into `(EffectEnvelope, bytes_consumed)`.
    pub fn decode_frame(buf: &[u8]) -> Result<(Self, usize), EffectTapeError> {
        let (payload, consumed) = match astream_wire::frame::decode_frame_slice(buf) {
            Ok(Some((payload, consumed))) => (payload, consumed),
            Ok(None) => return Err(EffectTapeError::Short),
            Err(e) => return Err(EffectTapeError::Frame(e)),
        };
        let (ver, r0) = take_u8(payload)?;
        if !envelope_version_matches(ver, EFFECT_TAPE_VERSION) {
            return Err(EffectTapeError::BadVersion(ver));
        }
        let (tag, r1) = take_u8(r0)?;
        let (seq_raw, r2) = take_u64_le(r1)?;
        let (record, tail) = match tag {
            1 => {
                let (v, rest) = take_u64_le(r2)?;
                (EffectRecord::Clock(v), rest)
            }
            2 => {
                let (v, rest) = take_u64_le(r2)?;
                (EffectRecord::Rand(v), rest)
            }
            3 => {
                let (path, r3) = take_str(r2)?;
                let (bytes_slice, rest) = take_bytes(r3)?;
                (
                    EffectRecord::File {
                        path,
                        bytes: bytes_slice.to_vec(),
                    },
                    rest,
                )
            }
            4 => {
                let (path, r3) = take_str(r2)?;
                let (kcode, rest) = take_u8(r3)?;
                let kind = code_to_error_kind(kcode)?;
                (EffectRecord::FileErr { path, kind }, rest)
            }
            5 => {
                let (v, rest) = take_u64_le(r2)?;
                (EffectRecord::Mono(v), rest)
            }
            6 => {
                let (door, r3) = take_str(r2)?;
                let (req_slice, r4) = take_bytes(r3)?;
                let (rep_slice, rest) = take_bytes(r4)?;
                (
                    EffectRecord::Exchange {
                        door,
                        request: req_slice.to_vec(),
                        reply: rep_slice.to_vec(),
                    },
                    rest,
                )
            }
            7 => {
                let (door, r3) = take_str(r2)?;
                let (bytes_slice, rest) = take_bytes(r3)?;
                (
                    EffectRecord::Emit {
                        door,
                        bytes: bytes_slice.to_vec(),
                    },
                    rest,
                )
            }
            8 => {
                let (door, r3) = take_str(r2)?;
                let (false_reads, rest) = take_u64_le(r3)?;
                (EffectRecord::Raised { door, false_reads }, rest)
            }
            other => return Err(EffectTapeError::BadTag(other)),
        };
        if !tail.is_empty() {
            return Err(EffectTapeError::BadLen);
        }
        Ok((
            Self {
                seq: Offset(seq_raw),
                record,
            },
            consumed,
        ))
    }
}

/// Encode a standalone [`EffectsLog`] (such as a `ptrace` foreign-process tape) into
/// monotonic offset-addressed (`0..N`), CRC-checked `astream-wire` frames.
pub fn encode_effects_tape(log: &EffectsLog) -> Result<Vec<u8>, EffectTapeError> {
    if log.0.len() > MAX_FOREIGN_TAPE_RECORDS {
        return Err(EffectTapeError::RecordCapExceeded {
            count: log.0.len(),
            max: MAX_FOREIGN_TAPE_RECORDS,
        });
    }
    let mut out = Vec::new();
    let mut idx = 0u64;
    let mut rest = log.0.as_slice();
    while let [rec, ref tail @ ..] = rest {
        let env = EffectEnvelope {
            seq: Offset(idx),
            record: rec.clone(),
        };
        let frame = env.encode_frame()?;
        out.extend_from_slice(&frame);
        idx = idx.saturating_add(1);
        rest = tail;
    }
    Ok(out)
}

/// Strictly decode a byte stream of CRC-framed [`EffectEnvelope`]s back into an
/// [`EffectsLog`], refusing corrupt frames, trailing bytes, non-monotonic offsets,
/// or tapes exceeding [`MAX_FOREIGN_TAPE_RECORDS`].
pub fn decode_effects_tape_strict(bytes: &[u8]) -> Result<EffectsLog, EffectTapeError> {
    let mut records = Vec::new();
    let mut rest = bytes;
    let mut expected_seq = 0u64;
    while !rest.is_empty() {
        if records.len() >= MAX_FOREIGN_TAPE_RECORDS {
            return Err(EffectTapeError::RecordCapExceeded {
                count: records.len().saturating_add(1),
                max: MAX_FOREIGN_TAPE_RECORDS,
            });
        }
        let (env, consumed) = EffectEnvelope::decode_frame(rest)?;
        if env.seq.0 != expected_seq {
            return Err(EffectTapeError::NonMonotonicSeq {
                expected: expected_seq,
                actual: env.seq.0,
            });
        }
        records.push(env.record);
        expected_seq = expected_seq.saturating_add(1);
        rest = rest.get(consumed..).unwrap_or(&[]);
    }
    Ok(EffectsLog(records))
}

/// Splice foreign-process [`ToolEffectSpan`] tapes onto a unified session event log.
///
/// Each [`ToolEffectSpan`] attaches its recorded [`EffectRecord`]s immediately before
/// the matching `tool_result_index`-th `Event::Cognition(CogRecord::ToolResult { .. })`
/// on the unified offset axis, preserving causal execution order (`In` -> `Out` ->
/// foreign `Effect`s -> `ToolResult` -> next `Completion`). Fails closed if spans are
/// out of order, exceed [`MAX_FOREIGN_TAPE_RECORDS`], reference a missing `ToolResult`,
/// or leave any foreign effect record unconsumed.
pub fn splice_foreign_tape(
    session: &[Event],
    spans: &[ToolEffectSpan],
) -> Result<Vec<Event>, ForeignTapeSpliceError> {
    let mut total_foreign = 0usize;
    let mut prev_index: Option<usize> = None;
    let mut span_rest = spans;
    while let [sp, ref tail @ ..] = span_rest {
        if let Some(prev) = prev_index {
            if sp.tool_result_index <= prev {
                return Err(ForeignTapeSpliceError::SpanOutOfOrder {
                    prev_index: prev,
                    index: sp.tool_result_index,
                });
            }
        }
        prev_index = Some(sp.tool_result_index);
        total_foreign = total_foreign.saturating_add(sp.tape.0.len());
        if total_foreign > MAX_FOREIGN_TAPE_RECORDS {
            return Err(ForeignTapeSpliceError::RecordCapExceeded {
                requested: total_foreign,
                max: MAX_FOREIGN_TAPE_RECORDS,
            });
        }
        span_rest = tail;
    }

    let clamped_total =
        foreign_tape_clamp_records(total_foreign as u64, MAX_FOREIGN_TAPE_RECORDS as u64);
    let _ = clamped_total;
    let mut out = Vec::new();

    let mut pending_spans = spans;
    let mut record_cursor = 0u64;
    let mut tool_result_ordinal = 0usize;
    let mut ev_rest = session;
    while let [ev, ref ev_tail @ ..] = ev_rest {
        if let Event::Cognition(CogRecord::ToolResult { .. }) = ev {
            if let [sp, ref sp_tail @ ..] = pending_spans {
                if sp.tool_result_index == tool_result_ordinal {
                    let mut r_rest = sp.tape.0.as_slice();
                    while let [rec, ref r_tail @ ..] = r_rest {
                        out.push(Event::Effect(rec.clone()));
                        let proposed = record_cursor.saturating_add(1);
                        let bounded = foreign_tape_clamp_records(proposed, clamped_total);
                        record_cursor = foreign_tape_cursor_advance(record_cursor, bounded);
                        r_rest = r_tail;
                    }
                    pending_spans = sp_tail;
                }
            }
            tool_result_ordinal = tool_result_ordinal.saturating_add(1);
        }
        out.push(ev.clone());
        ev_rest = ev_tail;
    }

    if let [unmatched, ..] = pending_spans {
        return Err(ForeignTapeSpliceError::MissingToolResult {
            target_index: unmatched.tool_result_index,
            observed_tool_results: tool_result_ordinal,
        });
    }
    if !foreign_tape_exhausted(record_cursor, clamped_total) {
        return Err(ForeignTapeSpliceError::UnconsumedRecords {
            remaining: (clamped_total.saturating_sub(record_cursor)) as usize,
        });
    }
    Ok(out)
}

/// Splice foreign-process [`ToolEffectSpan`] tapes onto `session` and run the hermetic
/// four-stream [`replay_session`] fold on one unified offset axis.
pub fn replay_session_with_foreign_tape(
    session: &[Event],
    spans: &[ToolEffectSpan],
    cols: u16,
    rows: u16,
) -> Result<Replay, ForeignTapeSpliceError> {
    let unified = splice_foreign_tape(session, spans)?;
    Ok(replay_session(&unified, cols, rows))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cog::{StopReason, ToolUse};
    use crate::unified::fork_session;

    #[test]
    fn effects_tape_roundtrips_all_eight_record_kinds_and_refuses_corruption() {
        let log = EffectsLog(vec![
            EffectRecord::Clock(1_700_000_000_123),
            EffectRecord::Rand(0xdead_beef_cafe_babe),
            EffectRecord::File {
                path: "/etc/hostname".to_owned(),
                bytes: b"node-a\n".to_vec(),
            },
            EffectRecord::FileErr {
                path: "/missing".to_owned(),
                kind: ErrorKind::NotFound,
            },
            EffectRecord::Mono(42_000),
            EffectRecord::Exchange {
                door: "ctl".to_owned(),
                request: b"ping".to_vec(),
                reply: b"pong".to_vec(),
            },
            EffectRecord::Emit {
                door: "journal".to_owned(),
                bytes: b"row-1".to_vec(),
            },
            EffectRecord::Raised {
                door: "stop".to_owned(),
                false_reads: 7,
            },
        ]);

        let bytes = encode_effects_tape(&log).expect("encode tape");
        let decoded = decode_effects_tape_strict(&bytes).expect("decode tape");
        assert_eq!(decoded, log);

        // Flipping one payload byte triggers CRC refusal.
        let mut corrupted = bytes.clone();
        let last = corrupted.len() - 1;
        corrupted[last] ^= 0x01;
        assert!(matches!(
            decode_effects_tape_strict(&corrupted),
            Err(EffectTapeError::Frame(_))
        ));

        // Out-of-order sequence offset is refused even when CRC is valid.
        let bad_seq = EffectEnvelope {
            seq: Offset(5),
            record: EffectRecord::Clock(1),
        }
        .encode_frame()
        .expect("encode bad_seq");
        assert_eq!(
            decode_effects_tape_strict(&bad_seq),
            Err(EffectTapeError::NonMonotonicSeq {
                expected: 0,
                actual: 5,
            })
        );
    }

    #[test]
    fn splice_foreign_tape_feeds_unified_replay_and_diverges_on_counterfactual_fork() {
        let base_session = vec![
            Event::In(b"check build\n".to_vec()),
            Event::Cognition(CogRecord::Completion {
                text: "running tool 0".to_owned(),
                calls: vec![ToolUse {
                    id: "call-0".to_owned(),
                    name: "foreign_probe".to_owned(),
                    input: b"{}".to_vec(),
                }],
                stop: StopReason::ToolUse,
            }),
            Event::Out(b"probe 0 failed\r\n".to_vec()),
            Event::Cognition(CogRecord::ToolResult {
                tool_use_id: "call-0".to_owned(),
                content: b"BUILD FAILED".to_vec(),
                is_error: true,
            }),
            Event::Cognition(CogRecord::Completion {
                text: "retrying with tool 1".to_owned(),
                calls: vec![ToolUse {
                    id: "call-1".to_owned(),
                    name: "foreign_fix".to_owned(),
                    input: b"{}".to_vec(),
                }],
                stop: StopReason::ToolUse,
            }),
            Event::Out(b"probe 1 ok\r\n".to_vec()),
            Event::Cognition(CogRecord::ToolResult {
                tool_use_id: "call-1".to_owned(),
                content: b"BUILD OK".to_vec(),
                is_error: false,
            }),
            Event::Cognition(CogRecord::Completion {
                text: "done".to_owned(),
                calls: vec![],
                stop: StopReason::EndTurn,
            }),
        ];

        // Foreign ptrace child 0 recorded Clock + Rand + File; child 1 recorded Clock + File.
        let spans = vec![
            ToolEffectSpan {
                tool_result_index: 0,
                tape: EffectsLog(vec![
                    EffectRecord::Clock(100),
                    EffectRecord::Rand(200),
                    EffectRecord::File {
                        path: "/workspace/status".to_owned(),
                        bytes: b"FAIL".to_vec(),
                    },
                ]),
            },
            ToolEffectSpan {
                tool_result_index: 1,
                tape: EffectsLog(vec![
                    EffectRecord::Clock(300),
                    EffectRecord::File {
                        path: "/workspace/status".to_owned(),
                        bytes: b"OK".to_vec(),
                    },
                ]),
            },
        ];

        let unified = splice_foreign_tape(&base_session, &spans).expect("splice foreign tapes");
        assert_eq!(unified.len(), base_session.len() + 5);

        let full_replay = replay_session(&unified, 80, 24);
        let direct_replay =
            replay_session_with_foreign_tape(&base_session, &spans, 80, 24).expect("direct replay");
        assert_eq!(full_replay, direct_replay);

        // Without the foreign tape, effect_digest is just the FNV offset basis.
        let empty_replay = replay_session(&base_session, 80, 24);
        assert_ne!(full_replay.effect_digest, empty_replay.effect_digest);

        // Counterfactual fork: swap tool result 0 (now at index 2 + 3 = 6) to finish early
        // by replacing the completion after it with EndTurn, proving child 1's foreign
        // syscalls are NOT folded when the branch finishes early!
        let forked = fork_session(
            &unified,
            7,
            Event::Cognition(CogRecord::Completion {
                text: "early finish".to_owned(),
                calls: vec![],
                stop: StopReason::EndTurn,
            }),
        );
        let forked_replay = replay_session(&forked, 80, 24);
        assert_ne!(forked_replay.effect_digest, full_replay.effect_digest);
        assert_ne!(forked_replay.effect_digest, empty_replay.effect_digest);
        assert!(forked_replay.events_reached < full_replay.events_reached);
    }

    #[test]
    fn splice_foreign_tape_refuses_out_of_order_or_missing_tool_result() {
        let session = vec![Event::Cognition(CogRecord::ToolResult {
            tool_use_id: "c0".to_owned(),
            content: b"ok".to_vec(),
            is_error: false,
        })];
        let bad_order = vec![
            ToolEffectSpan {
                tool_result_index: 1,
                tape: EffectsLog(vec![EffectRecord::Clock(1)]),
            },
            ToolEffectSpan {
                tool_result_index: 1,
                tape: EffectsLog(vec![EffectRecord::Clock(2)]),
            },
        ];
        assert_eq!(
            splice_foreign_tape(&session, &bad_order),
            Err(ForeignTapeSpliceError::SpanOutOfOrder {
                prev_index: 1,
                index: 1,
            })
        );

        let missing = vec![ToolEffectSpan {
            tool_result_index: 1,
            tape: EffectsLog(vec![EffectRecord::Clock(1)]),
        }];
        assert_eq!(
            splice_foreign_tape(&session, &missing),
            Err(ForeignTapeSpliceError::MissingToolResult {
                target_index: 1,
                observed_tool_results: 1,
            })
        );
    }
}
