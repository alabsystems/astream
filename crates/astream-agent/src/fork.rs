//! Record a turn to a cognition log, decode it back, and counterfactually fork it.

use crate::cog::CogRecord;
use crate::envelope::{encode_record, CogEnvelope, CogError};
use astream_wire::{Frame, Offset};

/// Record a turn as a cognition log: each [`CogRecord`] framed as a `COG_VERSION`
/// envelope at its offset, with a fixed `ts_logical = seed` (deterministic). The
/// returned bytes are the durable, replayable cognition log.
///
/// Fails closed, never panics: a record that cannot be framed — a tool result or
/// completion whose payload exceeds the wire frame's `MAX_PAYLOAD_LEN` (16 MiB)
/// — is `Err(CogError::Frame(FrameError::TooLarge))`, so an oversize `cat` of a
/// build log surfaces to the caller instead of aborting the recording process
/// (and losing every earlier record of the turn with it).
pub fn record_turn(seed: u64, records: &[CogRecord]) -> Result<Vec<u8>, CogError> {
    let mut out = Vec::new();
    for (i, r) in records.iter().enumerate() {
        out.extend_from_slice(&encode_record(Offset(i as u64), seed, r)?);
    }
    Ok(out)
}

/// Decode a cognition log back into its records, in order. Stops at the first
/// malformed/incomplete frame (panic-free, lenient — matches the engine's
/// recover-the-intact-prefix posture). When the caller needs to *know* the log
/// was fully intact, use [`decode_turn_strict`].
pub fn decode_turn(log: &[u8]) -> Vec<CogRecord> {
    let mut records = Vec::new();
    let mut pos = 0;
    while pos < log.len() {
        match Frame::decode(&log[pos..]) {
            Ok(Some(decoded)) => {
                match CogEnvelope::from_payload(&decoded.frame.payload) {
                    Ok(env) => records.push(env.record),
                    Err(_) => break,
                }
                pos += decoded.consumed;
            }
            _ => break,
        }
    }
    records
}

/// Like [`decode_turn`], but **strict**: any malformed/corrupt/incomplete frame
/// is an `Err`, not a silent truncation. A clean end-of-log (no trailing bytes)
/// is `Ok`. Use this when a partial decode would be data loss the caller must not
/// miss; use [`decode_turn`] when recovering the longest intact prefix is desired.
pub fn decode_turn_strict(log: &[u8]) -> Result<Vec<CogRecord>, crate::CogError> {
    let mut records = Vec::new();
    let mut pos = 0;
    while pos < log.len() {
        match Frame::decode(&log[pos..]) {
            Ok(Some(decoded)) => {
                let env = CogEnvelope::from_payload(&decoded.frame.payload)?;
                records.push(env.record);
                pos += decoded.consumed;
            }
            // A trailing incomplete frame is a torn tail — surfaced, not dropped.
            Ok(None) => return Err(crate::CogError::Short),
            Err(e) => return Err(crate::CogError::Frame(e)),
        }
    }
    Ok(records)
}

/// The index `at` names inside `records`, if it is in range. An `Offset` is a
/// 64-bit log position; on a target whose `usize` is narrower a truncating cast
/// would alias `Offset(1 << 32 | 1)` to index 1 and swap the WRONG record, so the
/// conversion is checked and an unrepresentable offset is simply out of range.
fn index_in(records: &[CogRecord], at: Offset) -> Option<usize> {
    usize::try_from(at.0).ok().filter(|&i| i < records.len())
}

/// Counterfactual fork: return a copy of `records` with the record at `at`
/// replaced — e.g. swapping a `BUILD FAILED` tool result for `BUILD OK`. Out-of-
/// range leaves the records unchanged (lenient). Use [`try_cog_fork_swap`] when
/// the caller needs to know the offset was in range.
pub fn cog_fork_swap(records: &[CogRecord], at: Offset, replacement: CogRecord) -> Vec<CogRecord> {
    let mut out = records.to_vec();
    if let Some(i) = index_in(records, at) {
        out[i] = replacement;
    }
    out
}

/// Like [`cog_fork_swap`], but returns `None` if `at` is past the end of
/// `records` — so forking at a bad offset is a signal, not a silent no-op.
pub fn try_cog_fork_swap(
    records: &[CogRecord],
    at: Offset,
    replacement: CogRecord,
) -> Option<Vec<CogRecord>> {
    let i = index_in(records, at)?;
    let mut out = records.to_vec();
    out[i] = replacement;
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cog::StopReason;
    use astream_wire::{FrameError, MAX_PAYLOAD_LEN};

    fn recs() -> Vec<CogRecord> {
        vec![
            CogRecord::Completion {
                text: "go".into(),
                calls: vec![],
                stop: StopReason::EndTurn,
            },
            CogRecord::ToolResult {
                tool_use_id: "t".into(),
                content: b"BUILD FAILED".to_vec(),
                is_error: true,
            },
        ]
    }

    fn ok_result() -> CogRecord {
        CogRecord::ToolResult {
            tool_use_id: "t".into(),
            content: b"BUILD OK".to_vec(),
            is_error: false,
        }
    }

    #[test]
    fn try_cog_fork_swap_signals_out_of_range() {
        let r = recs();
        // In range: swaps and returns Some.
        let forked = try_cog_fork_swap(&r, Offset(1), ok_result()).expect("in-range swap");
        assert_eq!(forked[1], ok_result());
        assert_eq!(forked[0], r[0], "prefix untouched");
        // Out of range: None, not a silent unchanged copy.
        assert!(try_cog_fork_swap(&r, Offset(2), ok_result()).is_none());
        assert!(try_cog_fork_swap(&r, Offset(99), ok_result()).is_none());
        // The lenient form still returns an unchanged copy for the bad offset.
        assert_eq!(cog_fork_swap(&r, Offset(2), ok_result()), r);
    }

    #[test]
    fn fork_offsets_wider_than_usize_are_out_of_range_not_aliased() {
        // An Offset is 64-bit. `(1 << 32) | 1` truncates to index 1 under a
        // `u64 as usize` cast on a 32-bit target (swapping the wrong record and
        // returning Some); the checked conversion makes it out of range on every
        // target. On 64-bit it is out of range either way; the u64::MAX probe is
        // the same contract at the far end.
        let r = recs();
        for bad in [Offset((1u64 << 32) | 1), Offset(u64::MAX)] {
            assert!(
                try_cog_fork_swap(&r, bad, ok_result()).is_none(),
                "{bad:?} must be out of range, never aliased to a low index"
            );
            assert_eq!(cog_fork_swap(&r, bad, ok_result()), r);
        }
    }

    #[test]
    fn decode_turn_strict_errs_on_a_torn_tail() {
        let log = record_turn(5, &recs()).unwrap();
        // A clean, intact log decodes fully under both forms.
        assert_eq!(decode_turn_strict(&log).unwrap(), recs());
        assert_eq!(decode_turn(&log), recs());
        // Truncate the final frame: lenient recovers the prefix, strict surfaces it.
        let torn = &log[..log.len() - 1];
        let lenient = decode_turn(torn);
        assert!(
            lenient.len() < recs().len(),
            "lenient drops the torn record"
        );
        assert!(
            decode_turn_strict(torn).is_err(),
            "strict surfaces the torn tail"
        );
    }

    #[test]
    fn record_turn_errs_on_an_oversize_record_instead_of_panicking() {
        // A tool result one byte past the 16 MiB frame cap (a `cat` of a large
        // build log) must surface as Err, not abort the recording process — and
        // the earlier, well-formed records must still record on their own.
        let mut r = recs();
        r.push(CogRecord::ToolResult {
            tool_use_id: "big".into(),
            content: vec![b'x'; MAX_PAYLOAD_LEN + 1],
            is_error: false,
        });
        assert_eq!(
            record_turn(5, &r),
            Err(CogError::Frame(FrameError::TooLarge)),
            "an oversize record is a checked error"
        );
        assert_eq!(decode_turn(&record_turn(5, &r[..2]).unwrap()), recs());
    }
}
