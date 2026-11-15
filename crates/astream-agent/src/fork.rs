//! Record a turn to a cognition log, decode it back, and counterfactually fork it.
//!
//! ## Formal Verification (`clean` Island — TLA+ Counterfactual Fork Prefix Stability)
//!
//! This module embeds a machine-checked Clean specification (`Astream.Agent.TlaCounterfactualFork`)
//! of counterfactual cognition-log forking:
//! - Swapping the record at `forkAt < logLen` produces a forked log where `curLog forkAt = replacementVal`
//!   and every other index `i ≠ forkAt` (and in particular every prefix index `i < forkAt`)
//!   is identically preserved (`curLog i = origLog i`), proving `Spec orig n ⊨ □ (Lift PrefixStabilityInv)`
//!   and `strict_prefix_untouched`.

use crate::cog::CogRecord;
use crate::envelope::{encode_record, CogEnvelope, CogError};
use astream_wire::Offset;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "fork_island.rs"]
mod fork_island;
#[cfg(not(clean_islands))]
pub use crate::twins::fork_prefix_bound;
#[cfg(clean_islands)]
pub use fork_island::fork_prefix_bound;

contract_fn! {
    /// Pure offset-bounds predicate linked to the Clean island's `fork_offset_in_range_isl`
    /// and discharged via `clean-kernel-defeq`.
    #[must_use]
    pub const fn fork_offset_in_range(at_off: u64, len: u64) -> bool
    clauses [ensures result == (at_off < len)]
    {
        at_off < len
    }
}

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
    // The undecoded tail. Advancing by re-slicing (rather than `pos += consumed`)
    // leaves no offset arithmetic to overflow. `Frame::decode` reports at most the
    // bytes it was given, so the re-slice is in range; were it not, decoding stops.
    let mut rest = log;
    while !rest.is_empty() {
        match astream_wire::frame::decode_frame_slice(rest) {
            Ok(Some((payload, consumed))) => {
                match CogEnvelope::from_payload(payload) {
                    Ok(env) => records.push(env.record),
                    Err(_) => break,
                }
                let Some(tail) = rest.get(consumed..) else {
                    break;
                };
                rest = tail;
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
    // The undecoded tail, advanced by re-slicing as in [`decode_turn`].
    let mut rest = log;
    while !rest.is_empty() {
        match astream_wire::frame::decode_frame_slice(rest) {
            Ok(Some((payload, consumed))) => {
                let env = CogEnvelope::from_payload(payload)?;
                records.push(env.record);
                // In range by `decode_frame_slice`'s contract; were it not, fail closed.
                rest = rest.get(consumed..).ok_or(crate::CogError::BadLen)?;
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
const fn index_in(records: &[CogRecord], at: Offset) -> Option<usize> {
    let len = records.len() as u64;
    if at.0 >= len {
        return None;
    }
    let bounded = if at.0 < len { at.0 } else { len };
    if bounded > usize::MAX as u64 {
        return None;
    }
    let i = bounded as usize;
    if i < records.len() {
        Some(i)
    } else {
        None
    }
}

/// Return the intact prefix of `records` strictly preceding `at` (clamped to
/// `records.len()` via the Clean-origin [`fork_prefix_bound`]).
#[must_use]
pub fn cog_fork_prefix(records: &[CogRecord], at: Offset) -> &[CogRecord] {
    let len = records.len();
    let end = if at.0 < len as u64 {
        at.0 as usize
    } else {
        len
    };
    match records.get(..end) {
        Some(s) => s,
        None => records,
    }
}

/// Counterfactual fork: return a copy of `records` with the record at `at`
/// replaced — e.g. swapping a `BUILD FAILED` tool result for `BUILD OK`. Out-of-
/// range leaves the records unchanged (lenient). Use [`try_cog_fork_swap`] when
/// the caller needs to know the offset was in range.
pub fn cog_fork_swap(records: &[CogRecord], at: Offset, replacement: CogRecord) -> Vec<CogRecord> {
    let mut out = records.to_vec();
    if let Some(i) = index_in(records, at) {
        if let Some(slot) = out.get_mut(i) {
            *slot = replacement;
        }
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
    if let Some(slot) = out.get_mut(i) {
        *slot = replacement;
    }
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

    #[test]
    fn decode_turn_advances_frame_by_frame_and_handles_trailing_garbage() {
        // Two turns back to back decode as one run of records, frame by frame.
        let mut log = record_turn(5, &recs()).unwrap();
        log.extend_from_slice(&record_turn(6, &recs()[..1]).unwrap());
        let mut want = recs();
        want.push(recs()[0].clone());
        assert_eq!(decode_turn(&log), want);
        assert_eq!(decode_turn_strict(&log).unwrap(), want);
        // A garbage byte after the last frame: lenient keeps the intact prefix,
        // strict reports it.
        log.push(0xFF);
        assert_eq!(decode_turn(&log), want);
        assert!(decode_turn_strict(&log).is_err());
        // An empty log is empty under both forms.
        assert!(decode_turn(&[]).is_empty());
        assert_eq!(decode_turn_strict(&[]).unwrap(), vec![]);
    }
}
