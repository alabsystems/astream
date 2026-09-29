//! Rung 2: resume + roaming. The `/a/state` projection and the exactly-once
//! input boundary — the two halves of "a connection is just a cursor over the
//! log".
//!
//! ## Resume ([`materialize`] + [`resume`])
//!
//! `/a/state` is the screen folded up to some offset `K`, captured as a
//! [`StateSnapshot`] with full parser state (via [`astream_term::Folder`]). A
//! reattaching client paints that snapshot, then folds **only the log tail after
//! `K`** — never re-folding the prefix — and lands on the exact screen of a
//! never-dropped run. Because the snapshot carries parser state, this is exact
//! even when an escape sequence straddles `K`.
//!
//! A snapshot never claims more than it folded: `K` is clamped to the records
//! it was given, and an empty log yields a snapshot that has folded *nothing*
//! ([`StateSnapshot::folded_through`] is `None`), so a record that arrives later
//! at offset 0 is applied on resume, not skipped.
//!
//! ## Exactly-once input ([`Session`])
//!
//! Input proposals are deduped by `(client_id, client_seq)` at the single ingest
//! point, so a keystroke re-sent after a drop is applied at most once. The
//! high-water is rebuildable from the log ([`high_water_from_log`]), so the
//! exactly-once guarantee survives a reconnect or crash — and a recovered log
//! is **continued**, not restarted, by [`Session::resume_from`], which sets the
//! next offset past the stored records and the seam clock past their
//! `ts_logical`s.
//!
//! ## Single writer ([`Session::apply_input_as`])
//!
//! A shared session takes input through its [`ControlToken`]: a non-holder's
//! proposal is refused before it reaches the dedup map or the log.
//!
//! Deferred: the *wire serialization* of `/a/state` (here the snapshot is an
//! in-memory folder clone) and the live transport.

use crate::control::ControlToken;
use crate::effects::{Clock, Disk, Effects};
use crate::envelope::{CausedBy, Envelope};
use crate::log::{EngineError, Log, ReadError};
use astream_term::{Folder, Record, Screen};
use astream_wire::Offset;
use std::collections::HashMap;

/// A materialized `/a/state`: the folded screen as of [`folded_through`], with
/// full parser state so resume is exact.
///
/// [`folded_through`]: StateSnapshot::folded_through
#[derive(Debug, Clone)]
pub struct StateSnapshot {
    folded_through: Option<Offset>,
    folder: Folder,
}

impl StateSnapshot {
    /// The screen as of the snapshot offset.
    pub fn screen(&self) -> &Screen {
        self.folder.screen()
    }

    /// The last offset this snapshot incorporates, or `None` if it folded no
    /// record at all (a snapshot of an empty log). Never beyond what was folded.
    pub fn folded_through(&self) -> Option<Offset> {
        self.folded_through
    }

    /// The offset a client tails the log from: the one after
    /// [`folded_through`](Self::folded_through), or [`Offset::ZERO`] when
    /// nothing was folded.
    pub fn next_offset(&self) -> Offset {
        match self.folded_through {
            // A folded offset came from a record index, so it is far below u64::MAX.
            Some(k) => k.checked_next().unwrap_or(Offset(u64::MAX)),
            None => Offset::ZERO,
        }
    }
}

/// The number of leading records `records[..n]` to fold for a snapshot through
/// `folded_through`, clamped to what exists.
fn prefix_len(records: &[Record], folded_through: Offset) -> usize {
    usize::try_from(folded_through.0)
        .ok()
        .and_then(|k| k.checked_add(1))
        .map_or(records.len(), |n| n.min(records.len()))
}

/// Materialize `/a/state` by folding `records[0..=folded_through]`. Records are a
/// dense log starting at [`Offset::ZERO`], so a record's position is its offset.
///
/// The snapshot is stamped with what was **actually** folded: a `folded_through`
/// past the end is clamped to the last record, and an empty `records` yields a
/// snapshot whose [`StateSnapshot::folded_through`] is `None`. Use
/// [`try_materialize`] to be told when the requested offset was out of range.
pub fn materialize(
    cols: u16,
    rows: u16,
    records: &[Record],
    folded_through: Offset,
) -> StateSnapshot {
    let mut folder = Folder::new(cols, rows);
    let take = prefix_len(records, folded_through);
    for rec in &records[..take] {
        folder.apply(rec);
    }
    StateSnapshot {
        folded_through: take.checked_sub(1).map(|i| Offset(i as u64)),
        folder,
    }
}

/// [`materialize`], but `None` when `folded_through` names no record in
/// `records` (past the end, or an empty log) — for a caller that must know the
/// snapshot covers exactly the offset it asked for.
pub fn try_materialize(
    cols: u16,
    rows: u16,
    records: &[Record],
    folded_through: Offset,
) -> Option<StateSnapshot> {
    let in_range = usize::try_from(folded_through.0).is_ok_and(|k| k < records.len());
    in_range.then(|| materialize(cols, rows, records, folded_through))
}

/// Resume from a snapshot: paint it, then fold only the records after
/// `folded_through` — no replay of the prefix — yielding the current screen.
pub fn resume(snapshot: &StateSnapshot, records: &[Record]) -> Screen {
    let mut folder = snapshot.folder.clone();
    let start = usize::try_from(snapshot.next_offset().0).unwrap_or(usize::MAX);
    for rec in records.iter().skip(start) {
        folder.apply(rec);
    }
    folder.into_screen()
}

/// Rebuild the per-client input high-water (the max `client_seq` seen per
/// `client_id`) from the log, so exactly-once dedup survives a reconnect or crash.
pub fn high_water_from_log(records: &[Record]) -> HashMap<u64, u64> {
    let mut hw = HashMap::new();
    for rec in records {
        if let Record::In {
            client_id,
            client_seq,
            ..
        } = rec
        {
            bump_high_water(&mut hw, *client_id, *client_seq);
        }
    }
    hw
}

fn bump_high_water(hw: &mut HashMap<u64, u64>, client_id: u64, client_seq: u64) {
    hw.entry(client_id)
        .and_modify(|h: &mut u64| *h = (*h).max(client_seq))
        .or_insert(client_seq);
}

/// A single-session writer that dedups input and appends to the log. The
/// exactly-once boundary: an input proposal is applied at most once per
/// `(client_id, client_seq)`.
pub struct Session<E: Effects> {
    log: Log,
    fx: E,
    high_water: HashMap<u64, u64>,
}

impl<E: Effects> Session<E> {
    /// A fresh session with an empty log.
    pub fn new(fx: E) -> Session<E> {
        Session {
            log: Log::new(),
            fx,
            high_water: HashMap::new(),
        }
    }

    /// A session whose dedup high-water is restored from a prior log (see
    /// [`high_water_from_log`]) but whose log is a **new offset axis** starting
    /// at [`Offset::ZERO`] on the seam's disk. It must not share a disk with the
    /// records the high-water came from — appending `seq 0` after `seq n-1`
    /// is exactly the corruption every reader stops at. To continue a recovered
    /// log in place, use [`resume_from`](Self::resume_from).
    pub fn with_high_water(fx: E, high_water: HashMap<u64, u64>) -> Session<E> {
        Session {
            log: Log::new(),
            fx,
            high_water,
        }
    }

    /// Resume over a seam whose disk already holds a recovered log: **continue**
    /// it. The stored records are decoded once to rebuild the dedup high-water,
    /// the next offset is set to one past the last stored record, and the seam
    /// clock is advanced past the largest stored `ts_logical` — so new records
    /// extend the same dense, clock-monotone axis and a later recover/read pass
    /// accepts the whole log.
    ///
    /// The disk must hold an intact log (e.g. the recovered prefix from
    /// [`crate::FileLog::open`]); a decode error, or a log that ends mid-frame
    /// ([`ReadError::Incomplete`]), is returned rather than resumed over. An
    /// empty disk resumes as a fresh session.
    pub fn resume_from(mut fx: E) -> Result<Session<E>, ReadError> {
        let mut high_water = HashMap::new();
        let mut next = Offset::ZERO;
        let mut last_ts: Option<u64> = None;
        let mut reader = Log::read_from(fx.disk(), Offset::ZERO);
        for item in &mut reader {
            let env = item?;
            if let Record::In {
                client_id,
                client_seq,
                ..
            } = env.record
            {
                bump_high_water(&mut high_water, client_id, client_seq);
            }
            last_ts = Some(last_ts.map_or(env.ts_logical, |t| t.max(env.ts_logical)));
            next = env.seq.checked_next().ok_or(ReadError::OffsetOverflow)?;
        }
        // Appending after a partial frame would make it swallow the new records.
        if let Some(at) = reader.incomplete_at() {
            return Err(ReadError::Incomplete { at });
        }
        if let Some(ts) = last_ts {
            fx.clock().advance_past(ts);
        }
        Ok(Session {
            log: Log::at(next),
            fx,
            high_water,
        })
    }

    /// The offset the next appended record will be assigned.
    pub fn next_offset(&self) -> Offset {
        self.log.next_offset()
    }

    /// Whether an input proposal would be a duplicate — `client_seq` at or below
    /// the client's recorded high-water. A read-only dedup check that commits
    /// nothing.
    ///
    /// For the deliver-then-commit pattern (write the keystroke to a PTY, then
    /// [`apply_input`](Self::apply_input)), this check alone is not enough for
    /// at-most-once: if the commit fails *after* delivery, the high-water stays
    /// unbumped and a re-send delivers the keystroke again. A commit can fail
    /// only when the `In` is unencodable (a body over the frame's 16 MiB
    /// `MAX_PAYLOAD_LEN` cap) or on offset overflow — both decidable up front —
    /// so use [`precheck_input`](Self::precheck_input), which also checks those,
    /// and then a commit after delivery cannot fail.
    pub fn is_duplicate(&self, client_id: u64, client_seq: u64) -> bool {
        self.high_water
            .get(&client_id)
            .is_some_and(|h| client_seq <= *h)
    }

    /// The full pre-delivery check for an input proposal of `body_len` bytes:
    /// `Ok(false)` if it is a duplicate (deliver nothing), `Ok(true)` if it is
    /// fresh **and** a following [`apply_input`](Self::apply_input) of it cannot
    /// fail (encodable, offset available), `Err` with the reason it would fail.
    /// Commits nothing. A caller that delivers a side effect only after `Ok(true)`
    /// keeps at-most-once even though delivery precedes the commit.
    pub fn precheck_input(
        &self,
        client_id: u64,
        client_seq: u64,
        body_len: usize,
    ) -> Result<bool, EngineError> {
        if self.is_duplicate(client_id, client_seq) {
            return Ok(false);
        }
        Envelope::check_in_encodable(body_len, None).map_err(EngineError::Envelope)?;
        self.log
            .next_offset()
            .checked_next()
            .ok_or(EngineError::OffsetOverflow)?;
        Ok(true)
    }

    /// Apply an input proposal exactly once. Returns the offset of the appended
    /// `In` record, or `None` if it was a duplicate (`client_seq` at or below the
    /// client's high-water). Takes no [`ControlToken`]: this is the single-writer
    /// path; a shared session ingests through [`apply_input_as`](Self::apply_input_as).
    pub fn apply_input(
        &mut self,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
    ) -> Result<Option<Offset>, EngineError> {
        self.ingest(client_id, client_seq, bytes, None)
    }

    /// [`apply_input`](Self::apply_input) **gated by the session's control token**:
    /// only the holder's input is applied. A non-holder gets
    /// [`EngineError::NotHolder`] before the dedup map or the log is touched, so
    /// a read-only client's keystroke leaves no trace.
    pub fn apply_input_as(
        &mut self,
        token: &ControlToken,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
    ) -> Result<Option<Offset>, EngineError> {
        token.check(client_id)?;
        self.ingest(client_id, client_seq, bytes, None)
    }

    /// Append PTY output to the log.
    pub fn append_output(&mut self, bytes: Vec<u8>) -> Result<Offset, EngineError> {
        self.log.append(&mut self.fx, Record::Out(bytes))
    }

    /// Append PTY output stamped with the in-offset it echoes (a same-log
    /// self-cause), so an echo can be matched to the keystroke it answers. The
    /// log checks that a same-log cause precedes this record
    /// ([`EngineError::CauseNotEarlier`] otherwise).
    pub fn append_output_caused(
        &mut self,
        bytes: Vec<u8>,
        caused_by: CausedBy,
    ) -> Result<Offset, EngineError> {
        self.log
            .append_caused(&mut self.fx, Record::Out(bytes), Some(caused_by))
    }

    /// Apply an input proposal that was **caused** by another record (an injected
    /// `In` naming the orchestrator `Out` that produced it). Same exactly-once
    /// dedup as [`apply_input`](Self::apply_input); the cause is stamped durably on
    /// the record's envelope header so it survives crash/reconnect.
    pub fn apply_input_caused(
        &mut self,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
        caused_by: CausedBy,
    ) -> Result<Option<Offset>, EngineError> {
        self.ingest(client_id, client_seq, bytes, Some(caused_by))
    }

    /// [`apply_input_caused`](Self::apply_input_caused) gated by the control token,
    /// exactly like [`apply_input_as`](Self::apply_input_as).
    pub fn apply_input_caused_as(
        &mut self,
        token: &ControlToken,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
        caused_by: CausedBy,
    ) -> Result<Option<Offset>, EngineError> {
        token.check(client_id)?;
        self.ingest(client_id, client_seq, bytes, Some(caused_by))
    }

    /// The one ingest point: dedup, append, then bump the high-water (only after
    /// the append succeeded, so a failed commit leaves the proposal re-sendable).
    fn ingest(
        &mut self,
        client_id: u64,
        client_seq: u64,
        bytes: Vec<u8>,
        caused_by: Option<CausedBy>,
    ) -> Result<Option<Offset>, EngineError> {
        if self.is_duplicate(client_id, client_seq) {
            return Ok(None);
        }
        let off = self.log.append_caused(
            &mut self.fx,
            Record::In {
                bytes,
                client_id,
                client_seq,
            },
            caused_by,
        )?;
        self.high_water.insert(client_id, client_seq);
        Ok(Some(off))
    }

    /// The stored log bytes (for replay or `/a/state` materialization).
    pub fn log_bytes(&mut self) -> Vec<u8> {
        self.fx.disk().read_all().to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::{MemDisk, Seeded};
    use crate::envelope::EnvelopeError;
    use astream_wire::{FrameError, MAX_PAYLOAD_LEN};

    /// The largest `In` body the frame cap admits, found from the top so the
    /// envelope's length arithmetic is not restated here.
    fn max_in_body() -> usize {
        (0..=MAX_PAYLOAD_LEN)
            .rev()
            .find(|n| Envelope::check_in_encodable(*n, None).is_ok())
            .expect("some In body fits")
    }

    #[test]
    fn precheck_input_decides_dedup_and_commitability_before_delivery() {
        let mut s = Session::new(Seeded::new(1));
        // Fresh and encodable: deliver, and the commit that follows cannot fail.
        assert_eq!(s.precheck_input(7, 1, 3), Ok(true));
        assert_eq!(s.apply_input(7, 1, b"abc".to_vec()), Ok(Some(Offset(0))));
        // Now a duplicate: deliver nothing.
        assert_eq!(s.precheck_input(7, 1, 3), Ok(false));
        // An unencodable body is refused up front, with the reason the commit
        // would have given after delivery.
        assert_eq!(
            s.precheck_input(7, 2, MAX_PAYLOAD_LEN + 1),
            Err(EngineError::Envelope(EnvelopeError::Frame(
                FrameError::TooLarge
            )))
        );
        // At the exact boundary the precheck and the commit agree both ways.
        let max = max_in_body();
        assert_eq!(s.precheck_input(7, 2, max), Ok(true));
        assert_eq!(s.apply_input(7, 2, vec![b'x'; max]), Ok(Some(Offset(1))));
        assert!(s.precheck_input(7, 3, max + 1).is_err());
        assert!(s.apply_input(7, 3, vec![b'x'; max + 1]).is_err());
    }

    #[test]
    fn resume_from_refuses_a_log_that_ends_mid_frame() {
        let mut a = Session::new(Seeded::new(1));
        a.append_output(b"one".to_vec()).unwrap();
        a.append_output(b"two".to_vec()).unwrap();
        let bytes = a.log_bytes();
        // The last frame is cut short and was never recovered. Continuing would
        // append after those bytes, and the torn frame would then swallow the
        // new records' bytes as its own payload: everything appended is lost.
        let torn = bytes[..bytes.len() - 1].to_vec();
        let second = bytes.len() / 2; // the two frames are the same length
        let resumed = Session::resume_from(Seeded::with_disk(1, MemDisk::from_bytes(torn)));
        assert_eq!(
            resumed.err(),
            Some(ReadError::Incomplete { at: second }),
            "resume must refuse a torn tail, naming where it starts"
        );
    }

    #[test]
    fn a_failed_commit_leaves_the_proposal_re_sendable_which_is_why_precheck_exists() {
        // The deliver-then-commit hazard: `is_duplicate` alone says "fresh", the
        // caller delivers, the commit fails (oversize), no high-water is bumped
        // -- so the re-send is fresh again and would be delivered a second time.
        let mut s = Session::new(Seeded::new(1));
        assert!(!s.is_duplicate(7, 1));
        assert!(s.apply_input(7, 1, vec![0u8; MAX_PAYLOAD_LEN + 1]).is_err());
        assert!(!s.is_duplicate(7, 1), "a failed commit bumps no high-water");
        assert!(s.log_bytes().is_empty(), "and writes nothing");
        // `precheck_input` closes the hazard: it refuses before any delivery.
        assert!(s.precheck_input(7, 1, MAX_PAYLOAD_LEN + 1).is_err());
    }
}
