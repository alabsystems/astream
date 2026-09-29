//! The single-partition, single-writer [`Log`].
//!
//! One [`Log`] owns one monotonic [`Offset`] axis: every [`append`](Log::append)
//! assigns the next offset and writes exactly one framed record to the seam
//! [`Disk`], so the log is dense and gapless by construction — there is no
//! second writer and no coordination. The bytes live on the disk, not in the
//! `Log`: the `Log` holds only the writer's counter, so a reader reconstructs
//! records *solely* from stored bytes (the property the replay claim rests on).
//!
//! A failed append is **effect-free**: every check that can reject a record
//! (cause validity, encodability, offset overflow) runs before the seam clock is
//! read or the disk is touched, so an `Err` leaves the clock, the disk, and the
//! offset counter exactly as they were. That is what keeps the seeded clock tick
//! positional (`tick == append index`), which the fork/prefix-stable evidence
//! rests on.

use crate::effects::{Clock, Disk, Effects};
use crate::envelope::{CausedBy, Envelope, EnvelopeError};
use astream_term::Record;
use astream_wire::{Frame, FrameError, Offset};

/// Why an engine operation failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineError {
    /// The offset counter reached `u64::MAX` (`Offset::checked_next` returned
    /// `None`) — never a silent wrap. Nothing was written.
    OffsetOverflow,
    /// The record could not be encoded (e.g. a body larger than `u32`, or a
    /// payload over the frame's `MAX_PAYLOAD_LEN` cap). Nothing was written.
    Envelope(EnvelopeError),
    /// A same-log `caused_by` (partition `None`) named an offset that is not
    /// strictly earlier than the record it was stamped on. A cause must precede
    /// its effect on one log; a forward or self pointer is a fabricated history,
    /// and the log refuses to store it.
    CauseNotEarlier {
        /// The offset the `caused_by` named.
        cause: u64,
        /// The offset the record would have been assigned.
        seq: Offset,
    },
    /// The client does not hold the session's [`ControlToken`](crate::ControlToken):
    /// its input was refused and left no trace on the log.
    NotHolder {
        /// The client that holds control.
        holder: u64,
        /// The client whose input (or handoff) was refused.
        client: u64,
    },
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::OffsetOverflow => write!(f, "log offset overflow"),
            EngineError::Envelope(e) => write!(f, "encode error: {e}"),
            EngineError::CauseNotEarlier { cause, seq } => write!(
                f,
                "same-log cause offset {cause} is not earlier than record offset {}",
                seq.0
            ),
            EngineError::NotHolder { holder, client } => write!(
                f,
                "client {client} does not hold control (holder is {holder})"
            ),
        }
    }
}

impl std::error::Error for EngineError {}

/// Why a read-back failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadError {
    /// The outer frame was malformed or its CRC did not match.
    Frame(FrameError),
    /// The frame payload was not a valid envelope.
    Envelope(EnvelopeError),
    /// A record's stored `seq` did not match its position in the log — the
    /// self-describing header disagreeing with the stream is corruption.
    SeqMismatch {
        /// The offset the reader expected next.
        expected: Offset,
        /// The offset actually stored in the record header.
        found: Offset,
    },
    /// The expected-offset counter overflowed while reading.
    OffsetOverflow,
    /// The log ends partway through a frame starting at byte `at`: a torn tail
    /// that was never recovered (see [`crate::recover`]).
    Incomplete {
        /// Byte offset of the incomplete frame.
        at: usize,
    },
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::Frame(e) => write!(f, "frame decode error: {e}"),
            ReadError::Envelope(e) => write!(f, "envelope decode error: {e}"),
            ReadError::SeqMismatch { expected, found } => {
                write!(f, "record seq {found:?} != expected {expected:?}")
            }
            ReadError::OffsetOverflow => write!(f, "read offset overflow"),
            ReadError::Incomplete { at } => {
                write!(
                    f,
                    "log ends mid-frame at byte {at} (an unrecovered torn tail)"
                )
            }
        }
    }
}

impl std::error::Error for ReadError {}

/// The single-writer log: just the next offset to assign.
pub struct Log {
    next: Offset,
}

impl Log {
    /// A fresh, empty log starting at [`Offset::ZERO`].
    pub fn new() -> Self {
        Log { next: Offset::ZERO }
    }

    /// A log that **continues** an existing offset axis: the next append is
    /// assigned `next`. This is how a recovered log is resumed rather than
    /// restarted — a writer over a disk that already holds `n` records must be
    /// `Log::at(Offset(n))`, or its first append would stamp `seq 0` after
    /// `seq n-1` and every reader/recover pass would stop there as corruption.
    pub fn at(next: Offset) -> Self {
        Log { next }
    }

    /// The offset the next append will be assigned (the log's length, for a
    /// dense log that starts at [`Offset::ZERO`]).
    pub fn next_offset(&self) -> Offset {
        self.next
    }

    /// Append one record. The logical clock is read **through the seam** here and
    /// frozen into the stored bytes, so the timestamp is a recorded input and
    /// replay is deterministic. Returns the offset assigned to this record.
    pub fn append<E: Effects>(
        &mut self,
        fx: &mut E,
        record: Record,
    ) -> Result<Offset, EngineError> {
        self.append_caused(fx, record, None)
    }

    /// Append one record stamped with a durable [`CausedBy`] pointer (the record
    /// that produced it). [`append`](Self::append) is `append_caused(.., None)`.
    ///
    /// A same-log cause (`partition: None`) must name an offset strictly earlier
    /// than this record's — [`EngineError::CauseNotEarlier`] otherwise. A cross-log
    /// cause names another partition's offset, which this log cannot check.
    ///
    /// Every rejection happens **before** the seam is touched: on `Err` the clock
    /// has not ticked, the disk is unchanged, and the next offset is unchanged.
    pub fn append_caused<E: Effects>(
        &mut self,
        fx: &mut E,
        record: Record,
        caused_by: Option<CausedBy>,
    ) -> Result<Offset, EngineError> {
        let seq = self.next;
        if let Some(CausedBy {
            partition: None,
            offset,
        }) = caused_by
        {
            if offset >= seq.0 {
                return Err(EngineError::CauseNotEarlier { cause: offset, seq });
            }
        }
        Envelope::check_encodable(&record, caused_by).map_err(EngineError::Envelope)?;
        let next = seq.checked_next().ok_or(EngineError::OffsetOverflow)?;

        // Only now the seam: the tick is consumed by exactly the records that land.
        let ts_logical = fx.clock().now_logical();
        let env = Envelope {
            seq,
            ts_logical,
            caused_by,
            record,
        };
        // Cannot fail after `check_encodable` (the same arithmetic); kept as an
        // error path rather than an unwrap so the engine stays panic-free.
        let frame_bytes = env.encode().map_err(EngineError::Envelope)?;
        fx.disk().append(&frame_bytes);
        self.next = next;
        Ok(seq)
    }

    /// A separate read-by-offset pass over the stored bytes. Borrows the disk
    /// directly (not the whole seam) so a reader can hold *only* the persisted
    /// bytes; yields every record whose offset is `>= start`.
    pub fn read_from<D: Disk>(disk: &D, start: Offset) -> LogReader<'_> {
        Self::read_bytes(disk.read_all(), start)
    }

    /// [`read_from`](Self::read_from) over a plain byte slice (a recovered
    /// [`crate::FileLog::bytes`], a partition's stored log), with no disk wrapper
    /// and no copy. The one decode discipline every reader shares: a frame is
    /// accepted only if it decodes, its payload is an envelope, and its `seq` is
    /// exactly the next expected offset; the first failure is yielded once as an
    /// `Err` and ends the iteration.
    pub fn read_bytes(bytes: &[u8], start: Offset) -> LogReader<'_> {
        LogReader {
            buf: bytes,
            pos: 0,
            expected: Offset::ZERO,
            start,
        }
    }
}

impl Default for Log {
    fn default() -> Self {
        Self::new()
    }
}

/// An iterator that decodes framed records out of a stored byte log. Any error
/// is yielded once and then terminates the iterator (it never loops on bad
/// bytes, and never panics).
pub struct LogReader<'d> {
    buf: &'d [u8],
    pos: usize,
    expected: Offset,
    start: Offset,
}

impl LogReader<'_> {
    /// Once the iterator has ended: the byte offset of trailing bytes that do
    /// not form a complete frame, if the log ends mid-frame. (An iteration that
    /// ended on an error has consumed everything, so this is `None` then.)
    pub(crate) fn incomplete_at(&self) -> Option<usize> {
        (self.pos < self.buf.len()).then_some(self.pos)
    }
}

impl Iterator for LogReader<'_> {
    type Item = Result<Envelope, ReadError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match Frame::decode(&self.buf[self.pos..]) {
                // Need more bytes (or none left): no further complete frames.
                Ok(None) => return None,
                Err(e) => {
                    self.pos = self.buf.len(); // terminate after this error
                    return Some(Err(ReadError::Frame(e)));
                }
                Ok(Some(decoded)) => {
                    self.pos += decoded.consumed;
                    let env = match Envelope::from_payload(&decoded.frame.payload) {
                        Ok(e) => e,
                        Err(e) => {
                            self.pos = self.buf.len();
                            return Some(Err(ReadError::Envelope(e)));
                        }
                    };
                    if env.seq != self.expected {
                        let err = ReadError::SeqMismatch {
                            expected: self.expected,
                            found: env.seq,
                        };
                        self.pos = self.buf.len();
                        return Some(Err(err));
                    }
                    match self.expected.checked_next() {
                        Some(n) => self.expected = n,
                        None => {
                            self.pos = self.buf.len();
                            return Some(Err(ReadError::OffsetOverflow));
                        }
                    }
                    if env.seq.0 < self.start.0 {
                        continue; // skip-by-offset; keep walking
                    }
                    return Some(Ok(env));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::{Effects, MemDisk, Seeded};
    use astream_wire::MAX_PAYLOAD_LEN;

    /// Record three records under a seeded seam and return the stored bytes.
    fn record_three() -> Vec<u8> {
        let mut fx = Seeded::new(1);
        let mut log = Log::new();
        log.append(&mut fx, Record::Out(b"a".to_vec())).unwrap();
        log.append(
            &mut fx,
            Record::In {
                bytes: b"b".to_vec(),
                client_id: 1,
                client_seq: 1,
            },
        )
        .unwrap();
        log.append(&mut fx, Record::Exit { code: 0 }).unwrap();
        fx.disk().read_all().to_vec()
    }

    fn headers(bytes: &[u8]) -> Vec<(u64, u64)> {
        Log::read_bytes(bytes, Offset::ZERO)
            .map(|r| {
                let e = r.unwrap();
                (e.seq.0, e.ts_logical)
            })
            .collect()
    }

    #[test]
    fn append_then_read_yields_records_in_order_with_offsets_and_ts() {
        let disk = MemDisk::from_bytes(record_three());
        let envs: Vec<Envelope> = Log::read_from(&disk, Offset::ZERO)
            .map(|r| r.unwrap())
            .collect();
        assert_eq!(envs.len(), 3);
        assert_eq!(envs[0].seq, Offset(0));
        assert_eq!(envs[1].seq, Offset(1));
        assert_eq!(envs[2].seq, Offset(2));
        assert_eq!(
            (envs[0].ts_logical, envs[1].ts_logical, envs[2].ts_logical),
            (0, 1, 2)
        );
        assert_eq!(envs[0].record, Record::Out(b"a".to_vec()));
        assert_eq!(envs[2].record, Record::Exit { code: 0 });
    }

    #[test]
    fn read_from_skips_offsets_below_start() {
        let disk = MemDisk::from_bytes(record_three());
        let envs: Vec<Envelope> = Log::read_from(&disk, Offset(2))
            .map(|r| r.unwrap())
            .collect();
        assert_eq!(envs.len(), 1);
        assert_eq!(envs[0].seq, Offset(2));
        assert_eq!(envs[0].record, Record::Exit { code: 0 });
    }

    #[test]
    fn read_bytes_equals_read_from_over_the_same_bytes() {
        let bytes = record_three();
        let disk = MemDisk::from_bytes(bytes.clone());
        let via_disk: Vec<_> = Log::read_from(&disk, Offset(1)).collect();
        let via_bytes: Vec<_> = Log::read_bytes(&bytes, Offset(1)).collect();
        assert_eq!(via_disk, via_bytes);
    }

    #[test]
    fn corrupt_disk_byte_yields_error_not_panic_and_terminates() {
        let mut bytes = record_three();
        let n = bytes.len();
        bytes[n - 1] ^= 0xFF; // flip a payload byte in the last frame -> CRC mismatch
        let disk = MemDisk::from_bytes(bytes);
        let results: Vec<_> = Log::read_from(&disk, Offset::ZERO).collect();
        // The iterator terminates (this collect returns) and surfaces an error.
        assert!(
            results.iter().any(|r| r.is_err()),
            "expected a decode error; got {results:?}"
        );
    }

    #[test]
    fn a_rejected_oversize_append_does_not_tick_the_clock_or_touch_the_disk() {
        let mut fx = Seeded::new(1);
        let mut log = Log::new();
        log.append(&mut fx, Record::Out(b"small".to_vec())).unwrap();
        let before = fx.disk().read_all().to_vec();

        let oversize = Record::Out(vec![0u8; MAX_PAYLOAD_LEN + 1]);
        assert_eq!(
            log.append(&mut fx, oversize),
            Err(EngineError::Envelope(EnvelopeError::Frame(
                FrameError::TooLarge
            )))
        );
        assert_eq!(fx.disk().read_all(), &before[..], "nothing was written");
        assert_eq!(log.next_offset(), Offset(1), "no offset was consumed");

        // The next record is stamped ts == seq: the failed append consumed no tick,
        // so re-recording the decoded records under the same seed is byte-identical.
        log.append(&mut fx, Record::Out(b"after".to_vec())).unwrap();
        let stored = fx.disk().read_all().to_vec();
        assert_eq!(headers(&stored), vec![(0, 0), (1, 1)]);
        let decoded: Vec<Record> = Log::read_bytes(&stored, Offset::ZERO)
            .map(|r| r.unwrap().record)
            .collect();
        assert_eq!(crate::fork::record_session(1, &decoded), stored);
    }

    #[test]
    fn a_same_log_cause_must_be_strictly_earlier_than_its_record() {
        let mut fx = Seeded::new(1);
        let mut log = Log::new();
        let self_cause = Some(CausedBy {
            partition: None,
            offset: 0,
        });
        // Offset 0 cannot be caused by offset 0 (itself) ...
        assert_eq!(
            log.append_caused(&mut fx, Record::Out(b"x".to_vec()), self_cause),
            Err(EngineError::CauseNotEarlier {
                cause: 0,
                seq: Offset(0)
            })
        );
        assert!(fx.disk().is_empty(), "the refused record left no trace");
        // ... nor by a forward pointer ...
        let forward = Some(CausedBy {
            partition: None,
            offset: 7,
        });
        assert!(matches!(
            log.append_caused(&mut fx, Record::Out(b"x".to_vec()), forward),
            Err(EngineError::CauseNotEarlier { cause: 7, .. })
        ));
        // ... but once a record exists, a later record may name it.
        log.append(&mut fx, Record::Out(b"cause".to_vec())).unwrap();
        assert_eq!(
            log.append_caused(&mut fx, Record::Out(b"effect".to_vec()), self_cause),
            Ok(Offset(1))
        );
        // A cross-log cause is not checked against this log's axis.
        let cross = Some(CausedBy {
            partition: Some(9),
            offset: 1_000,
        });
        assert_eq!(
            log.append_caused(&mut fx, Record::Out(b"inj".to_vec()), cross),
            Ok(Offset(2))
        );
        // The refused appends consumed no ticks: ts == seq throughout.
        assert_eq!(headers(fx.disk().read_all()), vec![(0, 0), (1, 1), (2, 2)]);
    }

    #[test]
    fn log_at_continues_the_offset_axis_and_overflow_refuses_before_writing() {
        let mut fx = Seeded::new(1);
        let mut log = Log::at(Offset(5));
        assert_eq!(log.next_offset(), Offset(5));
        assert_eq!(
            log.append(&mut fx, Record::Out(b"a".to_vec())),
            Ok(Offset(5))
        );
        assert_eq!(log.next_offset(), Offset(6));

        let mut top = Log::at(Offset(u64::MAX));
        let before = fx.disk().len();
        assert_eq!(
            top.append(&mut fx, Record::Out(b"z".to_vec())),
            Err(EngineError::OffsetOverflow)
        );
        assert_eq!(
            fx.disk().len(),
            before,
            "an overflowing append writes nothing"
        );
        assert_eq!(top.next_offset(), Offset(u64::MAX));
    }
}
