//! Step records: astream's generic opaque record, and the pure classifier that
//! tells a torn tail from a fault.
//!
//! A step record is one [`Frame`] whose payload is
//!
//! ```text
//! | STEP_VERSION (1) | step: u64 LE (8) | body_len: u32 LE (4) | body ... |
//! ```
//!
//! so a record of an `n`-byte body takes `HEADER_SIZE + STEP_HEADER + n` bytes.
//! The body is opaque: the record names no type, and the reader decides what a
//! body means (a workflow step's output, a keyframe, a chunk of history). The
//! frame's CRC covers the whole payload, so the step number and the length are
//! checked as well as the body.
//!
//! Steps are **dense**. A run that starts at step `first` is accepted only while
//! each record's step is exactly the next one — `first`, `first + 1`, … — so a
//! gap, a repeat or a reordering is seen, never skipped over. A run may start at
//! any step ([`scan_steps_from`]), because a ring that has overwritten its oldest
//! records, or the second half of a run split at a ring's wrap, continues the
//! count rather than restarting it. The count never wraps: `u64::MAX` is the last
//! step a run can hold, and an intact record after it is a fault
//! ([`StepFault::PastLastStep`]), never a step 0 accepted as the next.
//!
//! ## A torn tail or a fault
//!
//! [`scan_steps_from`] keeps the longest intact, in-order prefix and says what
//! ended it, as a [`StepEnd`]:
//!
//! * [`StepEnd::Clean`]: the bytes end exactly at a record boundary.
//! * [`StepEnd::Torn`]: an incomplete or corrupt last record with nothing
//!   decodable after it. This is what a writer that dies in the middle of an
//!   append to an append-only file leaves, so a file's reader may drop it: it
//!   held nothing anyone was told was committed.
//! * [`StepEnd::Fault`]: anything else — a record this build cannot read, a step
//!   out of order, or damage with an intact record after it. None of these is a
//!   crash's signature (but see the nested frame below), so a reader must not
//!   treat the bytes from there on as merely torn. Truncating at a fault in a
//!   file destroys records that were acknowledged.
//!
//! The rule that separates the two, [`frame_decodes_after`], is the one
//! `astream-engine`'s log store applies to its own envelope records: a crash
//! leaves nothing decodable behind its partial frame. Every function here is
//! pure and panic-free, so the classification is a function of the bytes alone.
//!
//! ### How far the search for a frame after the break goes
//!
//! "Nothing decodable after it" is looked for byte by byte, because a damaged
//! header carries no trustworthy length to skip by. A candidate whose header
//! looks like a frame (the magic, version 1, zero flags, a length within the
//! payload cap) and whose length fits the bytes runs a CRC over that length,
//! and nothing vouches for the bytes after a break: they are whatever the
//! damage, a foreign writer, or the record bodies an embedder stored left
//! there, and they may hold such a candidate at many offsets, each naming a
//! length near the whole buffer. Hashing them all is quadratic in the bytes, so
//! the search runs under a CRC-byte budget, `max(RESYNC_CRC_PER_BYTE * after,
//! RESYNC_CRC_FLOOR)` for the `after` bytes it scans: a candidate is charged its
//! declared length before its CRC runs, and the search stops when the next one
//! would overrun the budget. A stopped search answers that a frame decodes
//! after the break — a **fault**, never a torn tail. That is the safe direction:
//! a torn tail may be truncated, and a record a writer acknowledged, which the
//! unsearched bytes might hold, must never be dropped as one.
//!
//! So the bounded answer is the unbounded one, or "fault" when the budget ran
//! out, and what that costs is exactly this:
//!
//! * A fault is never read as torn. A `Torn` answer means every byte was
//!   scanned within the budget and no frame decodes there.
//! * The answers differ only where the unbounded search would find no frame
//!   (`Torn`) and the declared lengths of the look-alikes it passes over — whose
//!   CRCs fail — add up past the budget before the bytes run out. That torn tail
//!   is reported as the fault at the break instead: `CorruptFrame` or
//!   `LengthPastEnd` at the same offset.
//! * The prefix the scan keeps (its records and `valid_len`) is never touched:
//!   it is fixed before the end is classified. In a file the over-strictness is
//!   a refused `open` (its `open_truncating` repairs); inside a commit-word
//!   region any end that is not `Clean` is already a fault, so only the variant
//!   reported changes.
//! * Below the floor nothing changes at all: the answers are equal whenever the
//!   unbounded search would hash at most [`RESYNC_CRC_FLOOR`] bytes.
//!
//! The bound gives whoever chooses the bytes after a break no verdict they
//! could not already force: twelve bytes are a whole frame (the magic, version
//! 1, zero flags, length 0 and CRC 0, the CRC of no bytes), so any such party
//! could always turn a torn tail into a fault. What the bound takes away is the
//! time.
//!
//! ### A body that holds a frame of its own
//!
//! The rule reads bytes, not intent, and a body is opaque, so it cannot tell a
//! frame that follows the damage from a frame nested **inside** the damaged
//! record's own body. A step's output that embeds an encoded astream frame — a
//! step record, a log record, anything an astream-based workflow may hand back —
//! therefore changes what a crash leaves:
//!
//! * a cut inside that record **after** the nested frame's last byte is a
//!   [`StepFault::LengthPastEnd`] fault at the record, not [`StepEnd::Torn`]:
//!   the partial record's length runs past the end and a complete frame decodes
//!   after its start, which is exactly what a rotted length field looks like;
//! * a cut before the nested frame is complete is still `Torn`;
//! * damage to the last record, if it holds one, is a [`StepFault::CorruptFrame`]
//!   fault rather than `Torn`.
//!
//! The error runs one way only. A nested frame adds a frame that decodes; it
//! never hides one, so it can turn a torn tail into a fault but never a fault
//! into a torn tail. The prefix the scan keeps is the same either way, so the
//! nested frame never costs an acknowledged record; its cost is over-strictness:
//! a file's reader refuses where it could have truncated (the workflow journal's
//! `open` refuses, and its explicit `open_truncating` is the repair). The rule
//! cannot be made exact from the bytes alone — a body may nest the very record
//! a rotted length would hide behind it — and it errs strict on purpose: a rule
//! that read such a cut as torn would read a rotted length mid-file as torn
//! too, and a file's reader would truncate acknowledged records. Inside a
//! region bounded by a commit word (below) the case cannot arise: nothing torn
//! lies below the word, and an intact record is accepted by its length before
//! anything looks inside its body.
//!
//! ## Inside a region bounded by a commit word
//!
//! An embedder may keep step records in memory it publishes with a commit word:
//! the writer copies a record and then stores the word one past it (a release
//! store); a reader loads the word (an acquire load) and scans only the bytes
//! below it. A torn tail cannot appear below such a word. Every byte there was
//! written in full before the word admitted it, a process that dies loses no
//! store it already made to its memory, and a writer that dies in the middle of
//! a copy leaves its partial record above the word, where no reader looks.
//!
//! So inside a region bounded by a commit word, **any end that is not
//! [`StepEnd::Clean`] is a fault** — a bug, a version skew or damaged memory —
//! whichever variant names it: a `Torn` end there means bytes the word vouched
//! for do not decode. The reader keeps the intact prefix the scan returns and
//! counts the rest as lost; it does not truncate and carry on as a file reader
//! would.
//!
//! `astream-engine`'s workflow journal is the file-backed user of this module: it
//! truncates a `Torn` tail on open and refuses to open past a `Fault`.

use crate::frame::{decode_frame_header_bytes, Frame, FrameError, HEADER_SIZE, MAX_PAYLOAD_LEN};
use crate::hash::crc32_ieee_prefix;
use std::ops::Range;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "steps_island.rs"]
mod steps_island;
#[cfg(not(clean_islands))]
pub use crate::twins::step_prefix_advance;
#[cfg(clean_islands)]
pub use steps_island::step_prefix_advance;

contract_fn! {
    /// Kernel-certified step-cursor bound check (`pos <= limit`), backed by the
    /// Clean `step_within_bounds_isl` specification (`clean-kernel-defeq`) and the
    /// Clean-origin [`step_prefix_advance`] (`max(valid_len, next_pos)`).
    #[must_use]
    pub const fn step_within_bounds(pos: u64, limit: u64) -> bool
    clauses [ensures result == (pos <= limit)]
    {
        pos <= limit
    }
}

/// Step-record format version: the first payload byte of every step record.
///
/// It versions this one layout, so a build refuses a step record written under
/// a layout it does not know ([`StepFault::BadStep`]). It is **not** a tag that
/// tells one kind of stream from another, and must not be read as one: the
/// cognition `COG_VERSION` is also 1, and a cognition record handed to
/// [`scan_steps_from`] can read as a well-formed step record (its tag and
/// offset bytes land in the step field, its timestamp in the body length). A
/// reader knows what kind of records it holds from where it found them — the
/// journal file it opened, the region it mapped — before it scans a byte. The
/// value cannot move to make the kinds disjoint: every workflow journal on disk
/// holds records stamped 1.
pub const STEP_VERSION: u8 = 1;

/// Bytes of a step record's own header inside the frame payload: version (1) +
/// step (8) + body length (4). A record of an `n`-byte body takes
/// `HEADER_SIZE + STEP_HEADER + n` bytes in all.
pub const STEP_HEADER: usize = 13;

/// The largest body a step record can carry: the frame's payload cap less the
/// step header.
const MAX_STEP_BODY: usize = MAX_PAYLOAD_LEN - STEP_HEADER;

/// Where a record's body starts, counted from the start of its frame.
const BODY_OFFSET: usize = HEADER_SIZE + STEP_HEADER;

const fn drop_prefix(bytes: &[u8], n: usize) -> Option<&[u8]> {
    if bytes.len() < n {
        return None;
    }
    let mut rest = bytes;
    let mut skipped = 0usize;
    while let &[_, ref tail @ ..] = rest {
        if skipped >= n {
            return Some(rest);
        }
        skipped = skipped.saturating_add(1);
        rest = tail;
    }
    if skipped == n {
        Some(rest)
    } else {
        None
    }
}

/// Encode the 13-byte step record header (`STEP_VERSION | step u64 LE | len u32 LE`),
/// checking the body length against `MAX_STEP_BODY` (`MAX_PAYLOAD_LEN - STEP_HEADER`).
pub const fn encode_step_header(
    step: u64,
    body_len: usize,
) -> Result<[u8; STEP_HEADER], FrameError> {
    if body_len > MAX_STEP_BODY {
        return Err(FrameError::TooLarge);
    }
    // `MAX_STEP_BODY < MAX_PAYLOAD_LEN` (16 MiB), which always fits in `u32`.
    let s0 = (step & 0xff) as u8;
    let s1 = ((step >> 8) & 0xff) as u8;
    let s2 = ((step >> 16) & 0xff) as u8;
    let s3 = ((step >> 24) & 0xff) as u8;
    let s4 = ((step >> 32) & 0xff) as u8;
    let s5 = ((step >> 40) & 0xff) as u8;
    let s6 = ((step >> 48) & 0xff) as u8;
    let s7 = ((step >> 56) & 0xff) as u8;
    let len_u32 = body_len as u32;
    let l0 = (len_u32 & 0xff) as u8;
    let l1 = ((len_u32 >> 8) & 0xff) as u8;
    let l2 = ((len_u32 >> 16) & 0xff) as u8;
    let l3 = ((len_u32 >> 24) & 0xff) as u8;
    Ok([STEP_VERSION, s0, s1, s2, s3, s4, s5, s6, s7, l0, l1, l2, l3])
}

/// Encode one step record: `STEP_VERSION | step u64 LE | len u32 LE | body`,
/// inside a CRC [`Frame`].
///
/// A body too large for the frame's payload cap is [`FrameError::TooLarge`], as
/// it would be from [`Frame::encode`]; it is refused before anything is copied,
/// because [`encode_step_header`] checks the length first.
pub fn encode_step(step: u64, body: &[u8]) -> Result<Vec<u8>, FrameError> {
    let hdr = encode_step_header(step, body.len())?;
    let mut payload = Vec::with_capacity(STEP_HEADER + 256);
    payload.extend_from_slice(&hdr);
    payload.extend_from_slice(body);
    Frame::new(payload).encode()
}

/// Decode one 13-byte step record header `hdr` given a frame payload length of
/// `payload_len`, returning `(step, body_len)`.
#[must_use]
pub const fn decode_step_header_bytes(
    hdr: &[u8; STEP_HEADER],
    payload_len: usize,
) -> Option<(u64, usize)> {
    if payload_len < STEP_HEADER {
        return None;
    }
    if hdr[0] != STEP_VERSION {
        return None;
    }
    let step = (hdr[1] as u64)
        | ((hdr[2] as u64) << 8)
        | ((hdr[3] as u64) << 16)
        | ((hdr[4] as u64) << 24)
        | ((hdr[5] as u64) << 32)
        | ((hdr[6] as u64) << 40)
        | ((hdr[7] as u64) << 48)
        | ((hdr[8] as u64) << 56);
    let len = ((hdr[9] as u32)
        | ((hdr[10] as u32) << 8)
        | ((hdr[11] as u32) << 16)
        | ((hdr[12] as u32) << 24)) as usize;
    if len > payload_len - STEP_HEADER {
        return None;
    }
    Some((step, len))
}

/// Decode one step record's header at the front of `payload` given a frame
/// payload length of `payload_len`, returning `(step, body_len)`.
#[must_use]
pub const fn decode_step_header(payload: &[u8], payload_len: usize) -> Option<(u64, usize)> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, ref _rest @ ..] = payload else {
        return None;
    };
    decode_step_header_bytes(
        &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12],
        payload_len,
    )
}

/// Decode one step record's payload (the [`Frame`] payload, not the framed
/// bytes) into `(step, body)`.
///
/// `None` when the payload is shorter than the step header, carries another
/// [`STEP_VERSION`], or names a body longer than the bytes after the header.
/// Bytes after the body are ignored, as `astream-engine`'s journal always has
/// ignored them: the frame's CRC covers them, so they are not damage, and a
/// reader that refused them would refuse journals that open today. aterm's
/// post journal writes a record's heads there (its B05 review), so that an
/// earlier aterm reads the same body: a change to this rule breaks that.
#[must_use]
#[allow(clippy::question_mark)]
pub fn decode_step(payload: &[u8]) -> Option<(u64, &[u8])> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, ref rest @ ..] = payload else {
        return None;
    };
    let Some((step, len)) = decode_step_header_bytes(
        &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12],
        payload.len(),
    ) else {
        return None;
    };
    let Some(body) = rest.get(..len) else {
        return None;
    };
    Some((step, body))
}

/// What a scan of step records found: the longest intact, in-order prefix and
/// what ended it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepScan {
    /// Each accepted record, in order: its step, and the byte range of its body
    /// within the scanned bytes (`&bytes[range]` is the body).
    pub steps: Vec<(u64, Range<usize>)>,
    /// Byte length of the intact prefix: where the last accepted record ends,
    /// and where a file holding a torn tail would be truncated to.
    pub valid_len: usize,
    /// What ended the prefix.
    pub end: StepEnd,
}

/// What ended the intact prefix of a run of step records.
///
/// Inside a region bounded by a commit word, anything but [`StepEnd::Clean`] is
/// a fault (see the module doc); the variants below are named for an
/// append-only file, where a crash can leave a torn tail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepEnd {
    /// The bytes end exactly at a record boundary.
    Clean,
    /// Bytes past the prefix that hold no complete readable record: an
    /// incomplete or corrupt last record with nothing decodable after it, which
    /// is what a crash in the middle of an append leaves. (A rotted length field
    /// on the very last record looks the same.)
    Torn,
    /// Not a crash's signature: the record at byte `at` is readable but wrong, or
    /// damaged with an intact record after it. The one exception is a crash's
    /// partial record whose body nests a complete frame of its own, which reads
    /// as a `LengthPastEnd` or `CorruptFrame` fault (see the module doc). A
    /// nested frame can make a torn tail read as a fault, never a fault read as
    /// torn.
    Fault {
        /// Byte offset of the offending record in the scanned bytes.
        at: usize,
        /// Why it is a fault.
        kind: StepFault,
    },
}

/// Why a record ends a run as a [`StepEnd::Fault`] rather than a torn tail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepFault {
    /// The frame is corrupt (bad magic, version, flags or CRC), yet a complete
    /// frame decodes after it: damage inside the run, not at its end.
    CorruptFrame(FrameError),
    /// The frame's length runs past the end of the bytes, yet a complete frame
    /// decodes after it: a damaged length field, not a torn write.
    LengthPastEnd,
    /// The frame is intact, but its payload is not a step record this build
    /// reads (another [`STEP_VERSION`], or a body length past the payload).
    BadStep,
    /// The record is intact, but its step is not the next one the run expects.
    OutOfOrder {
        /// The step the scan expected.
        expected: u64,
        /// The step stored in the record.
        found: u64,
    },
    /// The record is intact, but it follows the record at step `u64::MAX`, the
    /// last a run can hold: no step can come next, so whatever step it names
    /// is out of order. It is its own variant because [`StepFault::OutOfOrder`]
    /// has no honest `expected` to report.
    PastLastStep {
        /// The step stored in the record.
        found: u64,
    },
}

impl std::fmt::Display for StepFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StepFault::CorruptFrame(e) => {
                write!(f, "corrupt frame ({e}) followed by a decodable frame")
            }
            StepFault::LengthPastEnd => write!(
                f,
                "frame length runs past the end of the bytes but a decodable frame follows it"
            ),
            StepFault::BadStep => write!(f, "unreadable step record"),
            StepFault::OutOfOrder { expected, found } => {
                write!(
                    f,
                    "out-of-order step record (step {found}, expected {expected})"
                )
            }
            StepFault::PastLastStep { found } => write!(
                f,
                "step record after the last step a run can hold (step {found} follows step {})",
                u64::MAX
            ),
        }
    }
}

/// Scan `bytes` as a run of step records whose first step is `first`, keeping the
/// longest intact, in-order prefix and classifying what ended it.
///
/// A record is accepted only when its frame decodes (magic, version, flags,
/// length and CRC all valid), its payload is a step record this build reads, and
/// its step equals `first + steps.len()`. The first record that fails any check
/// ends the prefix, as a torn tail or a fault (see [`StepEnd`]).
///
/// A record whose step is `u64::MAX` is the last the run can hold, because no
/// step can follow it, so the prefix cannot grow past it. The scan still looks at
/// what comes after, by the same rules as anywhere else: nothing is
/// [`StepEnd::Clean`], an incomplete or corrupt record with nothing decodable
/// after it is [`StepEnd::Torn`], damage with an intact record after it is a
/// fault, and an intact record is a fault too — [`StepFault::PastLastStep`], or
/// [`StepFault::BadStep`] if it is no step record. An intact record there is
/// never `Torn`: a file's reader may drop a torn tail, and that record could
/// have been acknowledged. (A counter that starts at 0 needs 2^64 records to
/// get here; only a caller's `first` near the top of the range can.)
///
/// Pure and panic-free: it reads `bytes` only through checked slicing and keeps
/// ranges, not bodies, so a caller copies only what it keeps.
pub fn scan_steps_from(bytes: &[u8], first: u64) -> StepScan {
    let mut steps: Vec<(u64, Range<usize>)> = Vec::new();
    let mut pos = 0usize;
    let mut rest = bytes;
    // The step the next record must carry; `None` once the run has accepted step
    // `u64::MAX`, after which no record can be in order.
    let mut expected = Some(first);
    let end = loop {
        match crate::frame::validate_frame_at(rest) {
            // No complete frame at `pos`: a clean end, a torn tail, or a rotted
            // length field.
            Ok(None) => break end_without_frame(bytes, pos),
            // A complete-but-corrupt frame (or an unreadable header).
            Err(e) => break end_at_corrupt_frame(bytes, pos, e),
            Ok(Some((payload_len, after_hdr))) => {
                match (decode_step_header(after_hdr, payload_len), expected) {
                    (None, _) => {
                        break StepEnd::Fault {
                            at: pos,
                            kind: StepFault::BadStep,
                        }
                    }
                    (Some((found, _)), None) => {
                        break StepEnd::Fault {
                            at: pos,
                            kind: StepFault::PastLastStep { found },
                        }
                    }
                    (Some((found, _)), Some(expected)) if found != expected => {
                        break StepEnd::Fault {
                            at: pos,
                            kind: StepFault::OutOfOrder { expected, found },
                        }
                    }
                    (Some((step, body_len)), Some(_)) => {
                        let start = pos.saturating_add(BODY_OFFSET);
                        steps.push((step, start..start.saturating_add(body_len)));
                        let consumed = HEADER_SIZE.saturating_add(payload_len);
                        pos = pos.saturating_add(consumed);
                        rest = match drop_prefix(after_hdr, payload_len) {
                            Some(tail) => tail,
                            None => &[],
                        };
                        expected = step.checked_add(1);
                    }
                }
            }
        }
    };
    StepScan {
        steps,
        valid_len: pos,
        end,
    }
}

/// What ends a run at `pos` when no complete frame starts there (the frame
/// codec needs more bytes than `bytes` holds).
///
/// [`StepEnd::Clean`] at the end of the bytes. Otherwise usually the incomplete
/// last frame a crash in the middle of an append leaves, [`StepEnd::Torn`]; but
/// if a complete frame decodes after `pos`, it is the frame's length field that
/// is wrong, and the end is a [`StepFault::LengthPastEnd`] fault.
#[must_use]
pub const fn end_without_frame(bytes: &[u8], pos: usize) -> StepEnd {
    if pos >= bytes.len() {
        StepEnd::Clean
    } else if frame_decodes_after(bytes, pos) {
        StepEnd::Fault {
            at: pos,
            kind: StepFault::LengthPastEnd,
        }
    } else {
        StepEnd::Torn
    }
}

/// What ends a run at `pos` when the frame there failed to decode with `e`.
///
/// If any complete frame decodes after it, the damage is inside the run, a
/// [`StepFault::CorruptFrame`] fault. If nothing after it decodes, it is the
/// tail a crash left, [`StepEnd::Torn`].
#[must_use]
pub const fn end_at_corrupt_frame(bytes: &[u8], pos: usize, e: FrameError) -> StepEnd {
    if frame_decodes_after(bytes, pos) {
        StepEnd::Fault {
            at: pos,
            kind: StepFault::CorruptFrame(e),
        }
    } else {
        StepEnd::Torn
    }
}

/// The CRC bytes the resync search may hash for each byte it scans after the
/// break, over and above [`RESYNC_CRC_FLOOR`]: the slope of the linear bound.
/// A candidate frame is charged its declared length (the bytes its CRC would
/// cover) before the CRC runs, and the search stops when the next candidate
/// would carry the total past the budget (see [`frame_decodes_after`]).
pub const RESYNC_CRC_PER_BYTE: usize = 2;

/// The least CRC work the resync search may do, whatever the bytes after the
/// break: one frame at the payload cap (16 MiB).
///
/// The slope alone already hashes the first candidate in full (a frame that
/// fits in the `after` bytes declares fewer than `after` of them, under the
/// slope's `2 * after`). The floor is what keeps the bound out of sight on
/// ordinary inputs: the bounded answer equals the unbounded one whenever the
/// unbounded search would hash at most 16 MiB, which is every file or region
/// short of the frame-look-alikes it takes to hash that much (about 20 KiB of
/// them packed end to end; the engine's frozen-oracle comparison scans a few
/// hundred bytes at a time). Its price is the worst case: up to 16 MiB of CRC
/// for one search over however few bytes.
pub const RESYNC_CRC_FLOOR: usize = MAX_PAYLOAD_LEN;

/// The resync search's CRC-byte budget over `bytes` after `pos`:
/// `max(RESYNC_CRC_PER_BYTE * after, RESYNC_CRC_FLOOR)`, linear in the `after`
/// bytes it would scan plus a constant.
#[must_use]
const fn resync_budget(bytes: &[u8], pos: usize) -> usize {
    let start = pos.saturating_add(1);
    let after = bytes.len().saturating_sub(start);
    let proportional = after.saturating_mul(RESYNC_CRC_PER_BYTE);
    if proportional > RESYNC_CRC_FLOOR {
        proportional
    } else {
        RESYNC_CRC_FLOOR
    }
}

/// What a bounded resync search found, and the CRC bytes it hashed doing it.
///
/// `hashed` is a counted-work seam, not a clock: a test drives [`resync`] with
/// a chosen budget and reads it to prove the hostile case is linear and that
/// the unbounded search (a huge budget) is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Resync {
    /// A complete CRC-valid frame decodes after the break, OR the budget ran
    /// out before the search could rule one out (`found` is then conservative).
    found: bool,
    /// The CRC bytes hashed: at most `budget` on a bounded answer.
    hashed: usize,
}

/// Look for a complete, CRC-valid frame after `pos` under a CRC-byte `budget`.
///
/// Each candidate header is decoded first (magic, version, flags, length — no
/// CRC), so a mismatch or a length past the bytes costs nothing and is passed
/// over, exactly as [`crate::frame::validate_frame_at`] would. Only a candidate
/// whose length fits the bytes would run a CRC; it is charged that length
/// before the CRC runs, and the search returns `found: true` the moment the
/// next such candidate would carry the total past `budget`. That is the
/// conservative answer: the search has not ruled out a frame in the bytes it
/// did not reach, and reading the break as torn there could truncate a record a
/// writer acknowledged (the module doc states the cost). `found: false` is
/// returned only after every byte has been scanned within budget, so a genuine
/// fault is never read as a torn tail — only a torn tail crowded with
/// frame-look-alikes past the budget is read as a fault.
#[must_use]
const fn resync(bytes: &[u8], pos: usize, budget: usize) -> Resync {
    let mut hashed = 0usize;
    if pos == usize::MAX {
        return Resync {
            found: false,
            hashed,
        };
    }
    let start = pos.saturating_add(1);
    let Some(mut rest) = drop_prefix(bytes, start) else {
        return Resync {
            found: false,
            hashed,
        };
    };
    while let &[_, ref next @ ..] = rest {
        if let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ref payload @ ..] = rest {
            if let Ok((len, crc)) =
                decode_frame_header_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11])
            {
                // Only a candidate whose length fits the bytes would run a CRC;
                // a length past the end is passed over for free, as
                // `validate_frame_at` does (`Ok(None)`).
                if len <= payload.len() {
                    // A CRC over `len` bytes would run here. Charge it first; the
                    // next candidate that would overrun the budget ends the search.
                    if len > budget.saturating_sub(hashed) {
                        return Resync {
                            found: true,
                            hashed,
                        };
                    }
                    hashed = hashed.saturating_add(len);
                    if let Some(actual) = crc32_ieee_prefix(payload, len) {
                        if actual == crc {
                            return Resync {
                                found: true,
                                hashed,
                            };
                        }
                    }
                }
            }
        }
        rest = next;
    }
    Resync {
        found: false,
        hashed,
    }
}

/// Whether a complete, CRC-valid frame starts anywhere after `pos` (never at
/// `pos` itself), answered conservatively under a linear CRC-byte budget.
/// A crash leaves nothing decodable behind its partial
/// frame, unless that frame's own body nests one, which this test cannot tell
/// from a frame that follows it (the module doc says what that costs). Scanning
/// byte by byte is the honest test: a damaged header carries no trustworthy
/// length to skip by.
///
/// The budget bounds the one superlinear cost the byte-by-byte scan had: a
/// candidate whose header looks like a frame and whose length fits runs a CRC
/// over that length, and bytes nobody vouches for can hold one at many offsets,
/// each naming a length near the whole buffer — an O(n²) search with no bound.
/// The declared length is charged before the CRC runs and the search stops when
/// the budget is spent, so one call hashes at most
/// `max(RESYNC_CRC_PER_BYTE * after, RESYNC_CRC_FLOOR)` bytes. When the budget
/// stops the search the answer is `true` (a fault), never `false` (a torn
/// tail): a torn tail may be truncated and a record a writer acknowledged must
/// never be dropped as one, so the unsearched bytes are treated as possibly
/// holding a frame. A `false` answer still means every byte was scanned, so a
/// real fault is never seen as torn. The module doc states exactly where the
/// bounded answer differs from the unbounded one.
#[must_use]
pub const fn frame_decodes_after(bytes: &[u8], pos: usize) -> bool {
    if pos == usize::MAX {
        return false;
    }
    resync(bytes, pos, resync_budget(bytes, pos)).found
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A step payload written by hand from the documented layout.
    fn payload(version: u8, step: u64, len: u32, body: &[u8]) -> Vec<u8> {
        let mut p = vec![version];
        p.extend_from_slice(&step.to_le_bytes());
        p.extend_from_slice(&len.to_le_bytes());
        p.extend_from_slice(body);
        p
    }

    #[test]
    fn a_step_record_round_trips_through_its_frame() {
        let bytes = encode_step(3, b"hello").unwrap();
        assert_eq!(bytes.len(), HEADER_SIZE + STEP_HEADER + 5);
        let decoded = Frame::decode(&bytes).unwrap().unwrap();
        assert_eq!(decoded.consumed, bytes.len());
        assert_eq!(
            decode_step(&decoded.frame.payload),
            Some((3, &b"hello"[..]))
        );
        let empty = encode_step(u64::MAX, b"").unwrap();
        let decoded = Frame::decode(&empty).unwrap().unwrap();
        assert_eq!(
            decode_step(&decoded.frame.payload),
            Some((u64::MAX, &b""[..]))
        );
    }

    #[test]
    fn decode_step_refuses_what_it_cannot_read_without_panicking() {
        // Every prefix shorter than the header is refused, the empty one too.
        let full = payload(STEP_VERSION, 7, 2, b"ok");
        for cut in 0..STEP_HEADER {
            assert_eq!(decode_step(&full[..cut]), None, "a {cut}-byte payload");
        }
        // Another version.
        assert_eq!(decode_step(&payload(STEP_VERSION + 1, 7, 2, b"ok")), None);
        // A body length past the payload, up to the largest the field can name.
        assert_eq!(decode_step(&payload(STEP_VERSION, 7, 3, b"ok")), None);
        assert_eq!(
            decode_step(&payload(STEP_VERSION, 7, u32::MAX, b"ok")),
            None
        );
        // The documented tolerance: bytes after the body are ignored.
        assert_eq!(
            decode_step(&payload(STEP_VERSION, 7, 1, b"ok")),
            Some((7, &b"o"[..]))
        );
    }

    /// The scan skips a record's tail too (the bytes after its body, under its CRC): its
    /// body range ends at the body, the next record reads, and the run is clean. aterm's
    /// post journal carries a record's heads there, read by no earlier aterm.
    #[test]
    fn the_scan_skips_a_records_tail_and_reads_the_next_record() {
        let tailed = Frame::new(payload(STEP_VERSION, 0, 4, b"bodyat 42"))
            .encode()
            .expect("frames");
        let mut bytes = tailed.clone();
        bytes.extend(encode_step(1, b"next").expect("frames"));
        let scan = scan_steps_from(&bytes, 0);
        assert_eq!(scan.end, StepEnd::Clean);
        assert_eq!(scan.valid_len, bytes.len());
        let bodies: Vec<(u64, &[u8])> = scan
            .steps
            .iter()
            .map(|(step, body)| (*step, &bytes[body.clone()]))
            .collect();
        assert_eq!(bodies, [(0, &b"body"[..]), (1, &b"next"[..])]);
        assert_eq!(scan.steps[0].1.end + b"at 42".len(), tailed.len());
    }

    #[test]
    fn the_header_refuses_a_body_length_past_the_cap_on_its_own() {
        // The guard `encode_step` runs before it copies a byte lives here, so it is
        // pinned here: `encode_step`'s error is the same TooLarge whether its guard
        // ran or `Frame::encode` refused after the copy, and cannot show which.
        // Without the guard the header would cast the length to `u32` and return
        // a record header that lies about its body: `usize::MAX` would come back
        // as `Ok` with a length field of `u32::MAX`.
        for body_len in [MAX_STEP_BODY + 1, MAX_PAYLOAD_LEN, usize::MAX] {
            assert_eq!(
                encode_step_header(0, body_len),
                Err(FrameError::TooLarge),
                "a {body_len}-byte body"
            );
        }
        // The largest body the cap admits gets a header naming exactly its length.
        let hdr = encode_step_header(7, MAX_STEP_BODY).unwrap();
        assert_eq!(
            decode_step_header_bytes(&hdr, STEP_HEADER + MAX_STEP_BODY),
            Some((7, MAX_STEP_BODY))
        );
    }

    #[test]
    fn an_oversized_body_is_too_large_and_the_largest_body_frames() {
        // One byte past what the frame can carry is the frame's own TooLarge.
        let body = vec![0u8; MAX_STEP_BODY + 1];
        assert_eq!(encode_step(0, &body), Err(FrameError::TooLarge));
        // Exactly the largest body still frames, and decodes back.
        let body = vec![0x5Au8; MAX_STEP_BODY];
        let bytes = encode_step(1, &body).unwrap();
        let scan = scan_steps_from(&bytes, 1);
        assert_eq!(scan.end, StepEnd::Clean);
        assert_eq!(
            scan.steps,
            vec![(1, HEADER_SIZE + STEP_HEADER..bytes.len())]
        );
    }

    #[test]
    fn frame_decodes_after_looks_strictly_past_pos() {
        let one = encode_step(0, b"a").unwrap();
        // The frame AT pos is not "after" it.
        assert!(!frame_decodes_after(&one, 0));
        let mut two = vec![0xFFu8];
        two.extend_from_slice(&one);
        assert!(frame_decodes_after(&two, 0));
        assert!(!frame_decodes_after(&two, 1));
        // Past the end, and at usize::MAX, it is simply false.
        assert!(!frame_decodes_after(&two, two.len()));
        assert!(!frame_decodes_after(&two, usize::MAX));
    }

    /// Bytes nobody vouches for after a break, crammed with frame-like headers
    /// each naming a length that reaches the end (so its CRC would run) and a
    /// wrong CRC (so none decodes): the worst case for the resync search.
    ///
    /// Every header names at least one byte. A header naming none would be a
    /// real frame, not a look-alike: its zero CRC is the CRC of no bytes.
    fn hostile_resync_bytes(n: usize) -> Vec<u8> {
        let mut b = vec![0u8; n];
        let mut p = 0usize;
        while p + HEADER_SIZE < n {
            write_look_alike(&mut b, p, (n - p - HEADER_SIZE).min(MAX_PAYLOAD_LEN));
            p += HEADER_SIZE;
        }
        b
    }

    /// Write a frame-like header at `p` naming `len` payload bytes: the magic,
    /// version 1, zero flags, the length, and a CRC of 0. The CRC is wrong for
    /// every `len` above zero, so the search runs it, rejects it and walks on.
    fn write_look_alike(b: &mut [u8], p: usize, len: usize) {
        assert!(
            len > 0,
            "a length-0 header with CRC 0 is a real empty frame"
        );
        let len = u32::try_from(len).expect("a look-alike length fits the field");
        b[p] = crate::frame::MAGIC[0];
        b[p + 1] = crate::frame::MAGIC[1];
        b[p + 2] = crate::frame::VERSION;
        b[p + 3] = 0; // flags
        b[p + 4..p + 8].copy_from_slice(&len.to_le_bytes());
        b[p + 8..p + HEADER_SIZE].fill(0);
    }

    /// The negative control: the search with no budget over `bytes` after 0.
    /// It must find no frame, so whatever the bounded search answers differently
    /// is the budget's doing and not a frame the bytes really hold.
    fn unbounded_finds_nothing(bytes: &[u8]) -> Resync {
        let unbounded = resync(bytes, 0, usize::MAX);
        assert!(
            !unbounded.found,
            "the control holds a real frame in {} bytes",
            bytes.len()
        );
        unbounded
    }

    #[test]
    fn twelve_bytes_are_a_whole_frame() {
        // Why the look-alikes above all name a length: the empty frame is the
        // magic, the version, zero flags, length 0 and CRC 0. It is also why the
        // bound gives whoever writes the bytes after a break no verdict they
        // could not already force: these twelve bytes make any break a fault.
        let empty = [
            crate::frame::MAGIC[0],
            crate::frame::MAGIC[1],
            crate::frame::VERSION,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        assert_eq!(
            crate::frame::validate_frame_at(&empty),
            Ok(Some((0, &[][..])))
        );
        let mut after = vec![0xFFu8];
        after.extend_from_slice(&empty);
        assert!(frame_decodes_after(&after, 0));
    }

    #[test]
    fn the_resync_search_is_linear_and_the_unbounded_one_is_not() {
        // A small explicit budget, so the bound bites with small bytes (the
        // production budget's 16 MiB floor would need a far larger buffer).
        let budget = 64 * 1024usize;
        for &n in &[8 * 1024usize, 16 * 1024, 32 * 1024] {
            let bytes = hostile_resync_bytes(n);
            let bounded = resync(&bytes, 0, budget);
            // The hostile case hashes no more than its budget, whatever the
            // size: the work is linear in the budget, not quadratic in the bytes.
            assert!(
                bounded.hashed <= budget,
                "bounded hashed {} over budget {budget} at {n} bytes",
                bounded.hashed
            );
            // And it answers conservatively: the budget ran out before the
            // search could rule a frame out, so the break is a fault, not torn.
            assert!(
                bounded.found,
                "budget cut off is a conservative fault at {n}"
            );

            // The negative control: the same search with no budget finds no
            // frame and hashes far more than the bound (the quadratic the
            // budget tames).
            let unbounded = unbounded_finds_nothing(&bytes);
            assert!(
                unbounded.hashed > budget,
                "unbounded hashed {} does not exceed the bound {budget} at {n}",
                unbounded.hashed
            );
        }
        // Unbounded work is super-linear: doubling the bytes more than doubles it.
        let small = unbounded_finds_nothing(&hostile_resync_bytes(8 * 1024)).hashed;
        let large = unbounded_finds_nothing(&hostile_resync_bytes(16 * 1024)).hashed;
        assert!(
            large > small.saturating_mul(2),
            "unbounded resync is super-linear: {small} -> {large}"
        );
    }

    #[test]
    fn the_production_budget_turns_a_crammed_torn_tail_into_a_fault() {
        // A real frame a short way after the break is found cheaply and read as a
        // fault, as it always was (the safety direction the budget keeps).
        let mut real = vec![0xFFu8; 3];
        real.extend_from_slice(&encode_step(0, b"x").unwrap());
        assert!(frame_decodes_after(&real, 0));

        // Below the floor nothing changes: these look-alikes cost the unbounded
        // search less than 16 MiB, and the bounded answer is its answer, torn.
        let light = hostile_resync_bytes(16 * 1024);
        assert!(unbounded_finds_nothing(&light).hashed <= RESYNC_CRC_FLOOR);
        assert!(!frame_decodes_after(&light, 0));

        for n in [24 * 1024usize, 48 * 1024] {
            // Crammed past the floor: the unbounded search hashes more than the
            // budget and finds no frame, so by the unbounded rule this is a
            // torn tail.
            let crammed = hostile_resync_bytes(n);
            let budget = resync_budget(&crammed, 0);
            assert_eq!(budget, RESYNC_CRC_FLOOR, "the floor's regime at {n}");
            let unbounded = unbounded_finds_nothing(&crammed);
            assert!(
                unbounded.hashed > budget,
                "the control must exceed the budget it is proving at {n}"
            );

            // The production search hashes at most its budget and answers a
            // fault, never a torn tail: the budget alone made the difference.
            let bounded = resync(&crammed, 0, budget);
            assert!(bounded.hashed <= budget, "{} over {budget}", bounded.hashed);
            assert!(bounded.found);
            assert!(frame_decodes_after(&crammed, 0));

            // In a run, the record before the break is kept either way, and the
            // break is the fault at the same offset where the unbounded rule
            // would have said Torn.
            let mut run = encode_step(7, b"kept").unwrap();
            let kept = run.len();
            run.extend_from_slice(&crammed);
            let scan = scan_steps_from(&run, 7);
            assert_eq!(
                scan.steps,
                vec![(7, HEADER_SIZE + STEP_HEADER..kept)],
                "the prefix at {n}"
            );
            assert_eq!(scan.valid_len, kept);
            assert_eq!(
                scan.end,
                StepEnd::Fault {
                    at: kept,
                    kind: StepFault::CorruptFrame(FrameError::ChecksumMismatch),
                },
                "at {n}"
            );
        }

        // Ordinary torn bytes with no frame after are still torn (false): a
        // genuine fault is never seen as torn, and a torn tail is not forced to
        // a fault unless the budget truly ran out.
        let plain = vec![0u8; 64 * 1024];
        assert!(!frame_decodes_after(&plain, 0));
    }

    #[test]
    fn past_eight_mib_after_the_break_the_budget_is_twice_those_bytes() {
        // The floor's regime ends where the slope passes it: at 8 MiB scanned the
        // budget is still the floor, one byte more and it is twice the bytes. A
        // search from `pos` scans the bytes after it, `len - pos - 1` of them.
        let at_the_floor = RESYNC_CRC_FLOOR / RESYNC_CRC_PER_BYTE;
        assert_eq!(at_the_floor, 8 << 20);
        let edge = vec![0u8; at_the_floor + 1];
        assert_eq!(resync_budget(&edge, 0), RESYNC_CRC_FLOOR);
        let edge = vec![0u8; at_the_floor + 2];
        assert_eq!(resync_budget(&edge, 0), RESYNC_CRC_FLOOR + 2);
        let n = 9 << 20;
        let zeros = vec![0u8; n];
        let budget = 2 * (n - 1);
        assert_eq!(resync_budget(&zeros, 0), budget);
        assert_eq!(resync_budget(&zeros, 4096), 2 * (n - 4097));

        // Through the production path: three look-alikes right after the break,
        // the first two each naming the rest of the 9 MiB and the third the
        // remainder of the budget, so their declared lengths add up to exactly
        // the slope's budget (the floor's 16 MiB would stop the search at the
        // second). Every candidate is hashed, no frame decodes, and the answer
        // is the unbounded one: Torn.
        let first = n - 1 - HEADER_SIZE; // at 1, its payload runs to the end
        let second = n - 1 - 2 * HEADER_SIZE; // at 13, the same
        let third = budget - first - second;
        let look_alikes = |third: usize| {
            let mut b = vec![0u8; n];
            write_look_alike(&mut b, 1, first);
            write_look_alike(&mut b, 1 + HEADER_SIZE, second);
            write_look_alike(&mut b, 1 + 2 * HEADER_SIZE, third);
            b
        };
        let exact = look_alikes(third);
        assert_eq!(unbounded_finds_nothing(&exact).hashed, budget);
        assert_eq!(
            resync(&exact, 0, resync_budget(&exact, 0)),
            Resync {
                found: false,
                hashed: budget
            }
        );
        assert!(!frame_decodes_after(&exact, 0));

        // One byte more and the third would carry the total past the budget: the
        // search stops before its CRC runs and answers a fault, while the
        // unbounded search still finds no frame. A budget that grew past the
        // slope (or had no bound at all) would read this Torn.
        let over = look_alikes(third + 1);
        assert_eq!(unbounded_finds_nothing(&over).hashed, budget + 1);
        assert_eq!(
            resync(&over, 0, resync_budget(&over, 0)),
            Resync {
                found: true,
                hashed: first + second
            }
        );
        assert!(frame_decodes_after(&over, 0));
    }

    #[test]
    fn a_run_that_reaches_the_last_step_ends_there() {
        let mut bytes = encode_step(u64::MAX - 1, b"a").unwrap();
        bytes.extend_from_slice(&encode_step(u64::MAX, b"b").unwrap());
        let scan = scan_steps_from(&bytes, u64::MAX - 1);
        assert_eq!(scan.end, StepEnd::Clean);
        assert_eq!(
            scan.steps.iter().map(|(s, _)| *s).collect::<Vec<_>>(),
            vec![u64::MAX - 1, u64::MAX]
        );
        assert_eq!(scan.valid_len, bytes.len());
    }

    #[test]
    fn clean_origin_step_prefix_advance_and_within_bounds_match_spec() {
        assert!(step_within_bounds(0, 0));
        assert!(step_within_bounds(25, 100));
        assert!(!step_within_bounds(101, 100));
        assert_eq!(step_prefix_advance(0, 25), 25);
        assert_eq!(step_prefix_advance(25, 10), 25);
        assert_eq!(step_prefix_advance(25, 50), 50);
    }
}
