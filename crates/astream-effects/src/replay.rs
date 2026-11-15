//! The REPLAY pass: re-feed the recorded tape, touching NO real effect.
//!
//! ## Formal Verification (`clean` Island — TLA+ Deterministic Effect Replay)
//!
//! This module embeds a machine-checked Clean specification (`Astream.Effects.TlaDeterministicReplay`)
//! of the deterministic effect-tape replay protocol:
//! - Every effect request (`Clock`, `Rand`, `File`) advances the replay cursor only when
//!   `diverged = false`, `cursor < tapeLen`, and both the effect kind and path match the
//!   recorded tape entry.
//! - Exhaustion (`cursor = tapeLen`), kind mismatch, or path divergence transitions to the
//!   fail-closed `diverged = true` state without advancing `cursor`, proving
//!   `Spec n ⊨ □ (Lift ReplaySafetyInv)` (`cursor <= tapeLen /\ matchedPrefix = cursor`).

use crate::seam::{EffectRecord, EffectSeam, EffectsLog, Latches};
use std::fmt;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "replay_island.rs"]
mod replay_island;
#[cfg(not(clean_islands))]
pub use crate::twins::replay_cursor_monotone;
#[cfg(clean_islands)]
pub use replay_island::replay_cursor_monotone;

contract_fn! {
    /// Pure cursor-bounds predicate linked to the Clean island's `replay_cursor_in_bounds_isl`
    /// and discharged via `clean-kernel-defeq`.
    #[must_use]
    pub const fn replay_cursor_in_bounds(cursor: u64, tape_len: u64) -> bool
    clauses [ensures result == (cursor < tape_len)]
    {
        cursor < tape_len
    }
}

/// Why a replay cannot reproduce the recorded execution. Every variant is a
/// divergence between what the program asks for now and what the tape recorded,
/// so the replay refuses rather than answer from anywhere but the tape.
///
/// Its `Display` and its `Debug` both show every byte string — the variant's
/// own, and those of a [`KindMismatch`](ReplayDivergence::KindMismatch)'s
/// found record — as a short window, never in full: a reply door carries
/// whole screens. Where two byte strings diverge, the window opens just before
/// the first byte where they differ, so the message shows the difference
/// rather than the head they share. The values themselves are whole: match on
/// the variant to read them.
#[derive(Clone, Eq)]
pub enum ReplayDivergence {
    /// The program asked for more effects than were recorded.
    Exhausted {
        /// The effect kind the program asked for, as
        /// [`EffectRecord::kind`] names it (`"Clock"`, `"Rand"`, `"File"`,
        /// `"Mono"`, `"Exchange"`, `"Emit"`).
        expected: &'static str,
    },
    /// The program ended with records left on the tape: it did less than the
    /// recorded run did — an output it no longer says, a read it no longer
    /// makes, a flag it no longer polls up to the read that saw it rise. Only
    /// [`ReplaySeam::finish`] refuses with it, because no door can see that
    /// the program has stopped asking; only the program knows where it ends.
    Unreached {
        /// How many records the program consumed: the index of `found`
        /// (`#N` counting from 0).
        position: usize,
        /// The first record the program never reached.
        found: EffectRecord,
    },
    /// The next recorded effect is of a different kind than the one asked for.
    KindMismatch {
        /// The effect kind the program asked for.
        expected: &'static str,
        /// The record the tape holds at this position instead.
        found: EffectRecord,
    },
    /// A file effect was recorded for a different path than the one asked for.
    PathDiverged {
        /// The path the tape recorded.
        recorded: String,
        /// The path the replayed program asked for.
        asked: String,
    },
    /// An exchange or an output went through a different door than the one
    /// the tape recorded at this position.
    DoorDiverged {
        /// The door the tape recorded.
        recorded: String,
        /// The door the replayed program used.
        asked: String,
    },
    /// An exchange went through the recorded door with a different request:
    /// the program is asking another question, so the recorded reply is not
    /// its answer.
    RequestDiverged {
        /// The door both agree on.
        door: String,
        /// The request the tape recorded.
        recorded: Vec<u8>,
        /// The request the replayed program sent.
        asked: Vec<u8>,
    },
    /// An output went through the recorded door with different bytes: the
    /// replayed program says something the recorded one did not.
    OutputDiverged {
        /// The door both agree on.
        door: String,
        /// The output the tape recorded.
        recorded: Vec<u8>,
        /// The output the replayed program produced.
        emitted: Vec<u8>,
    },
    /// A [`KeyedView`](crate::KeyedView) holds no exchange through this door
    /// with this request among the records it was asked to look in. Never a
    /// reason to ask the live world: the tape simply does not know.
    Unrecorded {
        /// The door asked.
        door: String,
        /// The request asked.
        request: Vec<u8>,
    },
}

impl PartialEq for ReplayDivergence {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Exhausted { expected: a }, Self::Exhausted { expected: b }) => a == b,
            (
                Self::Unreached {
                    position: pa,
                    found: fa,
                },
                Self::Unreached {
                    position: pb,
                    found: fb,
                },
            ) => pa == pb && fa == fb,
            (
                Self::KindMismatch {
                    expected: ea,
                    found: fa,
                },
                Self::KindMismatch {
                    expected: eb,
                    found: fb,
                },
            ) => ea == eb && fa == fb,
            (
                Self::PathDiverged {
                    recorded: ra,
                    asked: aa,
                },
                Self::PathDiverged {
                    recorded: rb,
                    asked: ab,
                },
            ) => ra == rb && aa == ab,
            (
                Self::DoorDiverged {
                    recorded: ra,
                    asked: aa,
                },
                Self::DoorDiverged {
                    recorded: rb,
                    asked: ab,
                },
            ) => ra == rb && aa == ab,
            (
                Self::RequestDiverged {
                    door: da,
                    recorded: ra,
                    asked: aa,
                },
                Self::RequestDiverged {
                    door: db,
                    recorded: rb,
                    asked: ab,
                },
            ) => da == db && ra == rb && aa == ab,
            (
                Self::OutputDiverged {
                    door: da,
                    recorded: ra,
                    emitted: ea,
                },
                Self::OutputDiverged {
                    door: db,
                    recorded: rb,
                    emitted: eb,
                },
            ) => da == db && ra == rb && ea == eb,
            (
                Self::Unrecorded {
                    door: da,
                    request: rqa,
                },
                Self::Unrecorded {
                    door: db,
                    request: rqb,
                },
            ) => da == db && rqa == rqb,
            _ => false,
        }
    }
}

/// Bytes in a divergence message: a window of at most [`WIDTH`](Shown::WIDTH)
/// of them, ASCII-escaped, with `…` on each side that was cut and the full
/// length whenever anything was.
///
/// A reply door carries whole screens, and so does the record a refusal found
/// in place of the one it wanted. A message that printed them in full would
/// bury the divergence in hundreds of kilobytes (a 64 KiB screen is 320 KB as
/// a `Vec<u8>`'s decimal list), and it would copy a recorded screen into
/// whatever stderr, log or reply carries the message, when the tape is the
/// one place a screen belongs. The `Debug` form is the same window,
/// because `Debug` is what `?` out of `main`, `unwrap` and `expect` print.
struct Shown<'a> {
    bytes: &'a [u8],
    /// The index of the window's first byte.
    from: usize,
}

impl<'a> Shown<'a> {
    /// The most bytes a window shows.
    const WIDTH: usize = 96;
    /// How many bytes [`around`](Shown::around) shows before the byte it
    /// centres on, so the reader sees what led up to the difference.
    const LEAD: usize = 16;

    /// The window at the start of `bytes`.
    const fn head(bytes: &'a [u8]) -> Shown<'a> {
        Shown { bytes, from: 0 }
    }

    /// The window over `bytes` that holds byte `at` and the
    /// [`LEAD`](Shown::LEAD) bytes before it.
    const fn around(bytes: &'a [u8], at: usize) -> Shown<'a> {
        Shown {
            bytes,
            from: at.saturating_sub(Shown::LEAD),
        }
    }
}

impl fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.bytes.len();
        let from = self.from.min(len);
        let rest: &[u8] = match self.bytes.get(from..) {
            Some(s) => s,
            None => &[],
        };
        let window: &[u8] = match rest.get(..Shown::WIDTH) {
            Some(w) => w,
            None => rest,
        };
        // `window` ends inside `bytes`, so its end is at most `len`.
        let cut_after = from.saturating_add(window.len()) < len;
        if from > 0 {
            f.write_str("…")?;
        }
        write!(f, "\"{}\"", window.escape_ascii())?;
        if cut_after {
            f.write_str("…")?;
        }
        if from > 0 || cut_after {
            write!(f, " ({len} bytes)")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The index of the first byte where `a` and `b` differ: the shorter one's
/// length when it is a prefix of the other (the longer one goes on).
const fn first_difference(a: &[u8], b: &[u8]) -> usize {
    let mut ra = a;
    let mut rb = b;
    let mut i = 0usize;
    while let &[ba, ref ta @ ..] = ra {
        let &[bb, ref tb @ ..] = rb else {
            break;
        };
        if ba != bb {
            return i;
        }
        i = i.saturating_add(1);
        ra = ta;
        rb = tb;
    }
    i
}

/// A record inside a divergence message: its variant and fields as the derived
/// `Debug` names them, with every byte string through [`Shown`]. A
/// [`KindMismatch`](ReplayDivergence::KindMismatch) found record is most often
/// a screen-carrying `Exchange` or `Emit` — what a replay that drifted by one
/// read finds next — so this is where the messages would otherwise grow.
struct Brief<'a>(&'a EffectRecord);

impl fmt::Debug for Brief<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            EffectRecord::Clock(v) => f.debug_tuple("Clock").field(v).finish(),
            EffectRecord::Rand(v) => f.debug_tuple("Rand").field(v).finish(),
            EffectRecord::Mono(v) => f.debug_tuple("Mono").field(v).finish(),
            EffectRecord::File { path, bytes } => f
                .debug_struct("File")
                .field("path", path)
                .field("bytes", &Shown::head(bytes))
                .finish(),
            EffectRecord::FileErr { path, kind } => f
                .debug_struct("FileErr")
                .field("path", path)
                .field("kind", kind)
                .finish(),
            EffectRecord::Exchange {
                door,
                request,
                reply,
            } => f
                .debug_struct("Exchange")
                .field("door", door)
                .field("request", &Shown::head(request))
                .field("reply", &Shown::head(reply))
                .finish(),
            EffectRecord::Emit { door, bytes } => f
                .debug_struct("Emit")
                .field("door", door)
                .field("bytes", &Shown::head(bytes))
                .finish(),
            EffectRecord::Raised { door, false_reads } => f
                .debug_struct("Raised")
                .field("door", door)
                .field("false_reads", false_reads)
                .finish(),
        }
    }
}

// The derived form, except that every byte string is a `Shown` window and a
// found record is a `Brief`; a diverged pair also names the offset of its
// first difference (`first_difference`), which is not a field but is the one
// number a reader of two 64 KiB screens needs.
impl fmt::Debug for ReplayDivergence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplayDivergence::Exhausted { expected } => f
                .debug_struct("Exhausted")
                .field("expected", expected)
                .finish(),
            ReplayDivergence::Unreached { position, found } => f
                .debug_struct("Unreached")
                .field("position", position)
                .field("found", &Brief(found))
                .finish(),
            ReplayDivergence::KindMismatch { expected, found } => f
                .debug_struct("KindMismatch")
                .field("expected", expected)
                .field("found", &Brief(found))
                .finish(),
            ReplayDivergence::PathDiverged { recorded, asked } => f
                .debug_struct("PathDiverged")
                .field("recorded", recorded)
                .field("asked", asked)
                .finish(),
            ReplayDivergence::DoorDiverged { recorded, asked } => f
                .debug_struct("DoorDiverged")
                .field("recorded", recorded)
                .field("asked", asked)
                .finish(),
            ReplayDivergence::RequestDiverged {
                door,
                recorded,
                asked,
            } => {
                let at = first_difference(recorded, asked);
                f.debug_struct("RequestDiverged")
                    .field("door", door)
                    .field("first_difference", &at)
                    .field("recorded", &Shown::around(recorded, at))
                    .field("asked", &Shown::around(asked, at))
                    .finish()
            }
            ReplayDivergence::OutputDiverged {
                door,
                recorded,
                emitted,
            } => {
                let at = first_difference(recorded, emitted);
                f.debug_struct("OutputDiverged")
                    .field("door", door)
                    .field("first_difference", &at)
                    .field("recorded", &Shown::around(recorded, at))
                    .field("emitted", &Shown::around(emitted, at))
                    .finish()
            }
            ReplayDivergence::Unrecorded { door, request } => f
                .debug_struct("Unrecorded")
                .field("door", door)
                .field("request", &Shown::head(request))
                .finish(),
        }
    }
}

impl fmt::Display for ReplayDivergence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplayDivergence::Exhausted { expected } => write!(
                f,
                "replay: effect tape exhausted — the program asked for a {expected} effect \
                 beyond what was recorded"
            ),
            ReplayDivergence::Unreached { position, found } => write!(
                f,
                "replay: the program ended with the tape unfinished — record {position}, {:?}, \
                 and any after it were never reached",
                Brief(found)
            ),
            ReplayDivergence::KindMismatch { expected, found } => {
                write!(
                    f,
                    "replay: expected a {expected} effect, got {:?}",
                    Brief(found)
                )
            }
            ReplayDivergence::PathDiverged { recorded, asked } => write!(
                f,
                "replay: file path diverged — recorded {recorded:?}, replay asked {asked:?}"
            ),
            ReplayDivergence::DoorDiverged { recorded, asked } => write!(
                f,
                "replay: door diverged — recorded {recorded:?}, replay used {asked:?}"
            ),
            ReplayDivergence::RequestDiverged {
                door,
                recorded,
                asked,
            } => {
                let at = first_difference(recorded, asked);
                write!(
                    f,
                    "replay: request through {door:?} diverged at byte {at} — recorded {}, \
                     replay asked {}",
                    Shown::around(recorded, at),
                    Shown::around(asked, at)
                )
            }
            ReplayDivergence::OutputDiverged {
                door,
                recorded,
                emitted,
            } => {
                let at = first_difference(recorded, emitted);
                write!(
                    f,
                    "replay: output through {door:?} diverged at byte {at} — recorded {}, \
                     replay emitted {}",
                    Shown::around(recorded, at),
                    Shown::around(emitted, at)
                )
            }
            ReplayDivergence::Unrecorded { door, request } => write!(
                f,
                "replay: no exchange through {door:?} with request {} was recorded",
                Shown::head(request)
            ),
        }
    }
}

impl std::error::Error for ReplayDivergence {}

/// The divergence for a record of the wrong kind at this position.
fn mismatch(expected: &'static str, found: &EffectRecord) -> ReplayDivergence {
    ReplayDivergence::KindMismatch {
        expected,
        found: found.clone(),
    }
}

/// Replays a tape in consumption order. It holds **no real backend**, so by
/// construction a replay run consumes no clock, rng, or file: for those doors
/// purity is structural, not inspected — there is nothing here to call.
///
/// The reply and flag doors are different, and this says so rather than
/// borrow the backend doors' guarantee. Their `live` closure is an ordinary
/// argument of [`exchange`](EffectSeam::exchange) and
/// [`raised`](EffectSeam::raised), handed to this seam like any other, and no
/// type stops an implementation from calling it. This one never does: both
/// methods bind the closure to `_`, so calling it takes an edit to the
/// signature a reviewer sees, and every replay test runs with closures that
/// panic if called (`tests/suite/exchange_replay.rs`, which also catches a replay
/// that falls back to the live world when the tape ends). So for the doors
/// that reach the outside world, "replay never calls `live`" is a property
/// this implementation keeps and its tests hold it to — inspected, not
/// structural.
///
/// A kind mismatch, a diverged path, door, request or output, or an exhausted
/// tape is refused with a [`ReplayDivergence`], so the program stops rather
/// than silently reading the real world. A tape the program ends before
/// reaching its end is refused too, but only where the program says it has
/// ended: [`finish`](ReplaySeam::finish), which a replay of a whole run calls
/// last — without it, a replay has checked a prefix of the tape, not the tape.
///
/// A refusal **consumes nothing**: after one, [`position`](ReplaySeam::position)
/// still names the record the program could not take and
/// [`peek`](ReplaySeam::peek) still shows it, which is what a report of "the
/// first divergence, at record N" reads.
///
/// The tape is any iterator of records — an in-memory [`EffectsLog`]
/// ([`ReplaySeam::new`]) or a reader decoding a file as replay goes
/// ([`ReplaySeam::streaming`]), so a long tape is never held whole.
pub struct ReplaySeam<I: Iterator<Item = EffectRecord> = std::vec::IntoIter<EffectRecord>> {
    tape: std::iter::Peekable<I>,
    consumed: usize,
    latches: Latches,
}

impl ReplaySeam {
    /// Replay `log` from the start.
    pub fn new(log: EffectsLog) -> ReplaySeam {
        ReplaySeam::streaming(log.0)
    }
}

impl<I: Iterator<Item = EffectRecord>> ReplaySeam<I> {
    /// Replay the records `records` yields, from the first, pulling each only
    /// when the program reaches it (plus one look-ahead record, for
    /// [`peek`](ReplaySeam::peek) and the [`raised`](EffectSeam::raised) door).
    pub fn streaming<T: IntoIterator<IntoIter = I, Item = EffectRecord>>(
        records: T,
    ) -> ReplaySeam<I> {
        ReplaySeam {
            tape: records.into_iter().peekable(),
            consumed: 0,
            latches: Latches::default(),
        }
    }

    /// The next record the program has not consumed, if the tape has one.
    pub fn peek(&mut self) -> Option<&EffectRecord> {
        self.tape.peek()
    }

    /// How many records the program has consumed: the index of the next one.
    pub fn position(&self) -> usize {
        self.consumed
    }

    /// The program has ended: `Ok` when it consumed every record on the tape,
    /// else [`ReplayDivergence::Unreached`] naming the first record it never
    /// reached. Like every refusal it consumes nothing, so
    /// [`position`](ReplaySeam::position) and [`peek`](ReplaySeam::peek) still
    /// name that record afterwards, and asking twice gives the same answer.
    ///
    /// The doors catch a tape that is too SHORT where the program finds it
    /// ended ([`Exhausted`](ReplayDivergence::Exhausted), an output past the
    /// end included). A tape that is too LONG no door can see, because the
    /// program simply stops asking: the records it never reached are what the
    /// recorded run went on to do — a last output the replayed one no longer
    /// says, a read it no longer makes, or a flag it stopped polling before
    /// the read that saw it rise. That last is silent at every door by design:
    /// [`raised`](EffectSeam::raised) answers false and leaves a `Raised`
    /// record it has not yet reached, so a run that polls once where the
    /// recorded run polled twice takes the not-stopped path and returns `Ok`.
    /// Only the program knows where it ends, so the check is a call it makes
    /// there.
    pub fn finish(&mut self) -> Result<(), ReplayDivergence> {
        match self.tape.peek() {
            None => Ok(()),
            Some(found) => Err(ReplayDivergence::Unreached {
                position: self.consumed,
                found: found.clone(),
            }),
        }
    }

    /// Consume the next record if it is of the `expected` kind and `read`
    /// accepts it, returning what `read` extracted; refuse (consuming nothing)
    /// with [`ReplayDivergence::KindMismatch`] when the record's
    /// [`kind`](EffectRecord::kind) is another, with `read`'s divergence, or
    /// with [`ReplayDivergence::Exhausted`] when the tape has ended.
    ///
    /// The kind is checked here, against [`EffectRecord::kind`], so the name a
    /// door asks with and the name its record answers to are one vocabulary
    /// rather than two lists kept alike by hand: a door whose name drifted
    /// from its record's would refuse every record of its own kind, which
    /// every replay test would see. Each `read`'s catch-all arm is the same
    /// refusal, reachable only through such a drift.
    fn peek_expected(&mut self, expected: &'static str) -> Result<&EffectRecord, ReplayDivergence> {
        let record = self
            .tape
            .peek()
            .ok_or(ReplayDivergence::Exhausted { expected })?;
        if record.kind() != expected {
            return Err(mismatch(expected, record));
        }
        Ok(record)
    }

    /// Step past the record [`peek`](ReplaySeam::peek) shows.
    fn advance(&mut self) {
        if self.tape.next().is_some() {
            // Bounded by the tape's length, which is a `usize` of records the
            // iterator produced; saturation only removes an add that could wrap.
            self.consumed = self.consumed.saturating_add(1);
            self.latches.record_boundary();
        }
    }
}

impl<I: Iterator<Item = EffectRecord>> EffectSeam for ReplaySeam<I> {
    type Error = ReplayDivergence;

    fn now_nanos(&mut self) -> Result<u64, ReplayDivergence> {
        let v = match self.peek_expected("Clock")? {
            EffectRecord::Clock(v) => *v,
            found => return Err(mismatch("Clock", found)),
        };
        self.advance();
        Ok(v)
    }
    fn mono_nanos(&mut self) -> Result<u64, ReplayDivergence> {
        let v = match self.peek_expected("Mono")? {
            EffectRecord::Mono(v) => *v,
            found => return Err(mismatch("Mono", found)),
        };
        self.advance();
        Ok(v)
    }
    fn next_rand(&mut self) -> Result<u64, ReplayDivergence> {
        let v = match self.peek_expected("Rand")? {
            EffectRecord::Rand(v) => *v,
            found => return Err(mismatch("Rand", found)),
        };
        self.advance();
        Ok(v)
    }
    /// Mirrors the recording seam's lossy door: a taped `FileErr` replays as the
    /// empty bytes the recorded program saw, so the output stays byte-identical.
    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, ReplayDivergence> {
        match self.try_read_file(path)? {
            Ok(bytes) => Ok(bytes),
            Err(_) => Ok(Vec::new()),
        }
    }
    fn try_read_file(&mut self, path: &str) -> Result<std::io::Result<Vec<u8>>, ReplayDivergence> {
        // The replayed program must read the SAME path it recorded. A diverged
        // path means the replay is not reproducing the recorded execution, so
        // refuse rather than hand back stale bytes (or a stale failure) for the
        // wrong file (the same fail-closed posture as a wrong-kind tape).
        let value = match self.peek_expected("File")? {
            EffectRecord::File {
                path: recorded,
                bytes,
            } => {
                if recorded != path {
                    return Err(ReplayDivergence::PathDiverged {
                        recorded: recorded.clone(),
                        asked: path.to_string(),
                    });
                }
                Ok(bytes.clone())
            }
            EffectRecord::FileErr {
                path: recorded,
                kind,
            } => {
                if recorded != path {
                    return Err(ReplayDivergence::PathDiverged {
                        recorded: recorded.clone(),
                        asked: path.to_string(),
                    });
                }
                Err(std::io::Error::from(*kind))
            }
            found => return Err(mismatch("File", found)),
        };
        self.advance();
        Ok(value)
    }
    /// The taped reply, never `live`'s: the closure is not called, so a replay
    /// can run where the socket, host or filesystem it stands for is gone.
    fn exchange(
        &mut self,
        door: &str,
        request: &[u8],
        _: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<Vec<u8>, ReplayDivergence> {
        let value = match self.peek_expected("Exchange")? {
            EffectRecord::Exchange {
                door: recorded,
                request: asked_then,
                reply,
            } => {
                if recorded != door {
                    return Err(ReplayDivergence::DoorDiverged {
                        recorded: recorded.clone(),
                        asked: door.to_string(),
                    });
                }
                if asked_then.as_slice() != request {
                    return Err(ReplayDivergence::RequestDiverged {
                        door: door.to_string(),
                        recorded: asked_then.clone(),
                        asked: request.to_vec(),
                    });
                }
                reply.clone()
            }
            found => return Err(mismatch("Exchange", found)),
        };
        self.advance();
        Ok(value)
    }
    fn emit(&mut self, door: &str, bytes: &[u8]) -> Result<(), ReplayDivergence> {
        match self.peek_expected("Emit")? {
            EffectRecord::Emit {
                door: recorded,
                bytes: said,
            } => {
                if recorded != door {
                    return Err(ReplayDivergence::DoorDiverged {
                        recorded: recorded.clone(),
                        asked: door.to_string(),
                    });
                }
                if said.as_slice() != bytes {
                    return Err(ReplayDivergence::OutputDiverged {
                        door: door.to_string(),
                        recorded: said.clone(),
                        emitted: bytes.to_vec(),
                    });
                }
            }
            found => return Err(mismatch("Emit", found)),
        }
        self.advance();
        Ok(())
    }
    /// Never refuses: a flag read that finds no `Raised` record for it — the
    /// next record is something else, the count says a later read, or the tape
    /// has ended — is a read the recording saw answer false, so it answers
    /// false and leaves the record for whatever the program asks next. A
    /// `Raised` record the program never reaches is caught there instead, as
    /// the kind mismatch of the next door it does use — or, when it uses no
    /// door after it, by [`finish`](ReplaySeam::finish), as the record left
    /// on the tape. A replay that returns without calling `finish` never
    /// learns of it.
    fn raised(
        &mut self,
        door: &str,
        _: &mut dyn FnMut() -> bool,
    ) -> Result<bool, ReplayDivergence> {
        if self.latches.is_raised(door) {
            return Ok(true);
        }
        let counted = self.latches.false_reads(door);
        let here = matches!(
            self.tape.peek(),
            Some(EffectRecord::Raised { door: recorded, false_reads })
                if recorded == door && *false_reads == counted
        );
        if !here {
            self.latches.note_false_read(door);
            return Ok(false);
        }
        self.advance();
        self.latches.raise(door);
        Ok(true)
    }
}
