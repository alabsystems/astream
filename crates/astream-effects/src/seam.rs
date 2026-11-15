//! The cooperative effect seam: the doors a program reads the world through and
//! writes its outputs through, and the typed tape of what crossed them.

/// The effect seam a program is written against. Implemented by
/// [`RecordingSeam`](crate::RecordingSeam) (real OS, taped),
/// [`ReplaySeam`](crate::ReplaySeam) (tape only, no OS) and
/// [`LiveSeam`](crate::LiveSeam) (real OS, taped nowhere).
///
/// Every door is fallible in the seam's own [`Error`](EffectSeam::Error): the
/// recording seam always answers (its error is [`std::convert::Infallible`]),
/// while the replay seam refuses with a [`ReplayDivergence`](crate::ReplayDivergence)
/// when the tape cannot reproduce what the program asked for. A program written
/// against the seam propagates that error (`?`) instead of the seam aborting the
/// process, so a diverged replay is a typed, recoverable refusal.
///
/// The first three doors read values the seam's backend produces (a clock, a
/// random word, a file). The last three carry a value the PROGRAM supplies at
/// the call: a reply from somewhere the seam knows nothing about
/// ([`exchange`](EffectSeam::exchange), the socket-reply door), an output the
/// program produces ([`emit`](EffectSeam::emit)), and a flag another thread may
/// raise ([`raised`](EffectSeam::raised)). Those take the live world as a
/// closure, because the seam cannot own every socket and flag a program talks
/// to — and the replay seam must be able to answer without ever calling it.
pub trait EffectSeam {
    /// Why this seam could not answer an effect.
    type Error;
    /// Read a wall-clock value, in nanoseconds.
    fn now_nanos(&mut self) -> Result<u64, Self::Error>;
    /// Read the monotonic clock: nanoseconds since the backend's own origin.
    /// A kind of its own, distinct from the wall [`Clock`](EffectRecord::Clock),
    /// because the two answer different questions — "how long has this taken"
    /// never jumps when the wall clock is set, "what time is it" may — and a
    /// replay that fed one where the program asked for the other would hand a
    /// deadline computation a calendar date.
    fn mono_nanos(&mut self) -> Result<u64, Self::Error>;
    /// Draw the next random word.
    fn next_rand(&mut self) -> Result<u64, Self::Error>;
    /// Read a file's bytes. A read that fails yields empty bytes — the lossy
    /// door; use [`try_read_file`](EffectSeam::try_read_file) when the program
    /// must see (and the tape must carry) the failure.
    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, Self::Error>;
    /// Read a file's bytes, surfacing an I/O failure as the inner `Err`. The
    /// default just wraps [`read_file`](EffectSeam::read_file) in `Ok`; the
    /// recording and replay seams override it so a failed read is taped as
    /// [`EffectRecord::FileErr`] and replayed as the same [`std::io::ErrorKind`].
    /// The outer `Err` is the seam's own refusal, never an I/O failure.
    fn try_read_file(&mut self, path: &str) -> Result<std::io::Result<Vec<u8>>, Self::Error> {
        self.read_file(path).map(Ok)
    }
    /// The socket-reply door: send `request` through the door named `door` and
    /// return the reply. `live` is the real exchange (a control-socket round
    /// trip, a call into a host, a derived probe of the filesystem); it gets the
    /// request bytes and returns the reply bytes.
    ///
    /// Recording calls `live` exactly once and tapes the (door, request, reply)
    /// triple as an [`EffectRecord::Exchange`], returning the reply `live`
    /// produced — the live value itself, so a tape can never change what the
    /// recorded program saw. Replay returns the taped reply and **never calls
    /// `live`**; a door or request other than the recorded one is refused.
    /// The seam does not interpret either byte string: encoding a request and
    /// decoding a reply is the program's business.
    fn exchange(
        &mut self,
        door: &str,
        request: &[u8],
        live: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<Vec<u8>, Self::Error>;
    /// An output the program produced through the door named `door` — a printed
    /// line, a journal row, a write it wants checked rather than performed.
    /// Recording tapes it as an [`EffectRecord::Emit`]; replay compares it with
    /// the recorded output and refuses a difference, so a replay that drifts in
    /// what it SAYS is caught where it drifts, not only where it next reads.
    /// The seam never performs the output itself: writing the line somewhere is
    /// still the program's job, and in replay it should not.
    fn emit(&mut self, door: &str, bytes: &[u8]) -> Result<(), Self::Error>;
    /// Read a sticky flag through the door named `door`: a stop that another
    /// thread raises while the program runs. `live` is the real flag read.
    ///
    /// The door is a **latch** on every seam: once a read of `door` answers
    /// true, every later read of it answers true without consulting `live`.
    /// That is what makes the door replayable at all — a flag the program saw
    /// raised and then saw lowered would need every read taped — and it holds
    /// on [`LiveSeam`](crate::LiveSeam) as well, so a program does not behave
    /// differently with recording off.
    ///
    /// So the door is right only for a flag whose rise is final for the
    /// reader. A stop is: nothing lowers it. Not every flag is — aterm's
    /// handover flag, for one, is raised for a worker and lowered again when a
    /// policy switch-off revokes that worker. Read through this door, such a
    /// flag goes on answering true after its owner lowered it, on every seam,
    /// with recording on or off. Read a flag that can fall back some other way
    /// (an [`exchange`](EffectSeam::exchange) per read tapes every answer), or
    /// through this door only at a read a later lowering cannot reach — aterm
    /// reads its handover once, at the run's end, so the first read is the
    /// only one and no latch is in play.
    ///
    /// Recording tapes only the first true read, as an
    /// [`EffectRecord::Raised`] that also counts the reads of `door` that
    /// answered false since the record before it. A flag polled every loop step
    /// therefore costs nothing on the tape until it is raised, and the count
    /// pins WHICH read saw it: two reads with no other effect between them
    /// (`if stopped() { .. } let gone = stopped() && ..`) are told apart
    /// even though nothing else on the tape separates them. Replay answers
    /// false, consuming nothing, until the next record is that `Raised` and
    /// this is the counted read; then it consumes the record and latches.
    /// It never calls `live`.
    fn raised(&mut self, door: &str, live: &mut dyn FnMut() -> bool) -> Result<bool, Self::Error>;
}

/// One recorded effect, tagged by kind so replay can detect a kind mismatch.
#[derive(Debug, Clone, Eq)]
pub enum EffectRecord {
    /// A wall-clock read (nanoseconds).
    Clock(u64),
    /// A random word.
    Rand(u64),
    /// A file read that succeeded: the path requested and the bytes returned.
    File {
        /// The path read.
        path: String,
        /// The bytes returned.
        bytes: Vec<u8>,
    },
    /// A file read that FAILED: the path requested and the I/O error kind the OS
    /// returned. Distinct from `File { bytes: [] }` (an empty file read cleanly)
    /// so a tape written by [`RecordingSeam`](crate::RecordingSeam) — the audit
    /// trail for "what did this program read?" — can tell "read `/etc/shadow`,
    /// got 1 KiB" from "read `/etc/shadow`, permission denied", and replay
    /// reproduces the failure rather than an empty success. The distinction is
    /// the RECORDING SEAM's, not the type's: the other producer of this log, the
    /// Linux `astream-host::foreign` tracer, does not emit this variant yet — it
    /// still tapes a failed read as `File { bytes: [] }`, so a foreign-process
    /// tape cannot be read for that difference.
    FileErr {
        /// The path the read was attempted on.
        path: String,
        /// The error kind the real read returned.
        kind: std::io::ErrorKind,
    },
    /// A monotonic-clock read: nanoseconds since the backend's origin. Never
    /// interchangeable with [`Clock`](EffectRecord::Clock) — see
    /// [`EffectSeam::mono_nanos`].
    Mono(u64),
    /// One round trip through a reply door: the door's name, the request the
    /// program sent, and the reply the live world returned (see
    /// [`EffectSeam::exchange`]). Both byte strings are opaque to this crate.
    Exchange {
        /// The door's name, e.g. `"ctl"` or `"host.at_idle"`.
        door: String,
        /// The request bytes, exactly as the program sent them.
        request: Vec<u8>,
        /// The reply bytes, exactly as the live world returned them.
        reply: Vec<u8>,
    },
    /// An output the program produced (see [`EffectSeam::emit`]).
    Emit {
        /// The door's name, e.g. `"out"` or `"journal"`.
        door: String,
        /// The output, exactly as the program produced it.
        bytes: Vec<u8>,
    },
    /// The first read of a sticky flag that answered true (see
    /// [`EffectSeam::raised`]).
    Raised {
        /// The flag's door, e.g. `"stop"`.
        door: String,
        /// How many reads of THIS door answered false between the record
        /// before this one (or the start of the tape) and the read that
        /// answered true. It is what lets replay pick the right read when
        /// several reads of the flag sit between the same two records.
        false_reads: u64,
    },
}

impl PartialEq for EffectRecord {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Clock(a), Self::Clock(b)) => a == b,
            (Self::Rand(a), Self::Rand(b)) => a == b,
            (
                Self::File {
                    path: pa,
                    bytes: ba,
                },
                Self::File {
                    path: pb,
                    bytes: bb,
                },
            ) => pa == pb && ba == bb,
            (Self::FileErr { path: pa, kind: ka }, Self::FileErr { path: pb, kind: kb }) => {
                pa == pb && ka == kb
            }
            (Self::Mono(a), Self::Mono(b)) => a == b,
            (
                Self::Exchange {
                    door: da,
                    request: rqa,
                    reply: rpa,
                },
                Self::Exchange {
                    door: db,
                    request: rqb,
                    reply: rpb,
                },
            ) => da == db && rqa == rqb && rpa == rpb,
            (
                Self::Emit {
                    door: da,
                    bytes: ba,
                },
                Self::Emit {
                    door: db,
                    bytes: bb,
                },
            ) => da == db && ba == bb,
            (
                Self::Raised {
                    door: da,
                    false_reads: fa,
                },
                Self::Raised {
                    door: db,
                    false_reads: fb,
                },
            ) => da == db && fa == fb,
            _ => false,
        }
    }
}

impl EffectRecord {
    /// The record's kind: the name a [`ReplaySeam`](crate::ReplaySeam) door
    /// asks for, and so the `expected` of a
    /// [`ReplayDivergence`](crate::ReplayDivergence). The replay seam refuses
    /// a record whose kind is not the one its door names before it reads a
    /// field, so `found.kind() != expected` holds for every
    /// [`KindMismatch`](crate::ReplayDivergence::KindMismatch) it returns.
    /// Both file outcomes are `"File"`, because one door reads either. A
    /// `Raised` record is taken only by the flag door, which never refuses
    /// (see [`EffectSeam::raised`]), so `"Raised"` is only ever a found kind.
    pub const fn kind(&self) -> &'static str {
        match self {
            EffectRecord::Clock(_) => "Clock",
            EffectRecord::Rand(_) => "Rand",
            EffectRecord::File { .. } | EffectRecord::FileErr { .. } => "File",
            EffectRecord::Mono(_) => "Mono",
            EffectRecord::Exchange { .. } => "Exchange",
            EffectRecord::Emit { .. } => "Emit",
            EffectRecord::Raised { .. } => "Raised",
        }
    }

    /// Numeric discriminator tag for this effect record variant (`1..=8`).
    #[must_use]
    pub const fn tag_byte(&self) -> u8 {
        match self {
            EffectRecord::Clock(_) => 1,
            EffectRecord::Rand(_) => 2,
            EffectRecord::File { .. } => 3,
            EffectRecord::FileErr { .. } => 4,
            EffectRecord::Mono(_) => 5,
            EffectRecord::Exchange { .. } => 6,
            EffectRecord::Emit { .. } => 7,
            EffectRecord::Raised { .. } => 8,
        }
    }
}

/// Encode a 9-byte scalar effect frame `(tag: u8, val: u64 LE)`.
#[must_use]
pub const fn encode_scalar_effect(tag: u8, val: u64) -> [u8; 9] {
    [
        tag,
        val as u8,
        (val >> 8) as u8,
        (val >> 16) as u8,
        (val >> 24) as u8,
        (val >> 32) as u8,
        (val >> 40) as u8,
        (val >> 48) as u8,
        (val >> 56) as u8,
    ]
}

/// Decode a 9-byte scalar effect frame into `(tag: u8, val: u64)`.
#[must_use]
pub const fn decode_scalar_effect(raw: &[u8; 9]) -> (u8, u64) {
    let val = (raw[1] as u64)
        | ((raw[2] as u64) << 8)
        | ((raw[3] as u64) << 16)
        | ((raw[4] as u64) << 24)
        | ((raw[5] as u64) << 32)
        | ((raw[6] as u64) << 40)
        | ((raw[7] as u64) << 48)
        | ((raw[8] as u64) << 56);
    (raw[0], val)
}

/// An ordered tape of the effects a program consumed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectsLog(pub Vec<EffectRecord>);

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "seam_island.rs"]
mod seam_island;
#[cfg(not(clean_islands))]
pub use crate::twins::seam_false_reads_advance;
#[cfg(clean_islands)]
pub use seam_island::seam_false_reads_advance;

contract_fn! {
    /// Verified check that a taped `Raised` record's `false_reads` matches the replay's
    /// `counted` false reads, linked via `clean-kernel-defeq` to `seam_false_reads_matches_isl`.
    #[must_use]
    pub const fn seam_false_reads_matches(recorded: u64, counted: u64) -> bool
    clauses [ensures result == (recorded == counted)]
    {
        recorded == counted
    }
}

/// The state every seam keeps for the [`raised`](EffectSeam::raised) door: the
/// doors already latched true, and — for the recording and replay seams — how
/// many reads of each door answered false since the last record was taped (or
/// consumed). Both lists hold one entry per flag a program polls, which is a
/// handful, so a linear scan beats any map and keeps the crate free of hashing.
#[derive(Debug, Default)]
pub(crate) struct Latches {
    raised: Vec<String>,
    quiet: Vec<(String, u64)>,
}

impl Latches {
    /// An empty latch table with no allocations and no call terminator.
    pub(crate) const EMPTY: Self = Self {
        raised: Vec::new(),
        quiet: Vec::new(),
    };

    /// Whether `door` has already answered true.
    pub(crate) fn is_raised(&self, door: &str) -> bool {
        let mut rest = self.raised.as_slice();
        while let [d, tail @ ..] = rest {
            if d == door {
                return true;
            }
            rest = tail;
        }
        false
    }

    /// Latch `door` true from now on.
    pub(crate) fn raise(&mut self, door: &str) {
        if !self.is_raised(door) {
            self.raised.push(door.to_string());
        }
    }

    /// The reads of `door` that answered false since the last record.
    pub(crate) fn false_reads(&self, door: &str) -> u64 {
        let mut rest = self.quiet.as_slice();
        while let [(d, n), tail @ ..] = rest {
            if d == door {
                return *n;
            }
            rest = tail;
        }
        0
    }

    /// One more read of `door` answered false. Saturating: a flag polled more
    /// than `u64::MAX` times between two records is not a tape anyone holds.
    pub(crate) fn note_false_read(&mut self, door: &str) {
        let mut i = 0usize;
        let mut rest = self.quiet.as_slice();
        while let [(d, n), tail @ ..] = rest {
            if d == door {
                let next = seam_false_reads_advance(*n, n.saturating_add(1));
                if let Some(slot) = self.quiet.get_mut(i) {
                    slot.1 = next;
                }
                return;
            }
            i = i.saturating_add(1);
            rest = tail;
        }
        self.quiet.push((door.to_string(), 1));
    }

    /// A record was taped or consumed: every door's false-read count restarts,
    /// because a [`Raised`](EffectRecord::Raised) count is relative to the
    /// record before it.
    pub(crate) fn record_boundary(&mut self) {
        self.quiet.clear();
    }
}
