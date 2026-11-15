//! The RECORD pass: wrap the real OS and tape every value it returns — and the
//! LIVE pass, the same real OS taped nowhere.

use crate::seam::{EffectRecord, EffectSeam, EffectsLog, Latches};
use std::collections::hash_map::RandomState;
use std::convert::Infallible;
use std::hash::{BuildHasher, Hasher};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "record_island.rs"]
mod record_island;
#[cfg(not(clean_islands))]
pub use crate::twins::record_mono_advance;
#[cfg(clean_islands)]
pub use record_island::record_mono_advance;

contract_fn! {
    /// Verified check that the SplitMix64 seed is strictly non-zero (`0 < seed`),
    /// linked via `clean-kernel-defeq` to `record_seed_non_zero_isl`.
    #[must_use]
    pub const fn record_seed_non_zero(seed: u64) -> bool
    clauses [ensures result == (0 < seed)]
    {
        0 < seed
    }
}

/// The real-world backend a [`RecordingSeam`] draws from. Factored out as a trait
/// so the recording wrapper is testable and the only real OS access lives here.
pub trait RealEffects {
    /// The real wall clock, in nanoseconds.
    fn real_now_nanos(&mut self) -> u64;
    /// The real monotonic clock: nanoseconds since this backend's origin.
    fn real_now_mono_nanos(&mut self) -> u64;
    /// The real next random word.
    fn real_next_rand(&mut self) -> u64;
    /// The real file bytes.
    fn real_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>>;
}

/// The actual OS: the wall clock, the monotonic clock measured from the moment
/// the backend was made, an OS-seeded SplitMix64, and the filesystem.
pub struct OsEffects {
    rng: u64,
    origin: Instant,
}

impl OsEffects {
    /// Seed the RNG from OS randomness — via `std`'s [`RandomState`], whose
    /// SipHash keys the standard library initialises from the operating system's
    /// random source (no third-party crate, no `/dev/urandom` read of our own) —
    /// mixed with the wall clock. Two record passes therefore draw different
    /// words, which is what makes replay non-trivial. The monotonic origin is
    /// taken here too, so [`real_now_mono_nanos`](RealEffects::real_now_mono_nanos)
    /// counts from this backend's birth: a small number a tape stores in a few
    /// bytes, not the OS's arbitrary boot-relative epoch.
    pub fn new() -> OsEffects {
        let mut h = RandomState::new().build_hasher();
        h.write_u64(0x6173_7472_6561_6d21); // "astream!"
        let os_word = h.finish();
        let clock = match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(d) => d.as_nanos() as u64,
            Err(_) => 0x1234_5678_9abc_def0,
        };
        OsEffects {
            rng: (os_word ^ clock) | 1, // never all-zero
            origin: Instant::now(),
        }
    }
}

impl Default for OsEffects {
    fn default() -> Self {
        OsEffects::new()
    }
}

impl RealEffects for OsEffects {
    fn real_now_nanos(&mut self) -> u64 {
        match SystemTime::now().duration_since(UNIX_EPOCH) {
            Ok(d) => d.as_nanos() as u64,
            Err(_) => 0,
        }
    }
    #[expect(
        clippy::manual_unwrap_or,
        reason = "a812042 spelled `unwrap_or` as a match for the verified lane; keep its form"
    )]
    fn real_now_mono_nanos(&mut self) -> u64 {
        // `Instant` never runs backwards, so this is monotone across calls. A
        // u64 of nanoseconds holds 584 years; past that it pins at the top
        // rather than wrapping to a small (earlier-looking) value.
        match u64::try_from(self.origin.elapsed().as_nanos()) {
            Ok(n) => n,
            Err(_) => u64::MAX,
        }
    }
    fn real_next_rand(&mut self) -> u64 {
        // SplitMix64.
        self.rng = self.rng.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.rng;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn real_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        std::fs::read(path)
    }
}

/// Where a [`RecordingSeam`] puts each record it tapes, in consumption order.
///
/// Two sinks come with the crate: an [`EffectsLog`], which keeps every record in
/// memory (the default — what [`RecordingSeam::new`] tapes into), and any
/// `FnMut(&EffectRecord)` closure, which is handed each record as it is made and
/// keeps none of them ([`RecordingSeam::with_sink`]). A long-running program
/// streams into the second, so its tape lives in a file a framing layer writes,
/// not in a `Vec` that grows for as long as the program runs.
pub trait RecordSink {
    /// Take one record. Called once per taped effect, in order.
    fn record(&mut self, record: &EffectRecord);
}

impl RecordSink for EffectsLog {
    fn record(&mut self, record: &EffectRecord) {
        self.0.push(record.clone());
    }
}

impl<F: FnMut(&EffectRecord)> RecordSink for F {
    fn record(&mut self, record: &EffectRecord) {
        self(record)
    }
}

/// Wraps a real backend and tapes every value it returns, in consumption order,
/// into a [`RecordSink`] (an in-memory [`EffectsLog`] unless built
/// [`with_sink`](RecordingSeam::with_sink)).
pub struct RecordingSeam<O: RealEffects, K: RecordSink = EffectsLog> {
    inner: O,
    sink: K,
    latches: Latches,
}

impl<O: RealEffects> RecordingSeam<O> {
    /// Record through `inner` (e.g. [`OsEffects`]) into an in-memory log.
    pub const fn new(inner: O) -> RecordingSeam<O> {
        RecordingSeam {
            inner,
            sink: EffectsLog(Vec::new()),
            latches: Latches::EMPTY,
        }
    }
    /// Consume the seam, returning the tape it recorded.
    pub fn into_log(self) -> EffectsLog {
        self.sink
    }
}

impl<O: RealEffects, K: RecordSink> RecordingSeam<O, K> {
    /// Record through `inner`, streaming each record to `sink` as it is made —
    /// a closure `|record: &EffectRecord| ..` or any other [`RecordSink`]. The
    /// seam keeps no copy, so its memory does not grow with the run.
    pub const fn with_sink(inner: O, sink: K) -> RecordingSeam<O, K> {
        RecordingSeam {
            inner,
            sink,
            latches: Latches::EMPTY,
        }
    }
    /// Tape one record. Every record restarts the
    /// [`raised`](EffectSeam::raised) door's false-read counts, which are
    /// relative to the record before a `Raised`.
    fn tape(&mut self, record: &EffectRecord) {
        self.sink.record(record);
        self.latches.record_boundary();
    }
}

impl<O: RealEffects, K: RecordSink> EffectSeam for RecordingSeam<O, K> {
    /// The real world always answers: a failed file read is the inner
    /// `io::Result` of [`try_read_file`](EffectSeam::try_read_file), not a
    /// refusal of the seam.
    type Error = Infallible;

    fn now_nanos(&mut self) -> Result<u64, Infallible> {
        let v = self.inner.real_now_nanos();
        self.tape(&EffectRecord::Clock(v));
        Ok(v)
    }
    fn mono_nanos(&mut self) -> Result<u64, Infallible> {
        let v = self.inner.real_now_mono_nanos();
        self.tape(&EffectRecord::Mono(v));
        Ok(v)
    }
    fn next_rand(&mut self) -> Result<u64, Infallible> {
        let v = self.inner.real_next_rand();
        self.tape(&EffectRecord::Rand(v));
        Ok(v)
    }
    /// The lossy door: the program sees empty bytes on a failed read, but the
    /// TAPE still carries the failure (as [`EffectRecord::FileErr`]), so an
    /// auditor reading the log can tell a denied read from an empty file, and
    /// replay hands the program the same empty bytes it saw.
    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, Infallible> {
        match self.inner.real_read_file(path) {
            Ok(bytes) => {
                self.tape(&EffectRecord::File {
                    path: path.to_string(),
                    bytes: bytes.clone(),
                });
                Ok(bytes)
            }
            Err(e) => {
                self.tape(&EffectRecord::FileErr {
                    path: path.to_string(),
                    kind: e.kind(),
                });
                Ok(Vec::new())
            }
        }
    }
    fn try_read_file(&mut self, path: &str) -> Result<std::io::Result<Vec<u8>>, Infallible> {
        let r = self.inner.real_read_file(path);
        let record = match &r {
            Ok(bytes) => EffectRecord::File {
                path: path.to_string(),
                bytes: bytes.clone(),
            },
            Err(e) => EffectRecord::FileErr {
                path: path.to_string(),
                kind: e.kind(),
            },
        };
        self.tape(&record);
        Ok(r)
    }
    /// The program gets the reply `live` produced, not a copy read back from
    /// the tape: the tape holds a clone, so nothing a sink does to its record
    /// can change what the recorded program saw.
    ///
    /// `live` runs INSIDE this call, under the seam's `&mut` borrow. A seam
    /// shared behind a lock is therefore locked for the whole round trip, and
    /// a door reached from inside `live` that takes the same lock — a control
    /// call made while a host call is answered — deadlocks (or panics) on its
    /// own thread. A recorder that must not hold its lock across a live round
    /// trip runs the round trip first, outside the lock, and then locks and
    /// hands this door the reply it already has:
    /// `seam.exchange(door, request, &mut |_| reply.clone())`. The record is
    /// the same (door, request, reply) triple either way.
    fn exchange(
        &mut self,
        door: &str,
        request: &[u8],
        live: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<Vec<u8>, Infallible> {
        let op: fn(_, _) -> _ = Option::map;
        let reply = op(Some(request), live).unwrap_or_default();
        self.tape(&EffectRecord::Exchange {
            door: door.to_string(),
            request: request.to_vec(),
            reply: reply.clone(),
        });
        Ok(reply)
    }
    fn emit(&mut self, door: &str, bytes: &[u8]) -> Result<(), Infallible> {
        self.tape(&EffectRecord::Emit {
            door: door.to_string(),
            bytes: bytes.to_vec(),
        });
        Ok(())
    }
    fn raised(&mut self, door: &str, live: &mut dyn FnMut() -> bool) -> Result<bool, Infallible> {
        if self.latches.is_raised(door) {
            // Latched: the flag is not read again, so a flag that falls back
            // can never show this program (or its replay) a lowered stop.
            return Ok(true);
        }
        let op: fn(_, _) -> _ = Option::unwrap_or_else;
        if !op(None, live) {
            self.latches.note_false_read(door);
            return Ok(false);
        }
        let false_reads = self.latches.false_reads(door);
        self.latches.raise(door);
        self.tape(&EffectRecord::Raised {
            door: door.to_string(),
            false_reads,
        });
        Ok(true)
    }
}

/// The real backend with no tape at all: every door answers from the live world
/// (a reply door calls its `live` closure, an output goes nowhere) and nothing
/// is kept. It is what a program written against [`EffectSeam`] runs on when no
/// one asked for a recording — the same code, the same answers as a
/// [`RecordingSeam`] over the same world, and no memory or I/O spent on a tape.
/// The one state it holds is the [`raised`](EffectSeam::raised) latch, because
/// the latch is part of that door's contract on every seam: a program must not
/// behave differently with recording off.
pub struct LiveSeam<O: RealEffects> {
    inner: O,
    latches: Latches,
}

impl<O: RealEffects> LiveSeam<O> {
    /// Run against `inner` (e.g. [`OsEffects`]) untaped.
    pub const fn new(inner: O) -> LiveSeam<O> {
        LiveSeam {
            inner,
            latches: Latches::EMPTY,
        }
    }
    /// Consume the seam, returning its backend.
    pub fn into_inner(self) -> O {
        self.inner
    }
}

impl<O: RealEffects> EffectSeam for LiveSeam<O> {
    type Error = Infallible;

    fn now_nanos(&mut self) -> Result<u64, Infallible> {
        Ok(self.inner.real_now_nanos())
    }
    fn mono_nanos(&mut self) -> Result<u64, Infallible> {
        Ok(self.inner.real_now_mono_nanos())
    }
    fn next_rand(&mut self) -> Result<u64, Infallible> {
        Ok(self.inner.real_next_rand())
    }
    fn read_file(&mut self, path: &str) -> Result<Vec<u8>, Infallible> {
        match self.inner.real_read_file(path) {
            Ok(bytes) => Ok(bytes),
            Err(_) => Ok(Vec::new()),
        }
    }
    fn try_read_file(&mut self, path: &str) -> Result<std::io::Result<Vec<u8>>, Infallible> {
        Ok(self.inner.real_read_file(path))
    }
    fn exchange(
        &mut self,
        _door: &str,
        request: &[u8],
        live: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<Vec<u8>, Infallible> {
        let op: fn(_, _) -> _ = Option::map;
        Ok(op(Some(request), live).unwrap_or_default())
    }
    fn emit(&mut self, _door: &str, _bytes: &[u8]) -> Result<(), Infallible> {
        Ok(())
    }
    fn raised(&mut self, door: &str, live: &mut dyn FnMut() -> bool) -> Result<bool, Infallible> {
        if self.latches.is_raised(door) {
            return Ok(true);
        }
        let op: fn(_, _) -> _ = Option::unwrap_or_else;
        let up = op(None, live);
        if up {
            self.latches.raise(door);
        }
        Ok(up)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn two_os_seeds_draw_different_first_words() {
        // The seed is OS randomness mixed with the clock; two fresh backends must
        // not replay each other's stream (that would make record/replay trivial).
        let (mut a, mut b) = (OsEffects::new(), OsEffects::new());
        assert_ne!(a.real_next_rand(), b.real_next_rand());
    }

    #[test]
    fn the_os_monotonic_clock_never_runs_backwards() {
        // Origin-relative and monotone: each read is at least the one before.
        // (No claim about how far it moves — that would be a latency budget.)
        let mut os = OsEffects::new();
        let mut last = os.real_now_mono_nanos();
        for _ in 0..1_000 {
            let now = os.real_now_mono_nanos();
            assert!(now >= last, "mono went from {last} to {now}");
            last = now;
        }
    }
}
