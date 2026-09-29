//! The effect seam: the single door to nondeterminism.
//!
//! Determinism is load-bearing from day one (doctrine §4.1): the engine reaches
//! the clock, randomness, and storage *only* through this seam, so a seeded seam
//! makes a recording reproducible and a replay exact. All four capability traits
//! ([`Clock`], [`Rng`], [`Disk`], [`Net`]) are named, though the engine consults
//! only the clock and the disk, so later effects slot in behind the same surface
//! with the engine untouched.
//!
//! The seam is taken by generic `<E: Effects>`, not `&mut dyn Effects`: there is
//! exactly one engine type, so monomorphization keeps the single-writer append
//! path inlinable with no vtable indirection, and [`Disk::read_all`] borrows the
//! stored bytes with no boxing.
//!
//! [`Seeded`] is the only seam implementation, and all three of its parts are
//! pure: a [`LogicalClock`] counter (never the wall clock), a seed-derived
//! [`SplitMix64`], and an in-memory [`MemDisk`]. There is no OS-backed seam;
//! durability comes from persisting a log's frames with [`crate::FileLog`].

/// A logical clock. Each read advances time and returns the previous value, so
/// the value is a *recorded input*: replay feeds it back and stays deterministic.
pub trait Clock {
    /// The current logical time; advances the clock by one tick.
    fn now_logical(&mut self) -> u64;

    /// Ensure every later [`now_logical`](Self::now_logical) returns a value
    /// strictly greater than `ts`. A session that resumes over a recovered log
    /// calls this with the last stored `ts_logical`, so the records it appends
    /// stay clock-monotone with the ones already on disk.
    ///
    /// The default reads the clock until it has passed `ts`, which is right for
    /// a clock that advances on its own; a pure counter overrides it with a jump
    /// (see [`LogicalClock`]). At `ts == u64::MAX` no later value exists, so it
    /// returns at once rather than spinning forever on a log stamped at the top
    /// of the range.
    fn advance_past(&mut self, ts: u64) {
        if ts == u64::MAX {
            return;
        }
        while self.now_logical() <= ts {}
    }
}

/// A deterministic random source (seam-mediated so randomness is replayable).
pub trait Rng {
    /// The next 64-bit draw.
    fn next_u64(&mut self) -> u64;
}

/// The log's byte store. The engine writes framed records here and a reader
/// decodes them back; the bytes are the only thing that crosses record/replay.
pub trait Disk {
    /// Append raw frame bytes to the end of the log.
    fn append(&mut self, bytes: &[u8]);
    /// Borrow the entire stored byte log (what a reader decodes).
    fn read_all(&self) -> &[u8];
    /// Total bytes stored.
    fn len(&self) -> usize;
    /// Whether the store holds no bytes.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// A network effect. Present so the seam is complete; unused on the rung-1
/// `Out`-driven path.
pub trait Net {
    /// Receive one inbound message, if any is ready.
    fn recv(&mut self) -> Option<Vec<u8>>;
}

/// The full effect seam: a clock, a random source, and a disk.
pub trait Effects {
    /// The clock implementation.
    type C: Clock;
    /// The random-source implementation.
    type R: Rng;
    /// The disk implementation.
    type D: Disk;
    /// The clock (mutable: a read advances logical time).
    fn clock(&mut self) -> &mut Self::C;
    /// The random source.
    fn rng(&mut self) -> &mut Self::R;
    /// The disk.
    fn disk(&mut self) -> &mut Self::D;
}

/// A fully deterministic, seeded seam: the only nondeterminism source in rung 1,
/// and itself pure. Two `Seeded::new(seed)` produce identical recordings.
pub struct Seeded {
    clock: LogicalClock,
    rng: SplitMix64,
    disk: MemDisk,
}

impl Seeded {
    /// A fresh seam: logical time at 0, RNG seeded, disk empty.
    pub fn new(seed: u64) -> Self {
        Self::with_disk(seed, MemDisk::new())
    }

    /// A seam over an existing `disk` (e.g. [`MemDisk::from_bytes`] of a
    /// recovered log). Logical time starts at 0: a session continuing that log
    /// must advance the clock past the stored `ts_logical`s — which is what
    /// [`crate::Session::resume_from`] does.
    pub fn with_disk(seed: u64, disk: MemDisk) -> Self {
        Seeded {
            clock: LogicalClock { tick: 0 },
            rng: SplitMix64::new(seed),
            disk,
        }
    }
}

impl Effects for Seeded {
    type C = LogicalClock;
    type R = SplitMix64;
    type D = MemDisk;
    fn clock(&mut self) -> &mut LogicalClock {
        &mut self.clock
    }
    fn rng(&mut self) -> &mut SplitMix64 {
        &mut self.rng
    }
    fn disk(&mut self) -> &mut MemDisk {
        &mut self.disk
    }
}

/// A pure monotonic counter standing in for a clock: read returns 0, 1, 2, …
/// (never the wall clock, so recordings are reproducible).
pub struct LogicalClock {
    tick: u64,
}

impl Clock for LogicalClock {
    fn now_logical(&mut self) -> u64 {
        let t = self.tick;
        // Saturate: a counter at the top of the range repeats it rather than
        // wrapping to 0 and running backwards.
        self.tick = self.tick.saturating_add(1);
        t
    }

    /// A counter jumps: the next read is exactly `ts + 1` (or the counter's
    /// current value, if it is already past), so a resumed log continues the
    /// positional `tick == append index` stamping of a never-interrupted one.
    fn advance_past(&mut self, ts: u64) {
        self.tick = self.tick.max(ts.saturating_add(1));
    }
}

/// SplitMix64: a small, fast, fully-specified seeded PRNG (no third-party dep).
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// Seed the generator.
    pub fn new(seed: u64) -> Self {
        SplitMix64 { state: seed }
    }
}

impl Rng for SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// An in-memory log store: one growing byte vector.
pub struct MemDisk {
    bytes: Vec<u8>,
}

impl MemDisk {
    /// An empty store.
    pub fn new() -> Self {
        MemDisk { bytes: Vec::new() }
    }

    /// A reader-side store holding exactly the already-persisted bytes. The
    /// replay pass uses this so the reader holds *only* the stored bytes — it
    /// cannot reach the live record list.
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        MemDisk { bytes }
    }
}

impl Default for MemDisk {
    fn default() -> Self {
        Self::new()
    }
}

impl Disk for MemDisk {
    fn append(&mut self, b: &[u8]) {
        self.bytes.extend_from_slice(b);
    }
    fn read_all(&self) -> &[u8] {
        &self.bytes
    }
    fn len(&self) -> usize {
        self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logical_clock_is_a_monotonic_counter() {
        let mut c = LogicalClock { tick: 0 };
        assert_eq!(
            [c.now_logical(), c.now_logical(), c.now_logical()],
            [0, 1, 2]
        );
    }

    #[test]
    fn advance_past_makes_the_next_read_strictly_later() {
        // The counter override jumps exactly to ts + 1 ...
        let mut c = LogicalClock { tick: 0 };
        c.advance_past(41);
        assert_eq!(c.now_logical(), 42);
        // ... never moves backwards ...
        c.advance_past(3);
        assert_eq!(c.now_logical(), 43);
        // ... and saturates instead of wrapping at the top of the range.
        c.advance_past(u64::MAX);
        assert_eq!(c.now_logical(), u64::MAX);
        // ... and stays there rather than wrapping to 0 on the next read.
        assert_eq!(c.now_logical(), u64::MAX);

        // The trait default (read until past ts) agrees with the override on the
        // only property a caller relies on: the next read is > ts.
        struct Plain(u64);
        impl Clock for Plain {
            fn now_logical(&mut self) -> u64 {
                let t = self.0;
                self.0 += 1;
                t
            }
        }
        let mut p = Plain(0);
        p.advance_past(9);
        assert!(p.now_logical() > 9);
        // No value is later than u64::MAX: the default returns instead of
        // spinning forever (a log stamped at the top of the range must not hang
        // a resume).
        let mut p = Plain(0);
        p.advance_past(u64::MAX);
        assert_eq!(p.now_logical(), 0);
    }

    #[test]
    fn seeded_with_disk_starts_over_the_given_bytes() {
        let mut fx = Seeded::with_disk(1, MemDisk::from_bytes(b"prior".to_vec()));
        assert_eq!(fx.disk().read_all(), b"prior");
        fx.disk().append(b"+new");
        assert_eq!(fx.disk().read_all(), b"prior+new");
        assert_eq!(fx.clock().now_logical(), 0, "the clock still starts at 0");
    }

    #[test]
    fn seeded_rng_is_reproducible_and_seed_sensitive() {
        let mut a = SplitMix64::new(0xABCD);
        let mut b = SplitMix64::new(0xABCD);
        assert_eq!(a.next_u64(), b.next_u64());
        assert_ne!(SplitMix64::new(1).next_u64(), SplitMix64::new(2).next_u64());
    }

    #[test]
    fn memdisk_roundtrips_appended_bytes() {
        let mut d = MemDisk::new();
        assert!(d.is_empty());
        d.append(b"ab");
        d.append(b"cd");
        assert_eq!(d.read_all(), b"abcd");
        assert_eq!(d.len(), 4);
    }
}
