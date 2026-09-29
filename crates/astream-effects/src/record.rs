//! The RECORD pass: wrap the real OS and tape every value it returns.

use crate::seam::{EffectRecord, EffectSeam, EffectsLog};
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hasher};
use std::time::{SystemTime, UNIX_EPOCH};

/// The real-world backend a [`RecordingSeam`] draws from. Factored out as a trait
/// so the recording wrapper is testable and the only real OS access lives here.
pub trait RealEffects {
    /// The real wall clock, in nanoseconds.
    fn real_now_nanos(&mut self) -> u64;
    /// The real next random word.
    fn real_next_rand(&mut self) -> u64;
    /// The real file bytes.
    fn real_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>>;
}

/// The actual OS: the wall clock, an OS-seeded SplitMix64, and the filesystem.
pub struct OsEffects {
    rng: u64,
}

impl OsEffects {
    /// Seed the RNG from OS randomness — via `std`'s [`RandomState`], whose
    /// SipHash keys the standard library initialises from the operating system's
    /// random source (no third-party crate, no `/dev/urandom` read of our own) —
    /// mixed with the wall clock. Two record passes therefore draw different
    /// words, which is what makes replay non-trivial.
    pub fn new() -> OsEffects {
        let mut h = RandomState::new().build_hasher();
        h.write_u64(0x6173_7472_6561_6d21); // "astream!"
        let os_word = h.finish();
        let clock = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0x1234_5678_9abc_def0);
        OsEffects {
            rng: (os_word ^ clock) | 1, // never all-zero
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
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
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

/// Wraps a real backend and tapes every value it returns, in consumption order.
pub struct RecordingSeam<O: RealEffects> {
    inner: O,
    log: EffectsLog,
}

impl<O: RealEffects> RecordingSeam<O> {
    /// Record through `inner` (e.g. [`OsEffects`]).
    pub fn new(inner: O) -> RecordingSeam<O> {
        RecordingSeam {
            inner,
            log: EffectsLog::default(),
        }
    }
    /// Consume the seam, returning the tape it recorded.
    pub fn into_log(self) -> EffectsLog {
        self.log
    }
}

impl<O: RealEffects> EffectSeam for RecordingSeam<O> {
    fn now_nanos(&mut self) -> u64 {
        let v = self.inner.real_now_nanos();
        self.log.0.push(EffectRecord::Clock(v));
        v
    }
    fn next_rand(&mut self) -> u64 {
        let v = self.inner.real_next_rand();
        self.log.0.push(EffectRecord::Rand(v));
        v
    }
    /// The lossy door: the program sees empty bytes on a failed read, but the
    /// TAPE still carries the failure (as [`EffectRecord::FileErr`]), so an
    /// auditor reading the log can tell a denied read from an empty file, and
    /// replay hands the program the same empty bytes it saw.
    fn read_file(&mut self, path: &str) -> Vec<u8> {
        self.try_read_file(path).unwrap_or_default()
    }
    fn try_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        let r = self.inner.real_read_file(path);
        self.log.0.push(match &r {
            Ok(bytes) => EffectRecord::File {
                path: path.to_string(),
                bytes: bytes.clone(),
            },
            Err(e) => EffectRecord::FileErr {
                path: path.to_string(),
                kind: e.kind(),
            },
        });
        r
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
}
