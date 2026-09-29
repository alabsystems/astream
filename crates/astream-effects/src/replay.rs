//! The REPLAY pass: re-feed the recorded tape, touching NO real effect.

use crate::seam::{EffectRecord, EffectSeam, EffectsLog};

/// Replays an [`EffectsLog`] in consumption order. It holds **no real backend**,
/// so by construction a replay run consumes no clock, rng, or file — purity is
/// structural, not inspected. A kind mismatch or an exhausted tape **panics**, so
/// the program aborts rather than silently reading the real world.
pub struct ReplaySeam {
    tape: std::vec::IntoIter<EffectRecord>,
}

impl ReplaySeam {
    /// Replay `log` from the start.
    pub fn new(log: EffectsLog) -> ReplaySeam {
        ReplaySeam {
            tape: log.0.into_iter(),
        }
    }
    fn pop(&mut self) -> EffectRecord {
        self.tape
            .next()
            .expect("replay: effect tape exhausted — the program asked for more than was recorded")
    }
}

impl EffectSeam for ReplaySeam {
    fn now_nanos(&mut self) -> u64 {
        match self.pop() {
            EffectRecord::Clock(v) => v,
            other => panic!("replay: expected a Clock effect, got {other:?}"),
        }
    }
    fn next_rand(&mut self) -> u64 {
        match self.pop() {
            EffectRecord::Rand(v) => v,
            other => panic!("replay: expected a Rand effect, got {other:?}"),
        }
    }
    /// Mirrors the recording seam's lossy door: a taped `FileErr` replays as the
    /// empty bytes the recorded program saw, so the output stays byte-identical.
    fn read_file(&mut self, path: &str) -> Vec<u8> {
        self.try_read_file(path).unwrap_or_default()
    }
    fn try_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        // The replayed program must read the SAME path it recorded. A diverged
        // path means the replay is not reproducing the recorded execution, so
        // abort rather than hand back stale bytes (or a stale failure) for the
        // wrong file (the same fail-closed posture as a wrong-kind tape).
        fn diverged(recorded: &str, asked: &str) -> ! {
            panic!("replay: file path diverged — recorded {recorded:?}, replay asked {asked:?}")
        }
        match self.pop() {
            EffectRecord::File {
                path: recorded,
                bytes,
            } => {
                if recorded != path {
                    diverged(&recorded, path);
                }
                Ok(bytes)
            }
            EffectRecord::FileErr {
                path: recorded,
                kind,
            } => {
                if recorded != path {
                    diverged(&recorded, path);
                }
                Err(std::io::Error::from(kind))
            }
            other => panic!("replay: expected a File effect, got {other:?}"),
        }
    }
}
