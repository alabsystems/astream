//! The demo program — written ONCE against [`EffectSeam`], run under record and
//! replay. Its digest folds the effects **non-commutatively** (so a replay bug
//! that transposes the two random words is observable), with the file bytes folded
//! last.

use crate::seam::{EffectRecord, EffectSeam, EffectsLog};

const P: u64 = 0x0000_0100_0000_01b3;

/// Fold the four effects into a digest. Non-commutative in `r0`/`r1`.
fn digest(c: u64, r0: u64, r1: u64, bytes: &[u8]) -> u64 {
    let mut d = c;
    d = d.wrapping_mul(P).wrapping_add(r0);
    d = d.wrapping_mul(P).wrapping_add(r1);
    for &b in bytes {
        d = d.wrapping_mul(P).wrapping_add(b as u64);
    }
    d
}

/// The program: read one clock, two random words, then one file — in that fixed
/// order — and fold them. Works against any [`EffectSeam`], so the *same code*
/// runs under record and replay.
pub fn run<S: EffectSeam>(seam: &mut S, path: &str) -> u64 {
    let c = seam.now_nanos();
    let r0 = seam.next_rand();
    let r1 = seam.next_rand();
    let bytes = seam.read_file(path);
    digest(c, r0, r1, &bytes)
}

/// A GENUINELY INDEPENDENT recomputation of the digest — the order-sensitive head
/// is spelled out as a **closed form**, written WITHOUT the `digest` loop, so a
/// copy-paste fold bug (e.g. an `r0`/`r1` transposition or a wrong multiplier in
/// `digest`) cannot also live here: the two would then disagree. Equal to `digest`
/// on correct inputs. So `run(replay) == oracle(recorded values)` catches both
/// replay-machinery bugs (value flows through the seam on one side, directly on the
/// other) AND a shared fold-algorithm bug — never `f(x) == f(x)`.
pub fn oracle(c: u64, r0: u64, r1: u64, bytes: &[u8]) -> u64 {
    let head = c
        .wrapping_mul(P)
        .wrapping_add(r0)
        .wrapping_mul(P)
        .wrapping_add(r1);
    bytes
        .iter()
        .fold(head, |d, &b| d.wrapping_mul(P).wrapping_add(b as u64))
}

/// Extract the `(clock, rand0, rand1, file-bytes)` a tape recorded, in order.
/// Returns `None` unless the tape is exactly `[Clock, Rand, Rand, File]`.
pub fn tape_values(log: &EffectsLog) -> Option<(u64, u64, u64, Vec<u8>)> {
    match log.0.as_slice() {
        [EffectRecord::Clock(c), EffectRecord::Rand(r0), EffectRecord::Rand(r1), EffectRecord::File { bytes, .. }] => {
            Some((*c, *r0, *r1, bytes.clone()))
        }
        _ => None,
    }
}
