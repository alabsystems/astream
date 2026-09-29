//! Evidence for the Effects rung, foreign-process form (`effects.foreign-process.record-replay`).
//! Linux-only: it uses `ptrace` to record and replay the syscall effects of a
//! non-cooperating child process. On non-Linux this file is cfg'd to nothing (the
//! manifest claim is platform-gated to linux, so the darwin gate skips it).
#![cfg(target_os = "linux")]

use astream_effects::EffectsLog;
use astream_host::foreign::{self, Effect};

/// Removes its file when dropped, so a test leaves nothing behind whether it passes
/// or panics.
struct Cleanup(String);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn fixture_path(tag: &str) -> (Cleanup, String) {
    let path = format!("/tmp/astream_foreign_{}_{}.bin", std::process::id(), tag);
    (Cleanup(path.clone()), path)
}

/// The `(clock, rand, file-bytes)` a tape recorded, in order. `None` unless the
/// tape is exactly `[Clock, Rand, File]` — the child's fixed effect program.
fn tape_values(tape: &EffectsLog) -> Option<(u64, u64, Vec<u8>)> {
    match tape.0.as_slice() {
        [Effect::Clock(c), Effect::Rand(r), Effect::File { bytes, .. }] => {
            Some((*c, *r, bytes.clone()))
        }
        _ => None,
    }
}

/// An INDEPENDENT recomputation of the child's digest over taped values, written
/// WITHOUT calling `foreign::fold`: the rotates are spelled as shift-or pairs and
/// the byte step as a closure over `Iterator::fold`, with the constants restated.
/// A transposition or wrong-multiplier bug that lived only in `fold` (which BOTH
/// the child and a lazy `f(x) == f(x)` check would share) disagrees with this.
#[allow(clippy::manual_rotate)] // the different spelling IS the independence
fn oracle(clock: u64, rand: u64, bytes: &[u8]) -> u64 {
    let rotl7 = (clock << 7) | (clock >> 57);
    let head = rotl7 ^ rand.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    bytes.iter().fold(head, |h, &b| {
        let m = (h ^ u64::from(b)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        (m << 11) | (m >> 53)
    })
}

/// Replay `tape` against `path` and report whether it ABORTED (a panic caught by
/// `catch_unwind`, fail-closed like `ReplaySeam`). A machinery `Err` is NOT an
/// abort — it fails the test loudly instead.
fn replay_aborts(path: &str, tape: &EffectsLog) -> bool {
    match std::panic::catch_unwind(|| foreign::replay(path, tape)) {
        Err(_) => true,
        Ok(Ok(_)) => false,
        Ok(Err(e)) => panic!("replay machinery failed instead of aborting: {e}"),
    }
}

#[test]
fn foreign_process_effects_record_then_replay_exactly() {
    let (_tmp, path) = fixture_path("main");
    std::fs::write(&path, b"astream-effect-fixture-v1").unwrap();

    // RECORD: tape the foreign child's real clock/rand/file effects + its digest.
    let (tape, rec) = foreign::record(&path).expect("record");
    assert_eq!(tape.0.len(), 3, "three effects taped (clock, rand, file)");
    let (clock, rand, bytes) = tape_values(&tape).expect("the tape is exactly [Clock, Rand, File]");
    assert_eq!(
        bytes, b"astream-effect-fixture-v1",
        "the taped File bytes are what the tracee actually read"
    );

    // Independent oracle over the taped values (spelled without `fold`), and
    // order-sensitivity of the fold.
    assert_eq!(
        rec,
        oracle(clock, rand, &bytes),
        "record digest == independent oracle over the taped values"
    );
    assert_ne!(
        oracle(clock, rand, &bytes),
        oracle(rand, clock, &bytes),
        "the fold is order-sensitive (clock vs rand not interchangeable)"
    );

    // Change the world so a NAIVE replay would diverge.
    std::fs::write(&path, b"A-COMPLETELY-DIFFERENT-WORLD-NOW").unwrap();

    // REPLAY injecting the tape: reproduces the recorded digest despite the changed
    // world — the process is a pure function of the tape.
    assert_eq!(
        rec,
        foreign::replay(&path, &tape).expect("replay"),
        "injected replay reproduces the record"
    );

    // NAIVE replay (no injection) against the changed world: MUST differ — proving
    // the injection is load-bearing, not incidental.
    assert_ne!(
        rec,
        foreign::run_naive(&path).expect("naive run"),
        "without injection the changed world diverges"
    );
}

#[test]
fn a_short_tape_aborts_replay_fail_closed() {
    let (_tmp, path) = fixture_path("short");
    std::fs::write(&path, b"astream-effect-fixture-v1").unwrap();
    let (tape, _rec) = foreign::record(&path).expect("record");

    // Truncate the tape: replaying it must ABORT (the process asks for more effects
    // than were recorded) rather than silently reading the real world.
    let mut short = tape.clone();
    short.0.truncate(1);
    assert!(
        replay_aborts(&path, &short),
        "a short tape must abort replay (fail-closed, like ReplaySeam)"
    );
}

#[test]
fn a_wrong_kind_tape_aborts_replay_fail_closed() {
    let (_tmp, path) = fixture_path("kind");
    std::fs::write(&path, b"astream-effect-fixture-v1").unwrap();
    let (tape, _rec) = foreign::record(&path).expect("record");

    // Swap Clock and Rand: the tracee's first effect is a clock read, the tape
    // now offers a Rand there — replay must ABORT, never substitute a default.
    let mut swapped = tape.clone();
    swapped.0.swap(0, 1);
    assert!(
        matches!(swapped.0[0], Effect::Rand(_)),
        "the swapped tape leads with a Rand"
    );
    assert!(
        replay_aborts(&path, &swapped),
        "a wrong-kind tape must abort replay (fail-closed, like ReplaySeam)"
    );

    // A tape recorded against a different file name: the File record's path
    // diverges from what this replay reads — ABORT.
    let (_tmp_other, other) = fixture_path("kind-other");
    std::fs::write(&other, b"astream-effect-fixture-v1").unwrap();
    assert!(
        replay_aborts(&other, &tape),
        "a path-divergent tape must abort replay"
    );
}

#[test]
fn an_over_long_file_record_aborts_instead_of_overrunning_the_tracee() {
    let (_tmp, path) = fixture_path("long");
    std::fs::write(&path, b"astream-effect-fixture-v1").unwrap();
    let (tape, _rec) = foreign::record(&path).expect("record");

    // A File record larger than the tracee's 256-byte read buffer: the tracer must
    // ABORT before poking (it bounds the injection to the read's `count`), not
    // write 4 KiB over the tracee's stack.
    let mut long = tape.clone();
    long.0[2] = Effect::File {
        path: path.clone(),
        bytes: vec![b'x'; 4096],
    };
    assert!(
        replay_aborts(&path, &long),
        "an over-long File record must abort replay (bounded by the tracee's buffer)"
    );
    // Exactly the buffer size is still injectable.
    let mut full = tape.clone();
    full.0[2] = Effect::File {
        path: path.clone(),
        bytes: vec![b'y'; 256],
    };
    let (clock, rand, _) = tape_values(&tape).unwrap();
    assert_eq!(
        foreign::replay(&path, &full).expect("replay a buffer-sized File record"),
        oracle(clock, rand, &[b'y'; 256]),
        "a buffer-sized File record replays to its oracle"
    );
}

#[test]
fn recording_an_unreadable_file_tapes_an_empty_read_not_a_panic() {
    // openat fails, so the tracee's read returns -EBADF: the tracer must tape an
    // empty File (never allocate from a negative return), and the child's digest
    // is the oracle over (clock, rand, []) — the tracee too treats it as empty.
    let (_tmp, path) = fixture_path("missing-never-created");
    let (tape, rec) = foreign::record(&path).expect("record of a missing file");
    let (clock, rand, bytes) = tape_values(&tape).expect("[Clock, Rand, File]");
    assert!(bytes.is_empty(), "a failed read is an empty File effect");
    assert_eq!(
        rec,
        oracle(clock, rand, &[]),
        "digest == oracle over the empty read"
    );
}
