//! Evidence for `effects.cooperative.record-replay`: a seam-cooperative program's
//! REAL clock/rng/file effects are recorded and replayed to a byte-identical
//! output, hermetically — replay touches no OS — verified against an INDEPENDENT
//! oracle, with order-sensitivity and abort-on-bad-tape proven so no drop /
//! wrong-value / wrong-kind / transposition mutation can pass green. A FAILED
//! file read is taped as the failure it was (not an empty success) and replays
//! as the same error kind.

use astream_effects::{
    oracle, run, tape_values, EffectRecord, EffectSeam, EffectsLog, OsEffects, RealEffects,
    RecordingSeam, ReplaySeam,
};
use std::io::{ErrorKind, Write};
use std::sync::Mutex;

/// Serialises the process-global panic-hook swap. `take_hook`/`set_hook` are each
/// atomic but the take → set(silent) → catch → set(prev) sequence is not: two
/// tests interleaving it can leave the silencing hook installed for the rest of
/// the process (swallowing a third test's diagnostics). One lock, held across the
/// whole swap, makes that impossible. `catch_unwind` absorbs the expected panic,
/// so the guard is released normally and never poisoned.
static HOOK_SWAP: Mutex<()> = Mutex::new(());

fn silent_catch<F: FnOnce() + std::panic::UnwindSafe>(f: F) -> bool {
    let _serial = HOOK_SWAP.lock().unwrap_or_else(|e| e.into_inner());
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(f);
    std::panic::set_hook(prev);
    r.is_err()
}

/// A temp path unique to THIS process and call: two concurrent `cargo test`
/// invocations (a developer's shell beside `astream-evidence run`) must not share
/// one file, or the loser reads the other's truncation/removal and flakes.
fn unique_temp_path(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let path = std::env::temp_dir().join(format!(
        "astream_effects_{tag}_{}_{nanos}.bin",
        std::process::id()
    ));
    (Cleanup(path.clone()), path)
}

/// Removes its file when dropped, so a test leaves nothing behind whether it passes
/// or panics. Bind it before whatever uses the file, so it drops after that.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[test]
fn record_then_replay_is_byte_identical_against_an_independent_oracle() {
    // A real temp file with known bytes.
    let (_tmp, path) = unique_temp_path("demo");
    let contents = b"astream effects rung: real bytes \xff\x00\x01";
    std::fs::File::create(&path)
        .unwrap()
        .write_all(contents)
        .unwrap();
    let path_s = path.to_str().unwrap().to_string();

    // RECORD pass: real OS effects, taped.
    let mut rec = RecordingSeam::new(OsEffects::new());
    let digest_rec = run(&mut rec, &path_s);
    let log = rec.into_log();

    // The tape is exactly [Clock, Rand, Rand, File].
    assert!(
        matches!(
            log.0.as_slice(),
            [
                EffectRecord::Clock(_),
                EffectRecord::Rand(_),
                EffectRecord::Rand(_),
                EffectRecord::File { .. }
            ]
        ),
        "unexpected tape shape: {:?}",
        log.0
    );
    let (c, r0, r1, bytes) = tape_values(&log).unwrap();
    assert_eq!(
        bytes, contents,
        "the recorded file bytes are the real file's"
    );

    // REPLAY pass: tape only, NO OS access (ReplaySeam holds no real backend).
    let digest_replay = run(&mut ReplaySeam::new(log.clone()), &path_s);

    // (a) Replay reproduces the recorded run.
    assert_eq!(
        digest_rec, digest_replay,
        "replay reproduces the recorded run"
    );
    // (b) Replay equals an INDEPENDENT oracle over the recorded values — the
    // value flowed through the seam machinery on one side, directly on the other.
    assert_eq!(
        digest_replay,
        oracle(c, r0, r1, &bytes),
        "replay == independent oracle over the recorded values"
    );
    // Distinctness + order-sensitivity: a transposition mutation would be caught.
    assert_ne!(r0, r1, "the two random words are distinct");
    assert_ne!(
        oracle(c, r0, r1, &bytes),
        oracle(c, r1, r0, &bytes),
        "the fold is order-sensitive (so r0/r1 transposition is observable)"
    );

    // A second replay from the same tape is identical (deterministic).
    let digest_replay2 = run(&mut ReplaySeam::new(log), &path_s);
    assert_eq!(digest_replay, digest_replay2, "replay is deterministic");
}

#[test]
fn a_short_tape_aborts_replay_rather_than_reading_the_real_world() {
    // A tape missing the File record: the program's read_file finds the tape
    // exhausted and ABORTS instead of silently falling back to a real read.
    let aborted = silent_catch(|| {
        let short = EffectsLog(vec![
            EffectRecord::Clock(1),
            EffectRecord::Rand(2),
            EffectRecord::Rand(3),
            // no File record
        ]);
        let _ = run(&mut ReplaySeam::new(short), "/etc/hostname");
    });
    assert!(
        aborted,
        "replay must abort on a short tape, not read the real file"
    );
}

#[test]
fn a_kind_mismatch_aborts_replay() {
    // First record is the wrong kind: now_nanos expects Clock but finds Rand.
    let aborted = silent_catch(|| {
        let wrong = EffectsLog(vec![
            EffectRecord::Rand(9),
            EffectRecord::Rand(2),
            EffectRecord::Rand(3),
            EffectRecord::File {
                path: "x".into(),
                bytes: vec![],
            },
        ]);
        let _ = run(&mut ReplaySeam::new(wrong), "x");
    });
    assert!(aborted, "replay must abort on a kind mismatch");
}

/// A backend whose file door fails with a chosen error kind — the denied-read
/// case the real filesystem cannot be made to produce portably in a test.
struct DeniedFs(ErrorKind);

impl RealEffects for DeniedFs {
    fn real_now_nanos(&mut self) -> u64 {
        7
    }
    fn real_next_rand(&mut self) -> u64 {
        8
    }
    fn real_read_file(&mut self, _path: &str) -> std::io::Result<Vec<u8>> {
        Err(std::io::Error::from(self.0))
    }
}

#[test]
fn a_failed_file_read_is_taped_as_the_failure_and_replays_as_it() {
    // A REAL missing file (this path is never created): the tape must say
    // NotFound, not "read an empty file".
    let (_tmp, missing) = unique_temp_path("missing");
    let missing_s = missing.to_str().unwrap().to_string();
    let mut rec = RecordingSeam::new(OsEffects::new());
    assert_eq!(
        rec.read_file(&missing_s),
        Vec::<u8>::new(),
        "the lossy door still hands the program empty bytes"
    );
    let log = rec.into_log();
    assert_eq!(
        log.0,
        vec![EffectRecord::FileErr {
            path: missing_s.clone(),
            kind: ErrorKind::NotFound,
        }],
        "the tape carries the failure, not an empty success"
    );
    // Replay: the lossy door reproduces the empty bytes the program saw, and the
    // checked door reproduces the SAME error kind — with no OS call (a replay of
    // this tape in a world where the file now exists must still fail).
    std::fs::write(&missing, b"now it exists").unwrap();
    let mut rep = ReplaySeam::new(log.clone());
    assert_eq!(rep.read_file(&missing_s), Vec::<u8>::new());
    let mut rep = ReplaySeam::new(log);
    let err = rep
        .try_read_file(&missing_s)
        .expect_err("replays the failure");
    assert_eq!(err.kind(), ErrorKind::NotFound);
    let _ = std::fs::remove_file(&missing);

    // A denied read (backend-simulated) is distinguishable from an empty file.
    let mut rec = RecordingSeam::new(DeniedFs(ErrorKind::PermissionDenied));
    let err = rec
        .try_read_file("/etc/shadow")
        .expect_err("the checked door surfaces the error");
    assert_eq!(err.kind(), ErrorKind::PermissionDenied);
    let log = rec.into_log();
    assert_ne!(
        log.0[0],
        EffectRecord::File {
            path: "/etc/shadow".into(),
            bytes: vec![],
        },
        "a denied read is not an empty read"
    );
    assert_eq!(
        ReplaySeam::new(log)
            .try_read_file("/etc/shadow")
            .expect_err("replayed")
            .kind(),
        ErrorKind::PermissionDenied
    );
}

#[test]
fn a_taped_failure_replayed_at_a_different_path_aborts() {
    // The path is part of the recorded effect for a failure too: replaying a
    // FileErr for a different file is a diverged execution, not a stale answer.
    let aborted = silent_catch(|| {
        let log = EffectsLog(vec![EffectRecord::FileErr {
            path: "/a".into(),
            kind: ErrorKind::NotFound,
        }]);
        let _ = ReplaySeam::new(log).read_file("/b");
    });
    assert!(
        aborted,
        "a diverged path must abort even for a taped failure"
    );
}
