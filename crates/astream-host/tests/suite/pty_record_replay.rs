//! Rung-2 evidence: a real PTY session records and replays. Backs the claim
//! `term.pty.records-and-replays`.
//!
//! Spawns a real pseudo-terminal (libc posix_openpt on Linux, openpty on other
//! Unix; then fork + exec) running a fixed deterministic child, drains the master
//! into `Record::Out` on the engine Log through the seam, reaps the child into
//! `Record::Exit`. Then — after the live
//! PTY and seam are dropped — a separate read-by-offset pass over ONLY the stored
//! bytes reconstructs the records and folds a screen byte-equal to both the live
//! screen and the known output's screen. Chunk boundaries/timing are NOT asserted
//! (they are nondeterministic); the chunk-invariant folded screen IS.

#![cfg(unix)]

use astream_engine::effects::{Disk, Effects};
use astream_engine::{Log, MemDisk, Offset, Seeded};
use astream_host::{Pty, KNOWN_OUTPUT};
use astream_term::{screen, Record};
use std::time::{Duration, Instant};

const COLS: u16 = 40;
const ROWS: u16 = 6;
const SEED: u64 = 0xC0DE;

#[test]
fn real_pty_session_records_and_replays() {
    let child = env!("CARGO_BIN_EXE_pty_child");

    // RECORD on a worker thread joined with a deadline, so a hang fails loudly
    // instead of blocking CI. The child writes a finite string and exits, so EOF
    // arrives promptly; the deadline is belt-and-suspenders.
    let worker = std::thread::spawn(move || {
        let mut fx = Seeded::new(SEED);
        let mut log = Log::new();
        let mut pty = Pty::spawn(child, &[], COLS, ROWS).expect("spawn pty");
        let chunks = pty.record_to_eof(&mut log, &mut fx).expect("record to eof");
        let stored = fx.disk().read_all().to_vec();
        let live = screen::fold(COLS, ROWS, &chunks).serialize();
        (stored, live)
    });

    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(15),
            "the pty recording timed out"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let (stored, live_screen) = worker.join().expect("record thread panicked");

    // REPLAY from stored bytes only — no PTY, no OS.
    let reader = MemDisk::from_bytes(stored);
    let mut replayed: Vec<Record> = Vec::new();
    let mut seqs: Vec<Offset> = Vec::new();
    for item in Log::read_from(&reader, Offset::ZERO) {
        let env = item.expect("decode from stored bytes");
        seqs.push(env.seq);
        replayed.push(env.record);
    }
    let folded = screen::fold(COLS, ROWS, &replayed).serialize();

    // (1) The from-disk screen equals what the real PTY emitted.
    assert_eq!(
        folded, live_screen,
        "replayed screen equals the live PTY screen"
    );

    // (2) ...and equals the independently-folded screen of the KNOWN child output
    //     (one side a constant the kernel did not produce — not a fold-vs-itself).
    let expected = screen::fold(COLS, ROWS, &[Record::Out(KNOWN_OUTPUT.to_vec())]).serialize();
    assert_eq!(folded, expected, "screen equals the known output's screen");

    // (3) The log is dense (seq == position) and sealed with the child's exit.
    for (i, seq) in seqs.iter().enumerate() {
        assert_eq!(*seq, Offset(i as u64), "dense, gapless offsets");
    }
    assert!(
        matches!(replayed.last(), Some(Record::Exit { code: 0 })),
        "the log is sealed with Exit {{ code: 0 }}, got {:?}",
        replayed.last()
    );

    // Sanity: a real session produced at least one Out record and the screen
    // shows the expected content.
    assert!(
        replayed.iter().any(|r| matches!(r, Record::Out(_))),
        "at least one Out record"
    );
    let final_screen = screen::fold(COLS, ROWS, &replayed);
    assert_eq!(
        final_screen.line_text(0),
        "ERR ok",
        "the folded screen content"
    );
}

/// Exercise the remaining `sys` wrappers (`set_winsize` and `write_master`) so no
/// `unsafe` is merely declared-but-untested. Content is not asserted (echoed
/// input may interleave); the point is the wrappers run on a real pty.
#[test]
fn resize_and_write_exercise_the_remaining_wrappers() {
    let child = env!("CARGO_BIN_EXE_pty_child");
    let mut fx = Seeded::new(7);
    let mut log = Log::new();
    let mut pty = Pty::spawn(child, &[], 24, 4).expect("spawn pty");
    pty.resize(80, 24).expect("resize the pty"); // set_winsize
    pty.write_input(b"x").expect("write to the master"); // write_master
    let chunks = pty.record_to_eof(&mut log, &mut fx).expect("record to eof");
    assert!(!chunks.is_empty(), "the child produced output");
}

/// Reaping settles the pid: once waited for, it is no longer this process's to
/// wait for again (the kernel may already have handed it to another child), so a
/// second `reap` answers from the first instead of calling `waitpid` again.
#[test]
fn a_second_reap_returns_the_first_outcome_without_waiting_again() {
    let mut fx = Seeded::new(5);
    let mut log = Log::new();
    let mut pty = Pty::spawn("/bin/sh", &["-c", "exit 3"], 24, 4).expect("spawn sh");
    pty.record_to_eof(&mut log, &mut fx).expect("record to eof"); // reaps: Exit 3
    assert_eq!(pty.reap().expect("a second reap"), 3);
    assert_eq!(pty.reap().expect("a third reap"), 3);
}

/// A program that cannot be exec'd is an `Err` from `Pty::spawn` (the child's exec
/// errno comes back over a close-on-exec status pipe) — never an `Ok` session that
/// merely ends in `Exit { 127 }`, which would be indistinguishable from a program
/// that ran and exited 127.
#[test]
fn spawning_a_program_that_cannot_exec_is_an_error_not_an_exit_127() {
    let err = match Pty::spawn("/no/such/dir/astream-no-such-binary", &[], 24, 4) {
        Err(e) => e,
        Ok(_) => panic!("spawn of a nonexistent program must fail"),
    };
    assert_eq!(
        err.kind(),
        std::io::ErrorKind::NotFound,
        "the child's exec errno (ENOENT) is reported: {err}"
    );
    // A directory is on disk but not an image: exec fails with EACCES.
    let err = match Pty::spawn("/tmp/", &[], 24, 4) {
        Err(e) => e,
        Ok(_) => panic!("spawn of a directory must fail"),
    };
    assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied, "{err}");
}

/// The child gets a real terminal's SIGPIPE disposition. The Rust runtime sets
/// SIGPIPE to SIG_IGN in this process and an ignored disposition survives exec;
/// a shell that signals ITSELF with SIGPIPE therefore survives (and prints) under
/// the inherited SIG_IGN, but dies with 128+13 under a terminal's SIG_DFL.
#[test]
fn the_child_runs_with_sigpipe_reset_to_default() {
    let worker = std::thread::spawn(|| {
        let mut fx = Seeded::new(3);
        let mut log = Log::new();
        let mut pty = Pty::spawn("/bin/sh", &["-c", "kill -PIPE $$; echo survived"], 40, 4)
            .expect("spawn sh");
        let chunks = pty.record_to_eof(&mut log, &mut fx).expect("record to eof");
        let out: Vec<u8> = chunks
            .into_iter()
            .flat_map(|r| match r {
                Record::Out(b) => b,
                _ => Vec::new(),
            })
            .collect();
        let stored = fx.disk().read_all().to_vec();
        (out, stored)
    });
    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(15),
            "the sh child timed out"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let (out, stored) = worker.join().expect("worker panicked");
    let text = String::from_utf8_lossy(&out);
    assert!(
        !text.contains("survived"),
        "SIGPIPE must be SIG_DFL in the child (it inherited SIG_IGN): output {text:?}"
    );
    let last = Log::read_from(&MemDisk::from_bytes(stored), Offset::ZERO)
        .map(|r| r.unwrap().record)
        .last();
    assert!(
        matches!(last, Some(Record::Exit { code: 141 })),
        "the shell died of SIGPIPE (128 + 13); got {last:?}"
    );
}
