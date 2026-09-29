//! Evidence for `term.drive.interactive-exactly-once`: the orchestrator drives a
//! REAL child process over a PTY, and a keystroke re-sent after a drop reaches the
//! child exactly once — deduped by `(client_id, client_seq)` at the single ingest
//! point, with the session log recording the distinct keystrokes.

#![cfg(unix)]

use astream_engine::{EngineError, Log, MemDisk, Offset, Seeded};
use astream_host::{Driver, HostError, Pty};
use astream_term::Record;
use std::time::{Duration, Instant};

#[test]
fn a_resent_keystroke_reaches_the_child_exactly_once() {
    let child = env!("CARGO_BIN_EXE_echo_child");

    // Drive on a worker thread joined with a deadline, so a hang fails loudly.
    let worker = std::thread::spawn(move || {
        let pty = Pty::spawn(child, &[], 40, 6).expect("spawn echo_child");
        let mut d = Driver::new(pty, Seeded::new(1));

        assert!(
            d.drive_input(7, 1, b"ping\n".to_vec()).unwrap(),
            "first ping is written"
        );
        assert!(
            !d.drive_input(7, 1, b"ping\n".to_vec()).unwrap(),
            "the re-sent ping (same client_seq) is deduped, not written"
        );
        assert!(
            d.drive_input(7, 2, b"quit\n".to_vec()).unwrap(),
            "quit is written"
        );

        // Drain the child's output to EOF.
        let mut output = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            let n = d.read_chunk(&mut buf).expect("read");
            if n == 0 {
                break;
            }
            output.extend_from_slice(&buf[..n]);
        }
        let _ = d.reap();
        (output, d.log_bytes())
    });

    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(15),
            "the drive timed out"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let (output, log) = worker.join().expect("worker panicked");

    // The child processed the keystroke exactly once (the duplicate never reached it).
    let text = String::from_utf8_lossy(&output);
    assert_eq!(
        text.matches("GOT:ping").count(),
        1,
        "the child responded to the keystroke exactly once; output = {text:?}"
    );

    // The session log recorded exactly two distinct keystrokes (ping, quit) — the
    // re-send was deduped, not a third record.
    let disk = MemDisk::from_bytes(log);
    let ins = Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .filter(|r| matches!(r, Record::In { .. }))
        .count();
    assert_eq!(
        ins, 2,
        "two distinct keystrokes recorded; the duplicate was dropped"
    );
}

/// A burst larger than the pty's kernel queues (1 KiB output / ~1-4 KiB input),
/// dispatched with NO drain in between, is delivered in full: the driver drains
/// the master concurrently while the input queue is full, so the echo + the
/// child's responses cannot wedge the child and, through it, the orchestrator.
/// A plain blocking write would hit the deadline here with the child alive.
#[test]
fn a_burst_larger_than_the_pty_queues_is_delivered_without_deadlock() {
    let child = env!("CARGO_BIN_EXE_echo_child");
    const LINES: usize = 128; // 128 x 64 B = 8 KiB of input before any read

    let worker = std::thread::spawn(move || {
        let pty = Pty::spawn(child, &[], 80, 6).expect("spawn echo_child");
        let mut d = Driver::new(pty, Seeded::new(2));
        for i in 0..LINES {
            let line = format!("{i:04}-{}\n", "x".repeat(58));
            assert_eq!(line.len(), 64);
            assert!(d.drive_input(7, i as u64 + 1, line.into_bytes()).unwrap());
        }
        assert!(d
            .drive_input(7, LINES as u64 + 1, b"quit\n".to_vec())
            .unwrap());
        let output = d.drain_to_eof().expect("drain");
        let _ = d.reap();
        (output, d.log_bytes())
    });

    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(20),
            "drive_input deadlocked on a burst larger than the pty queues"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    let (output, log) = worker.join().expect("worker panicked");

    let text = String::from_utf8_lossy(&output);
    for i in 0..LINES {
        let needle = format!("GOT:{i:04}-");
        assert_eq!(
            text.matches(&needle).count(),
            1,
            "line {i} reached the child exactly once"
        );
    }
    let disk = MemDisk::from_bytes(log);
    let ins = Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .filter(|r| matches!(r, Record::In { .. }))
        .count();
    assert_eq!(
        ins,
        LINES + 1,
        "every dispatched line (and quit) is an In record"
    );
}

/// Run `f` on a worker thread, failing loudly if it has not finished within
/// `secs` — a wedged or unbounded drive must not hang the whole test binary.
fn with_deadline<T: Send + 'static>(secs: u64, f: impl FnOnce() -> T + Send + 'static) -> T {
    let worker = std::thread::spawn(f);
    let start = Instant::now();
    while !worker.is_finished() {
        assert!(
            start.elapsed() < Duration::from_secs(secs),
            "the drive did not finish within {secs}s"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    worker.join().expect("worker panicked")
}

/// `total` bytes of 8-byte lines — line-terminated so the pty's canonical mode
/// releases them to the child a line at a time, which is what lets `flood_child`
/// consume its input slowly rather than not at all.
fn slow_lines(total: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(total);
    while v.len() < total {
        v.extend_from_slice(b"aaaaaaa\n");
    }
    v.truncate(total);
    v
}

/// The concurrent drain that keeps a burst from deadlocking is bounded in
/// MEMORY, not only in blocking. `flood_child` answers each input byte it
/// consumes with 8 KiB of output, so while `write_input` waits for input-queue
/// space it drains far more than it delivers: the held buffer must stop at
/// `PENDING_MAX` (8 MiB) and fail the write, instead of growing until the
/// orchestrator is OOM-killed.
///
/// Without the cap the drain has no stopping condition: the write either returns
/// success holding a buffer many times the cap, or — where the kernel makes a
/// full input queue block rather than discard — never returns at all. So this
/// asserts the error, and the deadline catches the non-returning form.
#[test]
fn a_flooding_child_that_outruns_its_input_fails_the_write_instead_of_growing_memory() {
    let child = env!("CARGO_BIN_EXE_flood_child");

    let (msg, log) = with_deadline(60, move || {
        let pty = Pty::spawn(child, &[], 80, 24).expect("spawn flood_child");
        let mut d = Driver::new(pty, Seeded::new(3));
        // 256 KiB of input: several times what any kernel buffers on the pty's
        // input side (~1 KiB on macOS, ~64 KiB of flip buffer on Linux), so the
        // write must wait, and the child answers the first 1 KiB it consumes with
        // 8 MiB of output — the cap is reached long before the input is delivered.
        let err = d
            .drive_input(7, 1, slow_lines(256 << 10))
            .expect_err("the drain buffer is bounded, so this write cannot succeed");
        (err.to_string(), d.log_bytes())
    });

    assert!(
        msg.contains("drain buffer filled"),
        "the write fails on the drain bound, not on something else; got {msg:?}"
    );
    // Nothing was committed: the keystroke stays re-sendable and the log has no In.
    let disk = MemDisk::from_bytes(log);
    let ins = Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .filter(|r| matches!(r, Record::In { .. }))
        .count();
    assert_eq!(ins, 0, "a failed write records no In");
}

/// A proposal whose `In` could never be committed is refused BEFORE any byte
/// reaches the child. `drive_input` delivers first and commits second, so a
/// commit that failed after delivery would leave the keystroke delivered with
/// the dedup high-water unbumped — a re-send would then reach the child a SECOND
/// time, contradicting the claim's at-most-once. `Session::precheck_input`
/// decides encodability (and offset availability) up front, closing that window.
///
/// Without the precheck the bytes go to the pty first, and against this child
/// they trip the drain bound: the caller gets the host's I/O error instead of
/// the engine's refusal, with the oversized keystroke already partly delivered.
#[test]
fn an_uncommittable_proposal_never_reaches_the_child() {
    let child = env!("CARGO_BIN_EXE_flood_child");
    // One byte past the frame payload cap (astream_wire::MAX_PAYLOAD_LEN, 16 MiB),
    // so `apply_input` of this body is guaranteed to fail.
    const OVER_CAP: usize = (16 << 20) + 1;

    let (err, log) = with_deadline(60, move || {
        let pty = Pty::spawn(child, &[], 80, 24).expect("spawn flood_child");
        let mut d = Driver::new(pty, Seeded::new(4));
        let err = d
            .drive_input(7, 1, slow_lines(OVER_CAP))
            .expect_err("an In this large is unencodable, so the proposal must be refused");
        (err, d.log_bytes())
    });

    assert!(
        matches!(err, HostError::Engine(EngineError::Envelope(_))),
        "refused by the engine before the pty write, not by the pty afterwards; got {err:?}"
    );
    let disk = MemDisk::from_bytes(log);
    let ins = Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .filter(|r| matches!(r, Record::In { .. }))
        .count();
    assert_eq!(ins, 0, "the refused proposal left no trace on the log");
}
