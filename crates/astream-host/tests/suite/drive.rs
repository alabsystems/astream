//! Evidence for `term.drive.interactive-exactly-once`: the orchestrator drives a
//! REAL child process over a PTY, and a keystroke re-sent after a drop reaches the
//! child exactly once — deduped by `(client_id, client_seq)` at the single ingest
//! point, with the session log recording the distinct keystrokes.

#![cfg(unix)]

use astream_engine::{CausedBy, ControlToken, EngineError, Log, MemDisk, Offset, Seeded};
use astream_host::{Driver, HostError, Pty};
use astream_term::{Predictor, Record, Verdict};
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
///
/// What reached the child is read from the child's own tally (`--tally`), not by
/// counting its `GOT:` lines in the master's output: the tty echoes input that
/// arrives while a response is blocked on the full output queue INTO that response,
/// so a line the child got can show as `GOT` … echo … `:0120-…`.
#[test]
fn a_burst_larger_than_the_pty_queues_is_delivered_without_deadlock() {
    let child = env!("CARGO_BIN_EXE_echo_child");
    const LINES: usize = 128; // 128 x 64 B = 8 KiB of input before any read

    let worker = std::thread::spawn(move || {
        let pty = Pty::spawn(child, &["--tally"], 80, 6).expect("spawn echo_child");
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
    let saw = text
        .lines()
        .find_map(|l| l.strip_prefix("SAW:"))
        .expect("the child's tally");
    let expected: Vec<String> = (0..LINES).map(|i| format!("{i:04}")).collect();
    assert_eq!(
        saw.trim_end().split(',').collect::<Vec<_>>(),
        expected,
        "every line reached the child exactly once, in order"
    );
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

fn read_until_needle(d: &mut Driver<Seeded>, needle: &str, collected: &mut Vec<u8>) {
    let mut buf = [0u8; 4096];
    let start = Instant::now();
    while !String::from_utf8_lossy(collected).contains(needle) {
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "timed out waiting for {needle:?}; collected so far: {:?}",
            String::from_utf8_lossy(collected)
        );
        let n = d.read_and_record_chunk(&mut buf).expect("read_and_record");
        assert!(n > 0, "unexpected EOF waiting for {needle:?}");
        collected.extend_from_slice(&buf[..n]);
    }
}

/// Token-gated live PTY driving (`Driver::drive_input_as` / `drive_input_caused_as`)
/// and live write→read `caused_by` correlation (`Driver::read_and_record_chunk`,
/// `Driver::drain_to_eof`):
///
/// 1. Only the `ControlToken` holder's keystrokes reach the live PTY child process;
///    a non-holder is refused with `EngineError::NotHolder` **before** any byte is
///    written to the PTY master, leaving the child untouched and the dedup
///    high-water unbumped.
/// 2. `token.claim(HUMAN)` immediately preempts the orchestrator on the live PTY,
///    and `token.grant(HUMAN, ORCH)` hands the keyboard back so the orchestrator's
///    earlier refused `(ORCH, 2)` proposal now succeeds.
/// 3. Each `Record::Out` chunk read after an `In` carries a durable same-log
///    `caused_by` naming the `In` offset that was most recently driven before it,
///    retiring `Predictor::apply_output_caused` predictions against the live PTY.
#[test]
fn control_token_gates_live_pty_input_and_stamps_same_log_caused_by_on_outputs() {
    let child = env!("CARGO_BIN_EXE_echo_child");
    const ORCH: u64 = 10;
    const VIEWER: u64 = 20;
    const HUMAN: u64 = 30;

    let (output, log) = with_deadline(20, move || {
        let pty = Pty::spawn(child, &[], 40, 8).expect("spawn echo_child");
        let mut d = Driver::new(pty, Seeded::new(5));
        let mut token = ControlToken::new(ORCH);
        let mut collected = Vec::new();

        // 1. Orchestrator holds the token: its keystroke reaches the PTY and logs In@0.
        assert!(d
            .drive_input_as(&token, ORCH, 1, b"alpha\n".to_vec())
            .unwrap());
        let in_alpha = d.last_in_offset().expect("last_in_offset after alpha");
        read_until_needle(&mut d, "GOT:alpha", &mut collected);

        // 2. Read-only viewer is refused BEFORE any byte reaches the live PTY.
        assert!(matches!(
            d.drive_input_as(&token, VIEWER, 1, b"intrude\n".to_vec()),
            Err(HostError::Engine(EngineError::NotHolder {
                holder: ORCH,
                client: VIEWER,
            }))
        ));

        // 3. Human seizes control (`claim`): orchestrator is immediately refused,
        //    leaving `(ORCH, 2)` unapplied and re-sendable.
        token.claim(HUMAN);
        assert!(matches!(
            d.drive_input_as(&token, ORCH, 2, b"after-claim\n".to_vec()),
            Err(HostError::Engine(EngineError::NotHolder {
                holder: HUMAN,
                client: ORCH,
            }))
        ));
        assert_eq!(
            d.last_in_offset(),
            Some(in_alpha),
            "refused non-holder input must not advance last_in_offset"
        );

        // 4. Human drives the live PTY while holding the token.
        assert!(d
            .drive_input_as(&token, HUMAN, 1, b"human-cmd\n".to_vec())
            .unwrap());
        let in_human = d.last_in_offset().expect("last_in_offset after human-cmd");
        assert!(in_human.0 > in_alpha.0);
        read_until_needle(&mut d, "GOT:human-cmd", &mut collected);

        // 5. Human grants control back to orchestrator; `(ORCH, 2)` is still fresh
        //    and now reaches the live PTY (also exercising `drive_input_caused_as`).
        token.grant(HUMAN, ORCH).unwrap();
        assert!(d
            .drive_input_caused_as(
                &token,
                ORCH,
                2,
                b"after-claim\n".to_vec(),
                CausedBy {
                    partition: None,
                    offset: in_human.0,
                },
            )
            .unwrap());
        let in_resumed = d.last_in_offset().expect("last_in_offset after resume");
        assert!(in_resumed.0 > in_human.0);
        read_until_needle(&mut d, "GOT:after-claim", &mut collected);

        assert!(d
            .drive_input_as(&token, ORCH, 3, b"quit\n".to_vec())
            .unwrap());
        let rest = d.drain_to_eof().expect("drain_to_eof");
        collected.extend_from_slice(&rest);
        let _ = d.reap();
        (collected, d.log_bytes())
    });

    let text = String::from_utf8_lossy(&output);
    assert_eq!(text.matches("GOT:alpha").count(), 1, "output={text:?}");
    assert_eq!(text.matches("GOT:human-cmd").count(), 1, "output={text:?}");
    assert_eq!(
        text.matches("GOT:after-claim").count(),
        1,
        "output={text:?}"
    );
    assert_eq!(
        text.matches("GOT:intrude").count(),
        0,
        "non-holder bytes must never reach the live PTY: output={text:?}"
    );

    let envs: Vec<_> = Log::read_bytes(&log, Offset::ZERO)
        .map(|r| r.unwrap())
        .collect();
    let in_clients: Vec<(u64, u64, Offset)> = envs
        .iter()
        .filter_map(|e| match e.record {
            Record::In {
                client_id,
                client_seq,
                ..
            } => Some((client_id, client_seq, e.seq)),
            _ => None,
        })
        .collect();
    assert_eq!(
        in_clients
            .iter()
            .map(|(cid, cseq, _)| (*cid, *cseq))
            .collect::<Vec<_>>(),
        vec![(ORCH, 1), (HUMAN, 1), (ORCH, 2), (ORCH, 3)],
        "the session log's In sequence is the exact auditable control history"
    );

    // Every Out recorded after the first In carries a valid same-log `caused_by`
    // pointing to the most recent preceding In offset, and retires predictions via
    // `Predictor::apply_output_caused`.
    let mut predictor = Predictor::new(40, 8);
    predictor.predict_at(1, in_clients[0].2 .0, b"alpha");
    predictor.predict_at(2, in_clients[1].2 .0, b"human-cmd");
    predictor.predict_at(3, in_clients[2].2 .0, b"after-claim");
    let mut verdicts = Vec::new();
    let mut current_in: Option<u64> = None;
    for e in &envs {
        match &e.record {
            Record::In { .. } => current_in = Some(e.seq.0),
            Record::Out(_) => {
                let expected_cb = current_in.map(|offset| CausedBy {
                    partition: None,
                    offset,
                });
                assert_eq!(
                    e.caused_by, expected_cb,
                    "live PTY Out at {:?} must stamp same-log caused_by naming the latest In",
                    e.seq
                );
                let in_off = e
                    .caused_by
                    .and_then(|cb| cb.partition.is_none().then_some(cb.offset));
                verdicts.extend(predictor.apply_output_caused(e.seq.0, in_off, &e.record));
            }
            _ => {}
        }
    }
    for seq in [1u64, 2, 3] {
        assert!(
            verdicts.contains(&(seq, Verdict::Confirmed)),
            "live PTY caused_by retired prediction {seq} as Confirmed; verdicts={verdicts:?}"
        );
    }
}
