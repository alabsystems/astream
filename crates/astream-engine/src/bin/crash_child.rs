//! Helper process for the `survives_real_sigkill_while_appending` test.
//!
//! Opens the log at `argv[1]` and appends fsync'd records in a loop, printing
//! `acked <seq>` on stdout (flushed) after each `FileLog::append` returns — i.e.
//! after that record's fsync. The parent test reads those acks and SIGKILLs this
//! process while it is still in the loop, then proves every record it acked
//! before the signal is recovered from the file it left behind. The kill lands
//! at an arbitrary point of the append loop, so the on-disk tail is whatever the
//! signal interrupted — not authored here.
//!
//! Bounded at `MAX_RECORDS` so a parent that fails to kill it cannot fill the
//! disk; past that it blocks forever (still killable). Not run by `cargo test`
//! directly; only spawned by the test via `CARGO_BIN_EXE_crash_child`.

use astream_engine::{Envelope, FileLog, Offset};
use astream_term::Record;
use std::io::Write;
use std::time::Duration;

const MAX_RECORDS: u64 = 20_000;
/// Each record carries a few KiB so an append is a real multi-page write.
const BODY_LEN: usize = 4096;

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: crash_child <log-path>");

    let (mut log, report) = FileLog::open(&path).expect("open log");
    let mut seq = report.records;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    while seq < MAX_RECORDS {
        let mut body = format!("line {seq} ").into_bytes();
        body.resize(BODY_LEN, b'x');
        let env = Envelope {
            seq: Offset(seq),
            ts_logical: seq,
            caused_by: None,
            record: Record::Out(body),
        };
        log.append(&env.encode().expect("encode")).expect("append");
        // Acked == durably on disk. Flushed so the parent sees it immediately.
        writeln!(out, "acked {seq}").expect("ack");
        out.flush().expect("flush");
        seq += 1;
    }
    loop {
        std::thread::sleep(Duration::from_secs(3600));
    }
}
