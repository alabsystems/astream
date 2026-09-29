//! Rung 1.5 evidence: Strict durability + crash recovery. Backs the manifest
//! claim `term.strict.survives-kill`.
//!
//! Deterministic, I/O-free recovery cases (clean / truncated tail / corrupt
//! final CRC — torn tails; and mid-log CRC damage / an unreadable envelope
//! version / an out-of-order record — faults); real-file cases that fsync
//! through `FileLog`: a torn tail is recovered and durably truncated, a fault
//! REFUSES to open (the file is left byte-for-byte untouched, the error names
//! the byte offset) until the explicit `open_truncating` repair, and a recovered
//! file is CONTINUED (resume + append + recover again) as one intact log. On
//! Unix, a real `SIGKILL` of a child process while it is appending fsync'd
//! records in a loop: every record it acked before the signal is recovered, and
//! whatever the kill left on disk recovers as a clean prefix.

use astream_engine::{
    recover, EnvelopeError, FaultKind, FileLog, Log, LogFault, MemDisk, Offset, Seeded, Session,
    Tail,
};
use astream_term::{screen, Record};
use astream_wire::{Frame, FrameError};

const COLS: u16 = 80;
const ROWS: u16 = 24;
const SEED: u64 = 0xA571_2026;

fn captured() -> Vec<Record> {
    vec![
        Record::Out(b"\x1b[2Jhello\r\n".to_vec()),
        Record::Out(b"\x1b[33mwarn\x1b[0m\r\n".to_vec()),
        Record::In {
            bytes: b"q\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Out(b"done".to_vec()),
        Record::Resize { cols: 30, rows: 8 },
        Record::Out(b"\x1b[2;1Hmid".to_vec()),
        Record::Exit { code: 0 },
    ]
}

/// Record a session under the seeded seam and return its stored log bytes.
fn record(recs: &[Record]) -> Vec<u8> {
    astream_engine::record_session(SEED, recs)
}

fn decode_all(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

/// The byte offset where each frame ends (so `ends[i]` is where frame `i+1` starts).
fn frame_ends(bytes: &[u8]) -> Vec<usize> {
    let mut ends = Vec::new();
    let mut pos = 0;
    while let Ok(Some(d)) = Frame::decode(&bytes[pos..]) {
        pos += d.consumed;
        ends.push(pos);
    }
    ends
}

/// Re-wrap every frame's payload with a different envelope version byte, CRC
/// intact — a log written by a build with another `ENV_VERSION`.
fn reversioned(bytes: &[u8], version: u8) -> Vec<u8> {
    let mut out = Vec::new();
    let mut pos = 0;
    while let Ok(Some(d)) = Frame::decode(&bytes[pos..]) {
        let mut payload = d.frame.payload.clone();
        payload[0] = version;
        out.extend_from_slice(&Frame::new(payload).encode().unwrap());
        pos += d.consumed;
    }
    out
}

fn fault_of(err: &std::io::Error) -> LogFault {
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    err.get_ref()
        .and_then(|e| e.downcast_ref::<LogFault>())
        .cloned()
        .expect("a LogFault inside the io::Error")
}

/// Removes its file when dropped, so a test leaves nothing behind whether it passes
/// or panics. Bind it before whatever uses the file, so it drops after that.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn tmp(name: &str) -> (Cleanup, std::path::PathBuf) {
    let p = std::env::temp_dir().join(format!("astream_{}_{}.log", name, std::process::id()));
    let _ = std::fs::remove_file(&p);
    (Cleanup(p.clone()), p)
}

#[test]
fn recover_clean_log_reports_all_records() {
    let recs = captured();
    let stored = record(&recs);
    let report = recover(&stored);
    assert_eq!(report.records, recs.len() as u64);
    assert!(!report.torn);
    assert_eq!(report.tail, Tail::Clean);
    assert_eq!(report.valid_len, stored.len());
}

#[test]
fn recover_truncated_tail_drops_the_partial_record() {
    let recs = captured();
    let stored = record(&recs);
    let report = recover(&stored[..stored.len() - 5]); // chop the last frame mid-body

    assert_eq!(report.records, recs.len() as u64 - 1);
    assert!(report.torn);
    assert_eq!(report.tail, Tail::Torn);

    // The recovered prefix decodes to all-but-last and folds to that screen.
    let got = decode_all(&stored[..report.valid_len]);
    assert_eq!(got, recs[..recs.len() - 1]);
    assert_eq!(
        screen::fold(COLS, ROWS, &got).serialize(),
        screen::fold(COLS, ROWS, &recs[..recs.len() - 1]).serialize()
    );
}

#[test]
fn recover_corrupt_final_crc_drops_the_record() {
    let recs = captured();
    let mut stored = record(&recs);
    let n = stored.len();
    stored[n - 1] ^= 0xFF; // corrupt the last frame's payload -> CRC mismatch
    let report = recover(&stored);
    assert_eq!(report.records, recs.len() as u64 - 1);
    assert!(report.torn);
    assert_eq!(
        report.tail,
        Tail::Torn,
        "nothing decodable follows: a torn tail"
    );
}

#[test]
fn recover_classifies_mid_log_damage_as_a_fault_not_a_torn_tail() {
    let recs = captured();
    let stored = record(&recs);
    let ends = frame_ends(&stored);

    // A flipped byte INSIDE record 1, with intact records after it: bit rot, not
    // a crash. The intact prefix is record 0 and the fault names record 1's offset.
    let mut rot = stored.clone();
    rot[ends[0] + 14] ^= 0x01;
    let report = recover(&rot);
    assert_eq!((report.records, report.valid_len), (1, ends[0]));
    assert_eq!(
        report.tail,
        Tail::Fault {
            at: ends[0],
            kind: FaultKind::CorruptFrame(FrameError::ChecksumMismatch)
        }
    );

    // A CRC-intact log under another envelope version: unreadable, not torn —
    // and the fault is at byte 0, so nothing would survive a truncation.
    let other = reversioned(&stored, 2);
    let report = recover(&other);
    assert_eq!((report.records, report.valid_len), (0, 0));
    assert_eq!(
        report.tail,
        Tail::Fault {
            at: 0,
            kind: FaultKind::BadEnvelope(EnvelopeError::BadVersion(2))
        }
    );

    // A record whose stored seq is not the next expected one.
    let mut regressed = stored[..ends[1]].to_vec();
    regressed.extend_from_slice(&stored[..ends[0]]); // seq 0 again after seq 1
    let report = recover(&regressed);
    assert_eq!((report.records, report.valid_len), (2, ends[1]));
    assert_eq!(
        report.tail,
        Tail::Fault {
            at: ends[1],
            kind: FaultKind::OutOfOrder {
                expected: 2,
                found: 0
            }
        }
    );
}

#[test]
fn filelog_fsyncs_and_recovers_a_torn_file() {
    use std::io::Write;

    let recs = captured();
    let stored = record(&recs);
    let live = screen::fold(COLS, ROWS, &recs);
    let (_tmp, path) = tmp("filelog");

    // Durable append (fsync), then close.
    {
        let (mut fl, rep0) = FileLog::open(&path).unwrap();
        assert_eq!(rep0.records, 0);
        assert_eq!(rep0.tail, Tail::Clean);
        fl.append(&stored).unwrap();
    }
    // Simulate a crash: append a half-written frame to the raw file.
    {
        let extra = record(&[Record::Out(b"interrupted".to_vec())]);
        let mut raw = std::fs::OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap();
        raw.write_all(&extra[..extra.len() / 2]).unwrap();
        raw.sync_all().unwrap();
    }
    // Reopen -> recover the torn tail.
    let (fl, report) = FileLog::open(&path).unwrap();
    assert_eq!(report.records, recs.len() as u64);
    assert!(report.torn);
    assert_eq!(report.tail, Tail::Torn);
    assert_eq!(
        fl.bytes(),
        &stored[..],
        "recovered bytes equal the acked prefix"
    );
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        stored.len() as u64,
        "the torn tail is truncated on disk"
    );

    // Re-fold from the recovered bytes == the live screen.
    let got = decode_all(fl.bytes());
    assert_eq!(screen::fold(COLS, ROWS, &got).serialize(), live.serialize());
}

#[test]
fn filelog_refuses_a_fault_untouched_until_the_explicit_repair() {
    let recs = captured();
    let stored = record(&recs);
    let ends = frame_ends(&stored);

    // (1) A log written under another envelope version: `open` must NOT wipe it.
    let (_tmp, path) = tmp("version");
    let other = reversioned(&stored, 2);
    std::fs::write(&path, &other).unwrap();
    let err = FileLog::open(&path).unwrap_err();
    assert_eq!(
        fault_of(&err),
        LogFault {
            at: 0,
            kind: FaultKind::BadEnvelope(EnvelopeError::BadVersion(2))
        }
    );
    assert!(err.to_string().contains("byte 0"), "{err}");
    assert_eq!(
        std::fs::read(&path).unwrap(),
        other,
        "a refused open leaves the file byte-for-byte untouched"
    );
    // The explicit repair truncates, durably, and says what it did.
    let (fl, report) = FileLog::open_truncating(&path).unwrap();
    assert_eq!((report.records, report.valid_len), (0, 0));
    assert!(matches!(report.tail, Tail::Fault { at: 0, .. }));
    assert!(fl.bytes().is_empty());
    assert_eq!(std::fs::metadata(&path).unwrap().len(), 0);
    let _ = std::fs::remove_file(&path);

    // (2) Bit rot in record 1 with acked records after it: refused, offset named.
    let (_tmp, path) = tmp("rot");
    let mut rot = stored.clone();
    rot[ends[0] + 14] ^= 0x01;
    std::fs::write(&path, &rot).unwrap();
    let err = FileLog::open(&path).unwrap_err();
    assert_eq!(
        fault_of(&err),
        LogFault {
            at: ends[0],
            kind: FaultKind::CorruptFrame(FrameError::ChecksumMismatch)
        }
    );
    assert_eq!(std::fs::read(&path).unwrap(), rot, "untouched");
    let (fl, report) = FileLog::open_truncating(&path).unwrap();
    assert_eq!((report.records, report.valid_len), (1, ends[0]));
    assert_eq!(fl.bytes(), &stored[..ends[0]]);
    assert_eq!(std::fs::metadata(&path).unwrap().len(), ends[0] as u64);
    let _ = std::fs::remove_file(&path);

    // (3) An out-of-sequence record (a writer that restarted at seq 0): refused.
    let (_tmp, path) = tmp("regressed");
    let mut regressed = stored[..ends[1]].to_vec();
    regressed.extend_from_slice(&stored[..ends[0]]);
    std::fs::write(&path, &regressed).unwrap();
    let err = FileLog::open(&path).unwrap_err();
    assert_eq!(
        fault_of(&err),
        LogFault {
            at: ends[1],
            kind: FaultKind::OutOfOrder {
                expected: 2,
                found: 0
            }
        }
    );
    assert_eq!(std::fs::read(&path).unwrap(), regressed, "untouched");
}

#[test]
fn a_recovered_file_log_is_continued_not_restarted() {
    let (_tmp, path) = tmp("continue");

    // Session 1 records three records into the file, then the process dies.
    let first = record(&captured()[..3]);
    {
        let (mut fl, _) = FileLog::open(&path).unwrap();
        fl.append(&first).unwrap();
    }

    // Session 2: recover, then CONTINUE the same offset axis over the recovered
    // bytes, appending two more records and persisting them to the same file.
    let all = {
        let (mut fl, report) = FileLog::open(&path).unwrap();
        assert_eq!((report.records, report.tail.clone()), (3, Tail::Clean));
        let disk = MemDisk::from_bytes(fl.bytes().to_vec());
        let mut s = Session::resume_from(Seeded::with_disk(SEED, disk)).unwrap();
        assert_eq!(s.next_offset(), Offset(3));
        assert_eq!(
            s.apply_input(1, 2, b"y\n".to_vec()).unwrap(),
            Some(Offset(3))
        );
        assert_eq!(s.append_output(b"ok\r\n".to_vec()).unwrap(), Offset(4));
        let all = s.log_bytes();
        fl.append(&all[first.len()..]).unwrap();
        all
    };

    // Session 3: recover again — one intact, dense, clock-monotone log.
    let (fl, report) = FileLog::open(&path).unwrap();
    assert_eq!(
        (report.records, report.tail.clone(), report.valid_len),
        (5, Tail::Clean, all.len())
    );
    assert_eq!(fl.bytes(), &all[..]);
    for (i, e) in Log::read_bytes(fl.bytes(), Offset::ZERO).enumerate() {
        let e = e.unwrap();
        assert_eq!((e.seq, e.ts_logical), (Offset(i as u64), i as u64));
    }
    assert_eq!(decode_all(fl.bytes()).len(), 5);
}

#[cfg(unix)]
#[test]
fn survives_real_sigkill_while_appending() {
    use std::io::{BufRead, BufReader};
    use std::time::{Duration, Instant};

    let (_tmp, path) = tmp("kill");

    // The child appends fsync'd records in a loop, printing `acked <seq>` after
    // each append returns (i.e. after its fsync).
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_crash_child"))
        .arg(&path)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("spawn crash_child");
    let mut acks = BufReader::new(child.stdout.take().expect("child stdout"));

    // Read acks until the child has acked a few records ... The count is
    // deliberately small and the deadline deliberately huge: every ack is one
    // fsync, so this wait is disk-bound, and on a machine running other test
    // suites an fsync can take orders of magnitude longer than the ~4 ms it
    // costs idle. The deadline is a HANG detector (the child died, or never
    // reached its loop), never a performance assertion — the assertions below
    // hold for any number of acked records.
    let start = Instant::now();
    let mut last_acked: Option<u64> = None;
    let mut line = String::new();
    while last_acked.is_none_or(|a| a < 2) {
        assert!(
            start.elapsed() < Duration::from_secs(300),
            "child never acked 3 records in 300 s (hung, not slow)"
        );
        line.clear();
        let n = acks.read_line(&mut line).expect("read ack");
        assert!(n > 0, "child exited before acking 8 records");
        let seq: u64 = line
            .trim()
            .strip_prefix("acked ")
            .expect("ack line")
            .parse()
            .expect("ack seq");
        last_acked = Some(seq);
    }
    // ... and SIGKILL it NOW, while it is still in its append loop: whatever the
    // signal interrupts is the on-disk tail — not authored by anyone.
    child.kill().expect("kill child");
    let _ = child.wait();
    let acked = last_acked.unwrap();

    // Recover the file the dead process left behind: every acked record is
    // there, in order, and the tail the kill left is a clean prefix or a torn
    // tail — never a mid-log fault.
    let (fl, report) = FileLog::open(&path).expect("recover");
    assert!(
        report.records > acked,
        "every record acked before the kill (0..={acked}) is recovered; got {}",
        report.records
    );
    assert!(
        !matches!(report.tail, Tail::Fault { .. }),
        "the kill leaves a torn tail or a clean end, never a fault: {:?}",
        report.tail
    );
    let recs = decode_all(fl.bytes());
    assert_eq!(recs.len() as u64, report.records);
    for (i, r) in recs.iter().enumerate() {
        match r {
            Record::Out(b) => assert!(
                b.starts_with(format!("line {i} ").as_bytes()),
                "record {i} is the one the child wrote"
            ),
            other => panic!("unexpected record {other:?}"),
        }
    }
}

#[test]
fn filelog_truncates_a_crc_corrupt_final_record_on_disk() {
    let recs = captured();
    let stored = record(&recs);
    let ends = frame_ends(&stored);
    let (_tmp, path) = tmp("corrupt_final");

    // The last frame's payload is damaged and nothing decodable follows it: the
    // same on-disk shape as a write torn inside the final record.
    let mut damaged = stored.clone();
    let n = damaged.len();
    damaged[n - 1] ^= 0xFF;
    std::fs::write(&path, &damaged).unwrap();

    let (fl, report) = FileLog::open(&path).unwrap();
    assert_eq!(
        report.tail,
        Tail::Torn,
        "a corrupt FINAL record is a torn tail, not a fault"
    );
    let intact = ends[ends.len() - 2]; // where the last (damaged) frame starts
    assert_eq!(
        (report.records, report.valid_len),
        (recs.len() as u64 - 1, intact)
    );
    assert_eq!(fl.bytes(), &stored[..intact]);
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        intact as u64,
        "the corrupt record is truncated on disk"
    );

    // Every prior record is retained and re-folds to the screen at that offset.
    let got = decode_all(fl.bytes());
    assert_eq!(got, recs[..recs.len() - 1]);
    assert_eq!(
        screen::fold(COLS, ROWS, &got).serialize(),
        screen::fold(COLS, ROWS, &recs[..recs.len() - 1]).serialize()
    );
}
