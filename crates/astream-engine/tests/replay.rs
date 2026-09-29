//! The rung-1 replay proof as `#[test]`s (the same three legs the example
//! asserts), plus a genuine mid-log read-by-offset subcase and a proptest that
//! decoding arbitrary bytes never panics.

use astream_engine::effects::{Disk, Effects};
use astream_engine::{Envelope, Log, MemDisk, Offset, Seeded};
use astream_term::{screen, Record};
use proptest::prelude::*;

const SEED: u64 = 0xA571_2026;
const COLS: u16 = 80;
const ROWS: u16 = 24;

fn captured() -> Vec<Record> {
    vec![
        Record::Out(b"\x1b[2J\x1b[H".to_vec()),
        Record::Out(b"\x1b[31;1mERR\x1b[0m ".to_vec()),
        Record::In {
            bytes: b"ls -la\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Out(b"line2 \x1b[1mbo".to_vec()),
        Record::Out(b"ld\x1b[22m end\r\n".to_vec()),
        Record::Resize { cols: 40, rows: 10 },
        Record::Out(b"\x1b[?1049h\x1b[2JALT".to_vec()),
        Record::Out(b"caf\xc3\xa9\x1b[K".to_vec()),
        Record::Out(b"\x1b[?1049l".to_vec()),
        Record::Out(b"\x1b[5;3Hmoved".to_vec()),
        Record::Exit { code: 0 },
    ]
}

fn record(captured: &[Record]) -> Vec<u8> {
    let mut fx = Seeded::new(SEED);
    let mut log = Log::new();
    for rec in captured {
        log.append(&mut fx, rec.clone()).unwrap();
    }
    fx.disk().read_all().to_vec()
}

#[test]
fn record_and_replay_is_byte_identical_and_reconstructs_the_screen() {
    let captured = captured();

    let stored = record(&captured);
    let live = screen::fold(COLS, ROWS, &captured);

    // Separate read pass over a reader holding ONLY the stored bytes.
    let reader_disk = MemDisk::from_bytes(stored.clone());
    let mut replayed = Vec::new();
    let mut headers: Vec<(Offset, u64)> = Vec::new();
    for item in Log::read_from(&reader_disk, Offset::ZERO) {
        let env = item.unwrap();
        headers.push((env.seq, env.ts_logical));
        replayed.push(env.record);
    }
    let folded = screen::fold(COLS, ROWS, &replayed);

    // LEG 1 — determinism: a second seeded pass is byte-identical.
    let stored2 = record(&replayed);
    assert_eq!(stored, stored2);

    // LEG 2 — reconstructed screen equals live.
    assert_eq!(folded.serialize(), live.serialize());

    // LEG 3 — header self-check from disk.
    for (i, (seq, ts)) in headers.iter().enumerate() {
        assert_eq!(*seq, Offset(i as u64));
        assert_eq!(*ts, i as u64);
    }
    assert_eq!(headers.len(), captured.len());
}

#[test]
fn read_from_mid_log_is_genuine_read_by_offset() {
    let captured = captured();
    let disk = MemDisk::from_bytes(record(&captured));

    let from4: Vec<Envelope> = Log::read_from(&disk, Offset(4))
        .map(|r| r.unwrap())
        .collect();

    assert!(
        from4.iter().all(|e| e.seq.0 >= 4),
        "every record at or past offset 4"
    );
    assert_eq!(
        from4.first().unwrap().seq,
        Offset(4),
        "first yielded is exactly offset 4"
    );
    assert_eq!(
        from4.len(),
        captured.len() - 4,
        "skipped exactly offsets 0..4"
    );
}

proptest! {
    /// Decoding arbitrary payload bytes never panics — only Ok or Err.
    #[test]
    fn envelope_from_payload_never_panics(bytes in prop::collection::vec(any::<u8>(), 0..256)) {
        let _ = Envelope::from_payload(&bytes);
    }

    /// Reading arbitrary disk bytes never panics and always terminates.
    #[test]
    fn log_reader_never_panics_on_arbitrary_bytes(bytes in prop::collection::vec(any::<u8>(), 0..512)) {
        let disk = MemDisk::from_bytes(bytes);
        for item in Log::read_from(&disk, Offset::ZERO) {
            let _ = item;
        }
    }
}
