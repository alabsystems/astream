//! THE rung-1 evidence command, behind manifest claim `term.replay.byte-identical`.
//!
//! Records a fixed, adversarial captured session into the [`Log`] under a seeded
//! seam, then — after dropping the live records — replays *only the stored bytes*
//! back through a separate read-by-offset pass and proves three things:
//!
//!   LEG 1  two seeded record passes produce byte-identical logs (determinism,
//!          including every recorded `ts_logical`);
//!   LEG 2  the screen folded from the stored bytes equals the live screen;
//!   LEG 3  the `seq`/`ts_logical` decoded from disk equal their recorded values.
//!
//! A failed assert panics → non-zero exit, and the evidence runner requires
//! exit-zero, so the asserts gate the run. On success it prints exactly one
//! deterministic line, whose SHA-256 the manifest pins.

use astream_engine::effects::{Disk, Effects};
use astream_engine::{Log, MemDisk, Offset, Seeded};
use astream_term::{screen, Record};
use astream_wire::fnv1a_64;

const SEED: u64 = 0xA571_2026;
const COLS: u16 = 80;
const ROWS: u16 = 24;

/// A fixed captured session standing in for a recorded terminal — captured seam
/// inputs, no live PTY. It exercises every tag and makes the fold do real work:
/// an escape and a word split across two `Out` records, a UTF-8 multibyte glyph,
/// an alternate-screen round-trip, an inline resize, and `In`/`Exit` that must
/// not paint.
fn captured() -> Vec<Record> {
    vec![
        Record::Out(b"\x1b[2J\x1b[H".to_vec()),         // clear + home
        Record::Out(b"\x1b[31;1mERR\x1b[0m ".to_vec()), // red+bold "ERR", reset
        Record::In {
            bytes: b"ls -la\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        }, // MUST NOT paint
        Record::Out(b"line2 \x1b[1mbo".to_vec()),       // bold on; split across...
        Record::Out(b"ld\x1b[22m end\r\n".to_vec()),    // ...the next Out (parser persists)
        Record::Resize { cols: 40, rows: 10 },          // inline resize
        Record::Out(b"\x1b[?1049h\x1b[2JALT".to_vec()), // enter altscreen, paint
        Record::Out(b"caf\xc3\xa9\x1b[K".to_vec()),     // UTF-8 (e-acute) + erase-line
        Record::Out(b"\x1b[?1049l".to_vec()),           // leave altscreen (restores main)
        Record::Out(b"\x1b[5;3Hmoved".to_vec()),        // cursor address + text
        Record::Exit { code: 0 },                       // MUST NOT paint; seals the log
    ]
}

fn main() {
    let captured = captured();

    // 1. RECORD pass under the seeded seam.
    let mut fx = Seeded::new(SEED);
    let mut log = Log::new();
    for rec in &captured {
        log.append(&mut fx, rec.clone()).expect("append");
    }

    // 2. LIVE screen — fold the ORIGINAL records directly (no framing path).
    let live = screen::fold(COLS, ROWS, &captured);

    // 3. PERSIST — snapshot the bytes off the seam's Disk.
    let stored: Vec<u8> = fx.disk().read_all().to_vec();

    // 4. DROP the live seam so the read pass cannot reach the in-memory records.
    drop(fx);

    // 5. SEPARATE read-by-offset pass over a reader holding ONLY the stored bytes.
    let reader_disk = MemDisk::from_bytes(stored.clone());
    let mut replayed: Vec<Record> = Vec::new();
    let mut headers: Vec<(Offset, u64)> = Vec::new();
    for item in Log::read_from(&reader_disk, Offset::ZERO) {
        let env = item.expect("decode envelope from stored bytes");
        headers.push((env.seq, env.ts_logical));
        replayed.push(env.record);
    }

    // 6. FOLD the replayed records (a different Vec; equal only under a lossless
    //    byte round-trip through Frame::decode + Envelope::from_payload).
    let folded = screen::fold(COLS, ROWS, &replayed);

    // 7. RE-RECORD pass: a fresh seam, same seed, the decoded records back in.
    let mut fx2 = Seeded::new(SEED);
    let mut log2 = Log::new();
    for rec in &replayed {
        log2.append(&mut fx2, rec.clone()).expect("re-append");
    }
    let stored2: Vec<u8> = fx2.disk().read_all().to_vec();

    // LEG 1 — determinism: two independent seeded passes are byte-identical.
    assert_eq!(
        stored, stored2,
        "two seeded record passes must be byte-identical"
    );
    // LEG 2 — screen reconstructed from stored bytes equals the live screen.
    assert_eq!(
        folded.serialize(),
        live.serialize(),
        "screen folded from stored bytes must equal the live screen"
    );
    // LEG 3 — header fields are falsifiable from disk: seq == position, ts == counter.
    for (i, (seq, ts)) in headers.iter().enumerate() {
        assert_eq!(*seq, Offset(i as u64), "decoded seq must equal position");
        assert_eq!(
            *ts, i as u64,
            "decoded ts_logical must equal the recorded counter"
        );
    }

    // Exactly one deterministic line; its SHA-256 is pinned in the manifest.
    println!(
        "replay ok offsets={} log_bytes={} log_fnv={:016x} screen_fnv={:016x}",
        headers.len(),
        stored.len(),
        fnv1a_64(&stored),
        fnv1a_64(&live.serialize()),
    );
}
