//! Public API feed benchmark, run unchanged against scalar HEAD and ASCII spans.
use astream_term::{render::frame_hash, Folder, Record};
use std::hint::black_box;
use std::time::Instant;

fn frame(text: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for row in 0..24 {
        bytes.extend_from_slice(format!("\x1b[{};1H", row + 1).as_bytes());
        bytes.extend_from_slice(text);
    }
    bytes
}

fn measure(name: &str, records: &[Record], recording: bool, iterations: usize) {
    let mut elapsed = [0; 3];
    let mut last = None;
    for sample in &mut elapsed {
        let start = Instant::now();
        for _ in 0..iterations {
            let mut folder = if recording {
                Folder::new_recording(80, 24)
            } else {
                Folder::new(80, 24)
            };
            for record in black_box(records) {
                folder.apply(black_box(record));
            }
            if recording {
                black_box(folder.take_ops());
            }
            black_box(folder.screen());
            last = Some(folder);
        }
        *sample = start.elapsed().as_nanos() / iterations as u128;
    }
    elapsed.sort_unstable();
    let folder = last.unwrap();
    println!(
        "ASCII_SPAN case={name} iterations={iterations} records={} ns_per_fold={} hash={} sync_bytes={}",
        records.len(), elapsed[1], frame_hash(folder.screen()), folder.sync_output_bytes()
    );
}

fn main() {
    let ordinary = frame(b"\x1b[32mhello \x1b[1mworld\x1b[0m the quick brown fox jumps");
    measure("ordinary", &[Record::Out(ordinary.clone())], false, 2000);
    measure("recording", &[Record::Out(ordinary)], true, 1000);
    measure(
        "long_ascii",
        &[Record::Out(frame(&[b'x'; 80]))],
        false,
        2000,
    );
    let tiny: Vec<_> = (0..32).map(|_| Record::Out(vec![b'x'])).collect();
    measure("tiny_records", &tiny, false, 5000);
    measure(
        "two_byte_runs",
        &[Record::Out(frame(
            b"ab\x1b[0mcd\x1b[0mef\x1b[0mgh\x1b[0mij",
        ))],
        false,
        2000,
    );
    measure(
        "non_ascii",
        &[Record::Out(frame("界é😀界é😀界é😀界é😀".as_bytes()))],
        false,
        2000,
    );
    let mut insert = b"\x1b[4h".to_vec();
    insert.extend_from_slice(&frame(b"hello short insert"));
    measure("insert_mode", &[Record::Out(insert)], false, 1000);
    let mut dec = b"\x1b(0".to_vec();
    dec.extend_from_slice(&frame(b"lqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqk"));
    measure("dec_graphics", &[Record::Out(dec)], false, 2000);
    let mut sync = b"\x1b[?2026h".to_vec();
    sync.extend_from_slice(&frame(b"the quick brown fox jumps over a log"));
    measure("synchronized", &[Record::Out(sync)], false, 2000);
    let mut scroll = Vec::new();
    for _ in 0..1000 {
        scroll.extend_from_slice(b"hello the quick brown fox jumps over a log\r\n");
    }
    measure("scrolling", &[Record::Out(scroll)], false, 100);
}
