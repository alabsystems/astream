//! Public-API viewport benchmark; run unchanged against HEAD and rotated Grid.
use astream_term::{
    ops::ScreenOp,
    render::frame_hash,
    screen::{self, Cell, Folder, Screen},
    Record,
};
use std::hint::black_box;
use std::time::Instant;

fn median(mut values: [u128; 3]) -> u128 {
    values.sort_unstable();
    values[1]
}
fn main() {
    println!("CELL bytes={}", std::mem::size_of::<Cell>());
    for (cols, rows) in [(80, 24), (120, 50), (240, 100)] {
        let mut times = [0; 3];
        for elapsed in &mut times {
            let mut s = Screen::new(cols, rows);
            let ops = [ScreenOp::ScrollUp(1)];
            let start = Instant::now();
            for i in 0..4000 {
                s.set_cell(
                    rows - 1,
                    0,
                    Cell {
                        ch: char::from(b'a' + (i % 26) as u8),
                        ..Cell::BLANK
                    },
                );
                screen::apply_ops_to(black_box(&mut s), black_box(&ops));
            }
            *elapsed = start.elapsed().as_nanos() / 4000;
            black_box(frame_hash(&s));
        }
        println!(
            "SCROLL cols={cols} rows={rows} ns_per_scroll={}",
            median(times)
        );
        for elapsed in &mut times {
            let mut s = Screen::new(cols, rows);
            screen::apply_ops_to(
                &mut s,
                &[
                    ScreenOp::ScrollUp(1),
                    ScreenOp::SetScrollRegion {
                        top: 1,
                        bottom: rows - 2,
                    },
                ],
            );
            let ops = [ScreenOp::ScrollUp(1)];
            let start = Instant::now();
            for i in 0..4000 {
                s.set_cell(
                    rows - 2,
                    0,
                    Cell {
                        ch: char::from(b'a' + (i % 26) as u8),
                        ..Cell::BLANK
                    },
                );
                screen::apply_ops_to(black_box(&mut s), black_box(&ops));
            }
            *elapsed = start.elapsed().as_nanos() / 4000;
            black_box(frame_hash(&s));
        }
        println!(
            "PARTIAL_SCROLL cols={cols} rows={rows} ns_per_scroll={}",
            median(times)
        );
        let mut bytes = Vec::new();
        for _ in 0..10000 {
            bytes.extend_from_slice(b"hello the quick brown fox jumps over a log\r\n");
        }
        let records = [Record::Out(bytes)];
        let mut hash = 0;
        for elapsed in &mut times {
            let start = Instant::now();
            let s = screen::fold(cols, rows, black_box(&records));
            *elapsed = start.elapsed().as_nanos();
            hash = black_box(frame_hash(&s));
        }
        println!(
            "FOLD cols={cols} rows={rows} lines=10000 ns={} final_hash={hash}",
            median(times)
        );
        let record = Record::Out(b"hello the quick brown fox jumps over a log\r\n".to_vec());
        for elapsed in &mut times {
            let mut folder = Folder::new(cols, rows);
            let start = Instant::now();
            for _ in 0..1000 {
                folder.apply(black_box(&record));
                black_box(frame_hash(folder.screen()));
            }
            *elapsed = start.elapsed().as_nanos() / 1000;
            hash = black_box(frame_hash(folder.screen()));
        }
        println!(
            "FOLD_HASH cols={cols} rows={rows} records=1000 ns_per_record={} final_hash={hash}",
            median(times)
        );
    }
    let mut chunk = Vec::new();
    for row in 0..24u16 {
        chunk.extend_from_slice(format!("\x1b[{};1H", row + 1).as_bytes());
        chunk.extend_from_slice(b"\x1b[32mhello \x1b[1mworld\x1b[0m the quick brown fox jumps");
    }
    let records = [Record::Out(chunk)];
    let mut times = [0; 3];
    let mut hash = 0;
    for elapsed in &mut times {
        let start = Instant::now();
        for _ in 0..2000 {
            let s = screen::fold(80, 24, black_box(&records));
            black_box(s.line_text(0));
            hash = black_box(frame_hash(&s));
        }
        *elapsed = start.elapsed().as_nanos() / 2000;
    }
    println!(
        "NO_SCROLL cols=80 rows=24 ns_per_fold_plus_hash={} final_hash={hash}",
        median(times)
    );
}
