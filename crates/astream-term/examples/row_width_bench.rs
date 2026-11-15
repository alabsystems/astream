//! Row-span copy controls; run unchanged against frozen Grid and the prototype.
use astream_term::{
    ops::ScreenOp,
    render::frame_hash,
    screen::{self, Cell, Color, Screen},
};
use std::hint::black_box;
use std::time::Instant;

fn median(mut values: [u128; 3]) -> u128 {
    values.sort_unstable();
    values[1]
}

fn seed(cols: u16, rows: u16, rotated: bool) -> Screen {
    let mut screen = Screen::new(cols, rows);
    if rotated {
        screen::apply_ops_to(&mut screen, &[ScreenOp::ScrollUp(rows / 2)]);
    }
    for row in 0..rows {
        for col in 0..cols {
            screen.set_cell(
                row,
                col,
                Cell {
                    ch: char::from(b'a' + ((row + col) % 26) as u8),
                    fg: Color::Indexed(col as u8),
                    bg_rgb: Some((row as u8, 17, 29)),
                    ..Cell::BLANK
                },
            );
        }
    }
    screen
}

fn main() {
    const ITERATIONS: usize = 4000;
    for (cols, rows) in [(80u16, 24u16), (120, 50), (240, 100)] {
        for rotated in [false, true] {
            for width in [2u16, 3, 4, 6, 8, 12, 16, 32] {
                let name = "width";
                let left = (cols - width) / 2;
                let right = left + width - 1;
                let from = 1;
                let to = rows - 2;
                let insert = false;
                for down in [false, true] {
                    {
                        let count = 1;
                        let mut times = [0; 3];
                        let mut hash = 0;
                        for elapsed in &mut times {
                            let mut s = seed(cols, rows, rotated);
                            screen::apply_ops_to(
                                &mut s,
                                &[
                                    ScreenOp::SetMode {
                                        params: vec![69],
                                        set: true,
                                    },
                                    ScreenOp::SetLeftRightMargins { left, right },
                                    ScreenOp::SetScrollRegion {
                                        top: from,
                                        bottom: to,
                                    },
                                    ScreenOp::MoveTo((from + to) / 2, left),
                                ],
                            );
                            let op = match (insert, down) {
                                (true, true) => ScreenOp::InsertLines(count),
                                (true, false) => ScreenOp::DeleteLines(count),
                                (false, true) => ScreenOp::ScrollDown(count),
                                (false, false) => ScreenOp::ScrollUp(count),
                            };
                            let start = Instant::now();
                            for i in 0..ITERATIONS {
                                s.set_cell(
                                    to,
                                    left,
                                    Cell {
                                        ch: char::from(b'a' + (i % 26) as u8),
                                        ..Cell::BLANK
                                    },
                                );
                                screen::apply_ops_to(
                                    black_box(&mut s),
                                    black_box(std::slice::from_ref(&op)),
                                );
                            }
                            *elapsed = start.elapsed().as_nanos() / ITERATIONS as u128;
                            hash = black_box(frame_hash(&s));
                        }
                        println!("ROW_WIDTH case={name} width={width} cols={cols} rows={rows} rotated={rotated} down={down} count={count} ns_per_scroll={} final_hash={hash}", median(times));
                    }
                }
            }
        }
    }
}
