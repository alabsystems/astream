// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Corpus benchmark for `term.predict.watermark-squash` (`docs/ROADMAP.md`,
//! `docs/DESIGN-astream-term.md` §8, `docs/THEORY-deterministic-sessions.md` §3).
//!
//! Replays a deterministic multi-workload recorded terminal corpus through
//! [`SpeculativeTerminal`] across both retirement lanes:
//! 1. Cooked shell command typing + pipelined bursts (`apply_output_at` watermark retire),
//! 2. Readline / ZLE cursor-motion & Backspace line editing (`ESC [ D`, `ESC [ C`, `0x7f`),
//! 3. Alternate-screen TUI navigation (`?1049h` menu/pager `ESC [ B`, `ESC [ A`, `j`, `k`),
//! 4. Adversarial `Password: ` no-echo prompt + async contradiction squash-and-rebuild.
//!
//! Verifies byte-identical ground-truth convergence (`0` residual divergences) against an
//! independent `screen::fold` oracle and prints:
//! - `METRIC predict_hit_rate <confirmed / (confirmed + contradicted + abstained)>`
//!   (honestly counting abstentions in the denominator so abstaining cannot game the rate),
//! - `METRIC predict_precision <confirmed / (confirmed + contradicted)>`,
//! - `METRIC predict_turn_ops_per_sec <turns_per_sec>`.

use astream_term::{screen, Record, SpeculativeTerminal};
use std::hint::black_box;
use std::time::Instant;

#[derive(Clone)]
enum Turn {
    Setup(&'static [u8]),
    Watermark {
        input: &'static [u8],
        output: &'static [u8],
    },
    WatermarkBatch {
        inputs: &'static [&'static [u8]],
        output: &'static [u8],
    },
    Causal {
        input: &'static [u8],
        output: &'static [u8],
    },
}

fn build_corpus() -> Vec<Turn> {
    let mut turns = Vec::new();

    // Workload 1: Cooked shell typing + pipelined multi-keystroke watermark bursts (140 inputs).
    turns.push(Turn::Setup(b"$ "));
    let commands: &[&[u8]] = &[
        b"git status -s",
        b"targo --unverified test --locked -p astream-term",
        b"asb stats 127.0.0.1:7777 /f/prod/>",
        b"aspump --group g1 --profile claude /f/prod/term/n1/s1/out",
    ];
    for cmd in commands {
        // Feed 3-keystroke pipelined bursts retired by batched authoritative echoes, then single keys.
        let mut i = 0usize;
        while i + 3 <= cmd.len() {
            let k0 = &cmd[i..i + 1];
            let k1 = &cmd[i + 1..i + 2];
            let k2 = &cmd[i + 2..i + 3];
            // Static single-byte slices via a small helper table below isn't needed if we push Causal/Watermark per byte;
            // to exercise genuine pipelined multi-keystroke watermark retirement, push fixed burst patterns too:
            let _ = (k0, k1, k2);
            i += 3;
        }
        for pos in 0..cmd.len() {
            turns.push(Turn::Watermark {
                input: &cmd[pos..pos + 1],
                output: &cmd[pos..pos + 1],
            });
        }
        turns.push(Turn::Causal {
            input: b"\r",
            output: b"\r\nok\r\n$ ",
        });
    }
    // Pipelined 3-keystroke bursts answered by single batched echoes on the watermark path.
    for _ in 0..8 {
        turns.push(Turn::WatermarkBatch {
            inputs: &[b"l", b"s", b" "],
            output: b"ls ",
        });
        turns.push(Turn::WatermarkBatch {
            inputs: &[b"-", b"l", b"a"],
            output: b"-la",
        });
        turns.push(Turn::Causal {
            input: b"\r",
            output: b"\r\n$ ",
        });
    }

    // Workload 2: Readline / ZLE cursor-motion & Backspace line editing (80 inputs).
    for _ in 0..10 {
        turns.push(Turn::Causal {
            input: b"echx",
            output: b"echx",
        });
        turns.push(Turn::Causal {
            input: b"\x7f",
            output: b"\x08 \x08",
        });
        turns.push(Turn::Causal {
            input: b"o hi",
            output: b"o hi",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[D",
            output: b"\x1b[D",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[D",
            output: b"\x1b[D",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[C",
            output: b"\x1b[C",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[C",
            output: b"\x1b[C",
        });
        turns.push(Turn::Causal {
            input: b"\r",
            output: b"\r\nhi\r\n$ ",
        });
    }

    // Workload 3: Alternate-screen TUI navigation (`?1049h` menu/pager — 96 inputs).
    turns.push(Turn::Setup(
        b"\x1b[?1049h[0] broker\r\n[1] engine\r\n[2] term\r\n[3] kafka\r\n[4] pump\x1b[H",
    ));
    for _ in 0..16 {
        turns.push(Turn::Causal {
            input: b"\x1b[B",
            output: b"\x1b[B",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[B",
            output: b"\x1b[B",
        });
        turns.push(Turn::Causal {
            input: b"j",
            output: b"\x1b[B",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[A",
            output: b"\x1b[A",
        });
        turns.push(Turn::Causal {
            input: b"k",
            output: b"\x1b[A",
        });
        turns.push(Turn::Causal {
            input: b"\x1b[A",
            output: b"\x1b[A",
        });
    }
    turns.push(Turn::Setup(b"\x1b[?1049l$ "));

    // Workload 4: Adversarial `Password: ` no-echo prompt + contradiction squash recovery.
    turns.push(Turn::Setup(b"sudo asb\r\nPassword: "));
    // First secret byte contradicts once and squashes; remaining 7 secret bytes suppress echo;
    // then Enter returns to `$ ` and normal 0-RTT cooked speculation resumes cleanly!
    turns.push(Turn::Causal {
        input: b"s",
        output: b"",
    });
    for &pw_byte in &[b"3" as &[u8], b"c", b"r", b"3", b"t", b"!", b"9"] {
        turns.push(Turn::Causal {
            input: pw_byte,
            output: b"",
        });
    }
    turns.push(Turn::Causal {
        input: b"\r",
        output: b"\r\n$ ",
    });
    for b in b"echo done" {
        let slice = std::slice::from_ref(b);
        let _ = slice;
    }
    turns.push(Turn::Watermark {
        input: b"echo done",
        output: b"echo done",
    });

    turns
}

fn run_corpus_once(turns: &[Turn], verify_oracle: bool) -> (SpeculativeTerminal, Vec<Record>) {
    let (cols, rows) = (80u16, 24u16);
    let mut term = SpeculativeTerminal::new(cols, rows);
    let mut auth_log = Vec::new();
    let mut seq = 1u64;
    let mut wm = 1u64;

    for turn in turns {
        match *turn {
            Turn::Setup(bytes) => {
                let rec = Record::Out(bytes.to_vec());
                term.apply_output(&rec);
                if verify_oracle {
                    auth_log.push(rec);
                }
            }
            Turn::Watermark { input, output } => {
                let _ = term.predict(seq, input);
                seq += 1;
                let rec = Record::Out(output.to_vec());
                let _ = term.apply_output_at(wm, &rec);
                wm += 1;
                if verify_oracle {
                    auth_log.push(rec);
                }
            }
            Turn::WatermarkBatch { inputs, output } => {
                for inp in inputs {
                    let _ = term.predict(seq, inp);
                    seq += 1;
                }
                let rec = Record::Out(output.to_vec());
                let _ = term.apply_output_at(wm, &rec);
                wm += 1;
                if verify_oracle {
                    auth_log.push(rec);
                }
            }
            Turn::Causal { input, output } => {
                let in_off = seq;
                let _ = term.predict_at(seq, in_off, input);
                seq += 1;
                let rec = Record::Out(output.to_vec());
                let _ = term.apply_output_caused(wm, Some(in_off), &rec);
                wm += 1;
                if verify_oracle {
                    auth_log.push(rec);
                }
            }
        }
    }
    let _ = term.reconcile();
    (term, auth_log)
}

fn main() {
    let corpus = build_corpus();
    let (verified, auth_log) = run_corpus_once(&corpus, true);
    let oracle = screen::fold(80, 24, &auth_log);
    assert_eq!(
        verified.pending_count(),
        0,
        "all speculative transitions retired after reconcile"
    );
    assert_eq!(
        verified.view().serialize(),
        oracle.serialize(),
        "0 residual screen divergences against independent VT fold oracle"
    );
    assert!(
        verified.squashes() >= 1,
        "corpus must exercise non-vacuous contradiction squash-and-rebuild"
    );

    let hits = verified.hits();
    let misses = verified.misses();
    let abstentions = verified.abstentions();
    let total_inputs = hits + misses + abstentions;
    let hit_rate = (hits as f64) / (total_inputs as f64);
    let precision = (verified.precision_bps() as f64) / 10_000.0;

    // Timed replay loop for throughput regression visibility.
    let iters: u64 = 200;
    let start = Instant::now();
    let mut acc = 0u64;
    for _ in 0..iters {
        let (t, _) = run_corpus_once(&corpus, false);
        acc = acc.wrapping_add(t.hits());
    }
    black_box(acc);
    let turns_per_sec = ((iters * (total_inputs)) as f64) / start.elapsed().as_secs_f64();

    println!("METRIC predict_hit_rate {hit_rate:.4}");
    println!("METRIC predict_precision {precision:.4}");
    println!("METRIC predict_turn_ops_per_sec {turns_per_sec:.0}");
}
