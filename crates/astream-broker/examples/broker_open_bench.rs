// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE OPEN OF A LARGE RETAINED LOG, PLAINTEXT AGAINST SEALED AT REST. Every open reads the
//! whole retained log and scans every record (a sealed one authenticates each record as it
//! scans), so the open of a log sealed at rest pays the AEAD over all of it. An embedder that
//! reopens its broker in place pays it at every reopen: aterm reopens its broker on every
//! update it applies in place and on every exit-75 restart.
//!
//! The bench writes a plaintext log of OPEN_MIB MiB (256 by default) of 4 KiB records over 64
//! subjects at Relaxed, closes it cleanly, copies it and seals the copy with
//! `BrokerLog::seal_plaintext` (timed: the offline seal's own cost), then opens the two A B B A
//! (plaintext, sealed, sealed, plaintext) at Ordered { 100 ms }, aterm's tier, the sealed one
//! with its key and bound, each open timed from the call to its return and closed cleanly
//! after. Both files are written by this process just before, so both opens read from the
//! page cache: what differs is the scan, not the device.
//!
//! METRIC lines: `broker_open_plain_ms` and `broker_open_sealed_ms` (the mean of each arm's
//! two opens), `broker_open_sealed_over_plain` (their ratio) and `broker_seal_plaintext_ms`.
//!
//!   OPEN_MIB=256 targo --unverified run --release -p astream-broker --features at-rest --example broker_open_bench

#[cfg(unix)]
use astream_broker::{BrokerLog, Durability, OpenOptions, Prepared};
#[cfg(unix)]
use std::path::{Path, PathBuf};
#[cfg(unix)]
use std::process::ExitCode;
#[cfg(unix)]
use std::time::{Duration, Instant};

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_open_bench seals with BrokerLog::seal_plaintext, which is unix-only");
}

/// Removes the bench's directory when dropped.
#[cfg(unix)]
struct Cleanup(PathBuf);

#[cfg(unix)]
impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[cfg(unix)]
const KEY: [u8; 32] = [0x42; 32];

/// Open `log` at aterm's tier (sealed: with the key, bound), time the open, close it cleanly.
#[cfg(unix)]
fn timed_open(log: &Path, sealed: bool) -> Duration {
    let mut opts = OpenOptions::new(Durability::Ordered {
        horizon: Some(Duration::from_millis(100)),
    });
    if sealed {
        opts.at_rest_key = Some(KEY);
        opts.require_bound_at_rest = true;
    }
    let start = Instant::now();
    let mut opened = BrokerLog::open_opts(log, opts, || Ok(Prepared::Nothing)).unwrap();
    let took = start.elapsed();
    opened.close_clean().unwrap();
    took
}

#[cfg(unix)]
fn main() -> ExitCode {
    let mib: u64 = match std::env::var("OPEN_MIB") {
        Err(_) => 256,
        Ok(s) => match s.trim().parse() {
            Ok(n) if n > 0 => n,
            _ => {
                eprintln!("broker_open_bench: OPEN_MIB must be a positive whole number, got {s:?}");
                return ExitCode::from(2);
            }
        },
    };
    let dir = PathBuf::from(format!("/tmp/asopen_{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let _cleanup = Cleanup(dir.clone());
    let plain = dir.join("plain.log");
    let sealed = dir.join("sealed.log");

    // The plaintext log: 4 KiB records over 64 subjects, pseudo-random bodies.
    let mut log = BrokerLog::open_with(&plain, Durability::Relaxed).unwrap();
    let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut body = vec![0u8; 4096];
    let mut seq = 0u64;
    while std::fs::metadata(&plain).unwrap().len() < mib << 20 {
        for b in body.chunks_mut(8) {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            b.copy_from_slice(&x.to_le_bytes()[..b.len()]);
        }
        seq += 1;
        log.publish(
            1,
            seq,
            format!("/f/F/pub/n-bench/s{}/ev", seq % 64),
            body.clone(),
        )
        .unwrap();
    }
    log.close_clean().unwrap();
    drop(log);
    let bytes = std::fs::metadata(&plain).unwrap().len();

    // The sealed copy, sealed offline.
    std::fs::copy(&plain, &sealed).unwrap();
    std::fs::copy(dir.join("plain.log.id"), dir.join("sealed.log.id")).unwrap();
    let start = Instant::now();
    let report = BrokerLog::seal_plaintext(&sealed, KEY).unwrap();
    let seal = start.elapsed();
    assert_eq!(report.head.0, seq, "every record sealed");

    // A B B A.
    let a1 = timed_open(&plain, false);
    let b1 = timed_open(&sealed, true);
    let b2 = timed_open(&sealed, true);
    let a2 = timed_open(&plain, false);
    let ms = |d: Duration| d.as_secs_f64() * 1000.0;
    let plain_ms = (ms(a1) + ms(a2)) / 2.0;
    let sealed_ms = (ms(b1) + ms(b2)) / 2.0;
    println!("METRIC broker_open_plain_ms {plain_ms:.1}");
    println!("METRIC broker_open_sealed_ms {sealed_ms:.1}");
    println!(
        "METRIC broker_open_sealed_over_plain {:.2}",
        sealed_ms / plain_ms
    );
    println!("METRIC broker_seal_plaintext_ms {:.1}", ms(seal));
    eprintln!(
        "astream-broker open: {seq} records, {:.1} MiB plaintext ({:.1} MiB sealed); opens A B B \
         A at Ordered 100 ms: plain {:.1} ms, sealed {:.1} ms, sealed {:.1} ms, plain {:.1} ms; \
         seal_plaintext {:.1} ms",
        bytes as f64 / f64::from(1u32 << 20),
        report.bytes as f64 / f64::from(1u32 << 20),
        ms(a1),
        ms(b1),
        ms(b2),
        ms(a2),
        ms(seal)
    );
    ExitCode::SUCCESS
}
