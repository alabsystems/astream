// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! WHAT `BrokerLog::stats` HOLDS THE LOG LOCK FOR AS A LOG RETAINS WILLS (aterm F19). aterm's
//! broker takes `Broker::health` every 30 s, and `Broker::stats` and `Broker::health` hold the
//! log lock over `BrokerLog::stats` (`stats_of`), which counts the pending wills.
//!
//! For each count of wills in `STATS_WILLS` (`32,1000` by default) the bench writes through a
//! broker, as aterm's broker is written, a Relaxed log of `STATS_RECORDS` (1,006,000 by default)
//! 128-byte records of one producer on one subject (aterm's attach-bench filler, as
//! `broker_index_bench`'s `filler`), with that many wills spread over it: before record
//! `k * records / wills` a connection registers will `k` under a producer of its own and ends,
//! and its will fires, so each will leaves its `/a/will` record and its firing on the log.
//! Connections use Unix sockets where available, otherwise loopback TCP. It
//! then reopens the log as an embedder does (`BrokerLog::open_opts`), at a residency budget of
//! 0 and of 16 MiB, and times `BrokerLog::stats` [`WALKS`] times, each alone: what the broker
//! holds its log lock for to answer one, with the records the walks read back from the file
//! (`BrokerLog::cold_reads`). The page cache is warm: the log was just written.
//!
//!   targo --unverified run --release -p astream-broker --example broker_stats_bench
//!
//! One line per count of wills and budget:
//! `STATS records=N wills=W budget=B resident=R walks=K walk_ns=M min_ns=F max_ns=S
//! cold_reads=C pending=P` (the median, fastest and slowest walk; the cold reads over all the
//! walks; the pending wills `stats` counts, 0 here, every will having fired).

#![deny(unsafe_code)]

use astream_broker::{will_seq, Broker, BrokerLog, Client, Durability, OpenOptions};
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

/// aterm's attach-bench filler: one subject, 128-byte bodies, one producer.
const SUBJECT: &str = "/f/lab/pub/n-a/s-one/ev";
const BODY: usize = 128;
const PRODUCER: u64 = 7;
/// Will `k` is registered under producer `WILL_PRODUCER + k`.
const WILL_PRODUCER: u64 = 1 << 40;
const BUDGETS: [usize; 2] = [0, 16 << 20];
/// The `stats` calls timed at each budget.
const WALKS: usize = 9;
/// The publishes the writer keeps in flight.
const WINDOW: usize = 256;
/// How long the wills' firings may take to land once the last connection ended: a hang
/// detector, not a budget.
const FIRED_WITHIN: Duration = Duration::from_secs(60);

/// Removes the bench's directory when dropped.
struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The positive whole numbers `var` lists, comma-separated (`default` when unset).
fn list(var: &str, default: &str) -> Result<Vec<u64>, String> {
    let raw = std::env::var(var).unwrap_or_else(|_| default.to_string());
    let mut out = Vec::new();
    for part in raw.split(',') {
        match part.trim().parse::<u64>() {
            Ok(n) if n > 0 => out.push(n),
            _ => return Err(format!("{var} takes positive whole numbers, got {raw:?}")),
        }
    }
    Ok(out)
}

/// Writes `records` filler records and `wills` fired wills spread over them to `path`,
/// through a broker serving on a socket in `dir`.
fn write(dir: &Path, path: &Path, records: u64, wills: u64) -> io::Result<()> {
    let broker = Broker::open_with(path, Durability::Relaxed)?;
    #[cfg(unix)]
    let sock = dir.join("stats.sock");
    #[cfg(unix)]
    let mut served = broker.serve(&sock)?;
    #[cfg(unix)]
    let connect = || Client::connect(&sock);
    #[cfg(not(unix))]
    let mut served = broker.serve_tcp("127.0.0.1:0")?;
    #[cfg(not(unix))]
    let address = served
        .tcp_addr()
        .ok_or_else(|| io::Error::other("the TCP benchmark has no bound address"))?
        .to_owned();
    #[cfg(not(unix))]
    let connect = || Client::connect_tcp(&address);
    #[cfg(not(unix))]
    let _ = dir;
    let mut cli = connect()?;
    let body = vec![b'e'; BODY];
    let seq = will_seq(1).ok_or_else(|| io::Error::other("no will seq for incarnation 1"))?;
    let mut owed = 0usize;
    let mut next_will = 0u64;
    for i in 0..records {
        while next_will < wills && next_will * records / wills <= i {
            let mut c = connect()?;
            let subject = format!("/f/bench/will/{next_will}");
            c.will(WILL_PRODUCER + next_will, seq, &subject, b"gone")?;
            drop(c);
            next_will += 1;
        }
        cli.send_publish(PRODUCER, i + 1, SUBJECT, &body)?;
        owed += 1;
        if owed == WINDOW {
            let (_, deduped) = cli.recv_publish_ack()?;
            assert!(!deduped, "a filler record was answered as a re-send");
            owed -= 1;
        }
    }
    for _ in 0..owed {
        cli.recv_publish_ack()?;
    }
    // Each will fires once its connection has ended, on the broker's time: wait for the last.
    let want = records + 2 * wills;
    let deadline = Instant::now() + FIRED_WITHIN;
    while broker.head() < want {
        if Instant::now() > deadline {
            return Err(io::Error::other(format!(
                "the wills' firings: the head is {} of {want} a minute on",
                broker.head()
            )));
        }
        std::thread::sleep(Duration::from_millis(1));
    }
    drop(cli);
    served.shutdown();
    drop(broker);
    Ok(())
}

/// Writes one log of `records` and `wills` and times `stats` on it at each budget.
fn run(dir: &Path, records: u64, wills: u64) -> io::Result<()> {
    let path = dir.join(format!("stats-{records}-{wills}.log"));
    write(dir, &path, records, wills)?;
    for budget in BUDGETS {
        let opts = OpenOptions::new(Durability::Relaxed).with_resident_budget(budget);
        let log = BrokerLog::open_opts(&path, opts, BrokerLog::prepare_nothing)?;
        assert_eq!(
            log.head().0 - log.base().0,
            records + 2 * wills,
            "the reopened log lost records"
        );
        let (resident, _, _) = log.residency();
        let cold_before = log.cold_reads();
        let mut walks: Vec<u64> = Vec::with_capacity(WALKS);
        let mut pending = 0usize;
        for _ in 0..WALKS {
            let one = Instant::now();
            let stats = log.stats();
            walks.push(u64::try_from(one.elapsed().as_nanos()).unwrap_or(u64::MAX));
            pending = stats.pending_wills;
        }
        let cold = log.cold_reads() - cold_before;
        walks.sort_unstable();
        println!(
            "STATS records={records} wills={wills} budget={budget} resident={resident} \
             walks={WALKS} walk_ns={} min_ns={} max_ns={} cold_reads={cold} pending={pending}",
            walks.get(WALKS / 2).copied().unwrap_or(0),
            walks.first().copied().unwrap_or(0),
            walks.last().copied().unwrap_or(0)
        );
        drop(log);
    }
    std::fs::remove_file(&path)?;
    Ok(())
}

fn main() -> ExitCode {
    let (records, wills) = match (
        list("STATS_RECORDS", "1006000"),
        list("STATS_WILLS", "32,1000"),
    ) {
        (Ok(r), Ok(w)) => (r, w),
        (Err(e), _) | (_, Err(e)) => {
            eprintln!("broker_stats_bench: {e}");
            return ExitCode::from(2);
        }
    };
    let dir = std::env::temp_dir().join(format!("asstats_{}.noindex", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("broker_stats_bench: {}: {e}", dir.display());
        return ExitCode::FAILURE;
    }
    let _cleanup = Cleanup(dir.clone());
    for &n in &records {
        for &w in &wills {
            if let Err(e) = run(&dir, n, w) {
                eprintln!("broker_stats_bench: {n} records, {w} wills: {e}");
                return ExitCode::FAILURE;
            }
        }
    }
    ExitCode::SUCCESS
}
