//! Multi-dimensional Pareto scoreboard for `astream-broker`:
//!   1. `Durability::Strict` (fsync-before-ack) 1-conn sequential (`p50`/`p99` µs, ops/s)
//!   2. `Durability::Strict` (fsync-before-ack) 1-conn pipelined (`window=512`, ops/s + speedup)
//!   3. `Durability::Relaxed` (page-cache crash-safe) 1-conn sequential (`p50`/`p99` µs, ops/s)
//!   4. `Durability::Relaxed` (page-cache crash-safe) 1-conn pipelined (`window=512`, ops/s)
//!   5. Counterfactual `ForkSubscribe` snapshot replay over a 10,000-record log (µs)
//!   6. Wire-level `Client::retire_subject` (`/a/retire`) subject reclamation (`p50` µs)
//!
//! Run:
//!   targo --unverified run --locked --release -p astream-broker --example broker_pareto_bench

#[cfg(unix)]
use astream_broker::{Broker, Client, Durability};
#[cfg(unix)]
use std::time::Instant;

#[cfg(not(unix))]
fn main() {
    eprintln!("broker_pareto_bench requires Unix-domain sockets; run it on a unix host");
}

#[cfg(unix)]
struct Cleanup(Vec<String>);

#[cfg(unix)]
impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let _ = std::fs::remove_file(path);
        }
    }
}

#[cfg(unix)]
fn percentile_us(samples_ns: &mut [u64], pct: f64) -> f64 {
    if samples_ns.is_empty() {
        return 0.0;
    }
    samples_ns.sort_unstable();
    let idx = (((samples_ns.len() - 1) as f64) * pct).round() as usize;
    samples_ns[idx.min(samples_ns.len() - 1)] as f64 / 1_000.0
}

#[cfg(unix)]
fn main() {
    let pid = std::process::id();
    let payload = vec![0xABu8; 64];

    // 1 & 2. Strict tier: 1-conn sequential vs 1-conn pipelined (window=512)
    let strict_log = format!("/tmp/aspareto_strict_{pid}.log");
    let strict_sock = format!("/tmp/aspareto_strict_{pid}.sock");
    let _ = std::fs::remove_file(&strict_log);
    let _g1 = Cleanup(vec![strict_log.clone(), strict_sock.clone()]);
    let strict_broker = Broker::open_with(&strict_log, Durability::Strict).unwrap();
    let mut strict_h = strict_broker.serve(&strict_sock).unwrap();
    let mut strict_c = Client::connect(&strict_sock).unwrap();

    let seq_n = 200usize;
    let mut strict_lat_ns = Vec::with_capacity(seq_n);
    let t0 = Instant::now();
    for i in 1..=seq_n {
        let s = Instant::now();
        strict_c
            .publish(1, i as u64, "/t/pareto/seq", &payload)
            .unwrap();
        strict_lat_ns.push(s.elapsed().as_nanos() as u64);
    }
    let strict_seq_ops = seq_n as f64 / t0.elapsed().as_secs_f64();
    let strict_p50_us = percentile_us(&mut strict_lat_ns, 0.50);
    let strict_p99_us = percentile_us(&mut strict_lat_ns, 0.99);

    let pipe_n = 10_000usize;
    let bodies: Vec<&[u8]> = (0..pipe_n).map(|_| payload.as_slice()).collect();
    let t1 = Instant::now();
    let acks = strict_c
        .publish_pipelined(2, "/a/pareto/pipe", &bodies, 512)
        .unwrap();
    let strict_pipe_ops = pipe_n as f64 / t1.elapsed().as_secs_f64();
    assert_eq!(acks.len(), pipe_n);
    let strict_speedup = strict_pipe_ops / strict_seq_ops;
    strict_h.shutdown();

    // 3 & 4 & 5 & 6. Relaxed tier + Counterfactual ForkSubscribe + Subject Retirement
    let rel_log = format!("/tmp/aspareto_rel_{pid}.log");
    let rel_sock = format!("/tmp/aspareto_rel_{pid}.sock");
    let _ = std::fs::remove_file(&rel_log);
    let _g2 = Cleanup(vec![rel_log.clone(), rel_sock.clone()]);
    let rel_broker = Broker::open_with(&rel_log, Durability::Relaxed).unwrap();
    let mut rel_h = rel_broker.serve(&rel_sock).unwrap();
    let mut rel_c = Client::connect(&rel_sock).unwrap();

    let rel_seq_n = 2_000usize;
    let mut rel_lat_ns = Vec::with_capacity(rel_seq_n);
    let t2 = Instant::now();
    for i in 1..=rel_seq_n {
        let s = Instant::now();
        rel_c
            .publish(1, i as u64, "/t/pareto/seq", &payload)
            .unwrap();
        rel_lat_ns.push(s.elapsed().as_nanos() as u64);
    }
    let rel_seq_ops = rel_seq_n as f64 / t2.elapsed().as_secs_f64();
    let rel_p50_us = percentile_us(&mut rel_lat_ns, 0.50);
    let rel_p99_us = percentile_us(&mut rel_lat_ns, 0.99);

    let t3 = Instant::now();
    let rel_acks = rel_c
        .publish_pipelined(2, "/a/pareto/pipe", &bodies, 512)
        .unwrap();
    let rel_pipe_ops = pipe_n as f64 / t3.elapsed().as_secs_f64();
    assert_eq!(rel_acks.len(), pipe_n);

    // 5. Counterfactual ForkSubscribe latency over 12,000 records
    let t_fork = Instant::now();
    let mut fork_sub = Client::connect(&rel_sock)
        .unwrap()
        .fork_subscribe(5_000, "/a/pareto/forked", b"branch", "/a/pareto/forked")
        .unwrap();
    let forked = fork_sub.recv().unwrap().unwrap();
    let fork_us = t_fork.elapsed().as_nanos() as f64 / 1_000.0;
    assert_eq!(forked.1, "/a/pareto/forked");

    // 6. Wire-level retire_subject latency
    let t_retire = Instant::now();
    let (_, absent) = rel_c.retire_subject(1, "/t/pareto/seq").unwrap();
    let retire_us = t_retire.elapsed().as_nanos() as f64 / 1_000.0;
    assert!(!absent);
    rel_h.shutdown();

    println!("METRIC broker_strict_seq_ops_per_sec {strict_seq_ops:.0}");
    println!("METRIC broker_strict_pipe_ops_per_sec {strict_pipe_ops:.0}");
    println!("METRIC broker_strict_pipe_speedup {strict_speedup:.1}");
    println!("METRIC broker_relaxed_seq_ops_per_sec {rel_seq_ops:.0}");
    println!("METRIC broker_relaxed_seq_p50_us {rel_p50_us:.1}");
    println!("METRIC broker_relaxed_seq_p99_us {rel_p99_us:.1}");
    println!("METRIC broker_relaxed_pipe_ops_per_sec {rel_pipe_ops:.0}");
    println!("METRIC broker_counterfactual_fork_us {fork_us:.1}");
    println!("METRIC broker_retire_subject_us {retire_us:.1}");
    eprintln!(
        "astream-broker pareto scoreboard:\n  \
         Strict 1-conn sequential : {strict_seq_ops:8.0} ops/s (p50={strict_p50_us:.1}us, p99={strict_p99_us:.1}us)\n  \
         Strict 1-conn pipelined  : {strict_pipe_ops:8.0} ops/s ({strict_speedup:.1}x speedup over 1-conn fsync)\n  \
         Relaxed 1-conn sequential: {rel_seq_ops:8.0} ops/s (p50={rel_p50_us:.1}us, p99={rel_p99_us:.1}us)\n  \
         Relaxed 1-conn pipelined : {rel_pipe_ops:8.0} ops/s\n  \
         Counterfactual fork (12k): {fork_us:8.1} us\n  \
         Wire retire_subject      : {retire_us:8.1} us"
    );
}
