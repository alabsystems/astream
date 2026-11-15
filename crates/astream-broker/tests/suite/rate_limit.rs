// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.rate-limit`: monotone token-bucket rate limiting (`TlaRateBudget`)
//! bounds record rate and byte rate per principal (`producer_id`), isolates noisy principals
//! from peers on guarded brokers, never starves commits/retirements/reads, and surfaces
//! structured `ERR_RATE_LIMITED` (`retry_after_ms`) refusals over the wire and `asb serve`.

#![cfg(unix)]

use astream_broker::{
    broker_refusal, Broker, BrokerRefusal, Client, Durability, OpenOptions, Prepared, RateLimit,
    ERR_RATE_LIMITED, MAX_RATE_BUDGET,
};
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

static NEXT_RL: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Self {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT_RL.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asrl-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Self(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch dir");
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn rate_limit_spec_parser_roundtrips_and_rejects_invalid_specs() {
    let rec = RateLimit::parse("250:500").expect("parse records spec");
    assert_eq!(rec, RateLimit::records(250, 500).unwrap());
    assert_eq!(rec.to_string(), "250:500");

    let rec_default_burst = RateLimit::parse("100").expect("default burst = 1s");
    assert_eq!(rec_default_burst, RateLimit::records(100, 100).unwrap());

    let bytes = RateLimit::parse("1000:2000,1048576:4194304").expect("parse bytes spec");
    assert_eq!(
        bytes,
        RateLimit::records(1000, 2000)
            .unwrap()
            .with_bytes(1024 * 1024, 4 * 1024 * 1024)
            .unwrap()
    );

    let both = RateLimit::parse("50:100,65536:131072").expect("parse composite spec");
    assert_eq!(both.records_per_sec, 50);
    assert_eq!(both.burst_records, 100);
    assert_eq!(both.bytes_per_sec, 64 * 1024);
    assert_eq!(both.burst_bytes, 128 * 1024);
    assert_eq!(RateLimit::parse(&both.to_string()).unwrap(), both);

    for bad in [
        "",
        "0",
        "10:0",
        "10:20,0:100",
        "10:20,100:0",
        "10,20,30",
        "unknown=5",
        &format!("{}", MAX_RATE_BUDGET + 1),
    ] {
        assert!(
            RateLimit::parse(bad).is_err(),
            "expected {bad:?} to be rejected"
        );
    }
}

#[test]
fn per_producer_token_bucket_throttles_burst_reports_retry_after_and_spares_commits_and_retires() {
    let s = Scratch::new("prod");
    let lim = RateLimit::records(20, 3).unwrap();
    let opts = OpenOptions::new(Durability::Relaxed).with_rate_limit(lim);
    let b = Broker::open_opts(s.path("b.log"), opts, || Ok(Prepared::Nothing)).unwrap();
    assert_eq!(b.rate_limit(), Some(lim));
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();

    let mut c1 = Client::connect(&sock).unwrap();
    let mut c2 = Client::connect(&sock).unwrap();

    // Producer 1 consumes its 3-record burst.
    assert_eq!(c1.publish(1, 1, "/m/a", b"1").unwrap(), (0, false));
    assert_eq!(c1.publish(1, 2, "/m/b", b"2").unwrap(), (1, false));
    assert_eq!(c1.publish(1, 3, "/m/c", b"3").unwrap(), (2, false));

    // 4th publish by Producer 1 is refused with ERR_RATE_LIMITED + retry_after_ms.
    let err = c1
        .publish(1, 4, "/m/d", b"4")
        .expect_err("4th burst record must be rate-limited");
    let refusal: &BrokerRefusal = broker_refusal(&err).expect("structured BrokerRefusal");
    assert_eq!(refusal.code, ERR_RATE_LIMITED);
    assert!(refusal.is_rate_limited());
    assert!(
        !refusal.is_permanent(),
        "rate limit refusal must be transient so clients back off and retry"
    );
    let retry_ms = refusal.retry_after_ms().expect("retry_after_ms parsed");
    assert!(
        (1..=60).contains(&retry_ms),
        "20/s = 50ms per token, got retry_after_ms={retry_ms}"
    );
    assert_eq!(b.stats().rate_limited, 1);

    // Producer 2 has an independent bucket and bursts 3 records without waiting.
    assert_eq!(c2.publish(2, 1, "/m/p2", b"x").unwrap(), (3, false));
    assert_eq!(c2.publish(2, 2, "/m/p2", b"y").unwrap(), (4, false));
    assert_eq!(c2.publish(2, 3, "/m/p2", b"z").unwrap(), (5, false));

    // Throttled Producer 1 can STILL commit consumer groups, retire subjects, and fetch/last!
    c1.commit("g1", 2).unwrap();
    assert!(!c1.retire_subject(1, "/m/a").unwrap().1);
    assert_eq!(c1.last("/m/>", "", 16).unwrap().0.len(), 3);
    assert_eq!(c1.fetch(0, "/m/>", 16).unwrap().0.len(), 6);

    // Wait 65ms (>= 50ms for 1 token at 20/s): Producer 1 refills and publishes seq=4!
    thread::sleep(Duration::from_millis(65));
    let (off4, dedup4) = c1.publish(1, 4, "/m/d", b"4").unwrap();
    assert!(!dedup4);
    assert!(off4 >= 7);

    // Disabling the rate limit live (`None`) unblocks arbitrary bursts immediately.
    b.set_rate_limit(None).unwrap();
    assert_eq!(b.rate_limit(), None);
    for seq in 5..=12 {
        c1.publish(1, seq, "/m/free", b"ok").unwrap();
    }
}

#[cfg(feature = "cap")]
#[test]
fn guarded_per_principal_byte_budget_isolates_noisy_principal_and_protects_process_and_produce() {
    use astream_cap::{mint, producer_id_of};
    const SECRET: &[u8] = b"rate-limit-guarded-secret-0123456789abcdef";

    let s = Scratch::new("cap");
    // Plenty of record tokens (1000:1000), tight byte ceiling: 1024 B/s sustained, 550 B burst
    // (each `/f/in/1` + 256-byte chunk charges 7 + 256 = 263 wire bytes -> 2 fit in 550 B, 3rd exceeds).
    let byte_lim = RateLimit::records(1000, 1000)
        .unwrap()
        .with_bytes(1024, 550)
        .unwrap();
    let mut opts = OpenOptions::new(Durability::Relaxed).with_rate_limit(byte_lim);
    opts.guard = Some(SECRET.to_vec());
    let b = Broker::open_opts(s.path("b.log"), opts, || Ok(Prepared::Nothing)).unwrap();
    let sock = s.path("b.sock");
    let _h = b.serve(&sock).unwrap();

    let alice_name = "n-0102030405060708";
    let bob_name = "n-1112131415161718";
    let alice_cap = mint(SECRET, &format!("rw,p={alice_name}:/>")).unwrap();
    let bob_cap = mint(SECRET, &format!("rw,p={bob_name}:/>")).unwrap();
    let alice_pid = producer_id_of(alice_name);
    let bob_pid = producer_id_of(bob_name);

    let mut alice = Client::connect(&sock).unwrap();
    alice.attach(&alice_cap.filter, &alice_cap.tag).unwrap();
    let mut bob = Client::connect(&sock).unwrap();
    bob.attach(&bob_cap.filter, &bob_cap.tag).unwrap();

    let chunk = [b'A'; 256];
    // Alice spends 2 * 263 = 526 bytes of her 550-byte burst; 3rd publish (263B) is throttled.
    alice.publish(alice_pid, 1, "/f/in/1", &chunk).unwrap();
    alice.publish(alice_pid, 2, "/f/in/2", &chunk).unwrap();
    let err = alice
        .publish(alice_pid, 3, "/f/in/3", &chunk)
        .expect_err("alice exceeded 550B burst_bytes");
    let refusal = broker_refusal(&err).unwrap();
    assert!(refusal.is_rate_limited());
    assert!(refusal.retry_after_ms().unwrap() >= 100);

    // Atomic `process_and_produce` by throttled Alice is also refused BEFORE committing `/g/alice`!
    let pp_err = alice
        .process_and_produce(alice_pid, 3, "/f/out/1", &chunk, "/g/alice", 2)
        .expect_err("throttled process_and_produce must fail atomically");
    assert!(broker_refusal(&pp_err).unwrap().is_rate_limited());
    assert_eq!(
        b.group_start("/g/alice"),
        0,
        "refused process_and_produce must not commit group offset"
    );

    // Meanwhile Bob has his full 550-byte burst untouched!
    bob.publish(bob_pid, 1, "/f/bob/1", &chunk).unwrap();
    bob.publish(bob_pid, 2, "/f/bob/2", &chunk).unwrap();
}

#[test]
fn asb_serve_rate_limit_flag_enforces_token_bucket_and_validates_syntax() {
    let s = Scratch::new("cli");
    let log = s.path("b.log");
    let sock = s.path("b.sock");

    let bad = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "serve",
            sock.to_str().unwrap(),
            log.to_str().unwrap(),
            "--rate-limit",
            "not-a-rate",
        ])
        .output()
        .unwrap();
    assert_eq!(bad.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&bad.stderr).contains("--rate-limit"));

    let mut child = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "serve",
            sock.to_str().unwrap(),
            log.to_str().unwrap(),
            "--durability",
            "relaxed",
            "--rate-limit",
            "5:2",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    let mut line = String::new();
    let mut reader = BufReader::new(child.stdout.take().unwrap());
    reader.read_line(&mut line).unwrap();
    assert!(line.starts_with("listening "), "got {line:?}");

    let mut c = Client::connect(&sock).unwrap();
    c.publish(9, 1, "/cli/1", b"a").unwrap();
    c.publish(9, 2, "/cli/2", b"b").unwrap();
    let err = c
        .publish(9, 3, "/cli/3", b"c")
        .expect_err("3rd CLI publish must hit burst=2");
    assert!(broker_refusal(&err).is_some_and(BrokerRefusal::is_rate_limited));

    let _ = child.kill();
    let _ = child.wait();
}
