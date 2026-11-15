//! Evidence for `broker.sharded-routing`: share-nothing partition sharding routes a
//! subject to ONE shard (per-subject order preserved), spreads distinct subjects across
//! shards (independent logs + writers — the scaling architecture), preserves per-shard
//! offset order, fans subscriptions in across all shards, and recovers every shard
//! after a restart. Ordering is per-partition (NOT a global total order) — the honest
//! Kafka-style trade-off for scale. Also pinned: the shard count is persisted and a
//! mismatching reopen/connect is refused; a shard's error reaches the fan-in consumer
//! instead of vanishing; so does a shard's gap notice, what retention gave up below its
//! tail (R4's addendum, A9); and dropping a fan-in releases its sockets and threads.
//! No sleeps (one bounded wait on the broker's own liveness reaper).

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::proto::{encode_response, read_frame, write_frame};
use astream_broker::{Broker, Response, ShardedBroker, ShardedClient, ShardedSubscription};
use std::collections::{HashMap, HashSet};
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard};
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Every test here holds this for its whole run. The fd-release test reads the
/// PROCESS-wide fd table, which a sibling test's brokers and sockets would
/// otherwise move under it (libtest runs tests on parallel threads).
static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Removes a test's directory when dropped, so the test leaves nothing behind whether
/// it passes or panics. Bound before the brokers serving from it, so it drops after
/// them.
struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn fresh_dir(tag: &str) -> (Cleanup, PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    // Under /tmp, not temp_dir(): the per-shard Unix socket paths must fit SUN_LEN.
    let dir = PathBuf::from(format!("/tmp/as_sh_{tag}_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    (Cleanup(dir.clone()), dir)
}

#[test]
fn sharded_routing_is_deterministic_ordered_fanned_in_and_recovers() {
    let _serial = serial();
    let (_tmp, dir) = fresh_dir("routing");
    let logs = dir.join("logs");
    let socks = dir.join("socks");

    const SHARDS: u32 = 4;
    const SUBJECTS: usize = 24;

    // What we expect each subject's shard + per-shard offset to be, computed
    // independently of the broker via the same canonical partitioner.
    let mut next_off = vec![0u64; SHARDS as usize]; // per-shard offset counter
    let mut expected: Vec<(usize, u64, Vec<u8>)> = Vec::new(); // (shard, offset, body)

    {
        let b = ShardedBroker::open(&logs, SHARDS).unwrap();
        let _h = b.serve(&socks).unwrap();
        let mut c = ShardedClient::connect(&socks, SHARDS).unwrap();

        for i in 0..SUBJECTS {
            let subject = format!("/a/k/{i}");
            let body = format!("v{i}").into_bytes();
            let shard = c.shard_of(&subject);
            let (s, off, deduped) = c.publish(1, (i + 1) as u64, &subject, &body).unwrap();
            assert_eq!(s, shard, "publish routed to the partitioner's shard");
            assert!(!deduped, "first send is not a dup");
            assert_eq!(off, next_off[shard], "per-shard offset is dense + in order");
            next_off[shard] += 1;
            expected.push((shard, off, body));

            // Routing is deterministic: re-asking gives the same shard, and a re-send is
            // deduped within that shard to the original offset.
            assert_eq!(c.shard_of(&subject), shard);
            let (s2, off2, dd2) = c.publish(1, (i + 1) as u64, &subject, b"dup").unwrap();
            assert_eq!(
                (s2, off2, dd2),
                (shard, off, true),
                "re-send deduped per shard"
            );
        }

        // Sharding actually happened: the subjects landed on more than one shard.
        let used: HashSet<usize> = expected.iter().map(|(s, _, _)| *s).collect();
        assert!(
            used.len() >= 2,
            "distinct subjects spread across shards (got {used:?})"
        );

        // Fan-in subscription sees EVERY record exactly once across all shards.
        let sub = ShardedSubscription::subscribe_all(&socks, SHARDS, 0, "/a/>").unwrap();
        let mut got: HashSet<(usize, u64)> = HashSet::new();
        let mut per_shard_seq: HashMap<usize, Vec<u64>> = HashMap::new();
        for _ in 0..SUBJECTS {
            let (shard, off, _subj, _body) = sub
                .recv()
                .unwrap()
                .expect("a delivery per published record");
            assert!(got.insert((shard, off)), "no duplicate delivery");
            per_shard_seq.entry(shard).or_default().push(off);
        }
        assert_eq!(got.len(), SUBJECTS, "every record fanned in exactly once");
        // Within each shard, offsets arrived in ascending (offset) order.
        for (shard, offs) in &per_shard_seq {
            let mut sorted = offs.clone();
            sorted.sort_unstable();
            assert_eq!(offs, &sorted, "shard {shard} delivered in offset order");
        }
    } // shutdown all shards

    // Restart: every shard's log recovers; the fan-in sees all records again.
    let b2 = ShardedBroker::open(&logs, SHARDS).unwrap();
    let _h2 = b2.serve(&socks).unwrap();
    let sub = ShardedSubscription::subscribe_all(&socks, SHARDS, 0, "/a/>").unwrap();
    let mut recovered: HashSet<(usize, u64)> = HashSet::new();
    for _ in 0..SUBJECTS {
        let (shard, off, _s, _b) = sub.recv().unwrap().expect("recovered delivery");
        recovered.insert((shard, off));
    }
    let expected_set: HashSet<(usize, u64)> = expected.iter().map(|(s, o, _)| (*s, *o)).collect();
    assert_eq!(
        recovered, expected_set,
        "all shards recovered after restart"
    );
}

/// The shard count is part of the data's routing, so it is persisted (a `shards`
/// sidecar in the log dir, and in the socket dir on serve) and a mismatching
/// reopen, connect, or fan-in is refused instead of silently stranding shards and
/// re-routing subjects. A pre-sidecar directory is validated against its
/// `shard-<i>.log` files.
#[test]
fn shard_count_is_persisted_and_a_mismatch_is_refused() {
    let _serial = serial();
    let (_tmp, dir) = fresh_dir("count");
    let logs = dir.join("logs");
    let socks = dir.join("socks");

    {
        let b = ShardedBroker::open(&logs, 4).unwrap();
        let _h = b.serve(&socks).unwrap();
    }
    assert_eq!(
        std::fs::read_to_string(logs.join("shards")).unwrap().trim(),
        "4"
    );
    for wrong in [2u32, 8] {
        let e = ShardedBroker::open(&logs, wrong)
            .err()
            .expect("expected an error");
        assert_eq!(e.kind(), std::io::ErrorKind::InvalidData, "{e}");
        assert!(
            e.to_string().contains("shard count mismatch")
                && e.to_string().contains("has 4 shards"),
            "{e}"
        );
    }
    // The right count reopens; clients with the wrong count are refused too.
    let b = ShardedBroker::open(&logs, 4).unwrap();
    let _h = b.serve(&socks).unwrap();
    assert_eq!(
        std::fs::read_to_string(socks.join("shards"))
            .unwrap()
            .trim(),
        "4"
    );
    let e = ShardedClient::connect(&socks, 2)
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("shard count mismatch"), "{e}");
    let e = ShardedSubscription::subscribe_all(&socks, 8, 0, "/a/>")
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("shard count mismatch"), "{e}");
    assert!(ShardedClient::connect(&socks, 4).is_ok());
    // A socket dir nobody served has no sidecar: refused, not guessed.
    let e = ShardedClient::connect(dir.join("nowhere"), 4)
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("no `shards` sidecar"), "{e}");

    // A legacy directory (shard logs, no sidecar) is validated against its files.
    let legacy = dir.join("legacy");
    std::fs::create_dir_all(&legacy).unwrap();
    for i in 0..3 {
        std::fs::write(legacy.join(format!("shard-{i}.log")), b"").unwrap();
    }
    let e = ShardedBroker::open(&legacy, 2)
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("has 3 shards"), "{e}");
    let e = ShardedBroker::open(&legacy, 4)
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("has 3 shards"), "{e}");
    {
        let b = ShardedBroker::open(&legacy, 3).unwrap();
        let _h = b.serve(dir.join("legacy-socks")).unwrap();
    }
    assert_eq!(
        std::fs::read_to_string(legacy.join("shards"))
            .unwrap()
            .trim(),
        "3",
        "the sidecar is recorded once validated"
    );
}

/// Hand-build a 2-shard socket directory: shard 0 is a real broker holding one
/// record; shard 1 is a listener that answers the subscribe with a broker-style
/// Error frame and closes (what a shard that refuses a filter, or is otherwise
/// unhealthy, looks like on the wire).
fn dir_with_a_failing_shard(dir: &Path) -> (Broker, astream_broker::BrokerHandle) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("shards"), "2\n").unwrap();
    let b = Broker::open(dir.join("shard-0.log")).unwrap();
    let h = b.serve(dir.join("shard-0.sock")).unwrap();
    let mut c = astream_broker::Client::connect(dir.join("shard-0.sock")).unwrap();
    c.publish(1, 1, "/a/x", b"from shard 0").unwrap();
    let l = UnixListener::bind(dir.join("shard-1.sock")).unwrap();
    std::thread::spawn(move || {
        if let Ok((mut s, _)) = l.accept() {
            // The modern client opts in before its one-way stream. This failing
            // shard is an older broker for that request, then refuses Subscribe.
            let _ = read_frame(&mut s);
            let _ = write_frame(
                &mut s,
                &encode_response(&Response::Error {
                    code: astream_broker::proto::ERR_REFUSED,
                    msg: "malformed request".into(),
                }),
            );
            // Read the Subscribe first: closing on an unread request would make the
            // client's write race the close and fail with EPIPE instead of reading
            // the Error below.
            let _ = read_frame(&mut s);
            let _ = write_frame(
                &mut s,
                &encode_response(&Response::Error {
                    code: 3,
                    msg: "bad filter (simulated shard failure)".into(),
                }),
            );
        }
    });
    (b, h)
}

/// A per-shard error is SURFACED to the fan-in consumer (an `Err` naming the
/// shard), never collapsed into silent shard loss or a premature end-of-stream;
/// the healthy shards still deliver. A filter the grammar rejects fails in
/// `subscribe_all` itself.
#[test]
fn fan_in_surfaces_a_shard_error_instead_of_silent_loss() {
    let _serial = serial();
    let (_tmp, dir) = fresh_dir("err");
    let (_b, _h) = dir_with_a_failing_shard(&dir);

    let e = ShardedSubscription::subscribe_all(&dir, 2, 0, "not a filter")
        .err()
        .expect("expected an error");
    assert!(e.to_string().contains("bad filter"), "{e}");

    // (The grammar rejection above never connected, so shard 1's one-shot listener
    // is still waiting.) Now fan in with a valid filter: shard 1 answers with an
    // Error frame, shard 0 with its record.
    let sub = ShardedSubscription::subscribe_all(&dir, 2, 0, "/a/>").unwrap();
    let mut delivered = None;
    let mut shard_err = None;
    for _ in 0..2 {
        match sub.recv() {
            Ok(Some((shard, off, subj, body))) => delivered = Some((shard, off, subj, body)),
            Err(e) => shard_err = Some(e),
            Ok(None) => panic!("end of stream before both shards reported"),
        }
    }
    assert_eq!(
        delivered,
        Some((0usize, 0u64, "/a/x".to_string(), b"from shard 0".to_vec())),
        "the healthy shard still delivers"
    );
    let e = shard_err.expect("the failing shard's error reaches the consumer");
    assert!(
        e.to_string().contains("shard 1") && e.to_string().contains("bad filter"),
        "error names the shard and carries the broker's message: {e}"
    );
}

/// Open file descriptors of this process (`/dev/fd` on macOS and Linux).
fn open_fds() -> usize {
    std::fs::read_dir("/dev/fd").unwrap().count()
}

/// Dropping a fan-in subscription closes every shard socket and joins every
/// forwarder thread — even when the shards are quiet — so a service that opens
/// and drops fan-ins does not accumulate blocked threads and open sockets on
/// either side. Observed through the process's fd table: after the drops the
/// count returns to its baseline (the broker side is reaped by its liveness
/// probe, hence the bounded wait; the leak never converged).
#[test]
fn dropping_a_fan_in_releases_its_sockets_and_threads() {
    let _serial = serial();
    let (_tmp, dir) = fresh_dir("drop");
    let logs = dir.join("logs");
    let socks = dir.join("socks");
    const SHARDS: u32 = 4;
    let b = ShardedBroker::open(&logs, SHARDS).unwrap();
    let _h = b.serve(&socks).unwrap();

    // One warm-up so any one-time allocation (thread-local state, etc.) is in the
    // baseline, then the baseline itself.
    drop(ShardedSubscription::subscribe_all(&socks, SHARDS, 0, "/a/>").unwrap());
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut baseline = open_fds();
    while Instant::now() < deadline {
        let now = open_fds();
        if now == baseline {
            break;
        }
        baseline = now;
        std::thread::sleep(Duration::from_millis(25));
    }

    const ROUNDS: usize = 8;
    for _ in 0..ROUNDS {
        // Quiet shards: nothing is ever delivered, so the old code's forwarders
        // would block in recv forever and the drop would detach them.
        let started = Instant::now();
        drop(ShardedSubscription::subscribe_all(&socks, SHARDS, 0, "/a/>").unwrap());
        assert!(
            started.elapsed() < Duration::from_secs(5),
            "drop must not hang joining its forwarders"
        );
    }

    let deadline = Instant::now() + Duration::from_secs(10);
    let mut now = open_fds();
    while now > baseline && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(25));
        now = open_fds();
    }
    assert!(
        now <= baseline,
        "fd table did not return to baseline: {baseline} before, {now} after {ROUNDS} \
         subscribe+drop rounds of {SHARDS} shards (a leaked socket per shard per round)"
    );
}

/// The records retention keeps on the gap test's shard: the bulk stream its newest two
/// records by their bytes, and mail for a week within three mails' bytes, past which the
/// oldest is given up unread.
#[cfg(feature = "retention")]
fn gap_rules() -> astream_broker::Retention {
    use astream_broker::{record_bytes, BrokerRecord, Retention, Rule};
    let bytes = |subject: &str| {
        record_bytes(&BrokerRecord {
            seq: astream_wire::Offset(0),
            producer_id: 1,
            producer_seq: 1,
            subject: subject.to_string(),
            body: b"body".to_vec(),
            commit: None,
        })
    };
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev")
                .unwrap()
                .max_bytes(2 * bytes("/f/F/pub/n1/s1/ev")),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_bytes(3 * bytes("/f/F/in/n1/from/a"))
                .max_age(Duration::from_secs(7 * 86_400)),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// What `read` makes of `sub` within a minute (a hang detector, never a budget), with `sub`
/// handed back.
#[cfg(feature = "retention")]
fn within_a_minute<T: Send + 'static>(
    sub: ShardedSubscription,
    read: impl FnOnce(&ShardedSubscription) -> T + Send + 'static,
) -> (ShardedSubscription, T) {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let got = read(&sub);
        let _ = tx.send((sub, got));
    });
    rx.recv_timeout(Duration::from_secs(60))
        .expect("the fan-in did not answer within a minute")
}

/// A SHARD'S GAP NOTICE REACHES THE FAN-IN (R4's addendum, A9). Shard 1's log gave up its two
/// oldest of five mails past the mail class's bytes, then was reopened, so its tail from 0
/// is owed the range `0..2` with no count. A fan-in that reads deliveries alone is still
/// handed the notice, tagged with its shard, by `take_gaps`, once; one that reads events
/// is told it before the three held mails it is then delivered. NC: forwarders that read
/// deliveries alone (`Subscription::recv`) hand back no notice.
#[cfg(feature = "retention")]
#[test]
fn a_shards_gap_notice_reaches_the_fan_in_before_its_records() {
    use astream_broker::{BrokerLog, Gap, ShardedEvent};
    let _serial = serial();
    let (_tmp, dir) = fresh_dir("gap");
    let logs = dir.join("logs");
    let socks = dir.join("socks");
    drop(ShardedBroker::open(&logs, 2).unwrap());
    {
        let mut log = BrokerLog::open(logs.join("shard-1.log")).unwrap();
        log.set_retention(gap_rules()).unwrap();
        let subjects = ["/f/F/in/n1/from/a"; 5]
            .into_iter()
            .chain(["/f/F/pub/n1/s1/ev"; 3]);
        for (seq, subject) in subjects.enumerate() {
            log.publish(1, seq as u64 + 1, subject.into(), b"body".to_vec())
                .unwrap();
        }
        let tick = log.retain_by_rules(1_800_000_000_000).unwrap();
        assert_eq!((tick.base, tick.carried), (6, 3));
    }
    let b = ShardedBroker::open(&logs, 2).unwrap();
    let _h = b.serve(&socks).unwrap();
    let told = Gap {
        from: 0,
        to: 2,
        records: None,
    };
    let mail = |offset: u64| {
        (
            1usize,
            offset,
            "/f/F/in/n1/from/a".to_string(),
            b"body".to_vec(),
        )
    };

    let sub = ShardedSubscription::subscribe_all(&socks, 2, 0, "/f/F/in/>").unwrap();
    let (sub, got) = within_a_minute(sub, |sub| {
        (0..3).map(|_| sub.recv().unwrap()).collect::<Vec<_>>()
    });
    assert_eq!(got, vec![Some(mail(2)), Some(mail(3)), Some(mail(4))]);
    assert_eq!(sub.take_gaps(), vec![(1, told)], "the notice a read passed");
    assert_eq!(sub.take_gaps(), vec![], "handed back once");
    drop(sub);

    let sub = ShardedSubscription::subscribe_all(&socks, 2, 0, "/f/F/in/>").unwrap();
    let (sub, got) = within_a_minute(sub, |sub| {
        (0..4)
            .map(|_| sub.recv_event().unwrap())
            .collect::<Vec<_>>()
    });
    assert_eq!(
        got,
        vec![
            Some(ShardedEvent::Gap {
                shard: 1,
                gap: told
            }),
            Some(ShardedEvent::Delivery(mail(2))),
            Some(ShardedEvent::Delivery(mail(3))),
            Some(ShardedEvent::Delivery(mail(4))),
        ]
    );
    assert_eq!(sub.take_gaps(), vec![(1, told)]);
}
