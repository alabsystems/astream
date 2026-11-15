// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A federation bridge by push: it parks on the source's tail, mirrors what the tail delivers
//! and commits the source group once per burst, with no timer on the path.

#![cfg(unix)]

use astream_broker::{
    Broker, BrokerHandle, Client, Durability, FederationBridge, FederationConfig,
    FederationEndpoint, FederationError, FederationReport, FederationRunner, SubjectRewrite,
    Transport,
};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver};
use std::thread::JoinHandle;
use std::time::Duration;

/// A hang detector, never a budget.
const HANG: Duration = Duration::from_secs(60);
/// Longer than this binary runs: a broker timer set to it never fires in a test.
const NEVER: Duration = Duration::from_secs(3600);

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Pair {
    dir: PathBuf,
    src: Broker,
    dst: Broker,
    src_handle: Option<BrokerHandle>,
    _dst_handle: BrokerHandle,
}

impl Pair {
    fn new(tag: &str) -> Self {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir = PathBuf::from(format!("/tmp/asfp-{tag}-{}-{n}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = Broker::open_with(dir.join("src.log"), Durability::Relaxed).unwrap();
        let dst = Broker::open_with(dir.join("dst.log"), Durability::Relaxed).unwrap();
        let src_handle = src.serve(dir.join("src.sock")).unwrap();
        let dst_handle = dst.serve(dir.join("dst.sock")).unwrap();
        Self {
            dir,
            src,
            dst,
            src_handle: Some(src_handle),
            _dst_handle: dst_handle,
        }
    }

    fn sock(&self, name: &str) -> String {
        self.dir.join(name).to_str().unwrap().to_string()
    }

    fn cfg(&self) -> FederationConfig {
        FederationConfig {
            source: FederationEndpoint::new(&self.sock("src.sock"), Transport::Unix),
            dest: FederationEndpoint::new(&self.sock("dst.sock"), Transport::Unix),
            group: "/g/fed/dst".to_string(),
            filter: "/f/pub/>".to_string(),
            carry: Vec::new(),
            producer_id: 77,
            rewrite: SubjectRewrite::passthrough(),
            relay: false,
        }
    }

    fn publisher(&self) -> Client<std::os::unix::net::UnixStream> {
        Client::connect(self.sock("src.sock")).unwrap()
    }

    fn src_head(&self) -> u64 {
        let mut c = self.publisher();
        let (_, (_, head)) = c.fetch(0, "/none", 0).unwrap();
        head
    }
}

impl Drop for Pair {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

type Running = JoinHandle<Result<(), FederationError>>;

/// The bridge on a thread of its own, with each burst's report on the receiver.
fn run(
    mut bridge: FederationBridge,
    max: usize,
) -> (
    Running,
    Receiver<FederationReport>,
    astream_broker::FederationBridgeCloser,
) {
    let closer = bridge.closer();
    let (tx, rx) = mpsc::channel();
    let running = std::thread::spawn(move || {
        bridge.run(max, &mut |report| {
            let _ = tx.send(report.clone());
        })
    });
    (running, rx, closer)
}

fn stop(running: Running, closer: &astream_broker::FederationBridgeCloser) {
    closer.close();
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(running.join().unwrap().map_err(|e| e.to_string()));
    });
    rx.recv_timeout(HANG)
        .expect("a closed bridge returns")
        .expect("a closed bridge returns Ok");
}

#[test]
fn a_record_reaches_the_destination_with_every_broker_timer_stopped() {
    let p = Pair::new("noclock");
    for broker in [&p.src, &p.dst] {
        broker.set_liveness_poll(NEVER);
        broker.set_idle_mark(NEVER);
    }
    let bridge = FederationBridge::open(p.cfg()).unwrap();
    let (running, rx, closer) = run(bridge, 256);

    // The tail has parked by the time it can only be woken: after the first caught-up mark.
    // Whether it has or not, nothing here but the publish's own wake can deliver the record.
    let mut publisher = p.publisher();
    publisher.publish(1, 1, "/f/pub/a", b"one").unwrap();
    let report = rx
        .recv_timeout(HANG)
        .expect("a burst with no timer running");
    assert_eq!((report.fetched, report.mirrored), (1, 1));

    let mut sub = Client::connect(p.sock("dst.sock"))
        .unwrap()
        .subscribe(0, "/f/pub/>")
        .unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"one".to_vec());

    // And again from a bridge that has been parked since.
    publisher.publish(1, 2, "/f/pub/a", b"two").unwrap();
    assert_eq!(rx.recv_timeout(HANG).unwrap().mirrored, 1);
    assert_eq!(sub.recv().unwrap().unwrap().2, b"two".to_vec());
    stop(running, &closer);
}

#[test]
fn a_burst_commits_the_source_group_once() {
    let p = Pair::new("burst");
    let mut publisher = p.publisher();
    for seq in 1..=10u64 {
        publisher.publish(1, seq, "/f/pub/a", b"x").unwrap();
    }
    let before = p.src_head();
    assert_eq!(before, 10);

    let (running, rx, closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    let report = rx.recv_timeout(HANG).unwrap();
    assert_eq!((report.fetched, report.mirrored), (10, 10));
    // A mark ended the burst at `next` 10; the commit is inclusive, so it names the last offset
    // scanned, 9, and the group resumes at 10, the first offset the burst did not scan.
    assert_eq!(report.committed_upto, Some(9));
    assert_eq!(p.src.group_start("/g/fed/dst"), 10);

    // One commit record on the source for those ten, and no report for that commit's own scan.
    publisher.publish(1, 11, "/f/pub/a", b"x").unwrap();
    let report = rx.recv_timeout(HANG).unwrap();
    assert_eq!(report.fetched, 1);
    assert_eq!(
        report.links[0].src_offset, 11,
        "offset 10 is the one commit"
    );
    stop(running, &closer);
    assert!(rx.try_recv().is_err(), "one report a burst");
}

#[test]
fn a_burst_past_the_cap_is_cut_and_commits_each_part() {
    let p = Pair::new("cap");
    let mut publisher = p.publisher();
    for seq in 1..=300u64 {
        publisher.publish(1, seq, "/f/pub/a", b"x").unwrap();
    }
    let (running, rx, closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    let first = rx.recv_timeout(HANG).unwrap();
    assert_eq!(first.mirrored, 256);
    // Cut at 256 records, offsets 0..=255: committed through 255, not 256, a record not mirrored.
    assert_eq!(first.committed_upto, Some(255));
    let second = rx.recv_timeout(HANG).unwrap();
    assert_eq!(second.mirrored, 44);
    // Through 299, the last record, or 300, the first burst's commit, if the tail scanned it.
    assert!(second.committed_upto.unwrap() >= 299);
    stop(running, &closer);
    assert_eq!(p.src_head(), 302, "the 300 records and two commits");
}

#[test]
fn a_restarted_bridge_resumes_from_its_group_with_nothing_mirrored_twice() {
    let p = Pair::new("resume");
    let mut publisher = p.publisher();
    publisher.publish(1, 1, "/f/pub/a", b"one").unwrap();
    let (running, rx, closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    assert_eq!(rx.recv_timeout(HANG).unwrap().mirrored, 1);
    stop(running, &closer);

    publisher.publish(1, 2, "/f/pub/a", b"two").unwrap();
    publisher.publish(1, 3, "/f/pub/a", b"three").unwrap();
    let (running, rx, closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    let report = rx.recv_timeout(HANG).unwrap();
    assert_eq!((report.fetched, report.deduped), (2, 0));
    stop(running, &closer);
}

/// Every record `dst` holds under `filter`, as (subject, body), in offset order.
fn held(p: &Pair, filter: &str) -> Vec<(String, Vec<u8>)> {
    let mut c = Client::connect(p.sock("dst.sock")).unwrap();
    let (records, _) = c.fetch(0, filter, 256).unwrap();
    records.into_iter().map(|(_, s, b)| (s, b)).collect()
}

/// One group following two lanes: `/f/pub/a` and `/f/pub/b` interleaved, with `/f/pub/c` beside
/// them, which it scans and does not carry.
fn interleaved(p: &Pair, seq: &mut u64, round: &str) {
    let mut publisher = p.publisher();
    for lane in ["b", "a", "c", "b"] {
        *seq += 1;
        let body = format!("{round}{lane}{seq}");
        publisher
            .publish(1, *seq, &format!("/f/pub/{lane}"), body.as_bytes())
            .unwrap();
    }
}

fn two_lanes(p: &Pair) -> FederationConfig {
    FederationConfig {
        carry: vec!["/f/pub/a".to_string(), "/f/pub/b".to_string()],
        ..p.cfg()
    }
}

/// A bridge that follows one group over two lanes carries each record of either lane once and
/// none of the third the group scans, by poll and by push, and across a restart. THE NEGATIVE
/// CONTROL is `two_bridges_on_one_group_strand_a_record_of_the_lane_that_commits_second`.
#[test]
fn one_group_over_two_lanes_carries_each_record_of_either_once() {
    let p = Pair::new("carry");
    let mut seq = 0;
    interleaved(&p, &mut seq, "poll");
    let mut bridge = FederationBridge::open(two_lanes(&p)).unwrap();
    let report = bridge.sync_once(256).unwrap();
    assert_eq!((report.fetched, report.mirrored, report.skipped), (4, 3, 1));
    assert_eq!(
        report.committed_upto,
        Some(3),
        "past the record it did not carry"
    );
    drop(bridge);

    let (running, rx, closer) = run(FederationBridge::open(two_lanes(&p)).unwrap(), 256);
    interleaved(&p, &mut seq, "push");
    let mut carried = 0;
    while carried < 3 {
        let report = rx.recv_timeout(HANG).expect("a burst");
        assert_eq!(report.deduped, 0, "nothing carried twice");
        carried += report.mirrored;
    }
    stop(running, &closer);
    let (running, rx, closer) = run(FederationBridge::open(two_lanes(&p)).unwrap(), 256);
    interleaved(&p, &mut seq, "again");
    let mut carried = 0;
    while carried < 3 {
        let report = rx.recv_timeout(HANG).expect("a burst after the restart");
        assert_eq!(report.deduped, 0, "the restart resends nothing");
        carried += report.mirrored;
    }
    stop(running, &closer);

    let bodies: Vec<String> = held(&p, "/f/pub/>")
        .into_iter()
        .map(|(_, b)| String::from_utf8(b).unwrap())
        .collect();
    let mut want = Vec::new();
    let mut n = 0;
    for round in ["poll", "push", "again"] {
        for lane in ["b", "a", "c", "b"] {
            n += 1;
            if lane != "c" {
                want.push(format!("{round}{lane}{n}"));
            }
        }
    }
    assert_eq!(
        bodies, want,
        "each carried record once, in order, and no `/f/pub/c`"
    );
}

/// THE NEGATIVE CONTROL: the same two lanes as two bridges on one group, one lane each. The
/// first commits past the second lane's record it scanned before its own, so the second, opening
/// on the group, starts past that record and never sends it.
#[test]
fn two_bridges_on_one_group_strand_a_record_of_the_lane_that_commits_second() {
    let p = Pair::new("strand");
    let mut seq = 0;
    interleaved(&p, &mut seq, "poll");
    let lane = |filter: &str| FederationConfig {
        filter: filter.to_string(),
        ..p.cfg()
    };
    let mut a = FederationBridge::open(lane("/f/pub/a")).unwrap();
    assert_eq!(a.sync_once(256).unwrap().committed_upto, Some(1));
    let mut b = FederationBridge::open(lane("/f/pub/b")).unwrap();
    let report = b.sync_once(256).unwrap();
    assert_eq!(report.mirrored, 1, "only the `b` after the commit");
    let bodies: Vec<Vec<u8>> = held(&p, "/f/pub/b").into_iter().map(|(_, b)| b).collect();
    assert_eq!(bodies, vec![b"pollb4".to_vec()], "`pollb1` is never sent");
}

/// A source whose producer changes (its key rotated) with a burst its old producer landed on the
/// destination and never committed at the source: the destination holds offsets 0 and 1 under
/// producer 77, the source group is still at 0, and the bridge now pushes under 78.
fn landed_uncommitted(p: &Pair) {
    let mut publisher = p.publisher();
    for seq in 0..3u64 {
        publisher
            .publish(1, seq + 1, "/f/pub/a", format!("r{seq}").as_bytes())
            .unwrap();
    }
    let mut dst = Client::connect(p.sock("dst.sock")).unwrap();
    for off in 0..2u64 {
        dst.publish(77, off, "/f/pub/a", format!("r{off}").as_bytes())
            .unwrap();
    }
}

fn rotated(p: &Pair) -> (FederationReport, Vec<Vec<u8>>) {
    let mut bridge = FederationBridge::open(FederationConfig {
        producer_id: 78,
        ..p.cfg()
    })
    .unwrap();
    let report = bridge.sync_once(256).unwrap();
    let bodies = held(p, "/f/pub/>").into_iter().map(|(_, b)| b).collect();
    (report, bodies)
}

/// A destination told that producer 78 continues 77 answers the rotated push's resend of what 77
/// landed from 77's records, and appends only the record 77 never sent. THE NEGATIVE CONTROL is
/// `without_the_lineage_a_rotated_mirror_appends_its_old_producers_burst_twice`.
#[test]
fn a_rotated_mirror_resends_its_old_producers_landed_burst_as_a_duplicate() {
    let p = Pair::new("lineage");
    landed_uncommitted(&p);
    p.dst.set_producer_lineage([(78, vec![77])]);
    let (report, bodies) = rotated(&p);
    assert_eq!((report.fetched, report.mirrored, report.deduped), (3, 3, 2));
    assert_eq!(bodies, vec![b"r0".to_vec(), b"r1".to_vec(), b"r2".to_vec()]);
    let mut dst = Client::connect(p.sock("dst.sock")).unwrap();
    assert_eq!(
        dst.publish(78, 7, "/f/pub/a", b"new").unwrap(),
        (3, false),
        "a sequence 77 never held is 78's own"
    );
}

/// THE NEGATIVE CONTROL: the same push with no lineage given appends 77's burst again.
#[test]
fn without_the_lineage_a_rotated_mirror_appends_its_old_producers_burst_twice() {
    let p = Pair::new("nolineage");
    landed_uncommitted(&p);
    let (report, bodies) = rotated(&p);
    assert_eq!((report.mirrored, report.deduped), (3, 0));
    assert_eq!(bodies.len(), 5, "r0 and r1 twice");
}

#[test]
fn a_carried_filter_outside_the_groups_filter_is_refused() {
    let p = Pair::new("outside");
    for carry in ["/f/other/>", "/f/>", "not a filter"] {
        let cfg = FederationConfig {
            carry: vec![carry.to_string()],
            ..p.cfg()
        };
        assert!(
            matches!(FederationBridge::open(cfg), Err(FederationError::Config(_))),
            "{carry}"
        );
    }
}

/// A bridge stopped right after a burst cut at its cap leaves its group committed through the
/// last record of that burst, so a restart mirrors the record at the cut. The first run's
/// `on_burst` panics once the commit is acked, which ends the run with no later burst committing
/// past the cut, however the tail's events arrive.
#[test]
fn a_restart_after_a_burst_cut_at_its_cap_mirrors_the_record_at_the_cut() {
    let p = Pair::new("cut");
    let mut publisher = p.publisher();
    for seq in 1..=3u64 {
        publisher.publish(1, seq, "/f/pub/a", b"x").unwrap();
    }
    let mut bridge = FederationBridge::open(p.cfg()).unwrap();
    let (tx, rx) = mpsc::channel();
    let running = std::thread::spawn(move || {
        bridge.run(2, &mut |report| {
            let _ = tx.send(report.clone());
            panic!("the first burst ends this run");
        })
    });
    let first = rx.recv_timeout(HANG).expect("the first burst");
    assert_eq!((first.fetched, first.mirrored), (2, 2));
    assert_eq!(
        first.links.iter().map(|l| l.src_offset).collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(
        first.committed_upto,
        Some(1),
        "through the cut's last record"
    );
    let (done_tx, done_rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = done_tx.send(running.join().is_err());
    });
    assert!(
        done_rx.recv_timeout(HANG).expect("the run ends"),
        "it ended by the panic"
    );
    assert_eq!(
        p.src.group_start("/g/fed/dst"),
        2,
        "the group resumes at the cut"
    );

    // The commit is offset 3; one more record lands at 4.
    publisher.publish(1, 4, "/f/pub/a", b"x").unwrap();
    let (running, rx, closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    let mut offsets = Vec::new();
    while offsets.last().is_none_or(|&o| o < 4) {
        let report = rx.recv_timeout(HANG).expect("a burst up to offset 4");
        offsets.extend(report.links.iter().map(|l| l.src_offset));
    }
    assert_eq!(
        offsets,
        [2, 4],
        "the record at the cut is mirrored after the restart"
    );
    stop(running, &closer);
}

/// `commit_before` is where the exclusive offset a reader scans next becomes the inclusive group
/// commit, so the group resumes exactly there: the store's convention, read back from the broker,
/// which the bound the bridge commits (`TlaPushEdge.Commit`) depends on. A `next` of 0 commits
/// nothing, where the group starts anyway.
#[test]
fn commit_before_has_the_group_resume_at_the_offset_it_names() {
    let p = Pair::new("before");
    let mut client = p.publisher();
    for n in 0..300u64 {
        client.publish(7, n + 1, "/f/x/a", b"x").unwrap();
    }
    for next in [1, 2, 256, 257] {
        let group = format!("/g/before/{next}");
        assert!(client.commit_before(&group, next).unwrap().is_some());
        assert_eq!(p.src.group_start(&group), next);
    }
    assert_eq!(client.commit_before("/g/before/zero", 0).unwrap(), None);
    assert_eq!(p.src.group_start("/g/before/zero"), 0);
    assert!(client.commit_before("/g/before/2", 1).unwrap().is_some());
    assert_eq!(
        p.src.group_start("/g/before/2"),
        2,
        "a lower commit moves nothing"
    );
}

#[test]
fn a_close_before_the_bridge_parks_still_ends_it() {
    let p = Pair::new("early");
    let mut bridge = FederationBridge::open(p.cfg()).unwrap();
    bridge.closer().close();
    bridge
        .run(256, &mut |_| panic!("a closed bridge mirrors nothing"))
        .unwrap();
}

#[test]
fn a_lost_source_ends_the_run_with_an_error() {
    let mut p = Pair::new("lost");
    let (running, _rx, _closer) = run(FederationBridge::open(p.cfg()).unwrap(), 256);
    // Stopped under the bridge, whether or not it has subscribed yet.
    drop(p.src_handle.take());
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(running.join().unwrap().is_err());
    });
    assert!(rx.recv_timeout(HANG).expect("the run ends"));
}

#[test]
fn a_source_silent_past_the_deadline_is_a_lost_connection() {
    let p = Pair::new("silent");
    // A broker that writes no idle mark looks, from the bridge, like one whose host lost power.
    p.src.set_idle_mark(NEVER);
    let mut bridge = FederationBridge::open(p.cfg()).unwrap();
    bridge.set_liveness_deadline(Duration::from_millis(50));
    let (running, _rx, _closer) = run(bridge, 256);
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(running.join().unwrap().is_err());
    });
    assert!(rx.recv_timeout(HANG).expect("the run ends"));
}

fn two_rule_runner(p: &Pair) -> FederationRunner {
    let rules = astream_broker::parse_federation_rules(
        "group=/g/fed/a filter=/f/pub/a/>\ngroup=/g/fed/b filter=/f/pub/b/>\n",
    )
    .unwrap();
    let cfg = p.cfg();
    FederationRunner::open(cfg.source, cfg.dest, 77, rules).unwrap()
}

#[test]
fn a_panic_in_on_burst_ends_the_other_rules_and_reaches_the_caller() {
    let p = Pair::new("panic");
    let mut runner = two_rule_runner(&p);
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            runner.run(&|_, _| panic!("a burst's callback panicked"))
        }));
        let _ = tx.send(outcome.is_err());
    });
    p.publisher().publish(1, 1, "/f/pub/a/x", b"one").unwrap();
    assert!(rx.recv_timeout(HANG).expect("the runner returns"));
}

#[test]
fn a_runner_runs_every_rule_by_push_until_closed() {
    let p = Pair::new("runner");
    let rules = astream_broker::parse_federation_rules(
        "group=/g/fed/a filter=/f/pub/a/>\ngroup=/g/fed/b filter=/f/pub/b/>\n",
    )
    .unwrap();
    let cfg = p.cfg();
    let mut runner = FederationRunner::open(cfg.source, cfg.dest, 77, rules).unwrap();
    let closer = runner.closer();
    let (tx, rx) = mpsc::channel();
    let tx = std::sync::Mutex::new(tx);
    let running = std::thread::spawn(move || {
        runner
            .run(&|group, report| {
                let _ = tx
                    .lock()
                    .unwrap()
                    .send((group.to_string(), report.mirrored));
            })
            .map_err(|e| e.to_string())
    });

    let mut publisher = p.publisher();
    publisher.publish(1, 1, "/f/pub/a/x", b"a").unwrap();
    publisher.publish(1, 2, "/f/pub/b/x", b"b").unwrap();
    let mut seen = vec![
        rx.recv_timeout(HANG).unwrap(),
        rx.recv_timeout(HANG).unwrap(),
    ];
    seen.sort();
    assert_eq!(
        seen,
        vec![("/g/fed/a".to_string(), 1), ("/g/fed/b".to_string(), 1)]
    );

    closer.close();
    let (done_tx, done_rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = done_tx.send(running.join().unwrap());
    });
    done_rx.recv_timeout(HANG).unwrap().unwrap();
}

#[test]
fn asb_federate_is_live_with_no_interval_and_refuses_the_old_flag() {
    use std::process::{Command, Stdio};
    let asb = env!("CARGO_BIN_EXE_asb");
    let p = Pair::new("cli");
    let (src, dst) = (p.sock("src.sock"), p.sock("dst.sock"));

    let refused = Command::new(asb)
        .args([
            "federate", &src, &dst, "--group", "/g/c", "--filter", "/f/>",
        ])
        .args(["--id", "9", "--interval-ms", "10"])
        .output()
        .unwrap();
    assert_eq!(refused.status.code(), Some(2));

    let mut child = Command::new(asb)
        .args([
            "federate", &src, &dst, "--group", "/g/c", "--filter", "/f/>",
        ])
        .args(["--id", "9"])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut publisher = p.publisher();
    publisher.publish(1, 1, "/f/pub/a", b"one").unwrap();

    let (seen_tx, seen_rx) = mpsc::channel();
    let dst_sock = dst.clone();
    std::thread::spawn(move || {
        let mut sub = Client::connect(dst_sock)
            .unwrap()
            .subscribe(0, "/f/pub/>")
            .unwrap();
        let _ = seen_tx.send(sub.recv().unwrap().unwrap().2);
    });
    let seen = seen_rx.recv_timeout(HANG);
    child.kill().unwrap();
    child.wait().unwrap();
    assert_eq!(seen.unwrap(), b"one".to_vec());
}
