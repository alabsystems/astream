//! Claim `broker.will-fires-exactly-once` (fabric R5): a connection registers a LAST
//! WILL, the broker persists it as a hidden `/a/will` record and appends it as an
//! ordinary publish when that connection ends — deduped by its own producer key
//! (a graceful goodbye makes it a no-op) and FENCED by any later record from the same
//! producer (a reconnected producer suppresses its previous incarnation structurally).
//! Every will the log still holds is re-fired on broker open, which is what closes the
//! "the broker died too" gap.
//!
//! Every step synchronizes on a delivery or an ack — no sleeps.
#![cfg(unix)]

use astream_broker::store::BrokerLog;
use astream_broker::{Broker, BrokerHandle, Client};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// The design's incarnation rule: a will publishes at the RESERVED TOP of its
/// incarnation's sequence space, so no ordinary publish of that incarnation can
/// collide with it and every sequence of the next incarnation is above it.
fn will_seq(inc: u64) -> u64 {
    (inc << 32) | 0xFFFF_FFFF
}
fn live_seq(inc: u64, n: u64) -> u64 {
    (inc << 32) | n
}

const PRESENCE: &str = "/f/F/pub/n1/node/presence";
const PID: u64 = 7;

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/aswill_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/aswill_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    p
}

impl Drop for Paths {
    /// Remove the socket, the log and every `<path>.*` sidecar beside them (the
    /// broker's `.hw`, `.base`, `.replica`, …) on success and on panic alike. A test
    /// binds its `Paths` before serving on them, so this runs after the broker is gone.
    fn drop(&mut self) {
        remove_with_sidecars(&self.sock);
        remove_with_sidecars(&self.log);
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

fn serve(p: &Paths) -> (Broker, BrokerHandle) {
    let broker = Broker::open(&p.log).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// A subscriber opened BEFORE anything is published, so every assertion is on the
/// exact sequence of deliveries — never on a timeout.
fn watch(sock: &str) -> astream_broker::Subscription {
    Client::connect(sock).unwrap().subscribe(0, "/f/>").unwrap()
}

/// The core: a will registered, acknowledged, and fired when the connection drops —
/// and the NEXT record on the log is the sentinel, so nothing crept in between.
#[test]
fn a_dropped_connection_publishes_its_will_and_nothing_else() {
    let p = fresh("basic");
    let (_b, _h) = serve(&p);
    let mut sub = watch(&p.sock);

    {
        let mut c = Client::connect(&p.sock).unwrap();
        let (next, head) = c
            .will(PID, will_seq(1), PRESENCE, b"v=1 state=gone inc=1")
            .unwrap();
        assert_eq!((next, head), (1, 1), "the /a/will record consumed offset 0");
        c.publish(PID, live_seq(1, 1), PRESENCE, b"v=1 state=live inc=1")
            .unwrap();
    } // dropped with no goodbye

    assert_eq!(
        sub.recv().unwrap().unwrap().2,
        b"v=1 state=live inc=1".to_vec()
    );
    let (will_off, subject, body) = sub.recv().unwrap().unwrap();
    assert_eq!(subject, PRESENCE);
    assert_eq!(body, b"v=1 state=gone inc=1".to_vec());

    // A sentinel from a THIRD connection is the very next record: no intervening one.
    let mut third = Client::connect(&p.sock).unwrap();
    let (sentinel_off, _) = third.publish(99, 1, "/f/F/sentinel", b"s").unwrap();
    assert_eq!(sentinel_off, will_off + 1);
    assert_eq!(sub.recv().unwrap().unwrap().0, sentinel_off);
}

/// EXACTLY-ONCE GOODBYE: a producer that publishes the will's reserved key itself
/// before closing makes the will a no-op — it dedups, appending nothing.
#[test]
fn a_graceful_goodbye_makes_the_will_a_no_op() {
    let p = fresh("goodbye");
    let (_b, _h) = serve(&p);
    let mut sub = watch(&p.sock);

    let goodbye_off = {
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"gone by will").unwrap();
        // The producer says goodbye ITSELF, under the will's own reserved key.
        c.publish(PID, will_seq(1), PRESENCE, b"gone by hand")
            .unwrap()
            .0
    };

    let (off, _, body) = sub.recv().unwrap().unwrap();
    assert_eq!((off, body), (goodbye_off, b"gone by hand".to_vec()));

    // The sentinel is the very NEXT record: the will appended nothing.
    let mut third = Client::connect(&p.sock).unwrap();
    let (sentinel_off, _) = third.publish(99, 1, "/f/F/sentinel", b"s").unwrap();
    assert_eq!(sentinel_off, goodbye_off + 1);
    assert_eq!(sub.recv().unwrap().unwrap().0, sentinel_off);
}

/// THE FENCE: a producer that reconnects as incarnation 2 and publishes `live inc=2`
/// suppresses incarnation 1's will structurally — when the half-open old connection
/// finally dies it appends nothing, and the retained value stays `live inc=2`.
#[test]
fn a_later_record_from_the_same_producer_fences_the_will() {
    let p = fresh("fence");
    let (_b, _h) = serve(&p);
    let mut sub = watch(&p.sock);

    let old = {
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"v=1 state=gone inc=1")
            .unwrap();
        c.publish(PID, live_seq(1, 1), PRESENCE, b"v=1 state=live inc=1")
            .unwrap();
        c
    };
    assert_eq!(
        sub.recv().unwrap().unwrap().2,
        b"v=1 state=live inc=1".to_vec()
    );

    // Incarnation 2 reconnects and publishes above incarnation 1's reserved top.
    let mut fresh_conn = Client::connect(&p.sock).unwrap();
    let (live2_off, _) = fresh_conn
        .publish(PID, live_seq(2, 1), PRESENCE, b"v=1 state=live inc=2")
        .unwrap();
    assert!(live_seq(2, 1) > will_seq(1), "the incarnation rule holds");
    assert_eq!(sub.recv().unwrap().unwrap().0, live2_off);

    drop(old); // the half-open incarnation-1 connection finally dies

    // Nothing was appended: the sentinel is the very next record.
    let (sentinel_off, _) = fresh_conn.publish(99, 1, "/f/F/sentinel", b"s").unwrap();
    assert_eq!(sentinel_off, live2_off + 1);
    assert_eq!(sub.recv().unwrap().unwrap().0, sentinel_off);

    // The retained value is still `live inc=2`, never a stale `gone`.
    let (page, _) = fresh_conn.last(PRESENCE, "", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].2, b"v=1 state=live inc=2".to_vec());
}

/// One per connection: a second `Will` REPLACES the first, so only the later one
/// fires.
#[test]
fn a_second_will_replaces_the_first() {
    let p = fresh("replace");
    let (_b, _h) = serve(&p);
    let mut sub = watch(&p.sock);
    {
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"first").unwrap();
        c.will(PID, will_seq(2), PRESENCE, b"second").unwrap();
    }
    let (off, _, body) = sub.recv().unwrap().unwrap();
    assert_eq!(body, b"second".to_vec(), "only the later will fired");
    let mut third = Client::connect(&p.sock).unwrap();
    assert_eq!(
        third.publish(99, 1, "/f/F/sentinel", b"s").unwrap().0,
        off + 1,
        "the replaced will appended nothing"
    );
}

/// REPLACEMENT IS DURABLE, because it is scoped to ONE producer id. "One per
/// connection, a second replaces" lived only in the connection thread's memory: the
/// superseded `/a/will` record stayed on the log, and `pending_wills` re-keys by
/// PRODUCER, not by connection. So two wills on one connection under DIFFERENT producer
/// ids left two live entries, and the next broker open fired the one the connection had
/// explicitly retracted — a goodbye the client took back, published for a producer whose
/// high water is below the will's reserved-top sequence, so nothing fenced it and
/// nothing deduped it. A second producer id on one connection is refused instead, which
/// makes the durable rule and the in-memory rule the same rule.
#[test]
fn a_second_will_under_a_different_producer_id_is_refused() {
    let p = fresh("twopid");
    let sock2 = format!("{}.2", p.sock);
    const A: &str = "/f/F/pub/a/node/presence";
    const B: &str = "/f/F/pub/b/node/presence";
    {
        let (_b, mut h) = serve(&p);
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(1, will_seq(1), A, b"gone A").unwrap();
        let e = c.will(2, will_seq(1), B, b"gone B").unwrap_err();
        assert!(
            e.to_string()
                .contains("already holds a will for producer 1"),
            "{e}"
        );
        // The connection survives the refusal, and REPLACEMENT under the SAME id still
        // works — that is the rule the claim states.
        c.will(1, will_seq(2), A, b"gone A2").unwrap();
        c.publish(1, live_seq(1, 1), A, b"live A").unwrap();
        c.publish(2, live_seq(1, 1), B, b"live B").unwrap();
        drop(c);
        // Only the will this connection actually held fired, and only its later form.
        let mut r = Client::connect(&p.sock).unwrap();
        assert_eq!(r.last(A, "", 8).unwrap().0[0].2, b"gone A2".to_vec());
        assert_eq!(r.last(B, "", 8).unwrap().0[0].2, b"live B".to_vec());
        drop(r);
        h.shutdown();
    }
    // AND ACROSS THE OPEN: the retracted will is not on the log to be re-fired, so B
    // stays live and A stays at the will that really was registered.
    let b2 = Broker::open(&p.log).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut r = Client::connect(&sock2).unwrap();
    assert_eq!(r.last(A, "", 8).unwrap().0[0].2, b"gone A2".to_vec());
    assert_eq!(
        r.last(B, "", 8).unwrap().0[0].2,
        b"live B".to_vec(),
        "a will the connection replaced fired on the next open"
    );
}

/// A FOLLOWER'S RESTART FIRES NOTHING. Re-firing on open is the presence epoch that
/// closes "the broker died too" — for a broker that OWNS its log. A replication target
/// must be outside that rule: the leader ships every committed record, hidden `/a/will`
/// records included, so a follower's log holds the LEADER's wills. Firing one here
/// appends, at this follower's own next offset, a record the leader does not have — a
/// forged death notice for a node that is still live, a log that is no longer an
/// identical prefix of the leader's, and, at the leader's next ship to that offset, a
/// `Diverged` refusal that fences the link for good, so every subsequent leader publish
/// is `not replicated to quorum` and the cluster is permanently write-unavailable.
///
/// Neither guard the will path has could catch it: the incarnation rule puts a will at
/// the RESERVED TOP of its sequence space, so the producer's high water is always below
/// it and the fence never fires; and the leader has not fired the will either — the node
/// is alive — so dedup has nothing to match.
#[test]
fn a_follower_restart_does_not_fire_the_leaders_wills() {
    let p = fresh("follower");
    let flog = p.log.clone();
    let llog = format!("{}.leader", p.log);
    let lsock = p.sock.clone();
    let _ = std::fs::remove_file(&llog);
    const PRESENCE_N1: &str = "/f/F/pub/n1/node/presence";

    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&lsock).unwrap();

    // A node registers its will on the leader and publishes `live`. Both records — the
    // hidden /a/will at 0 and the live row at 1 — are shipped to the follower.
    let mut node = Client::connect(&lsock).unwrap();
    node.will(PID, will_seq(1), PRESENCE_N1, b"state=gone inc=1")
        .unwrap();
    assert_eq!(
        node.publish(PID, live_seq(1, 1), PRESENCE_N1, b"state=live inc=1")
            .unwrap(),
        (1, false)
    );
    assert_eq!((leader.head(), follower.head()), (2, 2));

    // The follower is restarted for maintenance, on its own INTACT log — the supported
    // flow, and the one the audit reproduced.
    drop(follower);
    fh.shutdown();
    // A BARRIER AGAINST THE WRITER THREAD, before any assertion about what the restart
    // did NOT append. `Broker::open` fires pending wills ASYNCHRONOUSLY: it enqueues on
    // the writer's FIFO and returns, so reading the head straight after the open races
    // the writer's first `recv_timeout` and passes whether or not the replica guard is
    // in place. Opening the follower and DROPPING it is the happens-before — a `Broker`
    // that was never served stops and JOINS its writer on drop, and the writer drains
    // what is already queued before it exits. What the log holds afterwards is then a
    // statement about the guard, not about which thread was scheduled first.
    drop(Broker::open(&flog).unwrap());
    assert_eq!(
        BrokerLog::open(&flog).unwrap().head().0,
        2,
        "the follower appended a record of its OWN: the leader's will fired here"
    );
    let f2 = Broker::open(&flog).unwrap();
    let mut fh2 = f2.serve_tcp(&faddr).unwrap();

    // The node is still connected and still live: nothing may say otherwise.
    let (page, _) = Client::connect_tcp(&faddr)
        .unwrap()
        .last(PRESENCE_N1, "", 8)
        .unwrap();
    assert_eq!(
        page[0].2,
        b"state=live inc=1".to_vec(),
        "the follower reports a live node as gone"
    );

    // And the leader can still write: the link was never diverged.
    assert_eq!(
        node.publish(PID, live_seq(1, 2), PRESENCE_N1, b"v2")
            .unwrap(),
        (2, false)
    );
    assert_eq!(
        node.publish(PID, live_seq(1, 3), PRESENCE_N1, b"v3")
            .unwrap(),
        (3, false)
    );
    assert_eq!(f2.head(), 4, "the follower stayed in the quorum");

    drop(node);
    lh.shutdown();
    fh2.shutdown();
}

/// A will on a hidden subject is refused — a client cannot make the broker write one
/// of its own records for it.
#[test]
fn a_will_on_a_hidden_subject_is_refused() {
    let p = fresh("hidden");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    for hidden in ["/a/commit", "/a/will", "/a/bind"] {
        let e = c.will(PID, 1, hidden, b"x").unwrap_err();
        assert!(e.to_string().contains("reserved subject"), "{hidden}: {e}");
    }
    // The connection survives the refusal, and a legal will is still accepted.
    assert!(c.will(PID, will_seq(1), PRESENCE, b"gone").is_ok());
}

/// THE BROKER DIED TOO — the gap the design review flagged. A will is registered and
/// the broker's log is SNAPSHOT while it is still running, so the snapshot is exactly
/// the state a broker that died leaves behind: a persisted `/a/will` record whose will
/// has not fired and no connection thread left to fire it. Opening a broker on that
/// snapshot fires it EXACTLY ONCE, and opening again fires nothing more because the
/// first firing is on the log and dedups.
///
/// (The snapshot is taken with the broker live rather than after a clean shutdown,
/// because a clean shutdown force-closes connections and their wills fire on the way
/// out — which would make this test pass without ever exercising the open path.)
#[test]
fn a_will_survives_the_broker_and_fires_exactly_once_on_open() {
    let p = fresh("restart");
    let dead = format!("{}.dead", p.log);
    let sock2 = format!("{}.2", p.sock);
    let sock3 = format!("{}.3", p.sock);
    let _ = std::fs::remove_file(&dead);

    {
        let b = Broker::open(&p.log).unwrap();
        let mut h = b.serve(&p.sock).unwrap();
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"v=1 state=gone inc=1")
            .unwrap();
        c.publish(PID, live_seq(1, 1), PRESENCE, b"v=1 state=live inc=1")
            .unwrap();
        // Every acked record is fsync'd, so the copy IS the durable state.
        std::fs::copy(&p.log, &dead).unwrap();
        drop(c);
        h.shutdown();
    }
    assert_eq!(
        BrokerLog::open(&dead).unwrap().head().0,
        2,
        "the snapshot holds the /a/will record and the live row, and no goodbye"
    );

    // Open on the snapshot: the persisted will fires, exactly once.
    let sentinel_off = {
        let b2 = Broker::open(&dead).unwrap();
        let mut h2 = b2.serve(&sock2).unwrap();
        let mut c2 = Client::connect(&sock2).unwrap();
        let mut sub = Client::connect(&sock2)
            .unwrap()
            .subscribe(0, "/f/>")
            .unwrap();
        assert_eq!(
            sub.recv().unwrap().unwrap().2,
            b"v=1 state=live inc=1".to_vec()
        );
        let (gone_off, subject, body) = sub.recv().unwrap().unwrap();
        assert_eq!(subject, PRESENCE);
        assert_eq!(body, b"v=1 state=gone inc=1".to_vec(), "fired on open");
        let (sentinel_off, _) = c2.publish(99, 1, "/f/F/sentinel", b"s").unwrap();
        assert_eq!(
            sentinel_off,
            gone_off + 1,
            "exactly one record was appended"
        );
        drop(sub);
        drop(c2);
        h2.shutdown();
        sentinel_off
    };

    // Open AGAIN on the same log: a will that already fired never fires twice.
    let b3 = Broker::open(&dead).unwrap();
    let _h3 = b3.serve(&sock3).unwrap();
    let mut c3 = Client::connect(&sock3).unwrap();
    assert_eq!(
        c3.publish(98, 1, "/f/F/sentinel2", b"s2").unwrap().0,
        sentinel_off + 1,
        "the second open appended nothing of its own"
    );
}

/// A producer that came back and published `live inc+1` before the broker died
/// SUPERSEDES the will the next open would otherwise fire — the fence works across a
/// restart too, with no reader-side fold.
#[test]
fn a_reconnected_producer_supersedes_its_persisted_will_across_a_restart() {
    let p = fresh("supersede");
    let dead = format!("{}.dead", p.log);
    let sock2 = format!("{}.2", p.sock);
    let _ = std::fs::remove_file(&dead);
    {
        let b = Broker::open(&p.log).unwrap();
        let mut h = b.serve(&p.sock).unwrap();
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"gone inc=1").unwrap();
        c.publish(PID, live_seq(1, 1), PRESENCE, b"live inc=1")
            .unwrap();
        c.publish(PID, live_seq(2, 1), PRESENCE, b"live inc=2")
            .unwrap();
        std::fs::copy(&p.log, &dead).unwrap();
        drop(c);
        h.shutdown();
    }
    let b2 = Broker::open(&dead).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut c2 = Client::connect(&sock2).unwrap();
    // A BARRIER AGAINST THE WRITER THREAD. The open-time firing is enqueued on the
    // writer's FIFO before `open` returns and appends (if at all) LATER, on that
    // thread; a `last` issued straight after the open races it and reads `head = 3`
    // whether or not the fence held. This sentinel goes on the SAME queue, behind the
    // firing, so its ack means the writer has already processed the firing — and its
    // offset is where the firing would have landed.
    let (sentinel, _) = c2.publish(98, 1, "/f/F/sentinel", b"s").unwrap();
    assert_eq!(sentinel, 3, "the fenced will appended nothing on open");
    let (page, (_, head)) = c2.last(PRESENCE, "", 8).unwrap();
    assert_eq!(head, 4, "the sentinel is the only record the open added");
    assert_eq!(page[0].2, b"live inc=2".to_vec(), "still live, never gone");
}

/// The store's own rules, directly: the fence compares against the producer's high
/// water over VISIBLE records only, and `pending_wills` keeps the last will per
/// producer.
///
/// Both rules need a log that actually HOLDS wills, which `stage_will_register` (crate
/// private) will only put there through the `Will` verb — so the shape is built over
/// the wire and then read back with `BrokerLog` directly, off a copy taken before the
/// connection ends and the wills fire. Reading it back through `BrokerLog::open` is
/// also the path that matters here: the high water and the pending set the open-time
/// firing consults are the ones the OPEN rebuilds from the records.
#[test]
fn the_fence_and_the_pending_set_are_the_stores_own_rules() {
    let p = fresh("store");
    let snap = format!("{}.snap", p.log);
    let _ = std::fs::remove_file(&snap);
    {
        let (b, mut h) = serve(&p);
        let mut c = Client::connect(&p.sock).unwrap();
        // TWO wills under ONE producer, on one connection: the second replaces the
        // first, and both `/a/will` records stay on the log (nothing tombstones the
        // one that was replaced).
        c.will(PID, will_seq(1), PRESENCE, b"gone inc=1").unwrap();
        c.will(PID, will_seq(2), PRESENCE, b"gone inc=2").unwrap();
        assert_eq!(b.head(), 2, "two hidden /a/will records and nothing else");
        std::fs::copy(&p.log, &snap).unwrap();
        drop(c); // the will fires here — after the copy
        h.shutdown();
    }
    let mut log = BrokerLog::open(&snap).unwrap();
    // A will record does NOT raise the producer's high water: it is hidden, so
    // registering a will can never fence the will itself — not even the SECOND will of
    // a producer whose first registration sits above it on the log. (Both wills here
    // carry sequences at the reserved top of their incarnation, so a `/a/will` counted
    // into the high water would be seen at once by the assertions below.)
    assert_eq!(log.producer_high_water(PID), None);
    // `pending_wills` keeps the LAST will per producer, not both.
    let pending = log.pending_wills();
    assert_eq!(pending.len(), 1, "one will per producer, the latest");
    assert_eq!(pending[0].producer_id, PID);
    assert_eq!(pending[0].producer_seq, will_seq(2));
    assert_eq!(pending[0].subject, PRESENCE);
    assert_eq!(pending[0].body, b"gone inc=2".to_vec());
    // And the high water itself is monotone over visible records.
    log.publish(PID, 5, "/f/F/x".into(), b"a".to_vec()).unwrap();
    assert_eq!(log.producer_high_water(PID), Some(5));
    log.publish(PID, 3, "/f/F/x".into(), b"b".to_vec()).unwrap();
    assert_eq!(log.producer_high_water(PID), Some(5), "monotone");
}

/// With the `cap` feature, a will is authorized exactly as the publish it will become:
/// outside the grant, or under a producer id the grant's principal does not derive, it
/// is refused — so a connection cannot arm a publish it could not make itself.
#[cfg(feature = "cap")]
#[test]
fn a_will_is_authorized_exactly_as_the_publish_it_becomes() {
    use astream_cap::{mint, producer_id_of};
    let p = fresh("cap");
    let secret = b"fabric-broker-secret";
    let broker = Broker::open_guarded(&p.log, secret.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();
    let cap = mint(secret, "rw,p=n-1:/f/F/pub/n-1/>").unwrap();
    let pid = producer_id_of("n-1");

    let mut c = Client::connect(&p.sock).unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    // Outside the grant.
    let e = c
        .will(pid, will_seq(1), "/f/F/pub/n-2/node/presence", b"gone")
        .unwrap_err();
    assert!(e.to_string().contains("unauthorized"), "{e}");
    // Under a FOREIGN producer id, inside the grant.
    let e = c
        .will(
            producer_id_of("n-2"),
            will_seq(1),
            "/f/F/pub/n-1/node/presence",
            b"gone",
        )
        .unwrap_err();
    assert!(e.to_string().contains("unauthorized"), "{e}");
    // In scope and under its own id: accepted, and it fires on close.
    let reader = mint(secret, "ro:/f/F/>").unwrap();
    let mut rc = Client::connect(&p.sock).unwrap();
    rc.attach(&reader.filter, &reader.tag).unwrap();
    let mut sub = rc.subscribe(0, "/f/F/pub/n-1/>").unwrap();
    c.will(pid, will_seq(1), "/f/F/pub/n-1/node/presence", b"gone")
        .unwrap();
    drop(c);
    assert_eq!(sub.recv().unwrap().unwrap().2, b"gone".to_vec());
}
