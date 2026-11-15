// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Origin-keyed relay: a record keeps its origin's `(producer_id, producer_seq)` on every broker,
//! so bridges may form any graph. Each broker appends it once and each bridge's echo stops at the
//! first broker that holds it. A mirror's key names its path, which is why a mirror on a cycle
//! never stops. A relayed record answers for itself: a broker checks its origin's signature before
//! it appends it. And a subject that keeps only its `Last` row takes the origin's highest sequence,
//! whichever path brought what first. Every broker and bridge here speaks over socketpairs the
//! broker adopted (`serve_stream`), as an embedder's own transport does.

#![cfg(all(unix, feature = "relay", feature = "stream"))]

use astream_broker::proto::{
    ERR_ORIGIN_REFUSED, ERR_ORIGIN_UNKNOWN, ERR_RELAY_NOT_READY, ERR_SUBJECT_BOUND,
    ERR_UNAUTHORIZED,
};
use astream_broker::{
    broker_refusal, connect_stream, identity_principal, origin, AnyClient, Broker, Durability,
    FederationBridge, FederationBridgeCloser, FederationConfig, FederationEndpoint,
    FederationError, FederationReport, Pipelined, Retention, Rule, Seated, StreamDial, StreamLink,
    SubjectRewrite, ACK_SEQ_BASE, HELD_BYTES,
};
use astream_cap::{mint, producer_id_of, Capability};
use std::collections::BTreeMap;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// A hang detector, never a budget.
const HANG: Duration = Duration::from_secs(60);
const SECRET: &[u8] = b"relay-test-secret-of-some-length";
/// One origin's bound on distinct subjects (`MAX_SUBJECTS_PER_PRODUCER` in the store).
const SUBJECT_BUDGET: u64 = 4096;

/// An origin: a node's signing key, and what the key makes of it.
#[derive(Clone)]
struct Origin {
    seed: [u8; 32],
    key: [u8; 32],
    principal: String,
    id: u64,
}

fn origin(n: u8) -> Origin {
    let seed = [n; 32];
    let key = origin::public_key(&seed);
    let principal = identity_principal(&key);
    let id = producer_id_of(&principal);
    Origin {
        seed,
        key,
        principal,
        id,
    }
}

/// Every test's nodes, whose keys each broker holds. `UNKNOWN` signs and is held by none.
const A: u8 = 1;
const B: u8 = 2;
const C: u8 = 3;
const D: u8 = 4;
const UNKNOWN: u8 = 9;
/// The node whose connections carry records: a bridge's, and a test's own.
const CARRIER: u8 = 8;

impl Origin {
    /// `/m/<principal>/<leaf>`.
    fn subject(&self, leaf: &str) -> String {
        format!("/m/{}/{leaf}", self.principal)
    }

    fn seal(&self, subject: &str, seq: u64, payload: &[u8]) -> Vec<u8> {
        origin::seal(&self.seed, subject, seq, payload)
    }

    /// Relay this origin's own signed row of `leaf` through `client`.
    fn relay(
        &self,
        client: &mut AnyClient,
        seq: u64,
        leaf: &str,
        payload: &[u8],
    ) -> std::io::Result<(u64, bool)> {
        let subject = self.subject(leaf);
        client.relay(self.id, seq, &subject, &self.seal(&subject, seq, payload))
    }
}

static NEXT: AtomicU64 = AtomicU64::new(0);

/// A socketpair `broker` adopts as `who`'s verified connection, and this test's client on the
/// other end: what an embedder does for each stream of its own authenticated transport.
fn adopted(broker: &Broker, who: &Origin) -> AnyClient {
    connect_stream(adopt(broker, who.key).unwrap()).0
}

fn adopt(broker: &Broker, peer: [u8; 32]) -> std::io::Result<Arc<dyn StreamLink>> {
    let (ours, theirs) = UnixStream::pair()?;
    drop(broker.serve_stream(Arc::new(theirs), peer)?);
    Ok(Arc::new(ours))
}

/// What a bridge dials: a fresh adopted stream, on each connection and each reconnect.
struct Adopting {
    broker: Arc<Broker>,
    peer: [u8; 32],
}

impl StreamDial for Adopting {
    fn dial(&self) -> std::io::Result<Arc<dyn StreamLink>> {
        adopt(&self.broker, self.peer)
    }
}

struct Net {
    dir: PathBuf,
    brokers: Vec<Arc<Broker>>,
    /// What a bridge attaches on its source: it reads records and commits its group there.
    source_caps: Vec<Capability>,
    /// What a bridge attaches on its destination: it carries records there, and nothing else.
    dest_caps: Vec<Capability>,
}

impl Net {
    fn new(tag: &str, n: usize) -> Self {
        Self::build(tag, n, false)
    }

    fn guarded(tag: &str, n: usize) -> Self {
        Self::build(tag, n, true)
    }

    fn build(tag: &str, n: usize, guarded: bool) -> Self {
        let k = NEXT.fetch_add(1, Ordering::Relaxed);
        let dir = PathBuf::from(format!("/tmp/asrl-{tag}-{}-{k}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut brokers = Vec::new();
        for i in 0..n {
            let log = dir.join(format!("{i}.log"));
            let broker = if guarded {
                Broker::open_guarded(log, SECRET.to_vec()).unwrap()
            } else {
                Broker::open_with(log, Durability::Relaxed).unwrap()
            };
            broker.set_origin_keys([A, B, C, D].map(|n| origin(n).key));
            brokers.push(Arc::new(broker));
        }
        let carrier = origin(CARRIER).principal;
        let (source_caps, dest_caps) = if guarded {
            (
                vec![
                    mint(SECRET, "ro:/m/>").unwrap(),
                    mint(SECRET, &format!("rw,p={carrier}:/g/relay/>")).unwrap(),
                ],
                vec![mint(SECRET, &format!("rw,relay,p={carrier}:/m/>")).unwrap()],
            )
        } else {
            (Vec::new(), Vec::new())
        };
        Self {
            dir,
            brokers,
            source_caps,
            dest_caps,
        }
    }

    /// A connection to broker `i`, adopted as the carrier's.
    fn client(&self, i: usize) -> AnyClient {
        adopted(&self.brokers[i], &origin(CARRIER))
    }

    /// One bridge's endpoint on broker `i`: each dial a fresh socketpair the broker adopts.
    fn endpoint(&self, i: usize, caps: &[Capability]) -> FederationEndpoint {
        let dial = Arc::new(Adopting {
            broker: Arc::clone(&self.brokers[i]),
            peer: origin(CARRIER).key,
        });
        FederationEndpoint::stream(&format!("broker-{i}"), dial).with_caps(caps.to_vec())
    }

    fn relay_cfg(&self, from: usize, to: usize) -> FederationConfig {
        FederationConfig {
            source: self.endpoint(from, &self.source_caps),
            dest: self.endpoint(to, &self.dest_caps),
            group: format!("/g/relay/{to}"),
            filter: "/m/>".to_string(),
            carry: Vec::new(),
            producer_id: 0,
            rewrite: SubjectRewrite::passthrough(),
            relay: true,
        }
    }

    /// What broker `i` holds of `/m/>`, as `subject -> [body…]` in log order.
    fn held(&self, i: usize, caps: Option<&Capability>) -> Vec<(u64, String, Vec<u8>)> {
        let mut client = self.client(i);
        if let Some(cap) = caps {
            client.attach(&cap.filter, &cap.tag).unwrap();
        }
        let mut out = Vec::new();
        let mut from = 0;
        loop {
            let (page, (next, head)) = client.fetch(from, "/m/>", 1024).unwrap();
            out.extend(page);
            if next >= head {
                return out;
            }
            from = next;
        }
    }
}

impl Drop for Net {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Running relay bridges, each burst's report on one channel.
struct Bridges {
    running: Vec<(
        FederationBridgeCloser,
        JoinHandle<Result<(), FederationError>>,
    )>,
    reports: Receiver<FederationReport>,
    tx: Sender<FederationReport>,
    total: FederationReport,
}

impl Bridges {
    fn start(net: &Net, edges: &[(usize, usize)]) -> Self {
        let (tx, reports) = mpsc::channel();
        let mut bridges = Self {
            running: Vec::new(),
            reports,
            tx,
            total: FederationReport::default(),
        };
        for &(from, to) in edges {
            bridges.add(net.relay_cfg(from, to));
        }
        bridges
    }

    fn add(&mut self, cfg: FederationConfig) {
        self.add_holding(cfg, None);
    }

    /// Add a bridge that holds a record its destination does not take the origin of while
    /// `seated` says so ([`FederationBridge::hold_while`]).
    fn add_holding(&mut self, cfg: FederationConfig, seated: Option<Seated>) {
        let mut bridge = FederationBridge::open(cfg).unwrap();
        if let Some(seated) = seated {
            bridge.hold_while(seated);
        }
        let closer = bridge.closer();
        let tx = self.tx.clone();
        self.running.push((
            closer,
            std::thread::spawn(move || {
                bridge.run(256, &mut |report| {
                    let _ = tx.send(report.clone());
                })
            }),
        ));
    }

    /// Read reports until `done` says the running totals are complete.
    fn until(&mut self, what: &str, done: impl Fn(&FederationReport) -> bool) {
        let deadline = Instant::now() + HANG;
        while !done(&self.total) {
            let left = deadline.saturating_duration_since(Instant::now());
            let report = self
                .reports
                .recv_timeout(left)
                .unwrap_or_else(|_| panic!("{what}: hung at {:?}", self.total));
            self.total.fetched += report.fetched;
            self.total.mirrored += report.mirrored;
            self.total.deduped += report.deduped;
            self.total.skipped += report.skipped;
            self.total.refused += report.refused;
            // A gauge and a position: the last report's, of a test's one bridge.
            self.total.held = report.held;
            self.total.committed_upto = report.committed_upto;
            self.total.links.extend(report.links);
        }
    }

    fn stop(self) -> FederationReport {
        for (closer, running) in self.running {
            closer.close();
            let (tx, rx) = mpsc::channel();
            std::thread::spawn(move || {
                let _ = tx.send(running.join().unwrap().map_err(|e| e.to_string()));
            });
            rx.recv_timeout(HANG)
                .expect("a closed bridge returns")
                .expect("a closed bridge returns Ok");
        }
        let mut total = self.total;
        while let Ok(report) = self.reports.try_recv() {
            total.fetched += report.fetched;
            total.mirrored += report.mirrored;
            total.deduped += report.deduped;
            total.skipped += report.skipped;
            total.refused += report.refused;
        }
        total
    }
}

/// Publish `n` signed records as `who` on broker `at`: `/m/<principal>/k<seq>`, payload
/// `<principal>:<seq>`.
fn publish_as(net: &Net, at: usize, who: &Origin, n: u64) {
    let mut client = net.client(at);
    for seq in 1..=n {
        let subject = who.subject(&format!("k{seq}"));
        let payload = format!("{}:{seq}", who.principal);
        client
            .publish(
                who.id,
                seq,
                &subject,
                &who.seal(&subject, seq, payload.as_bytes()),
            )
            .unwrap();
    }
}

/// Every broker holds each `(origin, seq)` exactly once, under its own subject and the origin's
/// own envelope, whichever order the paths brought them in, and delivers each under its ORIGINAL
/// key.
fn assert_each_broker_holds_each_once(net: &Net, origins: &[&Origin], n: u64) {
    for i in 0..net.brokers.len() {
        let mut seen = BTreeMap::new();
        for (_, subject, body) in net.held(i, None) {
            *seen.entry((subject, body)).or_insert(0u32) += 1;
        }
        assert_eq!(seen.len() as u64, origins.len() as u64 * n, "broker {i}");
        for who in origins {
            for seq in 1..=n {
                let subject = who.subject(&format!("k{seq}"));
                let payload = format!("{}:{seq}", who.principal);
                let key = (subject.clone(), who.seal(&subject, seq, payload.as_bytes()));
                assert_eq!(seen.get(&key), Some(&1), "broker {i} holds {subject} once");
            }
        }
        let mut client = net.client(i);
        assert!(client.origin_stamps().unwrap());
        let mut sub = client.subscribe(0, "/m/>").unwrap();
        for _ in 0..origins.len() as u64 * n {
            let (_, subject, _) = sub.recv().unwrap().unwrap();
            let owner = subject.split('/').nth(2).unwrap();
            let seq: u64 = subject.rsplit("/k").next().unwrap().parse().unwrap();
            assert_eq!(
                sub.last_origin(),
                Some((producer_id_of(owner), seq)),
                "broker {i} delivers {subject} under its original key"
            );
        }
    }
}

/// THE NEGATIVE CONTROL: the same three-node cycle with mirror bridges. Each hop gives the record
/// a new key, so nothing ever deduplicates and every lap appends again, for as long as it runs.
#[test]
fn a_mirror_on_a_three_node_cycle_echoes_for_as_long_as_it_runs() {
    let net = Net::new("echo", 3);
    let mut bridges: Vec<FederationBridge> = (0..3)
        .map(|i| {
            FederationBridge::open(FederationConfig {
                relay: false,
                producer_id: 100 + i as u64,
                ..net.relay_cfg(i, (i + 1) % 3)
            })
            .unwrap()
        })
        .collect();
    publish_as(&net, 0, &origin(A), 1);

    let mut held = net.held(0, None).len();
    assert_eq!(held, 1);
    for lap in 0..6 {
        for bridge in &mut bridges {
            let report = bridge.sync_once(256).unwrap();
            assert_eq!(report.deduped, 0, "a mirror's key is new on every hop");
        }
        let now = net.held(0, None).len();
        assert!(now > held, "lap {lap}: {now} is not more than {held}");
        held = now;
    }
    assert_eq!(held, 7, "the one record, and one echo a lap");
}

#[test]
fn a_relay_on_the_same_cycle_delivers_each_record_exactly_once() {
    const N: u64 = 200;
    let net = Net::new("cycle", 3);
    let edges = [(0, 1), (1, 2), (2, 0)];
    let mut bridges = Bridges::start(&net, &edges);
    let (a, c) = (origin(A), origin(C));
    publish_as(&net, 0, &a, N);
    publish_as(&net, 2, &c, N);
    let want = edges.len() * 2 * N as usize;
    bridges.until("the cycle", |t| t.fetched >= want);
    let total = bridges.stop();

    // Conservation: each bridge read each record once. Of those reads, each of the two brokers
    // that lacked a record appended it, and the one read that came home deduplicated.
    assert_eq!(total.fetched, want, "no bridge read a record twice");
    let appended = total.mirrored - total.deduped;
    assert_eq!(appended, 2 * 2 * N as usize, "each broker appended once");
    assert_eq!(total.deduped, 2 * N as usize, "each record came home once");
    assert_each_broker_holds_each_once(&net, &[&a, &c], N);
}

#[test]
fn a_relay_on_a_ring_with_chords_delivers_each_record_exactly_once() {
    const N: u64 = 100;
    let net = Net::new("chords", 4);
    // The ring 0-1-2-3-0 and the chords 0-2, 1-3, both ways on each.
    let mut edges = Vec::new();
    for (a, b) in [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3)] {
        edges.push((a, b));
        edges.push((b, a));
    }
    let mut bridges = Bridges::start(&net, &edges);
    let origins = [origin(A), origin(B), origin(C), origin(D)];
    std::thread::scope(|scope| {
        for (at, who) in origins.iter().enumerate() {
            let net = &net;
            scope.spawn(move || publish_as(net, at, who, N));
        }
    });
    let records = origins.len() * N as usize;
    let want = edges.len() * records;
    bridges.until("the chords", |t| t.fetched >= want);
    let total = bridges.stop();

    assert_eq!(total.fetched, want, "no bridge read a record twice");
    let appended = total.mirrored - total.deduped;
    assert_eq!(appended, 3 * records, "each broker appended once");
    assert_eq!(total.deduped, want - 3 * records);
    let refs: Vec<&Origin> = origins.iter().collect();
    assert_each_broker_holds_each_once(&net, &refs, N);
}

#[test]
fn a_relay_runs_on_a_guarded_cycle_writing_with_a_relay_grant_alone() {
    const N: u64 = 20;
    let net = Net::guarded("guard", 3);
    let edges = [(0, 1), (1, 2), (2, 0)];
    let mut bridges = Bridges::start(&net, &edges);
    let a = origin(A);
    let own = mint(SECRET, &format!("rw,p={0}:/m/{0}/>", a.principal)).unwrap();
    let mut client = adopted(&net.brokers[0], &a);
    client.attach(&own.filter, &own.tag).unwrap();
    for seq in 1..=N {
        let subject = a.subject(&format!("k{seq}"));
        client
            .publish(a.id, seq, &subject, &a.seal(&subject, seq, b"x"))
            .unwrap();
    }
    bridges.until("the guarded cycle", |t| t.fetched >= 3 * N as usize);
    let total = bridges.stop();
    assert_eq!(total.mirrored - total.deduped, 2 * N as usize);
    let reader = mint(SECRET, "ro:/m/>").unwrap();
    for i in 0..3 {
        assert_eq!(net.held(i, Some(&reader)).len() as u64, N, "broker {i}");
    }
}

fn refusal_code(e: &std::io::Error) -> Option<u8> {
    broker_refusal(e).map(|r| r.code)
}

#[test]
fn a_relay_grant_carries_an_owners_records_and_writes_nothing_else() {
    let net = Net::guarded("grant", 1);
    let (a, b) = (origin(A), origin(B));
    let x = a.subject("x");
    let carrier = mint(
        SECRET,
        &format!("rw,relay,p={}:/m/>", origin(CARRIER).principal),
    )
    .unwrap();
    let mut client = net.client(0);
    client.attach(&carrier.filter, &carrier.tag).unwrap();

    assert!(!a.relay(&mut client, 7, "x", b"ok").unwrap().1);
    // Replayed, the same key appends nothing.
    assert!(a.relay(&mut client, 7, "x", b"ok").unwrap().1);

    // Under an id that is not the subject's owner's, its own included.
    let own_id = origin(CARRIER).id;
    for id in [b.id, own_id, 1] {
        let e = client.relay(id, 8, &x, &a.seal(&x, 8, b"no")).unwrap_err();
        assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED), "as {id}");
    }
    // On a subject its filter does not reach, and on one with no owner.
    let rows = format!("/t/rows/{}", b.principal);
    let e = client
        .relay(b.id, 1, &rows, &b.seal(&rows, 1, b"no"))
        .unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));
    let e = client.relay(a.id, 9, "/m/not-a-node/x", b"no").unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));

    // Not a publish, even under the id and subject a relay could carry.
    let e = client.publish(a.id, 10, &x, b"no").unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));
    let e = client
        .publish(own_id, 1, &origin(CARRIER).subject("x"), b"no")
        .unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));
    assert!(client.commit(&x, 1).is_err(), "not a commit");

    // A plain bound grant over the subject writes as its principal but relays nothing.
    let owner = mint(SECRET, &format!("rw,p={0}:/m/{0}/>", a.principal)).unwrap();
    let mut client = adopted(&net.brokers[0], &a);
    client.attach(&owner.filter, &owner.tag).unwrap();
    let e = a.relay(&mut client, 11, "x", b"no").unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));
    client.publish(a.id, 11, &x, b"yes").unwrap();

    // The god cap holds every write, a relay among them, still under the owner's id alone.
    let root = mint(SECRET, "rw:/>").unwrap();
    let mut client = net.client(0);
    client.attach(&root.filter, &root.tag).unwrap();
    assert!(!a.relay(&mut client, 12, "x", b"ok").unwrap().1);
    let e = client.relay(1, 13, &x, &a.seal(&x, 13, b"no")).unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_UNAUTHORIZED));
}

/// A relayed record answers for itself: what a carrying Mac can do with a genuine relay grant and
/// no origin's key. Each attempt is refused for what it is and appends nothing, and the real
/// record then lands under the key the forgery tried to take.
#[test]
fn a_forged_record_is_refused_and_cannot_take_the_real_ones_key() {
    let net = Net::guarded("forged", 1);
    let (a, b) = (origin(A), origin(B));
    let carrier = mint(
        SECRET,
        &format!("rw,relay,p={}:/m/>", origin(CARRIER).principal),
    )
    .unwrap();
    let mut client = net.client(0);
    client.attach(&carrier.filter, &carrier.tag).unwrap();
    let x = a.subject("x");
    let genuine = a.seal(&x, 1, b"real");

    let mut tampered = genuine.clone();
    *tampered.last_mut().unwrap() ^= 1;
    let mut bad_signature = genuine.clone();
    bad_signature[0] ^= 1;
    let other_subject = a.subject("y");
    for (what, subject, seq, body) in [
        (
            "the carrier's own key",
            x.clone(),
            1,
            b.seal(&x, 1, b"fake"),
        ),
        ("a changed payload", x.clone(), 1, tampered),
        ("a changed signature", x.clone(), 1, bad_signature),
        (
            "another sequence's signature",
            x.clone(),
            2,
            genuine.clone(),
        ),
        (
            "another subject's signature",
            other_subject,
            1,
            genuine.clone(),
        ),
        ("no envelope", x.clone(), 1, b"bare".to_vec()),
    ] {
        let e = client.relay(a.id, seq, &subject, &body).unwrap_err();
        assert_eq!(refusal_code(&e), Some(ERR_ORIGIN_REFUSED), "{what}");
        assert!(
            broker_refusal(&e).is_some_and(|r| r.is_permanent()),
            "{what}"
        );
    }
    assert_eq!(net.brokers[0].stats().origin_refused, 6);
    let reader = mint(SECRET, "ro:/m/>").unwrap();
    assert!(net.held(0, Some(&reader)).is_empty());

    let (_, deduped) = client.relay(a.id, 1, &x, &genuine).unwrap();
    assert!(!deduped, "no forgery took the key");
    assert_eq!(
        origin::payload(&net.held(0, Some(&reader))[0].2),
        Some(&b"real"[..])
    );
}

/// An origin the broker does not take now (no key, a revoked key, a revoked principal, a key the
/// embedder withdrew) is answered `ERR_ORIGIN_UNKNOWN`, which is not permanent: the same record
/// lands once the embedder lifts the revocation or gives the key, so a carrier that still seats
/// the origin may wait for it. Nothing about the record itself was judged.
#[test]
fn an_origin_a_broker_does_not_take_is_answered_so_its_carrier_may_wait() {
    let net = Net::new("known", 1);
    let broker = &net.brokers[0];
    let (a, b, stranger) = (origin(A), origin(B), origin(UNKNOWN));
    let mut client = net.client(0);
    let unknown = |e: &std::io::Error, what: &str| {
        let refusal = broker_refusal(e).unwrap_or_else(|| panic!("{what}: {e}"));
        assert_eq!(refusal.code, ERR_ORIGIN_UNKNOWN, "{what}");
        assert!(
            refusal.is_origin_unknown() && !refusal.is_permanent(),
            "{what}"
        );
    };

    // Correctly signed, by a key this broker does not hold.
    let e = stranger.relay(&mut client, 1, "x", b"later").unwrap_err();
    unknown(&e, "unknown");

    // Revoked by its key and the principal it derives, then lifted: the same record lands.
    assert!(!a.relay(&mut client, 1, "x", b"yes").unwrap().1);
    broker.revoke_identity(a.key);
    let e = a.relay(&mut client, 2, "x", b"after").unwrap_err();
    unknown(&e, "revoked key");
    assert!(broker.unrevoke_identity(&a.key));
    assert!(!a.relay(&mut client, 2, "x", b"after").unwrap().1, "lifted");

    // Revoked by its key alone: its principal keeps its standing.
    assert!(broker.revoke_key(a.key));
    assert!(!broker.is_principal_revoked(&a.principal), "the key alone");
    let e = a.relay(&mut client, 3, "x", b"third").unwrap_err();
    unknown(&e, "a key revoked alone");
    assert!(broker.unrevoke_key(&a.key));
    assert!(!a.relay(&mut client, 3, "x", b"third").unwrap().1);

    assert!(!b.relay(&mut client, 1, "x", b"yes").unwrap().1);
    assert!(broker.revoke_principal(&b.principal));
    let e = b.relay(&mut client, 2, "x", b"no").unwrap_err();
    unknown(&e, "revoked principal");

    // The embedder's set replaces the last: a member withdrawn is not taken, one added is.
    let c = origin(C);
    assert!(!c.relay(&mut client, 1, "x", b"yes").unwrap().1);
    broker.set_origin_keys([stranger.key]);
    let e = c.relay(&mut client, 2, "x", b"no").unwrap_err();
    unknown(&e, "withdrawn");
    assert!(!stranger.relay(&mut client, 1, "x", b"later").unwrap().1);
    assert_eq!(broker.stats().origin_refused, 0, "no record was at fault");
    assert_eq!(broker.stats().origin_unknown, 5);
    assert_eq!(net.held(0, None).len(), 6, "only what was taken");
}

/// A broker that was given no keys takes no relayed record, however it is signed. That says
/// nothing of the records, so a bridge commits nothing: when the keys come, they all still land.
#[test]
fn a_destination_with_no_origin_keys_yet_costs_a_bridge_nothing() {
    let net = Net::new("nokeys", 2);
    let a = origin(A);
    net.brokers[1].set_origin_keys([]);
    let mut client = net.client(1);
    let e = a.relay(&mut client, 1, "x", b"no").unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_RELAY_NOT_READY));
    assert_eq!(net.brokers[1].stats().origin_refused, 0);

    publish_as(&net, 0, &a, 3);
    let mut bridge = FederationBridge::open(net.relay_cfg(0, 1)).unwrap();
    let mut seen = Vec::new();
    let failed = bridge.run(256, &mut |report| seen.push(report.clone()));
    assert!(failed.is_err(), "the bridge stops");
    assert!(seen.is_empty(), "and reports no burst");
    assert!(net.held(1, None).is_empty());

    net.brokers[1].set_origin_keys([a.key]);
    let mut bridges = Bridges::start(&net, &[(0, 1)]);
    bridges.until("the keys", |t| t.mirrored >= 3);
    bridges.stop();
    assert_each_broker_holds_each_once(&net, &[&a], 3);
}

/// A burst of refusals pays its acks with the broker still reading, however large the burst: a
/// refusal written inline would stop the read half against a client still writing the burst.
#[test]
fn a_whole_burst_of_refused_records_does_not_stall_the_connection() {
    const N: u64 = 256;
    let net = Net::new("allrefused", 2);
    let stranger = origin(UNKNOWN);
    let payload = vec![7u8; 16 * 1024];
    let mut src = net.client(0);
    for seq in 1..=N {
        let subject = stranger.subject(&format!("k{seq}"));
        src.publish(
            stranger.id,
            seq,
            &subject,
            &stranger.seal(&subject, seq, &payload),
        )
        .unwrap();
    }
    let mut bridges = Bridges::start(&net, &[(0, 1)]);
    bridges.until("the refusals", |t| t.refused >= N as usize);
    let total = bridges.stop();
    assert_eq!(total.refused, N as usize);
    assert!(net.held(1, None).is_empty());
}

/// Replaying one genuine record spends nothing of its origin's: the bucket is the origin's, and
/// the carrier is not. With a limit one record wide, the origin still publishes.
#[test]
fn a_carrier_replaying_a_record_cannot_spend_its_origins_rate_limit() {
    let net = Net::new("ratelimit", 1);
    let a = origin(A);
    let mut client = net.client(0);
    a.relay(&mut client, 1, "x", b"one").unwrap();
    net.brokers[0]
        .set_rate_limit(Some(astream_broker::store::RateLimit {
            records_per_sec: 1,
            bytes_per_sec: 1 << 20,
            burst_records: 1,
            burst_bytes: 1 << 20,
        }))
        .unwrap();
    for _ in 0..16 {
        assert!(a.relay(&mut client, 1, "x", b"one").unwrap().1);
    }
    let y = a.subject("y");
    client.publish(a.id, 2, &y, &a.seal(&y, 2, b"two")).unwrap();
}

/// A bad record on an edge is counted and passed: the next one is not its fault. So is a record
/// whose origin the destination does not take, on a bridge never told to hold one.
#[test]
fn a_bridge_counts_a_refused_record_and_carries_the_rest() {
    let net = Net::new("refused", 2);
    let (a, stranger) = (origin(A), origin(UNKNOWN));
    let forged = a.subject("forged");
    let mut src = net.client(0);
    src.publish(a.id, 1, &forged, &stranger.seal(&forged, 1, b"no"))
        .unwrap();
    let foreign = stranger.subject("x");
    src.publish(stranger.id, 1, &foreign, &stranger.seal(&foreign, 1, b"no"))
        .unwrap();
    let real = a.subject("real");
    src.publish(a.id, 2, &real, &a.seal(&real, 2, b"yes"))
        .unwrap();

    let mut bridges = Bridges::start(&net, &[(0, 1)]);
    bridges.until("the refusals", |t| t.fetched >= 3);
    let total = bridges.stop();
    assert_eq!((total.refused, total.mirrored), (2, 1));
    let held = net.held(1, None);
    assert_eq!(held.len(), 1);
    assert_eq!(held[0].1, real);
    let stats = net.brokers[1].stats();
    assert_eq!((stats.origin_refused, stats.origin_unknown), (1, 1));
}

/// Publish `who`'s signed row `k<seq>` holding `payload` on `client`, answering its offset.
fn publish_one(client: &mut AnyClient, who: &Origin, seq: u64, payload: &[u8]) -> u64 {
    let subject = who.subject(&format!("k{seq}"));
    client
        .publish(who.id, seq, &subject, &who.seal(&subject, seq, payload))
        .unwrap()
        .0
}

/// A net of two whose destination, broker 1, does not take `D` yet; its source marks a quiet tail
/// often, so a held record is offered again soon.
fn net_without_d(tag: &str) -> Net {
    let net = Net::new(tag, 2);
    net.brokers[1].set_origin_keys([A, B, C].map(|n| origin(n).key));
    net.brokers[0].set_idle_mark(Duration::from_millis(100));
    net
}

/// What broker `i` holds of `who`'s, by subject, in log order.
fn subjects_of(net: &Net, i: usize, who: &Origin) -> Vec<String> {
    let mine = format!("/m/{}/", who.principal);
    net.held(i, None)
        .into_iter()
        .map(|(_, subject, _)| subject)
        .filter(|subject| subject.starts_with(&mine))
        .collect()
}

fn always_seated() -> Option<Seated> {
    Some(Arc::new(|_: &str| true))
}

/// A relay whose destination does not take an origin yet holds that origin's records back while
/// the source seats it (`TlaPushEdge.NoSkip`): each later burst commits below the first of them,
/// however many bursts pass, and the rest of the edge flows on. Once the destination takes the
/// origin, a quiet source's mark offers the first again and the rest follow, in the order they
/// left, with no restart.
#[test]
fn a_relay_holds_an_origin_its_destination_does_not_take_yet_and_delivers_it_once_it_does() {
    let net = net_without_d("held");
    let (a, d) = (origin(A), origin(D));
    let mut src = net.client(0);
    let first = publish_one(&mut src, &d, 1, b"d1");
    publish_one(&mut src, &d, 2, b"d2");
    publish_one(&mut src, &a, 1, b"a1");
    let mut bridges = Bridges::start(&net, &[]);
    bridges.add_holding(net.relay_cfg(0, 1), always_seated());
    bridges.until("a's record past d's", |t| t.mirrored >= 1 && t.held == 2);
    assert!(
        bridges.total.committed_upto.is_none_or(|c| c < first),
        "no commit passes the first record held: {:?}",
        bridges.total.committed_upto
    );
    publish_one(&mut src, &a, 2, b"a2");
    bridges.until("a later burst", |t| t.mirrored >= 2);
    assert_eq!(bridges.total.held, 2);
    assert!(
        bridges.total.committed_upto.is_none_or(|c| c < first),
        "a later burst still commits below it: {:?}",
        bridges.total.committed_upto
    );
    assert!(subjects_of(&net, 1, &d).is_empty());

    net.brokers[1].set_origin_keys([A, B, C, D].map(|n| origin(n).key));
    bridges.until("d's records", |t| t.mirrored >= 4 && t.held == 0);
    let total = bridges.stop();
    assert_eq!(total.refused, 0);
    assert!(total.committed_upto.is_some_and(|c| c > first));
    assert_eq!(
        subjects_of(&net, 1, &d),
        [d.subject("k1"), d.subject("k2")],
        "each once, in the order they left"
    );
}

/// A run that ends while it holds a record committed below it, so the next run delivers it, and
/// what the destination took already answers "already held".
#[test]
fn a_relay_restarted_while_it_holds_a_record_delivers_it() {
    let net = net_without_d("heldrestart");
    let (a, d) = (origin(A), origin(D));
    publish_as(&net, 0, &d, 1);
    publish_as(&net, 0, &a, 1);
    let mut bridges = Bridges::start(&net, &[]);
    bridges.add_holding(net.relay_cfg(0, 1), always_seated());
    bridges.until("the hold", |t| t.mirrored >= 1 && t.held == 1);
    bridges.stop();

    net.brokers[1].set_origin_keys([A, B, C, D].map(|n| origin(n).key));
    let mut again = Bridges::start(&net, &[]);
    again.add_holding(net.relay_cfg(0, 1), always_seated());
    again.until("the record held", |t| t.mirrored - t.deduped >= 1);
    let total = again.stop();
    assert_eq!((total.deduped, total.held), (1, 0));
    assert_each_broker_holds_each_once(&net, &[&a, &d], 1);
}

/// Once the source no longer seats an origin, what it held of it is let go and counted refused:
/// no destination will be told to take an origin its carrier does not, and the edge commits past.
#[test]
fn a_relay_lets_go_what_it_held_once_the_source_no_longer_seats_the_origin() {
    let net = net_without_d("letgo");
    let (a, d) = (origin(A), origin(D));
    let mut src = net.client(0);
    let held_at = publish_one(&mut src, &d, 1, b"d1");
    publish_one(&mut src, &a, 1, b"a1");
    let seated = Arc::new(AtomicBool::new(true));
    let still = Arc::clone(&seated);
    let mut bridges = Bridges::start(&net, &[]);
    bridges.add_holding(
        net.relay_cfg(0, 1),
        Some(Arc::new(move |_: &str| still.load(Ordering::Acquire))),
    );
    bridges.until("the hold", |t| t.mirrored >= 1 && t.held == 1);
    seated.store(false, Ordering::Release);
    bridges.until("the release", |t| t.refused >= 1 && t.held == 0);
    let total = bridges.stop();
    assert_eq!(total.refused, 1);
    assert!(total.committed_upto.is_some_and(|c| c > held_at));
    assert!(subjects_of(&net, 1, &d).is_empty());
}

/// Past what a run keeps in hand, a record is held by its offset alone: the edge flows on, and
/// once the destination took all the run kept, the run ends committed below that record, so the
/// next run reads again from it and delivers it.
#[test]
fn a_relay_past_its_held_bound_reads_again_from_the_record_it_could_not_keep() {
    let net = net_without_d("spill");
    let (a, d) = (origin(A), origin(D));
    let big = vec![5u8; HELD_BYTES / 2 + 1];
    let mut src = net.client(0);
    publish_one(&mut src, &d, 1, &big);
    let spilled = publish_one(&mut src, &d, 2, &big);
    publish_one(&mut src, &a, 1, b"a1");

    let mut bridge = FederationBridge::open(net.relay_cfg(0, 1)).unwrap();
    bridge.hold_while(Arc::new(|_: &str| true));
    let (tx, reports) = mpsc::channel();
    let running = std::thread::spawn(move || {
        bridge.run(256, &mut |report| {
            let _ = tx.send(report.clone());
        })
    });
    let deadline = Instant::now() + HANG;
    loop {
        let report = reports
            .recv_timeout(deadline.saturating_duration_since(Instant::now()))
            .expect("a report holding both of d's records");
        if report.held == 2 {
            break;
        }
    }
    net.brokers[1].set_origin_keys([A, B, C, D].map(|n| origin(n).key));
    let (tx, ended) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(running.join().unwrap());
    });
    match ended.recv_timeout(HANG).expect("the run ends") {
        Err(FederationError::HeldBack { from }) => assert_eq!(from, spilled),
        other => panic!("the run ends reading again from the record past its bound: {other:?}"),
    }
    assert_eq!(subjects_of(&net, 1, &d), [d.subject("k1")]);

    let mut again = Bridges::start(&net, &[]);
    again.add_holding(net.relay_cfg(0, 1), always_seated());
    again.until("the record past the bound", |t| t.mirrored - t.deduped >= 1);
    again.stop();
    assert_eq!(subjects_of(&net, 1, &d), [d.subject("k1"), d.subject("k2")]);
    assert_eq!(subjects_of(&net, 1, &a), [a.subject("k1")]);
}

#[test]
fn a_bridge_skips_a_record_its_producer_does_not_own_and_carries_the_rest() {
    let net = Net::new("skip", 2);
    let a = origin(A);
    let forged = a.subject("forged");
    let real = a.subject("real");
    let mut client = net.client(0);
    client.publish(999, 1, &forged, b"no").unwrap();
    client.publish(999, 2, "/m/unowned", b"no").unwrap();
    client
        .publish(a.id, 1, &real, &a.seal(&real, 1, b"yes"))
        .unwrap();
    let mut bridges = Bridges::start(&net, &[(0, 1)]);
    bridges.until("the skips", |t| t.fetched >= 3);
    let total = bridges.stop();
    assert_eq!((total.skipped, total.mirrored), (2, 1));
    let held = net.held(1, None);
    assert_eq!(held.len(), 1);
    assert_eq!(held[0].1, real);
}

/// A relayed record's subjects are its origin's to answer for: the carrier's id appears nowhere,
/// so a carrier of many origins spends none of its own budget and one origin cannot spend
/// another's.
#[test]
fn mirrored_subjects_are_charged_to_the_origin_not_the_bridge() {
    let net = Net::new("budget", 2);
    let (a, b, c) = (origin(A), origin(B), origin(C));
    let mut dst = net.client(1);
    for seq in 1..=SUBJECT_BUDGET {
        a.relay(&mut dst, seq, &format!("s{seq}"), b"x").unwrap();
    }
    // The one past the origin's budget is refused and is nobody else's problem.
    let e = a
        .relay(&mut dst, SUBJECT_BUDGET + 1, "over", b"x")
        .unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_SUBJECT_BOUND));
    for seq in 1..=SUBJECT_BUDGET {
        b.relay(&mut dst, seq, &format!("s{seq}"), b"x").unwrap();
    }

    // Through a bridge: a refused record is counted, not retried, and the burst still lands.
    let (over, fine) = (a.subject("over"), c.subject("fine"));
    let mut src = net.client(0);
    src.publish(
        a.id,
        SUBJECT_BUDGET + 1,
        &over,
        &a.seal(&over, SUBJECT_BUDGET + 1, b"x"),
    )
    .unwrap();
    src.publish(c.id, 1, &fine, &c.seal(&fine, 1, b"x"))
        .unwrap();
    let mut bridges = Bridges::start(&net, &[(0, 1)]);
    bridges.until("the budget", |t| t.fetched >= 2);
    let total = bridges.stop();
    assert_eq!(total.refused, 1);
    assert_eq!(total.mirrored, 1);
    let held = net.held(1, None);
    assert_eq!(held.len() as u64, 2 * SUBJECT_BUDGET + 1);
    assert_eq!(held.last().unwrap().1, fine);
}

#[test]
fn a_relay_bridge_takes_no_rewrite_and_no_polling() {
    let net = Net::new("config", 2);
    let cfg = FederationConfig {
        rewrite: SubjectRewrite::prefix_map("/m", "/x").unwrap(),
        ..net.relay_cfg(0, 1)
    };
    assert!(matches!(
        FederationBridge::open(cfg),
        Err(FederationError::Config(_))
    ));
    let mut bridge = FederationBridge::open(net.relay_cfg(0, 1)).unwrap();
    assert!(matches!(
        bridge.sync_once(1),
        Err(FederationError::Config(_))
    ));
}

/// A net whose brokers keep `Last` by default and every record under `/m/*/all/>`.
fn net_keeping_last(tag: &str, n: usize) -> Net {
    let net = Net::new(tag, n);
    for broker in &net.brokers {
        broker.set_retention(keeping_last()).unwrap();
    }
    net
}

fn keeping_last() -> Retention {
    Retention::new(
        vec![
            Rule::prefix("/journal/>").unwrap(),
            Rule::hold("/m/*/all/>").unwrap(),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// The subject's `Last` row on broker `i`, as `(payload, its origin's seq)`.
fn last_row(net: &Net, i: usize, subject: &str) -> (Vec<u8>, u64) {
    let (rows, _) = net.client(i).last_all(subject).unwrap();
    assert_eq!(rows.len(), 1, "{subject} on broker {i}");
    let (offset, _, body) = rows.into_iter().next().unwrap();
    let mut client = net.client(i);
    assert!(client.origin_stamps().unwrap());
    let mut sub = client.subscribe(offset, subject).unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().0, offset);
    (
        origin::payload(&body).unwrap().to_vec(),
        sub.last_origin().unwrap().1,
    )
}

/// Two paths bring the origin's rows to one broker in opposite orders: whichever way they raced,
/// it ends on the highest, with the bridges the only writers.
#[test]
fn the_highest_origin_seq_wins_over_two_paths_in_either_order() {
    let a = origin(A);
    let subject = a.subject("cpu");
    for newer_path_first in [true, false] {
        let net = net_keeping_last("twopaths", 3);
        // Each of two neighbours holds one of the origin's rows; broker 2 hears from both.
        a.relay(&mut net.client(0), 5, "cpu", b"old").unwrap();
        a.relay(&mut net.client(1), 9, "cpu", b"new").unwrap();
        let (first, second) = if newer_path_first { (1, 0) } else { (0, 1) };

        let mut bridges = Bridges::start(&net, &[(first, 2)]);
        bridges.until("the first path", |t| t.fetched >= 1);
        bridges.stop();
        let mut bridges = Bridges::start(&net, &[(second, 2)]);
        bridges.until("the second path", |t| t.fetched >= 1);
        let total = bridges.stop();

        assert_eq!(last_row(&net, 2, &subject), (b"new".to_vec(), 9));
        if newer_path_first {
            assert_eq!(
                (total.mirrored, total.deduped),
                (1, 1),
                "the late row is a dup"
            );
            assert_eq!(net.held(2, None).len(), 1, "and appends nothing");
        } else {
            assert_eq!((total.mirrored, total.deduped), (1, 0));
            assert_eq!(net.held(2, None).len(), 2);
        }
    }
}

/// THE NEGATIVE CONTROL for the rule above: the same arrivals on a subject that keeps every
/// record, where a late row must still arrive and the arrival order decides `Last`.
#[test]
fn a_subject_keeping_every_record_takes_each_in_arrival_order() {
    let a = origin(A);
    let net = net_keeping_last("arrival", 1);
    let mut client = net.client(0);
    assert!(!a.relay(&mut client, 9, "all/mail", b"new").unwrap().1);
    assert!(!a.relay(&mut client, 5, "all/mail", b"old").unwrap().1);
    assert_eq!(net.held(0, None).len(), 2);
    assert_eq!(
        last_row(&net, 0, &a.subject("all/mail")),
        (b"old".to_vec(), 5)
    );
    // A broker given no rules has no subject that keeps only its last row.
    let net = Net::new("norules", 1);
    let mut client = net.client(0);
    a.relay(&mut client, 9, "cpu", b"new").unwrap();
    assert!(!a.relay(&mut client, 5, "cpu", b"old").unwrap().1);
}

#[test]
fn a_late_row_is_answered_at_the_row_that_beat_it_and_within_a_batch() {
    let a = origin(A);
    let subject = a.subject("cpu");
    let net = net_keeping_last("answer", 1);
    let mut client = net.client(0);
    let (row, deduped) = a.relay(&mut client, 9, "cpu", b"nine").unwrap();
    assert!(!deduped);
    assert_eq!(
        a.relay(&mut client, 5, "cpu", b"five").unwrap(),
        (row, true)
    );
    assert_eq!(
        a.relay(&mut client, 9, "cpu", b"nine").unwrap(),
        (row, true)
    );
    let (next, deduped) = a.relay(&mut client, 10, "cpu", b"ten").unwrap();
    assert!(!deduped && next > row);
    assert_eq!(last_row(&net, 0, &subject), (b"ten".to_vec(), 10));

    // Rows staged together order the same way as rows that reached the log.
    let (twenty_body, fifteen_body) = (
        a.seal(&subject, 20, b"twenty"),
        a.seal(&subject, 15, b"fifteen"),
    );
    client
        .send_pipelined(&[
            Pipelined::Relay {
                producer_id: a.id,
                producer_seq: 20,
                subject: &subject,
                body: &twenty_body,
            },
            Pipelined::Relay {
                producer_id: a.id,
                producer_seq: 15,
                subject: &subject,
                body: &fifteen_body,
            },
        ])
        .unwrap();
    let (twenty, deduped) = client.recv_publish_ack().unwrap();
    assert!(!deduped);
    assert_eq!(client.recv_publish_ack().unwrap(), (twenty, true));
    assert_eq!(last_row(&net, 0, &subject), (b"twenty".to_vec(), 20));
}

/// An ack's sequence (`ACK_SEQ_BASE | offset`) is a source offset and orders nothing, so no floor
/// or row could answer a replay of it: a relay refuses the whole half, signed or not.
#[test]
fn a_relayed_sequence_in_the_ack_half_is_refused() {
    let a = origin(A);
    let net = net_keeping_last("ackhalf", 1);
    let mut client = net.client(0);
    let e = a
        .relay(&mut client, ACK_SEQ_BASE | 100, "state", b"ack")
        .unwrap_err();
    assert_eq!(refusal_code(&e), Some(ERR_ORIGIN_REFUSED));
    assert!(!a.relay(&mut client, 7, "state", b"seven").unwrap().1);
    assert!(a.relay(&mut client, 6, "state", b"six").unwrap().1);
}

/// Compaction cuts the dedup keys of what it drops. The row itself stays, so a slow neighbour's
/// late copy still appends nothing, the row's own key included, and a reopen changes none of it.
#[test]
fn compaction_and_a_reopen_leave_a_late_row_late() {
    let a = origin(A);
    let subject = a.subject("cpu");
    let k = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = PathBuf::from(format!("/tmp/asrl-compact-{}-{k}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let log = dir.join("0.log");
    let last_payload = |client: &mut AnyClient| {
        let (rows, _) = client.last_all(&subject).unwrap();
        assert_eq!(rows.len(), 1);
        origin::payload(&rows[0].2).unwrap().to_vec()
    };

    let head = {
        let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
        broker.set_retention(keeping_last()).unwrap();
        broker.set_origin_keys([a.key]);
        let mut client = adopted(&broker, &a);
        for seq in [1, 2, 3] {
            a.relay(&mut client, seq, "cpu", format!("{seq}").as_bytes())
                .unwrap();
        }
        broker.retain_before_carrying_state(broker.head()).unwrap();
        assert_eq!(
            client.stats("/m/>").unwrap().dedup_entries,
            0,
            "the cut took the keys"
        );
        let head = broker.head();
        for seq in [1, 2, 3] {
            assert!(
                a.relay(&mut client, seq, "cpu", b"late").unwrap().1,
                "seq {seq}"
            );
        }
        assert_eq!(broker.head(), head, "no late copy appended");
        assert_eq!(last_payload(&mut client), b"3".to_vec());
        head
    };

    // The rules are read back from the log, so nothing has to be said again first.
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    let mut client = adopted(&broker, &a);
    assert!(
        a.relay(&mut client, 2, "cpu", b"late").unwrap().1,
        "after a reopen"
    );
    assert_eq!(broker.head(), head);
    assert_eq!(last_payload(&mut client), b"3".to_vec());
    assert!(!a.relay(&mut client, 4, "cpu", b"4").unwrap().1);
    assert_eq!(last_payload(&mut client), b"4".to_vec());
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// The log of a test that cuts and reopens, and a broker of it with `who`'s keys.
fn cutting_log(tag: &str) -> (PathBuf, PathBuf) {
    let k = NEXT.fetch_add(1, Ordering::Relaxed);
    let dir = PathBuf::from(format!("/tmp/asrl-{tag}-{}-{k}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let log = dir.join("0.log");
    (dir, log)
}

/// A signature has no age. On a subject that keeps every record, a carrier holding an old envelope
/// could have it appended again once a cut took its key; the floor the cut raised answers instead,
/// across a reopen, and a newer record still lands.
#[test]
fn a_replay_after_a_cut_appends_nothing_live_or_after_a_reopen() {
    let a = origin(A);
    let (dir, log) = cutting_log("replay");
    let head = {
        let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
        broker.set_origin_keys([a.key]);
        let mut client = adopted(&broker, &a);
        for seq in [1, 2, 3] {
            a.relay(&mut client, seq, "mail", b"m").unwrap();
        }
        // A plain cut carries state too once the log has relayed: a reopen must keep the floor.
        broker.retain_before(broker.head()).unwrap();
        assert_eq!(client.stats("/m/>").unwrap().dedup_entries, 0);
        let head = broker.head();
        for seq in [1, 2, 3] {
            assert!(a.relay(&mut client, seq, "mail", b"m").unwrap().1, "{seq}");
        }
        assert_eq!(broker.head(), head, "a replay appends nothing");
        head
    };
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    let mut client = adopted(&broker, &a);
    assert!(a.relay(&mut client, 2, "mail", b"m").unwrap().1, "reopened");
    assert_eq!(
        broker.head(),
        head,
        "a replay appends nothing after a reopen"
    );
    assert!(!a.relay(&mut client, 4, "mail", b"m").unwrap().1);
    assert_eq!(broker.head(), head + 1, "a newer record lands");
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A log marks its first relayed record from an origin in that record's batch, so a reopen knows
/// the origin before anyone has said its key again: a plain cut there still carries a floor.
#[test]
fn a_cut_after_a_reopen_floors_what_the_last_run_relayed() {
    let a = origin(A);
    let (dir, log) = cutting_log("mark");
    {
        let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
        broker.set_origin_keys([a.key]);
        let mut client = adopted(&broker, &a);
        a.relay(&mut client, 1, "mail", b"m").unwrap();
    }
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.retain_before(broker.head()).unwrap();
    broker.set_origin_keys([a.key]);
    let head = broker.head();
    let mut client = adopted(&broker, &a);
    assert!(a.relay(&mut client, 1, "mail", b"m").unwrap().1);
    assert_eq!(broker.head(), head, "a replay appends nothing");
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// An origin's home log holds its plain publishes and may never have taken a relay. Holding the key
/// makes it an origin there, so a neighbour's replay of a record cut at home appends nothing.
#[test]
fn a_replay_to_an_origins_home_after_a_cut_appends_nothing() {
    let a = origin(A);
    let (dir, log) = cutting_log("home");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    let mut client = adopted(&broker, &a);
    let subject = a.subject("mail");
    client
        .publish(a.id, 1, &subject, &a.seal(&subject, 1, b"m"))
        .unwrap();
    broker.retain_before(broker.head()).unwrap();
    let head = broker.head();
    assert!(a.relay(&mut client, 1, "mail", b"m").unwrap().1);
    assert_eq!(broker.head(), head);
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A publish under a held key marks its origin durably, so a restart whose first cut comes before
/// anyone says the key again still floors it.
#[test]
fn a_cut_before_the_keys_return_floors_an_origins_own_publishes() {
    let a = origin(A);
    let (dir, log) = cutting_log("homemark");
    let subject = a.subject("mail");
    {
        let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
        broker.set_origin_keys([a.key]);
        let mut client = adopted(&broker, &a);
        client
            .publish(a.id, 1, &subject, &a.seal(&subject, 1, b"m"))
            .unwrap();
    }
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.retain_before(broker.head()).unwrap();
    broker.set_origin_keys([a.key]);
    let head = broker.head();
    let mut client = adopted(&broker, &a);
    assert!(a.relay(&mut client, 1, "mail", b"m").unwrap().1);
    assert_eq!(broker.head(), head);
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A key withdrawn before the cut leaves its origin one for the run: the seat may come back, with
/// its old records' signatures as good as ever.
#[test]
fn a_withdrawn_key_still_floors_its_origins_records() {
    let a = origin(A);
    let (dir, log) = cutting_log("withdrawn");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    broker.set_origin_keys([origin(B).key]);
    let mut client = adopted(&broker, &a);
    let subject = a.subject("mail");
    client
        .publish(a.id, 1, &subject, &a.seal(&subject, 1, b"m"))
        .unwrap();
    broker.retain_before(broker.head()).unwrap();
    broker.set_origin_keys([a.key]);
    let head = broker.head();
    assert!(a.relay(&mut client, 1, "mail", b"m").unwrap().1);
    assert_eq!(broker.head(), head);
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A producer no signature or key has made an origin raises no floor: its keys go with the cut, as
/// on any broker, and a log that never relays keeps nothing for them.
#[test]
fn a_producer_that_is_no_origin_raises_no_floor() {
    let a = origin(A);
    let (dir, log) = cutting_log("plain");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([origin(B).key]);
    let mut client = adopted(&broker, &a);
    let subject = a.subject("mail");
    client.publish(a.id, 9, &subject, b"plain").unwrap();
    broker.retain_before(broker.head()).unwrap();
    broker.set_origin_keys([a.key]);
    assert!(
        !a.relay(&mut client, 5, "mail", b"m").unwrap().1,
        "no floor stands over it"
    );
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// An origin's subjects travel different paths, so a cut of one floors only that one: mail still on
/// its way lands after the same origin's newer metrics were cut.
#[test]
fn a_cut_of_one_subject_refuses_nothing_late_on_another() {
    let a = origin(A);
    let (dir, log) = cutting_log("late");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    let mut client = adopted(&broker, &a);
    a.relay(&mut client, 10, "metrics", b"m").unwrap();
    broker.retain_before(broker.head()).unwrap();
    assert!(a.relay(&mut client, 10, "metrics", b"m").unwrap().1);
    assert!(
        !a.relay(&mut client, 5, "mail", b"late").unwrap().1,
        "mail below the metrics' floor still lands"
    );
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A subject whose keys are all still held answers from them, at the record's own offset; a floor
/// only answers for what a cut took.
#[test]
fn a_key_still_held_answers_at_its_offset_and_a_floor_just_below_the_base() {
    let a = origin(A);
    let (dir, log) = cutting_log("answer");
    let broker = Broker::open_with(&log, Durability::Relaxed).unwrap();
    broker.set_origin_keys([a.key]);
    let mut client = adopted(&broker, &a);
    a.relay(&mut client, 1, "mail", b"m").unwrap();
    let (kept, _) = a.relay(&mut client, 2, "mail", b"m").unwrap();
    broker.retain_before(kept).unwrap();
    assert_eq!(a.relay(&mut client, 2, "mail", b"m").unwrap(), (kept, true));
    assert_eq!(
        a.relay(&mut client, 1, "mail", b"m").unwrap(),
        (kept - 1, true)
    );
    drop(client);
    drop(broker);
    let _ = std::fs::remove_dir_all(&dir);
}
