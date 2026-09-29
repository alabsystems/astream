//! Claim `broker.cap-enforced-on-attach`: a guarded broker (built with the `cap`
//! feature via `open_guarded`) enforces the unforgeable capability mint on its
//! accept path -- every connection must Attach a capability that GRANTS each
//! subject it publishes and CONTAINS each filter it subscribes (plain, group, or
//! fork subscribe), and that GRANTS each consumer group it commits (a Commit, the
//! commit half of a read-process-write, or the commit a REPLICATED record carries --
//! whose subject is authorized like a publish); unauthorized or un-attached requests
//! are refused. This closes the "reachability = access" gap for cross-machine use
//! (a scoped agent gets exactly its subtree, nothing else). The default broker
//! sets no secret and is unaffected (separate default tests).
//!
//! The attach is a PROOF OF POSSESSION over the connection's nonce and is
//! ACKNOWLEDGED, so a forged capability is refused at the attach itself rather than
//! silently at the next request; the keyring, the binding table and the full §8.2
//! matrix are proven by `broker.cap-keyring-enforced` (tests/cap_keyring.rs).
#![cfg(all(unix, feature = "cap"))]

use astream_broker::client::Subscription;
use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::{Broker, BrokerHandle, Client, Request, Response};
use astream_cap::{mint, Capability};
use std::io::{self, Read, Write};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
        Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
    }
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            remove_with_sidecars(path);
        }
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

fn fresh(secret: &[u8]) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/ascap_{pid}_{n}.sock");
    let log = format!("/tmp/ascap_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

/// A connection that has attached `cap`.
fn attached(sock: &str, cap: &Capability) -> Client {
    let mut c = Client::connect(sock).unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    c
}

/// A streaming verb is refused either at the request or at its first `recv`.
fn refused<S: Read + Write>(r: io::Result<Subscription<S>>) -> bool {
    match r {
        Err(_) => true,
        Ok(mut s) => s.recv().is_err(),
    }
}

/// Drive the leader→follower `Replicate` verb directly: it has no `Client` method,
/// and it is the one remaining request that both names a subject and can advance a
/// consumer group. `cap` is `None` for an un-attached connection.
fn replicate(
    sock: &str,
    cap: Option<&Capability>,
    seq: u64,
    subject: &str,
    commit: Option<(&str, u64)>,
) -> Response {
    let mut s = match cap {
        Some(cap) => attached(sock, cap).into_stream(),
        None => Client::connect(sock).unwrap().into_stream(),
    };
    let req = Request::Replicate {
        seq,
        producer_id: 40 + seq,
        producer_seq: 1,
        subject: subject.to_string(),
        body: b"r".to_vec(),
        commit: commit.map(|(g, upto)| (g.to_string(), upto)),
    };
    write_frame(&mut s, &encode_request(&req)).unwrap();
    let payload = read_frame(&mut s).unwrap().expect("a response frame");
    decode_response(&payload).expect("a decodable response")
}

/// A refused request answers with an `unauthorized` error, never an ack.
fn is_unauthorized(r: &Response) -> bool {
    matches!(r, Response::Error { msg, .. } if msg.contains("unauthorized"))
}

#[test]
fn guarded_broker_enforces_capability_scope() {
    let secret = b"broker-secret-key";
    let (_tmp, _b, _h, sock) = fresh(secret);
    // A capability scoping the bearer to session s1's subtree, and nothing else.
    let cap = mint(secret, "/a/stream/s1/>").unwrap();

    // (1) attach with a valid cap, publish WITHIN the grant → ok.
    let mut a = Client::connect(&sock).unwrap();
    a.attach(&cap.filter, &cap.tag).unwrap();
    let (off, _dup) = a.publish(1, 1, "/a/stream/s1/out", b"hi").unwrap();
    assert_eq!(off, 0);

    // (2) attach, publish OUTSIDE the grant (a sibling session) → refused.
    let mut b = Client::connect(&sock).unwrap();
    b.attach(&cap.filter, &cap.tag).unwrap();
    let e = b.publish(2, 1, "/a/stream/s2/out", b"nope").unwrap_err();
    assert!(e.to_string().contains("unauthorized"), "publish s2: {e}");

    // (3) NO attach at all → refused (reachability is not access).
    let mut c = Client::connect(&sock).unwrap();
    let e = c.publish(3, 1, "/a/stream/s1/out", b"x").unwrap_err();
    assert!(
        e.to_string().contains("unauthorized"),
        "no-attach publish: {e}"
    );

    // (4) attach, subscribe WITHIN the grant → delivers the record from (1).
    let mut d = Client::connect(&sock).unwrap();
    d.attach(&cap.filter, &cap.tag).unwrap();
    let mut sub = d.subscribe(0, "/a/stream/s1/out").unwrap();
    let (o, subj, body) = sub.recv().unwrap().unwrap();
    assert_eq!(o, 0);
    assert_eq!(subj, "/a/stream/s1/out");
    assert_eq!(body, b"hi");

    // (5) attach, subscribe BROADER than the grant → refused (at subscribe or recv).
    let mut e = Client::connect(&sock).unwrap();
    e.attach(&cap.filter, &cap.tag).unwrap();
    assert!(
        refused(e.subscribe(0, "/a/>")),
        "subscribe broader than the grant must be refused"
    );

    // (6) a FORGED cap (real tag, widened filter) → refused AT THE ATTACH (the proof
    //     is over the widened grant, so it does not verify) — and, the ring being
    //     empty, the publish behind it is refused too.
    let mut f = Client::connect(&sock).unwrap();
    let e = f.attach("/a/>", &cap.tag).unwrap_err();
    assert!(e.to_string().contains("unauthorized"), "forged cap: {e}");
    let e = f.publish(6, 1, "/a/stream/s1/out", b"y").unwrap_err();
    assert!(e.to_string().contains("unauthorized"), "forged cap: {e}");

    // (7) NO attach: a plain subscribe and a commit are refused too — not only a
    //     publish (the un-attached case fails closed for EVERY request).
    assert!(
        refused(
            Client::connect(&sock)
                .unwrap()
                .subscribe(0, "/a/stream/s1/out")
        ),
        "un-attached subscribe must be refused"
    );
    let mut g = Client::connect(&sock).unwrap();
    let e = g.commit("/a/stream/s1/group/g", 0).unwrap_err();
    assert!(
        e.to_string().contains("unauthorized"),
        "un-attached commit: {e}"
    );
}

#[test]
fn guarded_broker_scopes_consumer_group_commits() {
    let secret = b"broker-secret-key";
    let (_tmp, _b, _h, sock) = fresh(secret);
    let cap = mint(secret, "/a/stream/s1/>").unwrap();

    // Seed a record within the grant.
    let mut p = Client::connect(&sock).unwrap();
    p.attach(&cap.filter, &cap.tag).unwrap();
    p.publish(1, 1, "/a/stream/s1/out", b"x").unwrap();

    // (a) FORGED cap (junk tag) → the attach is refused and so is the Commit behind
    // it. Closes the unauthenticated cross-tenant offset-forcing attack the audit
    // found.
    let mut f = Client::connect(&sock).unwrap();
    assert!(
        f.attach("/a/stream/s1/group/g", &[0u8; 32]).is_err(),
        "a junk tag must not attach"
    );
    assert!(
        f.commit("/a/stream/s1/group/g", 0).is_err(),
        "a forged-capability commit must be refused"
    );

    // (b) valid cap, commit an IN-SCOPE group (a subject the cap grants) → ok.
    let mut a = Client::connect(&sock).unwrap();
    a.attach(&cap.filter, &cap.tag).unwrap();
    assert!(
        a.commit("/a/stream/s1/group/pump", 0).is_ok(),
        "an in-scope group commit should succeed"
    );

    // (c) valid cap, commit an OUT-OF-SCOPE group (sibling session) → refused.
    let mut b = Client::connect(&sock).unwrap();
    b.attach(&cap.filter, &cap.tag).unwrap();
    assert!(
        b.commit("/a/stream/s2/group/x", 0).is_err(),
        "an out-of-scope group commit must be refused"
    );

    // (d) a non-subject group name → refused (fail-closed).
    let mut c = Client::connect(&sock).unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    assert!(
        c.commit("bare-group-name", 0).is_err(),
        "a non-subject group name must be refused"
    );
}

#[test]
fn guarded_broker_scopes_transactions_group_subscribes_and_forks() {
    let secret = b"broker-secret-key";
    let (_tmp, _b, _h, sock) = fresh(secret);
    let cap = mint(secret, "/a/stream/s1/>").unwrap();

    // Seed: one record within the grant, at offset 0.
    let mut p = attached(&sock, &cap);
    assert_eq!(p.publish(1, 1, "/a/stream/s1/out", b"x").unwrap().0, 0);

    // --- read-process-write: BOTH halves are scoped -----------------------------
    let mut a = attached(&sock, &cap);
    // (a) in-scope output, OUT-of-scope group → refused. (The commit half would
    //     otherwise force a sibling tenant's group offset forward — the exact
    //     cross-tenant data-loss hole, reopened through the transaction path.)
    let e = a
        .process_and_produce(2, 1, "/a/stream/s1/out", b"y", "/a/stream/s2/group/x", 0)
        .unwrap_err();
    assert!(
        e.to_string().contains("unauthorized"),
        "rpw out-of-scope group: {e}"
    );
    // (b) OUT-of-scope output, in-scope group → refused.
    let e = a
        .process_and_produce(2, 2, "/a/stream/s2/out", b"y", "/a/stream/s1/group/g", 0)
        .unwrap_err();
    assert!(
        e.to_string().contains("unauthorized"),
        "rpw out-of-scope output: {e}"
    );
    // (c) both in scope → the transaction commits: the output lands at offset 1
    //     (not deduped) and group g is durably at upto 0.
    assert_eq!(
        a.process_and_produce(2, 3, "/a/stream/s1/out", b"y", "/a/stream/s1/group/g", 0)
            .unwrap(),
        (1, false)
    );
    // (d) NO attach → refused.
    let mut n = Client::connect(&sock).unwrap();
    let e = n
        .process_and_produce(3, 1, "/a/stream/s1/out", b"z", "/a/stream/s1/group/g", 0)
        .unwrap_err();
    assert!(
        e.to_string().contains("unauthorized"),
        "un-attached rpw: {e}"
    );

    // --- group subscribe: authorized for what it READS (filter contained in the
    //     grant) AND for the group it COMMITS under (a subject the cap grants) ----
    // (e) contained filter, OUT-of-scope group → refused.
    assert!(
        refused(attached(&sock, &cap).subscribe_group("/a/stream/s2/group/x", "/a/stream/s1/out")),
        "group subscribe with an out-of-scope group must be refused"
    );
    // (f) in-scope group, filter BROADER than the grant → refused.
    assert!(
        refused(attached(&sock, &cap).subscribe_group("/a/stream/s1/group/g", "/a/>")),
        "group subscribe with a filter broader than the grant must be refused"
    );
    // (g) both in scope → resumes from the group's DURABLE commit: (c) committed
    //     g at upto 0, so delivery starts at offset 1 — the transaction's output.
    let mut g = attached(&sock, &cap)
        .subscribe_group("/a/stream/s1/group/g", "/a/stream/s1/out")
        .unwrap();
    assert_eq!(
        g.recv().unwrap().unwrap(),
        (1, "/a/stream/s1/out".to_string(), b"y".to_vec())
    );
    // (h) NO attach → refused.
    assert!(
        refused(
            Client::connect(&sock)
                .unwrap()
                .subscribe_group("/a/stream/s1/group/g", "/a/stream/s1/out")
        ),
        "un-attached group subscribe must be refused"
    );

    // --- counterfactual fork: a subscribe too, so its filter must be contained --
    // (i) filter broader than the grant → refused.
    assert!(
        refused(attached(&sock, &cap).fork_subscribe(0, "/a/stream/s1/out", b"r", "/a/>")),
        "fork with a filter broader than the grant must be refused"
    );
    // (j) contained → the forked snapshot: offset 0 swapped for the replacement,
    //     then the recorded offset 1, then end-of-snapshot.
    let mut f = attached(&sock, &cap)
        .fork_subscribe(0, "/a/stream/s1/out", b"r", "/a/stream/s1/out")
        .unwrap();
    assert_eq!(
        f.recv().unwrap().unwrap(),
        (0, "/a/stream/s1/out".to_string(), b"r".to_vec())
    );
    assert_eq!(
        f.recv().unwrap().unwrap(),
        (1, "/a/stream/s1/out".to_string(), b"y".to_vec())
    );
    assert_eq!(f.recv().unwrap(), None, "a fork ends after its snapshot");
    // (k) NO attach → refused.
    assert!(
        refused(Client::connect(&sock).unwrap().fork_subscribe(
            0,
            "/a/stream/s1/out",
            b"r",
            "/a/stream/s1/out"
        )),
        "un-attached fork must be refused"
    );

    // --- replicate: the SUBJECT and any carried commit group are both scoped -----
    //     A leader ships records at its own offsets; the follower authorizes each one
    //     like a publish, plus the group of any commit annotation it carries. Without
    //     this arm a leader holding a cap for s1 could force a SIBLING tenant's group
    //     offset forward through the replication path (silent cross-tenant data loss).
    // (l) in-scope subject, OUT-of-scope commit group → refused.
    let r = replicate(
        &sock,
        Some(&cap),
        2,
        "/a/stream/s1/out",
        Some(("/a/stream/s2/group/x", u64::MAX)),
    );
    assert!(is_unauthorized(&r), "replicate out-of-scope commit: {r:?}");
    // (m) OUT-of-scope subject, no commit at all → refused.
    let r = replicate(&sock, Some(&cap), 2, "/a/stream/s2/out", None);
    assert!(is_unauthorized(&r), "replicate out-of-scope subject: {r:?}");
    // (n) both in scope → the record is appended at the leader's offset (2, the next
    //     one on this log) and the carried commit advances the in-scope group.
    let r = replicate(
        &sock,
        Some(&cap),
        2,
        "/a/stream/s1/out",
        Some(("/a/stream/s1/group/g", 1)),
    );
    assert_eq!(
        r,
        Response::PublishAck {
            offset: 2,
            deduped: false
        },
        "an in-scope replicate must be accepted"
    );
    // (o) NO attach → refused (the replication path fails closed too).
    let r = replicate(&sock, None, 3, "/a/stream/s1/out", None);
    assert!(is_unauthorized(&r), "un-attached replicate: {r:?}");
}
