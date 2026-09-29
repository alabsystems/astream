//! Claim `broker.cap-keyring-enforced` (fabric R4): a guarded broker's attach is a
//! PROOF OF POSSESSION over a per-connection nonce (the tag never crosses the wire),
//! it is ACKNOWLEDGED (a refused attach is visible at once, not at the next request),
//! it APPENDS to a bounded KEYRING, and the §8.2 authorization matrix — including the
//! principal-derived producer binding that closes dedup-key poisoning, and its
//! deliberate absence on `Replicate` — is applied existentially over that ring.
#![cfg(all(unix, feature = "cap"))]

use astream_broker::broker::MAX_KEYRING;
use astream_broker::client::Subscription;
use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::store::BrokerLog;
use astream_broker::{Broker, BrokerHandle, Client, Request, Response};
use astream_cap::{attach_proof, mint, producer_id_of, Capability};
use std::io::{self, Read, Write};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

const SECRET: &[u8] = b"fabric-broker-secret";

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/askr_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/askr_{tag}_{pid}_{n}.log"),
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
    let broker = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// A connection whose keyring holds `grants`.
fn ring(sock: &str, grants: &[&Capability]) -> Client {
    let mut c = Client::connect(sock).unwrap();
    for g in grants {
        c.attach(&g.filter, &g.tag)
            .unwrap_or_else(|e| panic!("attach {:?}: {e}", g.filter));
    }
    c
}

fn refused<S: Read + Write>(r: io::Result<Subscription<S>>) -> bool {
    match r {
        Err(_) => true,
        Ok(mut s) => s.recv().is_err(),
    }
}

fn unauthorized(e: &io::Error) -> bool {
    e.to_string().contains("unauthorized")
}

/// The subscriber-visible head, learned through the one verb that reads it without
/// delivering anything.
fn head(c: &mut Client, filter: &str) -> u64 {
    let (_, (_, head)) = c.last(filter, "", 0).unwrap();
    head
}

// ---------------------------------------------------------------------------
// The handshake
// ---------------------------------------------------------------------------

/// The attach round trip: `Hello` yields a fresh 32-byte nonce, a genuine proof over
/// it is ACKNOWLEDGED with a `Mark` before any other request, a forged proof is
/// `Error 5`, an `Attach` with no preceding `Hello` is refused, and a captured attach
/// replayed on a second connection is refused.
#[test]
fn attach_is_a_proof_over_a_nonce_and_is_acknowledged() {
    let p = fresh("hs");
    let (_b, _h) = serve(&p);
    let cap = mint(SECRET, "ro:/f/F/pub/>").unwrap();

    // (1) Attach with NO preceding Hello → Error 5, naming the missing Hello.
    let mut raw = Client::connect(&p.sock).unwrap().into_stream();
    write_frame(
        &mut raw,
        &encode_request(&Request::Attach {
            grant: cap.filter.clone(),
            proof: vec![0u8; 32],
        }),
    )
    .unwrap();
    match decode_response(&read_frame(&mut raw).unwrap().unwrap()).unwrap() {
        Response::Error { code, msg } => {
            assert_eq!(code, 5);
            assert!(msg.contains("Hello"), "{msg}");
        }
        other => panic!("expected Error 5, got {other:?}"),
    }

    // (2) Hello → a 32-byte nonce, and two connections get DIFFERENT nonces.
    let mut a = Client::connect(&p.sock).unwrap();
    let mut b = Client::connect(&p.sock).unwrap();
    let na = a.hello().unwrap();
    let nb = b.hello().unwrap();
    assert_ne!(na, nb, "each connection gets its own nonce");

    // (3) A genuine proof is acknowledged with a Mark, BEFORE any other request —
    //     and it hands the client the head for free.
    let proof = attach_proof(&cap.tag, &na, &cap.filter);
    assert_ne!(
        proof.as_slice(),
        cap.tag.as_slice(),
        "the proof is not the tag, and the tag never goes on the wire"
    );
    assert_eq!(
        a.attach_with_proof(&cap.filter, &proof).unwrap(),
        (0, 0),
        "an empty log's head"
    );

    // (4) A forged proof (right grant, wrong bytes) → refused at the attach.
    let e = b.attach_with_proof(&cap.filter, &[7u8; 32]).unwrap_err();
    assert!(unauthorized(&e), "{e}");

    // (5) The CAPTURED attach frame from (3), replayed on a SECOND connection, is
    //     refused: the proof is bound to the nonce of the connection it was made for.
    let mut c = Client::connect(&p.sock).unwrap();
    c.hello().unwrap();
    let e = c.attach_with_proof(&cap.filter, &proof).unwrap_err();
    assert!(unauthorized(&e), "a replayed attach must be refused: {e}");
    assert!(
        refused(c.subscribe(0, "/f/F/pub/x")),
        "and the ring stayed empty"
    );
}

/// The keyring: `Attach` APPENDS, a repeated grant string REPLACES rather than
/// growing it, and the ring is bounded — the 17th distinct grant is refused while the
/// 16 already on it keep working.
#[test]
fn the_keyring_appends_dedups_and_is_bounded() {
    let p = fresh("ring");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    let caps: Vec<Capability> = (0..MAX_KEYRING)
        .map(|i| mint(SECRET, &format!("ro:/f/F/k{i}/>")).unwrap())
        .collect();
    for cap in &caps {
        c.attach(&cap.filter, &cap.tag).unwrap();
    }
    // A repeated grant REPLACES: it does not consume a slot.
    c.attach(&caps[0].filter, &caps[0].tag).unwrap();

    let one_more = mint(SECRET, "ro:/f/F/overflow/>").unwrap();
    let e = c.attach(&one_more.filter, &one_more.tag).unwrap_err();
    assert!(e.to_string().contains("keyring is full"), "{e}");

    // EVERY grant on the full ring still authorizes its own subtree — sampling the
    // first and the last would not show that a middle slot was clobbered.
    for i in 0..MAX_KEYRING {
        assert!(
            c.last(&format!("/f/F/k{i}/>"), "", 8).is_ok(),
            "grant {i} is still on the ring"
        );
    }
    // The refused grant authorizes nothing.
    assert!(refused(c.subscribe(0, "/f/F/overflow/x")));
}

/// AN ATTACH REFUSED FOR A FULL RING APPENDS NOTHING. A bound read-write grant's
/// attach binds its principal's derived producer id with a DURABLE `/a/bind` record;
/// that append used to run before the ring's capacity was even consulted, so every
/// refused attach left a committed record behind — a refusal that was not atomic with
/// respect to the log, against a store whose whole discipline is that a refusal leaves
/// the file untouched.
#[test]
fn an_attach_refused_for_a_full_ring_appends_no_binding() {
    let p = fresh("ringbind");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    for i in 0..MAX_KEYRING {
        let cap = mint(SECRET, &format!("ro:/f/F/k{i}/>")).unwrap();
        c.attach(&cap.filter, &cap.tag).unwrap();
    }
    // Read-only grants bind nothing, so the log is still empty.
    let mut probe = ring(&p.sock, &[&mint(SECRET, "ro:/f/>").unwrap()]);
    assert_eq!(head(&mut probe, "/f/>"), 0);

    for n in 0..3 {
        let over = mint(SECRET, &format!("rw,p=n-x{n}:/f/F/pub/n-x{n}/>")).unwrap();
        let e = c.attach(&over.filter, &over.tag).unwrap_err();
        assert!(e.to_string().contains("keyring is full"), "{e}");
    }
    assert_eq!(
        head(&mut probe, "/f/>"),
        0,
        "three refused attaches appended three /a/bind records"
    );
}

// ---------------------------------------------------------------------------
// The §8.2 matrix
// ---------------------------------------------------------------------------

/// A read-only grant reads its whole subtree — `Subscribe`, `Last` and `Fetch` — and
/// writes nothing: `Publish` and `Commit` are refused.
#[test]
fn a_read_only_grant_reads_everything_and_writes_nothing() {
    let p = fresh("ro");
    let (_b, _h) = serve(&p);
    let writer = mint(SECRET, "rw,p=h-a:/f/F/>").unwrap();
    let reader = mint(SECRET, "ro:/f/F/>").unwrap();

    let mut w = ring(&p.sock, &[&writer]);
    let (halt_off, _) = w
        .publish(producer_id_of("h-a"), 1, "/f/F/fleet/h-a/halt", b"state=on")
        .unwrap();

    let mut r = ring(&p.sock, &[&reader]);
    let (page, _) = r.last("/f/F/fleet/*/halt", "", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].0, halt_off);
    let (page, _) = r.fetch(0, "/f/F/>", 8).unwrap();
    assert_eq!(page.len(), 1, "the /a/bind record is not in a fetch page");

    let e = r
        .publish(producer_id_of("h-b"), 1, "/f/F/fleet/h-b/halt", b"x")
        .unwrap_err();
    assert!(unauthorized(&e), "a read-only grant must not publish: {e}");
    let e = r.commit("/f/F/cur/n1/x", 0).unwrap_err();
    assert!(unauthorized(&e), "a read-only grant must not commit: {e}");

    let mut sub = ring(&p.sock, &[&reader])
        .subscribe(0, "/f/F/fleet/>")
        .unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().0, halt_off);
}

/// TWO grants on ONE connection, each doing half the job: a read-only grant on the
/// broadcast subtree plus a read-write grant on the node's own cursor subtree makes
/// `SubscribeGroup{group in cur/, filter in fleet/}` legal — which NEITHER grant
/// authorizes alone. That is what the ring is for.
#[test]
fn a_group_subscribe_is_authorized_across_two_grants_never_by_one() {
    let p = fresh("two");
    let (_b, _h) = serve(&p);
    let fleet_ro = mint(SECRET, "ro:/f/F/fleet/>").unwrap();
    let cur_rw = mint(SECRET, "rw,p=n-1:/f/F/cur/n-1/>").unwrap();
    let group = "/f/F/cur/n-1/node/inbox";

    // Either grant ALONE is not enough.
    assert!(
        refused(ring(&p.sock, &[&fleet_ro]).subscribe_group(group, "/f/F/fleet/>")),
        "read-only alone cannot commit the group"
    );
    assert!(
        refused(ring(&p.sock, &[&cur_rw]).subscribe_group(group, "/f/F/fleet/>")),
        "the cursor grant alone does not contain the filter"
    );
    // Both, on ONE connection, are.
    let mut sub = ring(&p.sock, &[&fleet_ro, &cur_rw])
        .subscribe_group(group, "/f/F/fleet/>")
        .unwrap();

    let writer = mint(SECRET, "rw,p=h-a:/f/F/fleet/h-a/>").unwrap();
    ring(&p.sock, &[&writer])
        .publish(producer_id_of("h-a"), 1, "/f/F/fleet/h-a/notice", b"hi")
        .unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"hi".to_vec());
}

/// DEDUP-KEY POISONING, closed. A bound grant may publish ONLY under the producer id
/// the broker derives from its principal, so a co-permitted publisher can no longer
/// pre-take a peer's `(producer_id, producer_seq)` and make the peer's genuine record
/// dedup away to the attacker's offset.
#[test]
fn a_bound_grant_cannot_publish_under_another_principals_producer_id() {
    let p = fresh("poison");
    let (_b, _h) = serve(&p);
    // A and B may both write the same subtree — the co-permitted case.
    let a = mint(SECRET, "rw,p=s-aaaa:/f/F/in/>").unwrap();
    let b = mint(SECRET, "rw,p=s-bbbb:/f/F/in/>").unwrap();
    let (a_pid, b_pid) = (producer_id_of("s-aaaa"), producer_id_of("s-bbbb"));
    assert_ne!(a_pid, b_pid);

    // A tries to pre-take B's next key: refused before anything is staged.
    let mut ac = ring(&p.sock, &[&a]);
    let e = ac
        .publish(b_pid, 5, "/f/F/in/n1/s1/s-aaaa/ask", b"poison")
        .unwrap_err();
    assert!(
        unauthorized(&e),
        "a foreign producer id must be refused: {e}"
    );
    // A's own key works.
    let (a_off, a_dup) = ac
        .publish(a_pid, 5, "/f/F/in/n1/s1/s-aaaa/ask", b"mine")
        .unwrap();
    assert!(!a_dup);

    // B's GENUINE publish at the very key A tried to take is NOT deduped.
    let mut bc = ring(&p.sock, &[&b]);
    let (b_off, b_dup) = bc
        .publish(b_pid, 5, "/f/F/in/n1/s1/s-bbbb/ask", b"genuine")
        .unwrap();
    assert!(
        !b_dup,
        "B's record was not silently dropped onto A's offset"
    );
    assert_ne!(a_off, b_off);

    // Both records are really on the log, with their own bodies.
    let reader = mint(SECRET, "ro:/f/F/in/>").unwrap();
    let (page, _) = ring(&p.sock, &[&reader])
        .last("/f/F/in/n1/s1/*/ask", "", 8)
        .unwrap();
    let mut bodies: Vec<Vec<u8>> = page.into_iter().map(|(_, _, b)| b).collect();
    bodies.sort();
    assert_eq!(bodies, vec![b"genuine".to_vec(), b"mine".to_vec()]);

    // The read-process-write path carries the same binding.
    let e = ac
        .process_and_produce(
            b_pid,
            6,
            "/f/F/in/n1/s1/s-aaaa/ack",
            b"x",
            "/f/F/in/n1/s1/s-aaaa/g",
            0,
        )
        .unwrap_err();
    assert!(unauthorized(&e), "rpw under a foreign producer id: {e}");
}

/// An UNBOUND read-write grant is the god cap and keeps that power — every capability
/// minted before the grant string existed is one — which is exactly why the broker
/// warns at attach and why `asb mint` is meant to require an explicit mode.
#[test]
fn an_unbound_grant_still_publishes_under_any_producer_id() {
    let p = fresh("unbound");
    let (_b, _h) = serve(&p);
    let root = mint(SECRET, "/f/F/>").unwrap(); // a bare filter: read-write, unbound
    let mut c = ring(&p.sock, &[&root]);
    assert_eq!(c.publish(1, 1, "/f/F/x", b"a").unwrap(), (0, false));
    assert_eq!(
        c.publish(producer_id_of("h-someone-else"), 1, "/f/F/x", b"b")
            .unwrap(),
        (1, false)
    );
}

/// The `in` face's shape is enforced by the GRANT, not by convention: the `<src>`
/// segment is the one a sender cannot choose, and a trailing `*` admits exactly one
/// kind segment — so an over-long subject whose tail READS as `<src>/<kind>` cannot
/// impersonate anyone.
#[test]
fn the_sender_segment_and_the_kind_segment_are_both_pinned_by_the_grant() {
    let p = fresh("inface");
    let (_b, _h) = serve(&p);
    let s1 = mint(SECRET, "rw,p=s-1111:/f/F/in/*/*/s-1111/*").unwrap();
    let pid = producer_id_of("s-1111");
    let mut c = ring(&p.sock, &[&s1]);

    let e = c
        .publish(pid, 1, "/f/F/in/n2/s2/s-9999/ask", b"x")
        .unwrap_err();
    assert!(unauthorized(&e), "a forged sender segment: {e}");
    let e = c
        .publish(pid, 2, "/f/F/in/n2/s2/s-1111/h-andrew/answer", b"x")
        .unwrap_err();
    assert!(unauthorized(&e), "an eight-segment in subject: {e}");

    let (off, _) = c.publish(pid, 3, "/f/F/in/n2/s2/s-1111/ask", b"x").unwrap();
    let reader = mint(SECRET, "ro:/f/F/in/n2/>").unwrap();
    let mut sub = ring(&p.sock, &[&reader])
        .subscribe(0, "/f/F/in/n2/>")
        .unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (off, "/f/F/in/n2/s2/s-1111/ask".to_string(), b"x".to_vec()),
        "the pinned seven-segment shape lands and is delivered with that subject"
    );
}

/// `Replicate` needs a LINK GRANT — read-write, filter-matching, and UNBOUND. A
/// follower link ships the ORIGINAL producer's id, which no bound grant's principal
/// could ever derive, so the verb is not reachable from a bound `rw` grant at all.
///
/// This is the closure of dedup-key poisoning on the ONE verb that was outside it.
/// While `Replicate` was authorized by SUBJECT alone, any bound `rw` grant could write
/// a record under ANY producer id: the dedup map is keyed `(producer_id, producer_seq)`
/// with NO subject component, so the holder never even had to be co-permitted on the
/// victim's subtree — it burned the victim's keys from inside its own grant, and the
/// victim's genuine publish then deduped silently away at the attacker's offset.
#[test]
fn replicate_needs_an_unbound_link_grant_and_a_bound_one_cannot_reach_it() {
    let p = fresh("repl");
    let (_b, _h) = serve(&p);
    let bound = mint(SECRET, "rw,p=n-follow:/f/F/>").unwrap();
    let link = mint(SECRET, "/f/F/>").unwrap(); // UNBOUND rw: the follower link's grant
    let foreign_pid = producer_id_of("s-original");
    assert_ne!(producer_id_of("n-follow"), foreign_pid);

    let mut c = ring(&p.sock, &[&bound]);
    let start = head(&mut c, "/f/F/>");

    let replicate = |cap: &Capability, seq: u64, pid: u64, subject: &str, commit| {
        let mut s = ring(&p.sock, &[cap]).into_stream();
        write_frame(
            &mut s,
            &encode_request(&Request::Replicate {
                seq,
                producer_id: pid,
                producer_seq: 1,
                subject: subject.to_string(),
                body: b"r".to_vec(),
                commit,
            }),
        )
        .unwrap();
        decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap()
    };

    // THE BOUND GRANT CANNOT REPLICATE AT ALL — not under a foreign producer id...
    let r = replicate(&bound, start, foreign_pid, "/f/F/pub/n1/s1/ev", None);
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("unauthorized")),
        "a bound grant replicating a foreign producer id: {r:?}"
    );
    // ...and not even under its OWN, because a link grant is a distinct authority.
    let r = replicate(
        &bound,
        start,
        producer_id_of("n-follow"),
        "/f/F/pub/n1/s1/ev",
        None,
    );
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("unauthorized")),
        "a bound grant is not a link grant: {r:?}"
    );
    // Nothing landed: the head has not moved.
    assert_eq!(
        head(&mut c, "/f/F/>"),
        start,
        "a refused Replicate appends nothing"
    );

    // THE UNBOUND LINK GRANT replicates the original producer's record.
    assert_eq!(
        replicate(&link, start, foreign_pid, "/f/F/pub/n1/s1/ev", None),
        Response::PublishAck {
            offset: start,
            deduped: false
        }
    );
    // Its subject is still scoped...
    let r = replicate(&link, start + 1, foreign_pid, "/elsewhere/x", None);
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("unauthorized")),
        "an out-of-scope subject: {r:?}"
    );
    // ...and so is a carried commit group.
    let scoped_link = mint(SECRET, "/f/F/cur/>").unwrap();
    let r = replicate(
        &scoped_link,
        start + 1,
        foreign_pid,
        "/f/F/cur/n1/x",
        Some(("/other/group".to_string(), 0)),
    );
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("unauthorized")),
        "an out-of-scope commit group: {r:?}"
    );
    // The same foreign id on an ordinary Publish IS refused, as it always was.
    let e = c
        .publish(foreign_pid, 1, "/f/F/pub/n1/s1/ev", b"x")
        .unwrap_err();
    assert!(
        unauthorized(&e),
        "the binding still applies to Publish: {e}"
    );
}

/// THE POISONING, END TO END: the shape the audit reproduced. A holder of the minimal
/// designed session grant tries to burn a victim node's dedup key through `Replicate`
/// on a subject INSIDE its own subtree — the dedup map has no subject component, so
/// that used to be enough — and the victim's genuine record then lands, on its own
/// subject, NOT deduped.
#[test]
fn a_bound_grant_cannot_burn_a_peers_dedup_key_through_replicate() {
    let p = fresh("poison");
    let (_b, _h) = serve(&p);
    let mallory = mint(SECRET, "rw,p=s-mallory:/f/F/in/*/*/s-mallory/*").unwrap();
    let victim = mint(SECRET, "rw,p=n-victim:/f/F/pub/n-victim/>").unwrap();
    let vpid = producer_id_of("n-victim");

    let mut m = ring(&p.sock, &[&mallory]);
    let h = head(&mut m, "/f/F/in/*/*/s-mallory/*");
    let mut s = m.into_stream();
    write_frame(
        &mut s,
        &encode_request(&Request::Replicate {
            seq: h,
            producer_id: vpid,
            producer_seq: 7,
            subject: "/f/F/in/n1/s1/s-mallory/ask".to_string(),
            body: Vec::new(),
            commit: None,
        }),
    )
    .unwrap();
    let r = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("unauthorized")),
        "Mallory took the victim's dedup key: {r:?}"
    );
    drop(s);

    // The victim's genuine record lands, at its OWN offset, not deduped.
    let mut v = ring(&p.sock, &[&victim]);
    let vh = head(&mut v, "/f/F/pub/n-victim/>");
    assert_eq!(
        v.publish(vpid, 7, "/f/F/pub/n-victim/presence", b"state=up")
            .unwrap(),
        (vh, false),
        "the victim's record was discarded as a duplicate of a record it never made"
    );
    let (page, _) = v.last("/f/F/pub/n-victim/>", "", 8).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(page[0].2, b"state=up".to_vec());
}

/// A HIDDEN subject is not replicable into a broker that OWNS its log. `/a/will` and
/// `/a/bind` must replicate — a follower's log is the leader's spine byte for byte —
/// but on a broker that is not a replication target they are an injection: an injected
/// `/a/will` is an arbitrary publish, under an arbitrary producer id, executed by the
/// broker itself at its next open, outside the whole capability matrix.
///
/// SCOPE: this is the SETTLED log, and it is the only shape this file can pin. Its seed
/// `publish` blocks on the ack, so the head is already promoted when the `Replicate`
/// frames go out — and while the rule lived on the CONNECTION thread, reading that
/// promoted head with the append happening later in the writer, that was the one
/// arrangement in which it was sound. A record staged and not yet promoted (an unacked
/// pipelined publish ahead of the hidden frame) defeated it, and no client-side
/// arrangement makes that window open on demand. The rule now lives in
/// `BrokerLog::stage_replica`, under the lock that appends and independent of
/// guarding, so the general property is pinned deterministically there
/// (`store.rs`, `a_hidden_replicate_is_refused_once_this_batch_has_staged_a_record`)
/// and end to end over a socket in `tests/replica_injection.rs`. What THIS test
/// carries is the capability half: the attacker's `/a/>` god cap does not buy the
/// injection.
#[test]
fn a_hidden_subject_cannot_be_injected_by_replicate_into_a_log_this_broker_owns() {
    let p = fresh("inject");
    let sock2 = format!("{}.2", p.sock);
    // The attacker's cap is UNBOUND rw over astream's own subtree — a god cap by any
    // reading, and still not enough. It grants NOTHING on /f/.
    let root = mint(SECRET, "/a/>").unwrap();
    let seed = mint(SECRET, "/f/F/>").unwrap();
    let halt = "/f/F/fleet/h-andrew/halt";

    let b = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let mut h = b.serve(&p.sock).unwrap();

    // The log is a broker's own from its first record on.
    let mut w = ring(&p.sock, &[&seed]);
    let (_, _) = w.publish(1, 1, "/f/F/pub/n1/x", b"seed").unwrap();
    let start = head(&mut w, "/f/F/>");
    assert!(start > 0);

    // A direct publish to the fleet lane is refused (no /f/ grant on this ring).
    let mut a = ring(&p.sock, &[&root]);
    assert!(unauthorized(
        &a.publish(0xDEAD, 1, halt, b"state=on").unwrap_err()
    ));

    // ...and so is the same write smuggled in as a will through `Replicate`.
    let mut body = (halt.len() as u32).to_le_bytes().to_vec();
    body.extend_from_slice(halt.as_bytes());
    body.extend_from_slice(b"state=on");
    let mut s = a.into_stream();
    for subject in ["/a/will", "/a/bind"] {
        write_frame(
            &mut s,
            &encode_request(&Request::Replicate {
                seq: start,
                producer_id: 0xDEAD,
                producer_seq: u64::MAX,
                subject: subject.to_string(),
                body: body.clone(),
                commit: None,
            }),
        )
        .unwrap();
        let r = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
        assert!(
            matches!(&r, Response::Error { msg, .. } if msg.contains("reserved subject")),
            "{subject} was injected: {r:?}"
        );
    }
    drop(s);
    assert_eq!(head(&mut w, "/f/F/>"), start, "nothing was appended");
    drop(w);
    h.shutdown();

    // And the next open publishes no forged will: the log holds none.
    let b2 = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let reader = mint(SECRET, "ro:/f/>").unwrap();
    let mut r = ring(&sock2, &[&reader]);
    assert_eq!(
        r.last("/f/>", "", 64).unwrap().0.len(),
        1,
        "only the seed record: no fleet-halt row was ever published"
    );
}

// ---------------------------------------------------------------------------
// The binding table
// ---------------------------------------------------------------------------

/// The `/a/bind` table: a bound grant's attach records `producer id -> principal`
/// durably, re-attaching the same principal appends nothing, the record is invisible
/// to every reader, and the table is rebuilt on open.
#[test]
fn a_binding_is_durable_idempotent_invisible_and_rebuilt_on_open() {
    let p = fresh("bind");
    let sock2 = format!("{}.2", p.sock);
    let cap = mint(SECRET, "rw,p=n-node1:/f/F/pub/n-node1/>").unwrap();
    let pid = producer_id_of("n-node1");
    {
        let b = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
        let mut h = b.serve(&p.sock).unwrap();
        // The bind record consumed offset 0, so the first publish lands at 1.
        let mut c = ring(&p.sock, &[&cap]);
        assert_eq!(
            c.publish(pid, 1, "/f/F/pub/n-node1/x", b"v").unwrap(),
            (1, false)
        );
        // Re-attaching the SAME principal appends nothing: the next offset is 2.
        let mut c2 = ring(&p.sock, &[&cap]);
        assert_eq!(
            c2.publish(pid, 2, "/f/F/pub/n-node1/x", b"w").unwrap(),
            (2, false),
            "the second attach did not append a second bind record"
        );
        drop(c);
        drop(c2);
        h.shutdown();
    }
    {
        let log = BrokerLog::open(&p.log).unwrap();
        assert_eq!(
            log.binding(pid).map(|(p, _)| p.to_string()).as_deref(),
            Some("n-node1"),
            "rebuilt from the stored /a/bind record"
        );
    }

    let b2 = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let reader = mint(SECRET, "ro:/a/>").unwrap();
    let mut r = ring(&sock2, &[&reader]);
    let (page, (_, h)) = r.last("/a/>", "", 64).unwrap();
    assert_eq!(h, 3, "one bind record and two publishes");
    assert!(
        page.is_empty(),
        "a /a/bind record is never in a last-value page"
    );
    assert!(
        r.fetch(0, "/a/>", 64).unwrap().0.is_empty(),
        "and never in a fetch page"
    );

    // ...and never on the DELIVERY path either: a wildcard subscriber over /a/> is
    // handed the ordinary record published beside it, and nothing else.
    let root = mint(SECRET, "/a/>").unwrap();
    let mut w = ring(&sock2, &[&root]);
    assert_eq!(w.publish(9, 1, "/a/visible", b"seen").unwrap(), (3, false));
    let mut sub = ring(&sock2, &[&reader]).subscribe(0, "/a/>").unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (3, "/a/visible".to_string(), b"seen".to_vec()),
        "the /a/bind record at offset 0 was skipped, not delivered"
    );

    // The binding was REBUILT: re-attaching the same principal still appends nothing.
    let mut c = ring(&sock2, &[&cap]);
    assert_eq!(
        c.publish(pid, 3, "/f/F/pub/n-node1/x", b"z").unwrap(),
        (4, false)
    );
}

/// A producer id already bound to a DIFFERENT principal refuses the attach (`Error 5`,
/// "producer id collision") — the belt-and-braces behind `producer_id_of`'s 2^64
/// second-preimage cost, and the refusal survives a broker restart because `/a/bind`
/// is rebuilt on open.
///
/// A real SHA-256/64 collision cannot be searched for in a test, so the table is
/// forced into the colliding state through the leader→follower `Replicate` verb (which
/// ships whole records, hidden ones included, under a grant that matches them) rather
/// than pretended into it.
#[test]
fn a_producer_id_already_bound_to_another_principal_refuses_the_attach() {
    let p = fresh("collide");
    let sock2 = format!("{}.2", p.sock);
    let victim = mint(SECRET, "rw,p=n-victim:/f/F/>").unwrap();
    let pid = producer_id_of("n-victim");

    let b = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let mut h = b.serve(&p.sock).unwrap();

    // Force the collision: bind n-victim's derived id to a DIFFERENT principal.
    let root = mint(SECRET, "/a/>").unwrap(); // unbound rw over astream's own subtree
    let mut s = ring(&p.sock, &[&root]).into_stream();
    write_frame(
        &mut s,
        &encode_request(&Request::Replicate {
            seq: 0,
            producer_id: pid,
            producer_seq: 0,
            subject: "/a/bind".to_string(),
            body: b"n-imposter".to_vec(),
            commit: None,
        }),
    )
    .unwrap();
    assert_eq!(
        decode_response(&read_frame(&mut s).unwrap().unwrap()),
        Some(Response::PublishAck {
            offset: 0,
            deduped: false
        })
    );

    // The victim's own grant can no longer attach: its derived id is taken.
    let mut c = Client::connect(&p.sock).unwrap();
    let e = c.attach(&victim.filter, &victim.tag).unwrap_err();
    assert!(
        e.to_string().contains("producer id collision"),
        "expected a collision refusal, got: {e}"
    );
    assert!(
        c.publish(pid, 1, "/f/F/x", b"x").is_err(),
        "and nothing was added to the ring"
    );
    drop(s);
    drop(c);
    h.shutdown();

    // The refusal survives a restart: /a/bind is rebuilt on open.
    let b2 = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut c = Client::connect(&sock2).unwrap();
    let e = c.attach(&victim.filter, &victim.tag).unwrap_err();
    assert!(
        e.to_string().contains("producer id collision"),
        "the binding table must be rebuilt on open: {e}"
    );
}
