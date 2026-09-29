//! Regressions for the broker core: the two ways a durable fact about the log
//! got out of step with what a client was told (`broker.will-fires-exactly-once`), and
//! the paging, streaming and bound defects found beside them.
//!
//! MOST tests here FAIL on the pre-fix code; two are CHARACTERIZATION tests, pinning
//! behaviour a fix deliberately left alone, and each says so in its own doc:
//! `a_replica_still_appends_a_clients_write_and_the_doc_says_so` (the fix there was to
//! the documentation, so the assertions hold on the pre-fix tree too) and
//! `an_empty_log_is_still_declared_by_the_first_record_a_leader_ships` (pre-fix
//! `stage_replica` marked on every extending record, so an empty log taking a leader's
//! first record was marked there too — what the fix narrowed is the case its sibling
//! `an_echoed_replicate_does_not_convert_an_owned_log_into_a_replica` covers). They are
//! kept because what they pin is what the narrowing must not break.
//!
//! No sleeps as synchronisation: each step
//! blocks on an ack, a delivery, or a joined writer thread. The one polling loop
//! (`the_ack_writer_does_not_override_the_connections_write_timeout`) is a HANG
//! DETECTOR with a deliberately generous deadline, not a performance assertion — the
//! difference it separates is 150 ms from 10 s.
#![cfg(unix)]

use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::store::{BrokerLog, Durability, MAX_SUBJECTS_PER_PRODUCER};
use astream_broker::{Broker, BrokerHandle, Client, Request, Response};
use astream_wire::Filter;
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr2core_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr2core_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    let _ = std::fs::remove_file(format!("{}.replica", p.log));
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

/// The design's incarnation rule: a will publishes at the RESERVED TOP of its
/// incarnation's sequence space.
fn will_seq(inc: u64) -> u64 {
    (inc << 32) | 0xFFFF_FFFF
}

const PRESENCE: &str = "/f/F/pub/n1/node/presence";
const PID: u64 = 7;

/// AN ECHO IS NOT A DECLARATION. `stage_replica` used to write the durable
/// `<log>.replica` marker on EVERY accepted `Replicate`, including the branch that
/// appends nothing at all: a record already held byte for byte. So any client on the
/// socket could `fetch` record 0, echo it back as a `Replicate`, receive
/// `PublishAck{deduped: true}` — and leave the broker permanently unable to fire a
/// will, for every producer on it, with zero new bytes on the log, no line anywhere,
/// and no verb to undo it.
///
/// A log this broker OWNS — one that already holds records of its own — is not
/// converted by anything a reader can construct. A follower seeded from a copy is
/// DECLARED, with `Broker::open_replica`.
#[test]
fn an_echoed_replicate_does_not_convert_an_owned_log_into_a_replica() {
    let p = fresh("echo");
    let snap = format!("{}.snap", p.log);
    let _ = std::fs::remove_file(&snap);
    let _ = std::fs::remove_file(format!("{snap}.replica"));
    let sock2 = format!("{}.2", p.sock);
    let _ = std::fs::remove_file(&sock2);
    {
        let (b, mut h) = serve(&p);
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(PID, will_seq(1), PRESENCE, b"v=1 state=gone inc=1")
            .unwrap();
        assert_eq!(
            c.publish(PID, 1, PRESENCE, b"v=1 state=live inc=1")
                .unwrap(),
            (1, false)
        );

        // THE ATTACK, on a second connection and with no capability of any kind: read
        // record 1 back and ship it in again as a `Replicate` at its own offset.
        let (page, (next, _head)) = Client::connect(&p.sock)
            .unwrap()
            .fetch(1, PRESENCE, 1)
            .unwrap();
        assert_eq!((page.len(), next), (1, 2));
        let mut s = Client::connect(&p.sock).unwrap().into_stream();
        write_frame(
            &mut s,
            &encode_request(&Request::Replicate {
                seq: 1,
                producer_id: PID,
                producer_seq: 1,
                subject: PRESENCE.to_string(),
                body: b"v=1 state=live inc=1".to_vec(),
                commit: None,
            }),
        )
        .unwrap();
        let echoed = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
        drop(s);

        // The echo appends nothing either way — that is what makes it free, and what
        // made marking on it so cheap an attack.
        assert_eq!(b.head(), 2, "the echo appended nothing");
        assert!(
            matches!(
                echoed,
                Response::PublishAck {
                    offset: 1,
                    deduped: true
                }
            ) || matches!(echoed, Response::Error { .. }),
            "an echo is answered as a dedup or refused, never as a new record: {echoed:?}"
        );
        // THE PROPERTY, directly: the durable marker beside the log was not written.
        assert!(
            !std::path::Path::new(&format!("{}.replica", p.log)).exists(),
            "a byte-identical echo wrote the durable replica marker: will-firing is now \
             off for every producer on this broker, permanently, and the only undo is \
             an operator finding and deleting that file"
        );
        // Snapshot the log AND whatever marker sits beside it — a broker restart reads
        // both — so the consequence below is the one an operator would meet.
        std::fs::copy(&p.log, &snap).unwrap();
        let _ = std::fs::copy(format!("{}.replica", p.log), format!("{snap}.replica"));
        drop(c);
        h.shutdown();
    }
    assert!(
        !BrokerLog::open(&snap).unwrap().is_replica(),
        "an echo made the log a replica"
    );

    // And the consequence that matters: the will the log holds still fires on open.
    let b2 = Broker::open(&snap).unwrap();
    let mut h2 = b2.serve(&sock2).unwrap();
    let mut sub = Client::connect(&sock2)
        .unwrap()
        .subscribe(0, "/f/>")
        .unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"v=1 state=live inc=1");
    let (_, subject, body) = sub.recv().unwrap().unwrap();
    assert_eq!(
        (subject.as_str(), body.as_slice()),
        (PRESENCE, b"v=1 state=gone inc=1".as_slice()),
        "the will did not fire: one echoed frame disabled presence for the whole broker"
    );
    drop(sub);
    h2.shutdown();
}

/// The SHIPPED follower bring-up is unchanged: a follower that starts on an EMPTY log
/// through a plain `Broker::open` is declared by the leader's first shipped record, and
/// stays declared across its own restart. (`tests/will.rs` proves the consequence — a
/// follower restart fires none of the leader's wills. This pins the declaration itself,
/// beside the echo case above, so the two rules are read together.)
#[test]
fn an_empty_log_is_still_declared_by_the_first_record_a_leader_ships() {
    let p = fresh("bringup");
    let llog = format!("{}.leader", p.log);
    let _ = std::fs::remove_file(&llog);
    let follower = Broker::open(&p.log).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&p.sock).unwrap();

    let mut node = Client::connect(&p.sock).unwrap();
    assert_eq!(node.publish(PID, 1, PRESENCE, b"live").unwrap(), (0, false));
    assert_eq!(follower.head(), 1, "the follower took the leader's record");

    drop(node);
    lh.shutdown();
    drop(follower);
    fh.shutdown();
    assert!(
        std::path::Path::new(&format!("{}.replica", p.log)).exists(),
        "an EMPTY log that takes a leader's record declares itself"
    );
    assert!(BrokerLog::open(&p.log).unwrap().is_replica());
}

/// A WILL THE LOG HOLDS IS A WILL THE CONNECTION HOLDS. On the Replicated tier the
/// `/a/will` record is committed locally FIRST and the ack is decided afterwards, from
/// the quorum watermark — so with a follower down the client was told "will was not
/// persisted" for a record the leader's log went on to hold. The connection's
/// in-memory will stayed `None`, nothing fired at connection end, and the NEXT OPEN
/// fired it from the log: a `gone` for a producer that believed it registered nothing,
/// and one the fence cannot reach (a will sits at the reserved top of its incarnation,
/// above every ordinary publish of that incarnation).
///
/// The registration is broker-internal bookkeeping that no subscriber ever sees, so it
/// is acked on its own commit. Either the client is told the will exists and it fires,
/// or it is told nothing was persisted and the log holds nothing — never one and then
/// the other.
#[test]
fn a_will_registered_without_a_quorum_is_the_will_the_connection_fires() {
    let p = fresh("quorum");
    let flog = format!("{}.follower", p.log);
    let _ = std::fs::remove_file(&flog);
    let _ = std::fs::remove_file(format!("{flog}.replica"));
    // The follower is up at open (a quorum that could never be met is refused there),
    // then goes away: from here nothing reaches a quorum and every ordinary publish is
    // answered "not replicated to quorum".
    let follower = Broker::open(&flog).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&p.log, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&p.sock).unwrap();
    drop(follower);
    fh.shutdown();
    let mut c = Client::connect(&p.sock).unwrap();

    // The will registers. Its record is on the leader's log whatever the follower did,
    // so the answer must be the record's own fate.
    c.will(PID, will_seq(1), PRESENCE, b"v=1 state=gone inc=1")
        .unwrap();
    assert_eq!(leader.head(), 1, "the /a/will record is on the log");

    // The bridge goes on publishing `live` under ORDINARY sequences of the same
    // incarnation, every one of them nacked for quorum and every one of them below the
    // will's reserved-top sequence, so the fence can never suppress the will.
    for n in 1..=3u64 {
        let e = c
            .publish(PID, (1 << 32) | n, PRESENCE, b"v=1 state=live inc=1")
            .unwrap_err();
        assert!(e.to_string().contains("quorum"), "{e}");
    }
    assert_eq!(leader.head(), 4);

    // The connection ends. Because the registration was acknowledged, the connection
    // HELD the will and fired it here — which is what makes the goodbye a statement
    // about this connection rather than about the broker's next restart.
    drop(c);
    lh.shutdown();
    drop(leader);

    let _ = std::fs::remove_file(&flog);
    let _ = std::fs::remove_file(format!("{flog}.replica"));
    let log = BrokerLog::open(&p.log).unwrap();
    let fired = log
        .read_from(astream_wire::Offset(0))
        .iter()
        .any(|r| r.subject == PRESENCE && r.producer_seq == will_seq(1));
    assert!(
        fired,
        "the will was acknowledged and then not fired at connection end: the log holds \
         the /a/will record the client was told was not persisted, and the next open \
         would publish a `gone` for a producer that is alive"
    );
}

/// A FORK SNAPSHOT SAYS WHEN IT IS COMPLETE. The snapshot used to end with a bare EOF,
/// which `Subscription::recv` reports as `Ok(None)` — the same answer a connection torn
/// down mid-snapshot gives. With the per-connection write bound now armed for the whole
/// life of the socket, a fork reader slower than the broker's writer could be cut off
/// mid-history and could not tell. The closing `Mark` is the difference.
#[test]
fn a_fork_snapshot_ends_with_a_mark_not_a_bare_eof() {
    use astream_broker::Event;
    let p = fresh("fork");
    let (b, mut h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();
    for i in 0..4u64 {
        c.publish(1, i, "/f/F/x", format!("m{i}").as_bytes())
            .unwrap();
    }
    let head = b.visible_head();

    let mut fork = Client::connect(&p.sock)
        .unwrap()
        .fork_subscribe(2, "/f/F/x", b"SWAPPED", "/f/>")
        .unwrap();
    let mut bodies = Vec::new();
    let mut marked = None;
    loop {
        match fork.recv_event().unwrap() {
            Some(Event::Delivery { body, .. }) => bodies.push(body),
            Some(Event::Mark { next, head }) => marked = Some((next, head)),
            None => break,
        }
    }
    assert_eq!(
        bodies,
        vec![
            b"m0".to_vec(),
            b"m1".to_vec(),
            b"SWAPPED".to_vec(),
            b"m3".to_vec()
        ]
    );
    assert_eq!(
        marked,
        Some((head, head)),
        "a complete fork snapshot is indistinguishable from a truncated one without it"
    );
    drop(c);
    h.shutdown();
}

/// `Broker::open_replica` used to promise, flatly, that "this broker appends NOTHING of
/// its own to the log". Only the will-on-open half was ever enforced: a client that
/// reaches a replica's listener still publishes, and the record lands at the follower's
/// own next offset — which is the divergence the marker exists to prevent, and which
/// `tests/replicated.rs` deliberately performs. The doc now says so; this pins the
/// behaviour it describes, so the sentence and the code cannot drift apart again.
#[test]
fn a_replica_still_appends_a_clients_write_and_the_doc_says_so() {
    let p = fresh("replicadoc");
    {
        // Seed the log the way an operator seeding a follower from a copy would.
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        log.publish(1, 1, "/a/r/x".into(), b"m1".to_vec()).unwrap();
    }
    let b = Broker::open_replica(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();

    // A publisher pointed at the follower's listener is NOT refused.
    let mut c = Client::connect(&p.sock).unwrap();
    assert_eq!(
        c.publish(9, 9, "/a/r/own", b"own").unwrap(),
        (1, false),
        "open_replica does not make the log append-proof — do not expose it to publishers"
    );
    assert_eq!(b.head(), 2);
    drop(c);
    h.shutdown();
}

/// A WILL IS REFUSED AT REGISTRATION IF ITS GOODBYE COULD NOT BE DELIVERED. The will
/// FIRING is an ordinary publish, so it met the per-producer distinct-subject bound
/// like any other record — but its ack is discarded (fire-and-forget), so the refusal
/// reached nobody, the `/a/will` record stayed on the log, and every later open
/// re-attempted and re-failed it. The goodbye was lost permanently and silently.
///
/// The bound now applies at REGISTRATION, where a client is still listening; and the
/// firing is exempt from it, because that subject was already checked and answered for.
#[test]
fn a_will_whose_subject_is_over_the_bound_is_refused_when_it_is_registered() {
    let p = fresh("willbound");
    {
        // Fill producer PID's distinct-subject budget exactly.
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        for i in 0..MAX_SUBJECTS_PER_PRODUCER {
            log.publish(PID, i as u64, format!("/f/F/s/{i:05}"), b"x".to_vec())
                .unwrap();
        }
        assert_eq!(log.subjects_per_producer(PID), MAX_SUBJECTS_PER_PRODUCER);
    }
    let b = Broker::open(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();
    let head = b.head();
    let mut c = Client::connect(&p.sock).unwrap();

    // A will on a NEW subject cannot be delivered, and the client is told so now.
    let e = c
        .will(PID, will_seq(1), PRESENCE, b"gone")
        .expect_err("a will that could never fire was acknowledged");
    assert!(e.to_string().contains("MAX_SUBJECTS_PER_PRODUCER"), "{e}");
    assert_eq!(b.head(), head, "a refused registration appends nothing");

    // A will on a subject the producer ALREADY holds is accepted, and it fires: the
    // firing is exempt from the bound, so an accepted will is always deliverable.
    c.will(PID, will_seq(1), "/f/F/s/00000", b"gone").unwrap();
    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(b.visible_head(), "/f/F/s/00000")
        .unwrap();
    drop(c);
    assert_eq!(sub.recv().unwrap().unwrap().2, b"gone".to_vec());
    drop(sub);
    h.shutdown();
}

/// `Last`'s RESUME CURSOR NEVER NAMES A SUBJECT THE FILTER DOES NOT MATCH. The index
/// walk starts at the filter's LITERAL prefix (`/f/F/in/*/*/n-1/*` -> `/f/F/in/`) and
/// reports the last entry it VISITED; when the scan bound cuts the page, that entry is
/// whatever the walk stopped on, matched or not. Under a prefix as broad as `/f/F/in/`
/// that is routinely another node's, another session's, another human's inbox lane —
/// one out-of-grant subject NAME per over-scanned page, on a fabric where provenance is
/// the address.
///
/// This log holds more than `LAST_SCAN_MAX` subjects under the prefix and NONE that the
/// filter matches, so the pre-fix cursor is always an out-of-scope name.
#[test]
fn lasts_resume_cursor_never_names_a_subject_outside_the_filter() {
    let p = fresh("cursor");
    let n = astream_broker::broker::LAST_SCAN_MAX + 1024;
    {
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        // Distinct subjects under the filter's literal prefix, none of them matching
        // it — other nodes', other sessions', other humans' inbox lanes. Spread over
        // producers so the per-producer distinct-subject bound is not the thing that
        // stops us.
        for i in 0..n {
            let pid = (i / (MAX_SUBJECTS_PER_PRODUCER / 2)) as u64 + 1;
            log.publish(
                pid,
                i as u64,
                format!("/f/F/in/n-{i:06}/s-7/h-andrew/ask"),
                b"x".to_vec(),
            )
            .unwrap();
        }
    }
    let filter = "/f/F/in/*/*/n-1/*";
    let filt = Filter::new(filter).unwrap();
    let b = Broker::open(&p.log).unwrap();
    let mut h = b.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    let (page, _, resume) = c.last_page(filter, "", 64).unwrap();
    assert!(page.is_empty(), "nothing on this log matches the filter");
    assert!(
        resume.is_empty()
            || astream_wire::Subject::new(resume.as_str()).is_ok_and(|s| filt.matches(&s)),
        "the closing Mark handed back {resume:?}, a subject this filter does not match \
         — and so one no capability that contained the filter had to grant"
    );
    drop(c);
    h.shutdown();
}

/// THE PIPELINED ACK-WRITER DOES NOT OVERRIDE `Broker::set_write_timeout`.
/// `set_write_timeout` is `setsockopt(SO_SNDTIMEO)`, a property of the SOCKET rather
/// than of the descriptor, and the ack-writer runs on a `try_clone` of the connection's
/// own socket — so the hard-coded `ACK_WRITE_TIMEOUT` it used to set replaced the
/// operator's configured bound for the whole connection, its own writes included, from
/// the first `Publish` onward. An operator who set 150 ms to bound `MAX_CONNS`
/// exhaustion got 10 s.
///
/// The wait below is a HANG DETECTOR, not a performance assertion: it separates a
/// configured 150 ms from a hard-coded 10 s, and gives the 150 ms case thirty times its
/// budget.
#[test]
fn the_ack_writer_does_not_override_the_connections_write_timeout() {
    use std::io::Write;
    let p = fresh("ackto");
    {
        // Enough bytes that no socket buffer can absorb the page.
        let mut log = BrokerLog::open_with(&p.log, Durability::Relaxed).unwrap();
        let body = vec![b'x'; 8192];
        for i in 0..2000u64 {
            log.publish(i % 4, i, format!("/w/{i:05}"), body.clone())
                .unwrap();
        }
    }
    let b = Broker::open(&p.log).unwrap();
    b.set_write_timeout(std::time::Duration::from_millis(150));
    b.set_max_conns(1);
    let mut h = b.serve(&p.sock).unwrap();

    let mut wedged = Client::connect(&p.sock).unwrap();
    // ONE publish: this is what lazily starts the connection's `Pipeline`, whose
    // ack-writer thread is the one that used to re-arm the shared socket at 10 s.
    wedged.publish(77, 1, "/w/pipeline", b"start").unwrap();
    let mut wedged = wedged.into_stream();
    // Now ask for a big page and never read a byte of it.
    write_frame(
        &mut wedged,
        &encode_request(&Request::Fetch {
            from_offset: 0,
            filter: "/w/>".to_string(),
            max: u32::MAX,
        }),
    )
    .unwrap();
    wedged.flush().unwrap();

    // The one slot must come back on the CONFIGURED bound. 5 s is far above 150 ms and
    // far below the 10 s constant the ack-writer used to impose.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    let mut served = false;
    while std::time::Instant::now() < deadline {
        if let Ok(mut c) = Client::connect(&p.sock) {
            if c.last("/w/>", "", 1).is_ok() {
                served = true;
                break;
            }
        }
        std::thread::sleep(std::time::Duration::from_millis(25));
    }
    assert!(
        served,
        "the connection's configured 150 ms write bound was replaced by the ack-writer's \
         own constant: the wedged reader held the only slot far past it"
    );
    drop(wedged);
    h.shutdown();
}
