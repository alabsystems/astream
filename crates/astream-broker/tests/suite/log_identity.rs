//! Evidence for `broker.log-identity`: every log names itself, and says when its
//! offsets stopped meaning what a client was told they meant.
//!
//! An offset is a position in ONE log. These tests drive each way the log at an
//! address can stop being the log a client read — the file deleted and recreated, a
//! repair that cuts records, an older copy restored over it, another log put under its
//! name — and assert the identity CHANGES; and each way it stays the same log —
//! reopen, a repair with nothing to cut, a log that only grew — and assert it does
//! NOT, so a consumer re-reads exactly when it must. Then the wire: the identity rides
//! the answer to `Hello`, and a replica reports its leader's.
//!
//! No sleeps and no clocks: every step is a file operation, an open, or a request.
#![cfg(unix)]

use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::store::BrokerLog;
use astream_broker::{Broker, Client, Durability, LogIdentity, Request, Response};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A log path (and socket path) unique to this test run, and the guard that removes
/// both with every `<path>.*` sidecar beside them, on success and on panic alike.
struct Paths {
    log: PathBuf,
    sock: PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        log: PathBuf::from(format!("/tmp/aslid_{tag}_{pid}_{n}.log")),
        sock: PathBuf::from(format!("/tmp/aslid_{tag}_{pid}_{n}.sock")),
    };
    remove_with_sidecars(&p.log);
    remove_with_sidecars(&p.sock);
    p
}

impl Drop for Paths {
    fn drop(&mut self) {
        remove_with_sidecars(&self.log);
        remove_with_sidecars(&self.sock);
    }
}

fn remove_with_sidecars(path: &Path) {
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

fn id_sidecar(log: &Path) -> PathBuf {
    astream_broker::identity_path(log)
}

/// Open `log`, publish `bodies` (producer 1, from `seq`), and return its identity.
fn publish(log: &Path, seq: u64, bodies: &[&str]) -> LogIdentity {
    let mut l = BrokerLog::open(log).unwrap();
    for (i, b) in bodies.iter().enumerate() {
        l.publish(1, seq + i as u64, "/a/id/x".into(), b.as_bytes().to_vec())
            .unwrap();
    }
    l.identity()
}

fn identity(log: &Path) -> LogIdentity {
    BrokerLog::open(log).unwrap().identity()
}

#[test]
fn a_log_keeps_its_identity_across_reopens_and_growth() {
    let p = fresh("keep");
    let first = publish(&p.log, 1, &["a", "b"]);
    assert_eq!(first.generation, 0);
    assert!(id_sidecar(&p.log).exists(), "the open recorded it");
    assert_eq!(identity(&p.log), first, "a plain reopen");
    assert_eq!(publish(&p.log, 3, &["c"]), first, "a log that only grew");
    assert_eq!(identity(&p.log), first);
    let (log, dropped) = BrokerLog::open_repair(&p.log, Durability::Strict).unwrap();
    assert_eq!(dropped, 0);
    assert_eq!(log.identity(), first, "a repair with nothing to cut");
}

#[test]
fn a_deleted_and_recreated_log_is_another_log() {
    let p = fresh("recreate");
    let old = publish(&p.log, 1, &["a", "b", "c"]);
    // The predecessor's sidecar stays behind at the name: it must not be inherited.
    std::fs::remove_file(&p.log).unwrap();
    assert!(id_sidecar(&p.log).exists());
    let new = publish(&p.log, 1, &["a", "b", "c"]);
    assert_ne!(new.id, old.id, "the same records, but not the same log");
    assert_eq!(new.generation, 0);
}

#[test]
fn a_repair_that_cuts_records_moves_the_generation() {
    let p = fresh("repair");
    let before = publish(&p.log, 1, &["a", "b", "c", "d"]);
    // Corrupt the third record's payload (its CRC no longer matches).
    let mut bytes = std::fs::read(&p.log).unwrap();
    let mut frame_starts = vec![0usize];
    while let Ok(Some(d)) = astream_wire::Frame::decode(&bytes[*frame_starts.last().unwrap()..]) {
        let next = frame_starts.last().unwrap() + d.consumed;
        frame_starts.push(next);
    }
    bytes[frame_starts[2] + 14] ^= 0x55;
    std::fs::write(&p.log, &bytes).unwrap();

    let recorded = std::fs::read(id_sidecar(&p.log)).unwrap();
    let refused = BrokerLog::open(&p.log).err().expect("corrupt: refused");
    assert_eq!(refused.kind(), std::io::ErrorKind::InvalidData);
    assert_eq!(
        std::fs::read(id_sidecar(&p.log)).unwrap(),
        recorded,
        "a refused open records nothing"
    );

    let (log, dropped) = BrokerLog::open_repair(&p.log, Durability::Strict).unwrap();
    assert!(dropped > 0);
    let after = log.identity();
    drop(log);
    assert_eq!(after.id, before.id, "the same log file");
    assert_eq!(
        after.generation,
        before.generation + 1,
        "its cut offsets will be reused"
    );
    assert_eq!(identity(&p.log), after, "the bump is durable");
    // Appends now reuse the cut offsets, under the new generation.
    assert_eq!(publish(&p.log, 10, &["x"]), after);
}

#[test]
fn an_older_copy_restored_over_the_log_moves_the_generation() {
    let p = fresh("restore");
    let id = publish(&p.log, 1, &["a", "b"]);
    let backup = std::fs::read(&p.log).unwrap();
    assert_eq!(publish(&p.log, 3, &["c", "d", "e"]), id);
    assert_eq!(identity(&p.log), id, "the open that saw head 5");
    std::fs::write(&p.log, &backup).unwrap();
    let restored = identity(&p.log);
    assert_eq!(restored.id, id.id);
    assert_eq!(
        restored.generation,
        id.generation + 1,
        "offsets 2..5 will name new records"
    );
    // Regrowing past the old head does not undo it.
    assert_eq!(publish(&p.log, 10, &["f", "g", "h", "i"]), restored);
}

#[test]
fn another_log_put_under_the_name_moves_the_generation() {
    let p = fresh("swap");
    let other = fresh("swap_other");
    let id = publish(&p.log, 1, &["a", "b", "c"]);
    assert_eq!(identity(&p.log), id);
    // A different log, at least as long, moved over this one (its own sidecar left
    // behind): the newest record this name's last open saw is not there any more.
    publish(&other.log, 1, &["x", "y", "z", "w"]);
    std::fs::copy(&other.log, &p.log).unwrap();
    let swapped = identity(&p.log);
    assert_eq!(swapped.generation, id.generation + 1);
    // And from here it is that log's identity: a reopen keeps it.
    assert_eq!(identity(&p.log), swapped);
}

#[test]
fn a_log_that_predates_identity_derives_one_from_its_bytes() {
    let p = fresh("derive");
    publish(&p.log, 1, &["a", "b"]);
    std::fs::remove_file(id_sidecar(&p.log)).unwrap();
    let derived = identity(&p.log);
    assert_eq!(derived.generation, 0);
    std::fs::remove_file(id_sidecar(&p.log)).unwrap();
    assert_eq!(identity(&p.log), derived, "deterministic in the same bytes");
    // A log holding anything else derives another.
    publish(&p.log, 3, &["c"]);
    std::fs::remove_file(id_sidecar(&p.log)).unwrap();
    let grown = identity(&p.log);
    assert_ne!(grown.id, derived.id);
    // An unreadable sidecar is replaced by a readable one, never refused — and with a
    // FRESH id, not the one these bytes derive (`grown`): the log had an identity, and
    // a derived id could be that very one.
    std::fs::write(id_sidecar(&p.log), b"not an identity").unwrap();
    let replaced = identity(&p.log);
    assert_eq!(replaced.generation, 0);
    assert_ne!(replaced.id, grown.id, "unreadable is not absent");
    assert_eq!(identity(&p.log), replaced);
}

#[test]
fn an_open_that_cannot_read_or_record_the_identity_fails() {
    let p = fresh("unrecordable");
    publish(&p.log, 1, &["a"]);
    let sidecar = id_sidecar(&p.log);
    let tmp = PathBuf::from(format!("{}.tmp", sidecar.display()));
    // Unrecordable: a directory planted where the new sidecar is staged.
    std::fs::remove_file(&sidecar).unwrap();
    std::fs::create_dir(&tmp).unwrap();
    let err = BrokerLog::open(&p.log)
        .err()
        .expect("must not open unrecorded");
    assert!(
        err.to_string().contains(&*sidecar.to_string_lossy()),
        "{err}"
    );
    std::fs::remove_dir(&tmp).unwrap();
    // Unreadable: a directory where the sidecar is.
    std::fs::create_dir(&sidecar).unwrap();
    let err = BrokerLog::open(&p.log).err().expect("must not open unread");
    assert!(
        err.to_string().contains(&*sidecar.to_string_lossy()),
        "{err}"
    );
    std::fs::remove_dir(&sidecar).unwrap();
    BrokerLog::open(&p.log).unwrap();
}

#[test]
fn hello_answers_with_the_identity_of_the_log_served() {
    let p = fresh("hello");
    let id = publish(&p.log, 1, &["a"]);
    let broker = Broker::open(&p.log).unwrap();
    assert_eq!(broker.log_identity(), id);
    let mut h = broker.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    assert_eq!(c.seen_log_identity(), None, "nothing asked yet");
    assert_eq!(c.log_identity().unwrap(), Some(id));
    assert_eq!(c.seen_log_identity(), Some(id));
    let (_nonce, log) = c.hello_identity().unwrap();
    assert_eq!(log, Some(id));
    // The connection stays in step for ordinary requests.
    assert_eq!(c.publish(1, 2, "/a/id/x", b"b").unwrap(), (1, false));
    h.shutdown();
    drop(broker);
    // The log replaced under the broker's path is another identity on the wire.
    std::fs::remove_file(&p.log).unwrap();
    let q = fresh("hello_again");
    let broker = Broker::open(&p.log).unwrap();
    let mut h = broker.serve(&q.sock).unwrap();
    let again = Client::connect(&q.sock).unwrap().log_identity().unwrap();
    assert_ne!(again.map(|i| i.id), Some(id.id));
    h.shutdown();
}

/// Beside the identity, the answer to `Hello` carries its extension block: the tier
/// the broker serves, and the lineage — so after a Relaxed broker stopped uncleanly and
/// came back in another boot (stood in by `Boot::Known`), a client learns the
/// generation moved AND where it still agrees with the one it kept offsets under, and
/// resumes there. A Strict broker says Strict, with no lineage to tell.
#[test]
fn hello_tells_the_served_tier_and_the_lineage() {
    use astream_broker::{Boot, OpenOptions, Prepared, ServedReason, Tier, Volume};
    let p = fresh("lineage");
    let opts = |boot: [u8; 16]| {
        let mut o = OpenOptions::new(Durability::Relaxed);
        o.boot = Boot::Known(boot);
        o.volume = Volume::Boot;
        o
    };
    let earlier = {
        let mut log =
            BrokerLog::open_opts(&p.log, opts([1; 16]), || Ok(Prepared::Nothing)).unwrap();
        for i in 1..=3 {
            log.publish(7, i, "/a/ln/x".into(), b"m".to_vec()).unwrap();
        }
        log.identity()
        // Dropped without a clean close: the run stopped uncleanly.
    };
    let broker = Broker::open_opts(&p.log, opts([2; 16]), || Ok(Prepared::Nothing)).unwrap();
    let mut h = broker.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    assert_eq!(c.log_lineage(), None, "nothing asked yet");
    let now = c.log_identity().unwrap().expect("an identity");
    assert_eq!(
        (now.id, now.generation),
        (earlier.id, earlier.generation + 1)
    );
    let lineage = c.log_lineage().expect("a lineage beside the identity");
    assert_eq!(now.continues(earlier, lineage), Some(3));
    let served = c.served_durability().expect("the served tier");
    assert_eq!(
        (served.requested, served.served),
        (Tier::Relaxed, Tier::Relaxed)
    );
    assert_eq!(
        (served.reason, served.horizon_ms, served.rules),
        (ServedReason::None, None, 0)
    );
    h.shutdown();
    drop(broker);

    let q = fresh("lineage_strict");
    publish(&q.log, 1, &["a"]);
    let broker = Broker::open(&q.log).unwrap();
    let mut h = broker.serve(&q.sock).unwrap();
    let mut c = Client::connect(&q.sock).unwrap();
    c.hello().unwrap();
    assert_eq!(c.served_durability().map(|s| s.served), Some(Tier::Strict));
    assert_eq!(c.log_lineage().map(|l| l.steps().len()), Some(0));
    h.shutdown();
}

/// One raw `Replicate` of `(seq, producer 7, seq + 1, /f/r/x)` carrying `leader`,
/// and its answer.
fn replicate(sock: &Path, seq: u64, leader: Option<LogIdentity>) -> Response {
    replicate_body(sock, seq, "r", leader)
}

/// [`replicate`] with the record's body.
fn replicate_body(sock: &Path, seq: u64, body: &str, leader: Option<LogIdentity>) -> Response {
    let mut s = Client::connect(sock).unwrap().into_stream();
    write_frame(
        &mut s,
        &encode_request(&Request::Replicate {
            seq,
            producer_id: 7,
            producer_seq: seq + 1,
            subject: "/f/r/x".to_string(),
            body: body.as_bytes().to_vec(),
            commit: None,
            leader,
        }),
    )
    .unwrap();
    decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap()
}

/// A follower serving a replica of `bodies` (records 0.., from a leader that predates
/// log identity, so the follower still carries its own).
fn replica_of(p: &Paths, bodies: &[&str]) -> (Broker, astream_broker::BrokerHandle) {
    let follower = Broker::open(&p.log).unwrap();
    let h = follower.serve(&p.sock).unwrap();
    for (seq, body) in bodies.iter().enumerate() {
        assert!(matches!(
            replicate_body(&p.sock, seq as u64, body, None),
            Response::PublishAck { deduped: false, .. }
        ));
    }
    (follower, h)
}

/// A replica takes its leader's identity only once the leader's records, shipped in
/// order, reach the replica's NEWEST record — and not at all in an open that found it
/// holding a different record than the leader's. A byte-identical echo of a shared
/// PREFIX vouches for nothing above it: a follower that kept records its leader has
/// since cut (a repair, which moved the leader's generation) shares the leader's
/// records below the cut and not above, so taking the leader's new identity there
/// would tell a client that fails over to it that offsets read from the leader name
/// the records this follower holds. The leader fences such a link at the first
/// divergence; the identity must not have moved before it.
#[test]
fn a_replica_takes_its_leaders_identity_only_when_the_leader_reaches_its_newest_record() {
    let leader = LogIdentity {
        id: [6; 16],
        generation: 1,
    };
    let p = fresh("replica_diverged");
    let (follower, mut fh) = replica_of(&p, &["a", "b", "c"]);
    let own = follower.log_identity();
    // The leader shares record 0 and holds another at 1, and ships from its base.
    assert!(matches!(
        replicate_body(&p.sock, 0, "a", Some(leader)),
        Response::PublishAck {
            offset: 0,
            deduped: true
        }
    ));
    assert_eq!(
        follower.log_identity(),
        own,
        "an echo of a prefix vouches for nothing above it"
    );
    assert!(matches!(
        replicate_body(&p.sock, 1, "B", Some(leader)),
        Response::Error { .. }
    ));
    // An identical record past the divergence (a re-sent publish the leader appended
    // in the same order) reaches the newest one and still hands nothing over.
    assert!(matches!(
        replicate_body(&p.sock, 2, "c", Some(leader)),
        Response::PublishAck {
            offset: 2,
            deduped: true
        }
    ));
    assert_eq!(
        follower.log_identity(),
        own,
        "it holds a record that is not the leader's"
    );
    fh.shutdown();
    drop(follower);

    // CONTROL: the same records, the leader's all the way up — taken at the newest.
    let q = fresh("replica_caught_up");
    let (follower, mut fh) = replica_of(&q, &["a", "b", "c"]);
    let own = follower.log_identity();
    for (seq, body) in [(0, "a"), (1, "b")] {
        assert!(matches!(
            replicate_body(&q.sock, seq, body, Some(leader)),
            Response::PublishAck { deduped: true, .. }
        ));
        assert_eq!(follower.log_identity(), own, "below the newest, at {seq}");
    }
    assert!(matches!(
        replicate_body(&q.sock, 2, "c", Some(leader)),
        Response::PublishAck { deduped: true, .. }
    ));
    assert_eq!(
        follower.log_identity(),
        leader,
        "every record is the leader's"
    );
    fh.shutdown();
}

#[test]
fn a_replica_reports_its_leaders_identity() {
    let p = fresh("replica");
    let leader_log = fresh("replica_leader");
    // A real leader and follower: the follower takes the leader's records, so it
    // reports the leader's identity — the offsets are the leader's.
    let follower = Broker::open(&p.log).unwrap();
    let mut fh = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = fh.tcp_addr().unwrap().to_string();
    let leader = Broker::open_replicated(&leader_log.log, std::slice::from_ref(&faddr), 1).unwrap();
    let mut lh = leader.serve(&leader_log.sock).unwrap();
    assert_ne!(
        follower.log_identity(),
        leader.log_identity(),
        "two logs, so far"
    );
    Client::connect(&leader_log.sock)
        .unwrap()
        .publish(1, 1, "/a/r/x", b"m")
        .unwrap();
    assert_eq!(follower.log_identity(), leader.log_identity());
    assert_eq!(
        Client::connect_tcp(&faddr).unwrap().log_identity().unwrap(),
        Some(leader.log_identity()),
        "and says so on the wire"
    );
    let adopted = leader.log_identity();
    lh.shutdown();
    fh.shutdown();
    drop(follower);
    drop(leader);
    assert_eq!(
        identity(&p.log),
        adopted,
        "durably: across the follower's reopen"
    );
}

#[test]
fn only_a_replica_adopts_an_identity_and_an_old_leader_sends_none() {
    // A leader that predates log identity: the follower becomes a replica and keeps
    // its own identity.
    let p = fresh("oldleader");
    let follower = Broker::open(&p.log).unwrap();
    let own = follower.log_identity();
    let mut fh = follower.serve(&p.sock).unwrap();
    assert!(matches!(
        replicate(&p.sock, 0, None),
        Response::PublishAck { offset: 0, .. }
    ));
    assert_eq!(follower.log_identity(), own);
    // ...until a record that carries one commits.
    let foreign = LogIdentity {
        id: [9; 16],
        generation: 4,
    };
    assert!(matches!(
        replicate(&p.sock, 1, Some(foreign)),
        Response::PublishAck { offset: 1, .. }
    ));
    assert_eq!(follower.log_identity(), foreign);
    fh.shutdown();

    // CONTROL: a broker that OWNS its log (it holds a record of its own, so a
    // replicated record beside it does not make it a replica) takes the record and
    // keeps its own identity.
    let q = fresh("owner");
    publish(&q.log, 1, &["mine"]);
    let owner = Broker::open(&q.log).unwrap();
    let own = owner.log_identity();
    let mut oh = owner.serve(&q.sock).unwrap();
    assert!(matches!(
        replicate(&q.sock, 1, Some(foreign)),
        Response::PublishAck { offset: 1, .. }
    ));
    assert_eq!(owner.log_identity(), own, "a log it owns names itself");
    oh.shutdown();
}

/// A replica found rewritten does not number its leader's rewrites: an older copy of a
/// follower's log restored under it gives it a FRESH id at generation 0, never the
/// leader's id at generation + 1 — a name the leader's own next rewrite could take —
/// and the next replicated record hands the leader's identity back. (The same restore
/// on a log the broker owns keeps the id and moves the generation:
/// `an_older_copy_restored_over_the_log_moves_the_generation`.)
#[test]
fn a_rewritten_replica_takes_a_fresh_id_until_its_leader_names_it_again() {
    let p = fresh("replica_rewound");
    let leader = LogIdentity {
        id: [5; 16],
        generation: 2,
    };
    let follower = Broker::open(&p.log).unwrap();
    let mut fh = follower.serve(&p.sock).unwrap();
    assert!(matches!(
        replicate(&p.sock, 0, Some(leader)),
        Response::PublishAck { offset: 0, .. }
    ));
    // Strict: the acked record is durable, so this copy holds it.
    let backup = std::fs::read(&p.log).unwrap();
    assert!(matches!(
        replicate(&p.sock, 1, Some(leader)),
        Response::PublishAck { offset: 1, .. }
    ));
    assert_eq!(follower.log_identity(), leader);
    fh.shutdown();
    drop(follower);
    assert_eq!(identity(&p.log), leader, "the open that saw head 2");

    std::fs::write(&p.log, &backup).unwrap();
    let rewound = identity(&p.log);
    assert_ne!(rewound.id, leader.id, "not the leader's lineage");
    assert_eq!(rewound.generation, 0);
    assert_eq!(identity(&p.log), rewound, "and recorded");

    let follower = Broker::open(&p.log).unwrap();
    let mut fh = follower.serve(&p.sock).unwrap();
    assert!(matches!(
        replicate(&p.sock, 1, Some(leader)),
        Response::PublishAck { offset: 1, .. }
    ));
    assert_eq!(follower.log_identity(), leader, "the leader names it again");
    fh.shutdown();
}

/// Retention prunes the front of a log and keeps every surviving record at its
/// offset, so the log is the same log: the identity survives `retain_before` and the
/// reopen after it.
#[cfg(feature = "retention")]
#[test]
fn retention_keeps_the_identity() {
    let p = fresh("retained");
    let mut log = BrokerLog::open(&p.log).unwrap();
    for i in 0..5u64 {
        log.publish(1, i + 1, "/a/id/x".into(), vec![b'a' + i as u8])
            .unwrap();
    }
    let id = log.identity();
    drop(log);
    assert_eq!(identity(&p.log), id, "the open that saw head 5");
    let mut log = BrokerLog::open(&p.log).unwrap();
    assert_eq!(log.retain_before(astream_wire::Offset(3)).unwrap(), 3);
    assert_eq!(log.identity(), id);
    drop(log);
    assert_eq!(identity(&p.log), id, "across the reopen at the new base");
}

/// A log that predates identity but whose every record retention pruned stores no
/// frame to derive from — only its base and head, which another such log can share —
/// so it is minted a fresh id, not derived: two settlings of it differ. (A log that
/// still stores records derives the same id each time:
/// `a_log_that_predates_identity_derives_one_from_its_bytes`.)
#[cfg(feature = "retention")]
#[test]
fn a_pre_identity_log_with_every_record_pruned_is_minted_not_derived() {
    let p = fresh("pruned");
    let mut log = BrokerLog::open(&p.log).unwrap();
    for i in 0..3u64 {
        log.publish(1, i + 1, "/a/id/x".into(), vec![b'a']).unwrap();
    }
    assert_eq!(log.retain_before(astream_wire::Offset(3)).unwrap(), 3);
    drop(log);
    std::fs::remove_file(id_sidecar(&p.log)).unwrap();
    let first = identity(&p.log);
    std::fs::remove_file(id_sidecar(&p.log)).unwrap();
    assert_ne!(identity(&p.log).id, first.id, "two numbers are no lineage");
}

/// A client that attaches learns the identity from the `Hello` its attach already
/// sent: `seen_log_identity` holds it after `attach_all`, with nothing else asked.
#[cfg(feature = "cap")]
#[test]
fn an_attach_learns_the_identity_from_its_own_hello() {
    let p = fresh("attach");
    let secret = b"log-identity-secret".to_vec();
    let broker = Broker::open_guarded(&p.log, secret.clone()).unwrap();
    let mut h = broker.serve(&p.sock).unwrap();
    let cap = astream_cap::mint(&secret, "ro:/f/F/>").unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    assert_eq!(c.seen_log_identity(), None);
    c.attach_all([(cap.filter.as_str(), &cap.tag[..])])
        .unwrap()
        .expect("one grant, one acknowledgement");
    assert_eq!(c.seen_log_identity(), Some(broker.log_identity()));
    h.shutdown();
}

/// A copy taken while the log was written ends inside a frame. Restored ALONE over a
/// log whose durable floor is above where it ends, it is a SHORTER log — not damage
/// below the floor, which a power loss never leaves: it opens, cut to its last whole
/// record, and the generation moves with no lineage (offsets kept from the longer log
/// mean nothing now). It is not refused until an operator repairs it.
#[test]
fn a_copy_ending_inside_a_frame_below_the_floor_opens_as_a_shorter_log() {
    let p = fresh("short_copy");
    let earlier = publish(&p.log, 1, &["one", "two", "three", "four", "five"]);
    let full = std::fs::read(&p.log).unwrap();
    // Reopened: the floor is recorded at 5.
    assert_eq!(identity(&p.log), earlier);
    // The copy: three whole records and the first 20 bytes of the fourth.
    let mut pos = 0usize;
    for _ in 0..3 {
        let len = u32::from_le_bytes(full[pos + 4..pos + 8].try_into().unwrap()) as usize;
        pos += 12 + len;
    }
    std::fs::write(&p.log, &full[..pos + 20]).unwrap();
    let log = BrokerLog::open(&p.log).expect("a shorter log opens, it is not refused");
    assert_eq!(log.head().0, 3);
    let now = log.identity();
    assert_eq!(
        (now.id, now.generation),
        (earlier.id, earlier.generation + 1)
    );
    assert_eq!(now.continues(earlier, log.lineage()), None, "no lineage");
    drop(log);
    assert_eq!(std::fs::read(&p.log).unwrap(), &full[..pos]);
}
