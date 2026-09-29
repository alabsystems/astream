//! WHOSE LOG THIS IS, IS DECIDED WHERE THE RECORD IS APPENDED.
//!
//! `Replicate` may carry a hidden subject only onto a log that is a replication target
//! or is still EMPTY — an injected `/a/will` is an arbitrary publish, to an arbitrary
//! subject, under an arbitrary producer id, executed by the broker itself at its next
//! open and outside the capability matrix; an injected `/a/bind` locks a victim
//! principal out of attaching for good. Round 2 put that rule on the CONNECTION thread,
//! where it reads the promoted head and then drops the lock, and narrowed the
//! replica-marking to a different predicate in the WRITER thread. Between the two, a
//! record pipelined on the same connection is staged but not promoted: the guard reads
//! "still empty" about a log that already holds a record of its own, and the hidden
//! record lands on a log the broker OWNS and fires at the next open.
//!
//! The deterministic proof of the fix is in `store.rs`'s own tests
//! (`a_hidden_replicate_is_refused_once_this_batch_has_staged_a_record`), which drives
//! the writer's predicate directly with a record staged and not promoted. What THIS
//! file adds is the real socket path end to end.
//!
//! `a_replicate_refused_for_size_leaves_will_firing_enabled` is deterministic and fails
//! on the pre-fix code every time. `a_pipelined_hidden_replicate_is_never_injected`
//! drives the group-commit window itself: POST-FIX it holds on every interleaving —
//! the writer refuses the record whether or not the connection thread's early check
//! already did — which is what makes its assertion valid rather than lucky. Pre-fix it
//! is a repeated probe of a race, and it caught the injection on round 1 of 20 on every
//! run against the pre-fix code here. Nothing in it waits on a clock.
#![cfg(unix)]

use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::store::BrokerLog;
use astream_broker::{Broker, Client, Request, Response};
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr4inj_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr4inj_{tag}_{pid}_{n}.log"),
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

/// The stored `/a/will` body: `u32 LE subject length ‖ subject ‖ body`, which any
/// client can construct.
fn will_body(subject: &str, body: &[u8]) -> Vec<u8> {
    let mut out = (subject.len() as u32).to_le_bytes().to_vec();
    out.extend_from_slice(subject.as_bytes());
    out.extend_from_slice(body);
    out
}

/// A `Replicate` REFUSED FOR SIZE must leave the log an ordinary one. `mark_replica` is
/// one-way, durable and fsynced, and it stops this broker firing ANY will, on this open
/// or any later one; a record the log does not take must not write it. The frame limit
/// accepts request payloads whose record payload does not fit, so the attacker picks the
/// body length: no capability, not one byte appended, and the broker's whole last-will
/// facility silently disabled.
#[test]
fn a_replicate_refused_for_size_leaves_will_firing_enabled() {
    let p = fresh("size");
    let broker = Broker::open(&p.log).unwrap();
    let mut h = broker.serve(&p.sock).unwrap();

    // A record payload one byte over the record cap, inside a request frame that is
    // exactly at the frame cap: accepted by `read_frame`, refused by `encode`.
    let body = vec![7u8; 16 * 1024 * 1024 - 39];
    let mut s = Client::connect(&p.sock).unwrap().into_stream();
    write_frame(
        &mut s,
        &encode_request(&Request::Replicate {
            seq: 0,
            producer_id: 1,
            producer_seq: 1,
            subject: "/f/x".to_string(),
            body,
            commit: None,
        }),
    )
    .unwrap();
    let r = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
    assert!(
        matches!(&r, Response::Error { msg, .. } if msg.contains("too large")),
        "expected a size refusal, got {r:?}"
    );
    drop(s);
    assert!(
        !std::path::Path::new(&format!("{}.replica", p.log)).exists(),
        "a refused record declared the log a replication target"
    );

    // The observable consequence: wills still fire.
    let mut sub = Client::connect(&p.sock)
        .unwrap()
        .subscribe(0, "/f/>")
        .unwrap();
    // Hang detector, not a performance assertion.
    sub.set_read_timeout(Some(Duration::from_secs(30))).unwrap();
    {
        let mut c = Client::connect(&p.sock).unwrap();
        c.will(9, 4, "/f/x/gone", b"state=gone").unwrap();
    }
    let rec = sub
        .recv()
        .unwrap()
        .expect("the subscription closed before the goodbye landed");
    assert_eq!(
        (rec.1.as_str(), rec.2.as_slice()),
        ("/f/x/gone", b"state=gone".as_slice()),
        "the will did not fire: the log had been marked a replica by a record it refused"
    );
    h.shutdown();
}

/// One connection, one write: an ordinary `Publish` and then a hidden `Replicate`, with
/// neither ack read first. The publish is staged by the writer while the connection
/// thread is already evaluating the hidden-subject rule against a head that has not
/// moved yet — the ordinary group-commit window, not an exotic interleaving.
#[test]
fn a_pipelined_hidden_replicate_is_never_injected() {
    for round in 0..20 {
        let p = fresh("pipe");
        let broker = Broker::open(&p.log).unwrap();
        let mut h = broker.serve(&p.sock).unwrap();
        let mut s = Client::connect(&p.sock).unwrap().into_stream();

        // Both frames in ONE write: the second is in the broker's socket buffer before
        // the first has been committed.
        let mut buf = Vec::new();
        write_frame(
            &mut buf,
            &encode_request(&Request::Publish {
                producer_id: 1,
                producer_seq: 1,
                subject: "/f/x/one".to_string(),
                body: vec![b'z'; 1 << 20],
            }),
        )
        .unwrap();
        write_frame(
            &mut buf,
            &encode_request(&Request::Replicate {
                seq: 1,
                producer_id: 4242,
                producer_seq: 7,
                subject: "/a/will".to_string(),
                body: will_body("/f/pwned/gone", b"owned"),
                commit: None,
            }),
        )
        .unwrap();
        s.write_all(&buf).unwrap();

        let first = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
        assert!(
            matches!(first, Response::PublishAck { offset: 0, .. }),
            "round {round}: the seed publish did not land: {first:?}"
        );
        let second = decode_response(&read_frame(&mut s).unwrap().unwrap()).unwrap();
        assert!(
            matches!(&second, Response::Error { msg, .. } if msg.contains("reserved subject")),
            "round {round}: an /a/will was injected onto a log this broker owns: {second:?}"
        );
        drop(s);
        h.shutdown();

        // Nothing on the log to fire, and the log is still the broker's own.
        let log = BrokerLog::open(&p.log).unwrap();
        assert!(
            log.pending_wills().is_empty(),
            "round {round}: the log holds a forged will"
        );
        assert!(!log.is_replica(), "round {round}");
        assert_eq!(log.head().0, 1, "round {round}: only the publish landed");
        drop(log);
    }
}
