// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.unclean-generation` through the two doors an EMBEDDER's tests
//! use to stand in what they cannot cause in process: `Broker::arm_unclean_stop`, a
//! broker that stops as a killed process does (no clean close, `<log>.id` as its open
//! wrote it), and `Lineage::from_steps`, a lineage no single unclean open made. Both are
//! public so that such a test stops forging astream's files: saving `<log>.id` after
//! the open and writing it back after the stop, or hand-encoding the `Hello` block's
//! lineage entry and parsing it back. These tests hold each door to what it stands in
//! for, from outside the crate, as an embedder reaches them:
//!
//! - Under the seam, a served broker's stop and an unserved one's drop leave `<log>.id`
//!   byte for byte as the open wrote it and release the log. The next open in the SAME
//!   boot moves nothing (a process crash loses nothing) — the boot named and the log on
//!   the boot volume, as these tests declare; elsewhere every unclean weak stop moves it.
//!   In ANOTHER boot, a run that served Relaxed or Ordered moves the generation once
//!   with lineage at the head it recovered, and one served Strict moves nothing. Each
//!   path is judged on its own log, so the reboot reads the sidecar the run under test
//!   left. Ordered is served only on Apple, and elsewhere is served Strict, so its run is
//!   judged by the tier it SERVED, which is what `<log>.id` records. The negative
//!   control is the same run without the seam: its clean close rewrites the sidecar,
//!   and the reboot keeps the identity at every tier.
//! - A broker stopped under the seam writes nothing more, as a killed process writes
//!   nothing: kept after its stop, it refuses retention while a successor serves the log
//!   it released, and every record the successor acked is still there at the next open
//!   (with the `retention` feature, which is what can rewrite a stopped broker's log).
//! - `from_steps` is the lineage a `Hello` answer carrying the same steps decodes to,
//!   and refuses what that decoder refuses. The sweep holds lists that each of the
//!   decoder's rules refuses alone, so a constructor that skipped either would fail it
//!   (the negative control).
//!
//! No sleeps and no clocks: every step is a file operation, an open, a stop or a request.
#![cfg(unix)]

use astream_broker::proto::{decode_response, encode_response};
use astream_broker::{
    identity_path, Boot, Broker, Client, Durability, Lineage, LogIdentity, NonceExt, OpenOptions,
    Prepared, Response, Tier, Volume,
};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// The boot the writing runs serve in, and the one after the stand-in reboot.
const SERVED: [u8; 16] = [0x5A; 16];
const AFTER: [u8; 16] = [0xA5; 16];

/// A log path and a socket path unique to this test run, and the guard that removes
/// both with every `<path>.*` sidecar beside them, on success and on panic alike.
struct Paths {
    log: PathBuf,
    sock: PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        log: PathBuf::from(format!("/tmp/asunclean_{tag}_{pid}_{n}.log")),
        sock: PathBuf::from(format!("/tmp/asunclean_{tag}_{pid}_{n}.sock")),
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

/// `<log>.id` ([`identity_path`]), read as bytes: what these tests compare, never parse.
fn sidecar(log: &Path) -> Vec<u8> {
    std::fs::read(identity_path(log)).expect("the open wrote <log>.id")
}

/// A broker on `log` at `durability` in `boot`, the log declared on the boot volume (so
/// the same-boot rule may trust the page cache, and Apple may serve Ordered).
fn open(log: &Path, durability: Durability, boot: [u8; 16]) -> Broker {
    let mut o = OpenOptions::new(durability);
    o.boot = Boot::Known(boot);
    o.volume = Volume::Boot;
    Broker::open_opts(log, o, || Ok(Prepared::Nothing)).expect("open")
}

/// The tiers each run asks for, with the tier this platform serves it: Ordered only on
/// Apple (the log on the boot volume, the barrier probe accepted), Strict elsewhere.
fn tiers() -> [(Durability, Tier); 3] {
    let ordered = if cfg!(target_vendor = "apple") {
        Tier::Ordered
    } else {
        Tier::Strict
    };
    [
        (Durability::Relaxed, Tier::Relaxed),
        (Durability::Ordered { horizon: None }, ordered),
        (Durability::Strict, Tier::Strict),
    ]
}

/// Serve `broker` on `sock`, publish three records through a client, stop it (the last
/// listener's shutdown, then the drop) and return the identity it served under.
fn serve_three_and_stop(broker: Broker, sock: &Path) -> LogIdentity {
    let mut h = broker.serve(sock).expect("serve");
    let mut c = Client::connect(sock).expect("connect");
    for seq in 1..=3 {
        c.publish(7, seq, "/a/unclean/x", b"m").expect("publish");
    }
    drop(c);
    let identity = broker.log_identity();
    h.shutdown();
    drop(broker);
    identity
}

/// What a client told after the stand-in reboot reads: the identity and the lineage
/// its `Hello` answer carries.
fn told(broker: &Broker, sock: &Path) -> (LogIdentity, Lineage) {
    let mut h = broker.serve(sock).expect("serve");
    let mut c = Client::connect(sock).expect("connect");
    let now = c.log_identity().expect("hello").expect("an identity");
    let lineage = c.log_lineage().cloned().expect("a lineage beside it");
    drop(c);
    h.shutdown();
    (now, lineage)
}

/// Reboot the three-record log `p` left by a run stopped under the seam, and judge what
/// a client reads against the identity that run served under: a run that SERVED a weak
/// tier moves the generation once with lineage at the head the reboot RECOVERED (3,
/// every record kept), so a reader resumes there; one served Strict moves nothing.
fn reboot_and_judge(p: &Paths, durability: Durability, served: Tier, before: LogIdentity) {
    let rebooted = open(&p.log, durability, AFTER);
    assert_eq!(rebooted.head(), 3, "{durability:?}: every record kept");
    let (now, lineage) = told(&rebooted, &p.sock);
    drop(rebooted);
    if served == Tier::Strict {
        assert_eq!(
            now, before,
            "{durability:?} served Strict: its acks were on stable media"
        );
        return;
    }
    assert_eq!(
        (now.id, now.generation),
        (before.id, before.generation + 1),
        "{durability:?} served {served:?}: the generation moved once"
    );
    assert_eq!(
        lineage.steps().last(),
        Some(&(now.generation, 3)),
        "{durability:?}: lineage at the recovered head"
    );
    assert_eq!(
        now.continues(before, &lineage),
        Some(3),
        "{durability:?}: a reader resumes at the head instead of forgetting"
    );
}

/// THE SEAM STOPS A BROKER AS A KILL DOES, at every tier. A run serves three records
/// with the seam armed and stops: `<log>.id` is still the open's, byte for byte, and
/// the reboot straight after it — what an embedder's test of a reboot does — moves the
/// generation once, with lineage at the head it recovered, exactly when the run SERVED
/// a weak tier: Relaxed, Ordered where it is served, and never Strict — an Ordered
/// request served Strict off Apple included, since the sidecar records the tier served.
/// That run's open recorded head 0, so lineage at the recovered head (3) is the
/// recovery's doing, not a copy of what the open saw. (claim broker.unclean-generation)
///
/// The same-boot half runs on a log of its own, so the reboot above judges the served
/// run's sidecar and nothing written since: the log's lock is released, so it reopens
/// in this process, and in the SAME boot (a process crash, the boot named and the log on
/// the boot volume) nothing moves. That reopen, armed and dropped unserved, leaves its
/// own open's sidecar too, and the reboot after it is judged as the run it was.
///
/// Negative control: the same run without the seam. Its clean close rewrites the
/// sidecar (`Closed`, the floor at the head), and the reboot keeps the identity at every
/// tier, the weak ones included, so the move above is the seam's doing.
#[test]
fn the_seam_stops_a_broker_as_a_kill_does_and_only_a_weak_run_moves_after_a_reboot() {
    for (durability, served) in tiers() {
        // A served run, stopped under the seam, then a reboot.
        let p = fresh("seam");
        let broker = open(&p.log, durability, SERVED);
        assert_eq!(broker.served_durability().served, served, "{durability:?}");
        let opened = sidecar(&p.log);
        broker.arm_unclean_stop();
        let before = serve_three_and_stop(broker, &p.sock);
        assert_eq!(
            sidecar(&p.log),
            opened,
            "{durability:?}: the stop left the sidecar the open wrote"
        );
        reboot_and_judge(&p, durability, served, before);

        // A process crash: the same boot, and the lock already released.
        let s = fresh("crash");
        let broker = open(&s.log, durability, SERVED);
        broker.arm_unclean_stop();
        let before = serve_three_and_stop(broker, &s.sock);
        let again = open(&s.log, durability, SERVED);
        assert_eq!(again.log_identity(), before, "{durability:?}: same boot");
        assert_eq!(again.head(), 3, "{durability:?}: every record kept");
        let reopened = sidecar(&s.log);
        again.arm_unclean_stop();
        drop(again); // unserved: the drop is this broker's stop
        assert_eq!(
            sidecar(&s.log),
            reopened,
            "{durability:?}: an unserved broker's drop under the seam leaves its open's sidecar"
        );
        reboot_and_judge(&s, durability, served, before);

        // NEGATIVE CONTROL: the same run, no seam.
        let q = fresh("clean");
        let broker = open(&q.log, durability, SERVED);
        let opened = sidecar(&q.log);
        let before = serve_three_and_stop(broker, &q.sock);
        assert_ne!(
            sidecar(&q.log),
            opened,
            "{durability:?}: the clean close rewrote the sidecar"
        );
        let rebooted = open(&q.log, durability, AFTER);
        assert_eq!(
            rebooted.log_identity(),
            before,
            "{durability:?}: a clean stop's reboot moves nothing"
        );
    }
}

/// A BROKER STOPPED UNDER THE SEAM WRITES NOTHING MORE, as a killed process writes
/// nothing. A Strict run serves six records with the seam armed and stops, and the
/// test keeps the `Broker` value, as an embedder's test holding one does. A successor
/// opens the log it released; the stopped broker's retention calls are refused, naming
/// the release; the successor acks two more Strict records; and the next open holds all
/// eight, none pruned. Before the stop latched the log shut, `retain_before` here
/// answered `Ok(3)` and renamed its compacted copy over the successor's log, whose two
/// durable acks went to the unlinked file and were gone at the reopen.
///
/// Beside it, the same run stopped cleanly: its log is refused as closed cleanly, which
/// the armed stop does not do, so the refusal above is the release's.
#[cfg(feature = "retention")]
#[test]
fn a_broker_stopped_under_the_seam_writes_nothing_under_its_successor() {
    for armed in [true, false] {
        let p = fresh("successor");
        let stopped = open(&p.log, Durability::Strict, SERVED);
        if armed {
            stopped.arm_unclean_stop();
        }
        let mut h = stopped.serve(&p.sock).expect("serve");
        let mut c = Client::connect(&p.sock).expect("connect");
        for seq in 1..=6 {
            c.publish(7, seq, "/a/unclean/x", b"m").expect("publish");
        }
        drop(c);
        h.shutdown();

        let successor = open(&p.log, Durability::Strict, SERVED);
        assert_eq!(successor.head(), 6, "armed={armed}: the lock was released");
        let refusal = if armed { "released" } else { "closed cleanly" };
        for (what, res) in [
            ("retain_before", stopped.retain_before(3)),
            (
                "retain_before_carrying_state",
                stopped.retain_before_carrying_state(3),
            ),
        ] {
            let err = res.expect_err("a stopped broker's log refuses retention");
            assert!(
                err.to_string().contains(refusal),
                "armed={armed}: {what} refused as {refusal:?}: {err}"
            );
        }

        let mut h = successor.serve(&p.sock).expect("serve the successor");
        let mut c = Client::connect(&p.sock).expect("connect");
        for seq in 1..=2 {
            c.publish(8, seq, "/a/unclean/y", b"m").expect("publish");
        }
        drop(c);
        h.shutdown();
        assert_eq!(successor.head(), 8);
        drop(successor);
        drop(stopped);

        let reopened = open(&p.log, Durability::Strict, SERVED);
        assert_eq!(
            (reopened.base(), reopened.head()),
            (0, 8),
            "armed={armed}: every record the successor acked, none pruned"
        );
    }
}

/// Step lists for the `from_steps` sweep: every list of up to three steps over
/// generations {0, 1, u64::MAX} (equal, falling and rising neighbours), its commons
/// falling; and for every length up to two past `Lineage::MAX`, the rising chain alone
/// and with each neighbour made equal — the only lists that reach the cap.
fn step_lists() -> Vec<Vec<(u64, u64)>> {
    const GENS: [u64; 3] = [0, 1, u64::MAX];
    let mut lists = vec![Vec::new()];
    let mut frontier: Vec<Vec<(u64, u64)>> = vec![Vec::new()];
    for _ in 0..3 {
        let mut next = Vec::new();
        for steps in &frontier {
            for g in GENS {
                let mut longer = steps.clone();
                longer.push((g, 9 - longer.len() as u64));
                lists.push(longer.clone());
                next.push(longer);
            }
        }
        frontier = next;
    }
    for n in 1..=Lineage::MAX as u64 + 2 {
        let chain: Vec<(u64, u64)> = (1..=n).map(|g| (g, 50 + g)).collect();
        lists.push(chain.clone());
        for i in 1..chain.len() {
            let mut equal = chain.clone();
            equal[i].0 = equal[i - 1].0;
            lists.push(equal);
        }
    }
    lists
}

/// The lineage a client reads from a `Nonce` answer whose extension block carries
/// `steps` as its lineage entry (tag 0x02, `len u16 LE`, `n u8`, `n × (generation u64
/// LE, common u64 LE)`, the layout `NonceExt` documents), through the decoder every
/// client runs; `None` when that decoder refuses the frame.
fn told_in_hello(steps: &[(u64, u64)]) -> Option<Lineage> {
    let mut frame = encode_response(&Response::Nonce {
        nonce: vec![0; 32],
        log: Some(LogIdentity {
            id: [0; 16],
            generation: 0,
        }),
        ext: NonceExt::default(),
    });
    let mut body = vec![u8::try_from(steps.len()).unwrap()];
    for (generation, common) in steps {
        body.extend_from_slice(&generation.to_le_bytes());
        body.extend_from_slice(&common.to_le_bytes());
    }
    frame.push(0x02);
    frame.extend_from_slice(&u16::try_from(body.len()).unwrap().to_le_bytes());
    frame.extend_from_slice(&body);
    match decode_response(&frame)? {
        Response::Nonce { ext, .. } => ext.lineage,
        other => panic!("a Nonce frame decoded as {other:?}"),
    }
}

/// `Lineage::from_steps` is the lineage a `Hello` answer carrying the same steps
/// decodes to, and `None` exactly where that decoder refuses the frame (more than
/// `Lineage::MAX` steps, generations that do not rise), over every list of
/// [`step_lists`]: an embedder's test builds the lineage it needs instead of the bytes
/// that carry it. (claim broker.unclean-generation)
///
/// Negative controls: the sweep holds lists that each rule ALONE refuses, rising chains
/// past the cap and lists within the cap whose generations do not rise, and the decoder
/// refuses every one. A `from_steps` that dropped either rule would answer `Some` for
/// them and fail the agreement; one that refused too much would fail it on the chains
/// accepted at and below the cap. (The library's own `logid` test runs those mutants
/// directly, since only inside the crate can a lineage be built unchecked.)
#[test]
fn from_steps_is_the_lineage_a_hello_answer_decodes_to() {
    let lists = step_lists();
    let disagree: Vec<&Vec<(u64, u64)>> = lists
        .iter()
        .filter(|steps| Lineage::from_steps(steps) != told_in_hello(steps))
        .collect();
    assert!(disagree.is_empty(), "from_steps disagrees on {disagree:?}");

    let rises = |steps: &[(u64, u64)]| steps.windows(2).all(|w| w[0].0 < w[1].0);
    let past_cap: Vec<_> = lists
        .iter()
        .filter(|s| rises(s) && s.len() > Lineage::MAX)
        .collect();
    let not_rising: Vec<_> = lists
        .iter()
        .filter(|s| !rises(s) && s.len() <= Lineage::MAX)
        .collect();
    assert!(!past_cap.is_empty() && !not_rising.is_empty());
    for steps in past_cap.iter().chain(&not_rising) {
        assert_eq!(told_in_hello(steps), None, "the decoder refuses {steps:?}");
    }
    let at_cap = lists
        .iter()
        .find(|s| rises(s) && s.len() == Lineage::MAX)
        .expect("a rising chain at the cap");
    assert_eq!(
        Lineage::from_steps(at_cap).map(|l| l.steps().to_vec()),
        Some(at_cap.clone()),
        "accepted at the cap, the steps as given"
    );
}
