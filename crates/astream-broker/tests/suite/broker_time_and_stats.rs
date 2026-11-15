// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end verification of `REQUIREMENTS-fabric-operations-2026-09-14.md`
//! **R3** (monotone broker-stamped wall time `bt=<unix ms>`) and **R5** (the `Stats` wire
//! request for operators, which a guarded broker gates on a read grant over `/f/<F>/>`).
//!
//! Claims: `broker.monotone-broker-time` and `broker.wire-stats`.
#![cfg(unix)]

use astream_broker::{Broker, Client, Durability, StampedRecord};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

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

fn paths(tag: &str) -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asbt_{tag}_{pid}_{n}.log");
    let sock = format!("/tmp/asbt_{tag}_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _ = std::fs::remove_file(&sock);
    (Cleanup::new(&[&log, &sock]), log, sock)
}

fn wait_until(desc: &str, mut pred: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !pred() {
        assert!(Instant::now() < deadline, "timed out waiting for {desc}");
        std::thread::yield_now();
    }
}

/// R3 acceptance + negative controls:
/// 1. Two producers whose sender `t=` clocks differ by an hour append 1 s apart on the
///    broker's clock -> `bt=` is 1,000 ms apart in append order while each sender's `t=`
///    in the payload body is preserved byte-for-byte.
/// 2. A backward wall-clock step (`1_700_000_001_000 -> 1_700_000_000_500`) never
///    produces a smaller `bt=`: the next record is clamped to `1_700_000_001_000`.
/// 3. A `Will`-fired goodbye on disconnect carries its own monotone `bt=`.
/// 4. `Fetch` (`fetch_stamped`), `Last` (`last_all_stamped`), and `Subscribe`
///    (`subscribe_stamped` + `recv_stamped`) surface identical `bt=` stamps, while
///    un-negotiated `Client::fetch` and `Client::subscribe` keep legacy wire framing.
/// 5. A replica opened from the copied log (`Broker::open_replica`) under an unrelated
///    wall clock (`9_999_999_999_000`) serves the exact original `bt=` values (stored in
///    the record's `0xB6` trailer, never recomputed).
#[test]
fn r3_monotone_broker_time_across_fetch_last_subscribe_will_and_replica() {
    let (_tmp, log, sock) = paths("r3");
    let (_rtmp, rlog, rsock) = paths("r3rep");

    let broker = Broker::open_with(&log, Durability::Strict).unwrap();
    let clock = Arc::new(AtomicU64::new(1_700_000_000_000));
    broker.set_clock_override(Some(clock.clone()));
    let mut handle = broker.serve(&sock).unwrap();

    // Hello advertises both R3 (`REQUEST_BROKER_TIMES`) and R5 (`REQUEST_STATS`).
    let mut probe = Client::connect(&sock).unwrap();
    let _ = probe.hello().unwrap();
    assert!(probe.supports_broker_times());
    assert!(probe.supports_stats());

    // Producer 1 (sender t=10_000) publishes presence + registers a Will.
    let mut p1 = Client::connect(&sock).unwrap();
    let (off0, dup0) = p1
        .publish(
            101,
            1,
            "/f/alpha/pub/n1/s1/presence",
            b"v=1 t=10000 state=live",
        )
        .unwrap();
    assert_eq!((off0, dup0), (0, false));
    p1.will(
        101,
        2,
        "/f/alpha/pub/n1/s1/presence",
        b"v=1 t=10005 state=gone",
    )
    .unwrap();

    // Producer 2's sender clock is 1 hour ahead (`t=3_610_000`), appended 1 s later on
    // the broker's clock (`1_700_000_001_000`).
    clock.store(1_700_000_001_000, Ordering::Relaxed);
    let mut p2 = Client::connect(&sock).unwrap();
    let (off_p2_first, _) = p2
        .publish(202, 1, "/f/alpha/pub/n2/s2/ev", b"v=1 t=3610000 seq=1")
        .unwrap();
    assert_eq!(off_p2_first, 2, "offset 1 is the hidden /a/will record");

    // Step the broker's wall clock BACKWARDS by 500 ms: `bt=` must clamp monotonically.
    clock.store(1_700_000_000_500, Ordering::Relaxed);
    let (off_p2_second, _) = p2
        .publish(202, 2, "/f/alpha/pub/n2/s2/ev", b"v=1 t=3610001 seq=2")
        .unwrap();
    assert_eq!(off_p2_second, 3);

    // Advance the broker's clock to +2.5 s and disconnect p1 so its Will fires.
    clock.store(1_700_000_002_500, Ordering::Relaxed);
    drop(p1);
    wait_until("will settled", || broker.stats().wills_settled >= 1);

    let expected: Vec<StampedRecord> = vec![
        (
            0,
            "/f/alpha/pub/n1/s1/presence".to_string(),
            b"v=1 t=10000 state=live".to_vec(),
            Some(1_700_000_000_000),
        ),
        (
            2,
            "/f/alpha/pub/n2/s2/ev".to_string(),
            b"v=1 t=3610000 seq=1".to_vec(),
            Some(1_700_000_001_000),
        ),
        (
            3,
            "/f/alpha/pub/n2/s2/ev".to_string(),
            b"v=1 t=3610001 seq=2".to_vec(),
            Some(1_700_000_001_000),
        ),
        (
            4,
            "/f/alpha/pub/n1/s1/presence".to_string(),
            b"v=1 t=10005 state=gone".to_vec(),
            Some(1_700_000_002_500),
        ),
    ];

    // 1. Fetch stamped:
    let (fetched, (next, head)) = probe.fetch_stamped(0, "/f/alpha/>", 16).unwrap();
    assert_eq!(fetched, expected);
    assert_eq!((next, head), (5, 5));
    // Acceptance: the two producers 1 hour apart on their own clocks are 1,000 ms apart on `bt=`.
    assert_eq!(fetched[1].3.unwrap() - fetched[0].3.unwrap(), 1_000);

    // 2. Last stamped:
    let (last_rows, _) = probe.last_all_stamped("/f/alpha/>").unwrap();
    assert_eq!(
        last_rows,
        vec![
            (
                4,
                "/f/alpha/pub/n1/s1/presence".to_string(),
                b"v=1 t=10005 state=gone".to_vec(),
                Some(1_700_000_002_500),
            ),
            (
                3,
                "/f/alpha/pub/n2/s2/ev".to_string(),
                b"v=1 t=3610001 seq=2".to_vec(),
                Some(1_700_000_001_000),
            ),
        ]
    );

    // 3. Subscribe stamped:
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe_stamped(0, "/f/alpha/>")
        .unwrap();
    let mut streamed = Vec::new();
    for want in &expected {
        let row = sub.recv_stamped().unwrap().unwrap();
        assert_eq!(sub.last_bt_ms(), want.3);
        streamed.push(row);
    }
    assert_eq!(streamed, expected);
    drop(sub);

    // 4. Negative control: legacy un-negotiated Fetch & Subscribe keep plain framing.
    let mut legacy = Client::connect(&sock).unwrap();
    let (plain_page, _) = legacy.fetch(0, "/f/alpha/>", 16).unwrap();
    assert_eq!(plain_page.len(), 4);
    assert_eq!(plain_page[0].2, b"v=1 t=10000 state=live");
    let mut plain_sub = legacy.subscribe(0, "/f/alpha/>").unwrap();
    let first_plain = plain_sub.recv().unwrap().unwrap();
    assert_eq!(first_plain.0, 0);
    assert_eq!(plain_sub.last_bt_ms(), None);
    drop(plain_sub);
    drop(p2);
    drop(probe);

    handle.shutdown();
    drop(broker);

    // 5. Open a replica from the copied log under an unrelated clock (`9_999_999_999_000`):
    //    `bt=` comes from the stored record bytes, never recomputed.
    std::fs::copy(&log, &rlog).unwrap();
    std::fs::copy(format!("{log}.id"), format!("{rlog}.id")).unwrap();
    let replica = Broker::open_replica(&rlog).unwrap();
    replica.set_clock_override(Some(Arc::new(AtomicU64::new(9_999_999_999_000))));
    let mut rhandle = replica.serve(&rsock).unwrap();

    let mut rclient = Client::connect(&rsock).unwrap();
    let (rfetched, _) = rclient.fetch_stamped(0, "/f/alpha/>", 16).unwrap();
    assert_eq!(rfetched, expected);
    let (rlast, _) = rclient.last_all_stamped("/f/alpha/>").unwrap();
    assert_eq!(rlast, last_rows);
    drop(rclient);
    rhandle.shutdown();
}

/// Live `Replicated` follower shipping + state-carrying retention (`<log>.held` and
/// `<log>.state`) preserve exact leader `bt=` values across replication, compaction, and
/// restart.
#[test]
fn r3_live_replicated_follower_and_compacted_held_store_preserve_bt() {
    let (_ftmp, flog, fsock) = paths("r3f");
    let (_ltmp, llog, lsock) = paths("r3l");

    let follower = Broker::open(&flog).unwrap();
    follower.set_clock_override(Some(Arc::new(AtomicU64::new(8_888_888_888_000))));
    let mut f_tcp = follower.serve_tcp("127.0.0.1:0").unwrap();
    let faddr = f_tcp.tcp_addr().unwrap().to_string();
    let mut f_unix = follower.serve(&fsock).unwrap();

    let leader = Broker::open_replicated(&llog, std::slice::from_ref(&faddr), 1).unwrap();
    let lclock = Arc::new(AtomicU64::new(1_700_000_100_000));
    leader.set_clock_override(Some(lclock.clone()));
    let mut l_unix = leader.serve(&lsock).unwrap();

    let mut pubc = Client::connect(&lsock).unwrap();
    pubc.publish(1, 1, "/f/alpha/pub/n1/s1/ev", b"m1").unwrap();
    lclock.store(1_700_000_102_000, Ordering::Relaxed);
    pubc.publish(1, 2, "/f/alpha/pub/n1/s1/ev", b"m2").unwrap();
    drop(pubc);

    // Read directly from the follower: its `bt=` stamps are the leader's, not 8_888_888_888_000!
    let mut fclient = Client::connect(&fsock).unwrap();
    let (fpage, _) = fclient.fetch_stamped(0, "/f/alpha/>", 16).unwrap();
    assert_eq!(
        fpage,
        vec![
            (
                0,
                "/f/alpha/pub/n1/s1/ev".to_string(),
                b"m1".to_vec(),
                Some(1_700_000_100_000),
            ),
            (
                1,
                "/f/alpha/pub/n1/s1/ev".to_string(),
                b"m2".to_vec(),
                Some(1_700_000_102_000),
            ),
        ]
    );
    drop(fclient);
    l_unix.shutdown();
    f_unix.shutdown();
    f_tcp.shutdown();
    drop(leader);
    drop(follower);

    #[cfg(feature = "retention")]
    {
        use astream_broker::parse_rules;

        let (_ctmp, clog, csock) = paths("r3comp");
        let rules = parse_rules(
            "prefix bytes=512 /f/alpha/pub/*/*/ev\n\
             hold bytes=65536 /f/alpha/in/>\n\
             hold bytes=65536 last /f/alpha/pub/*/*/presence\n\
             default bytes=65536\n",
        )
        .unwrap();

        let broker = Broker::open(&clog).unwrap();
        let cclock = Arc::new(AtomicU64::new(1_700_000_200_000));
        broker.set_clock_override(Some(cclock.clone()));
        broker.set_retention(rules.clone()).unwrap();
        let mut h = broker.serve(&csock).unwrap();
        let mut c = Client::connect(&csock).unwrap();

        c.publish(1, 1, "/f/alpha/pub/n1/s1/presence", b"live")
            .unwrap();
        cclock.store(1_700_000_201_000, Ordering::Relaxed);
        c.publish(1, 2, "/f/alpha/in/n1/s1/mgr/task", b"unread-mail")
            .unwrap();
        cclock.store(1_700_000_205_000, Ordering::Relaxed);
        for seq in 3..=25u64 {
            c.publish(1, seq, "/f/alpha/pub/n1/s1/ev", &[b'x'; 64])
                .unwrap();
        }
        broker.retention_tick_at(10_000).unwrap();
        assert!(
            broker.stats().log.base.0 > 2,
            "prefix cut passed offsets 0 and 1"
        );
        drop(c);
        h.shutdown();
        drop(broker);

        // Reopen under a completely different clock and verify both `<log>.held` and
        // `<log>.state` carried the exact `bt=` stamps!
        let reopened = Broker::open(&clog).unwrap();
        reopened.set_clock_override(Some(Arc::new(AtomicU64::new(5_555_555_555_000))));
        reopened.set_retention(rules).unwrap();
        let mut rh = reopened.serve(&csock).unwrap();
        let mut rc = Client::connect(&csock).unwrap();

        let (last_presence, _) = rc.last_all_stamped("/f/alpha/pub/*/*/presence").unwrap();
        assert_eq!(last_presence.len(), 1);
        assert_eq!(last_presence[0].0, 0);
        assert_eq!(last_presence[0].3, Some(1_700_000_200_000));

        let ((held_mail, _), _) = rc.fetch_told_stamped(0, "/f/alpha/in/>", 16).unwrap();
        assert_eq!(held_mail.len(), 1);
        assert_eq!(held_mail[0].0, 1);
        assert_eq!(held_mail[0].2, b"unread-mail");
        assert_eq!(held_mail[0].3, Some(1_700_000_201_000));

        drop(rc);
        rh.shutdown();
    }
}

/// R5 acceptance + negative controls + `asb` CLI `--bt` & wire `stats` round-trip:
/// - Two attached producers (`n-worker1` with a pending `Will` + 1 published record, and
///   quiet `n-worker2`) -> `Stats` lists both principals, their transports, attach times,
///   `last_bt_ms`, `records=1` under `/f/alpha/pub`, `pending_wills=1`, `dedup_entries>=1`,
///   `disk_segments>=1`, `disk_bytes>0`, and zero bodies.
/// - Disconnect `n-worker1` -> its `Will` fires -> `Stats` lists 1 producer (`n-worker2`),
///   `pending_wills=0`, and `records=2` under `/f/alpha/pub` (event + goodbye).
/// - Negative controls: unattached client -> `ERR_UNAUTHORIZED`; narrow `ro:/f/alpha/in/n1/>`
///   client -> `ERR_UNAUTHORIZED`; sibling-fleet `ro:/f/beta/>` client -> `ERR_UNAUTHORIZED`
///   for `/f/alpha/>` and sees zero `/f/alpha` producers or faces under `/f/beta/>`!
#[cfg(feature = "cap")]
#[test]
fn r5_wire_stats_operators_acceptance_and_cli_roundtrip() {
    use astream_broker::{broker_refusal, mint, producer_id_of};
    use std::process::{Command, Stdio};

    const SECRET: &[u8] = b"r5-stats-secret-0123456789abcdef01234567";
    let (_tmp, log, sock) = paths("r5");
    let dir = std::env::temp_dir().join(format!(
        "asbt_r5_caps_{}_{}",
        std::process::id(),
        CTR.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();

    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let clock = Arc::new(AtomicU64::new(1_700_000_500_000));
    broker.set_clock_override(Some(clock.clone()));
    let mut unix_h = broker.serve(&sock).unwrap();

    #[cfg(feature = "aead")]
    const AEAD_KEY: [u8; 32] = [0x42; 32];
    #[cfg(feature = "aead")]
    let mut sealed_h = broker.serve_tcp_sealed("127.0.0.1:0", AEAD_KEY).unwrap();
    #[cfg(feature = "aead")]
    let sealed_addr = sealed_h.tcp_addr().unwrap().to_string();

    // Producer 1 (`n-worker1`) attaches on Unix, registers a Will, and publishes 1 record.
    let cap_w1 = mint(SECRET, "rw,p=n-worker1:/f/alpha/>").unwrap();
    let pid_w1 = producer_id_of("n-worker1");
    let mut p1 = Client::connect(&sock).unwrap();
    p1.attach(&cap_w1.filter, &cap_w1.tag).unwrap();
    p1.will(pid_w1, 100, "/f/alpha/pub/n1/w1/presence", b"state=gone")
        .unwrap();
    clock.store(1_700_000_501_000, Ordering::Relaxed);
    let (ev_off, _) = p1
        .publish(
            pid_w1,
            1,
            "/f/alpha/pub/n1/w1/ev",
            b"secret-body-never-in-stats",
        )
        .unwrap();

    // Producer 2 (`n-worker2`) attaches (over sealed TCP when `aead` is enabled, else Unix)
    // and stays quiet.
    let cap_w2 = mint(SECRET, "rw,p=n-worker2:/f/alpha/>").unwrap();
    let pid_w2 = producer_id_of("n-worker2");
    #[cfg(feature = "aead")]
    let p2 = {
        let mut c = Client::connect_tcp_sealed(&sealed_addr, AEAD_KEY).unwrap();
        c.attach(&cap_w2.filter, &cap_w2.tag).unwrap();
        c
    };
    #[cfg(not(feature = "aead"))]
    let p2 = {
        let mut c = Client::connect(&sock).unwrap();
        c.attach(&cap_w2.filter, &cap_w2.tag).unwrap();
        c
    };

    // Negative control 1: unattached client is refused ERR_UNAUTHORIZED (code 8).
    let mut unauth = Client::connect(&sock).unwrap();
    let err = unauth.stats("/f/alpha/>").unwrap_err();
    assert_eq!(broker_refusal(&err).map(|r| r.code), Some(8));

    // Negative control 2: narrow read grant (`ro:/f/alpha/in/n1/>`) cannot read fleet Stats.
    let cap_narrow = mint(SECRET, "ro:/f/alpha/in/n1/>").unwrap();
    let mut narrow = Client::connect(&sock).unwrap();
    narrow.attach(&cap_narrow.filter, &cap_narrow.tag).unwrap();
    let err = narrow.stats("/f/alpha/in/n1/>").unwrap_err();
    assert_eq!(broker_refusal(&err).map(|r| r.code), Some(8));
    let err = narrow.stats("/f/alpha/>").unwrap_err();
    assert_eq!(broker_refusal(&err).map(|r| r.code), Some(8));

    // Negative control 3: sibling-fleet grant (`ro:/f/beta/>`) is refused `/f/alpha/>`, and
    // querying `/f/beta/>` leaks neither `/f/alpha`'s attached producers nor its faces!
    let cap_beta = mint(SECRET, "ro:/f/beta/>").unwrap();
    let mut beta = Client::connect(&sock).unwrap();
    beta.attach(&cap_beta.filter, &cap_beta.tag).unwrap();
    let err = beta.stats("/f/alpha/>").unwrap_err();
    assert_eq!(broker_refusal(&err).map(|r| r.code), Some(8));
    let beta_stats = beta.stats("/f/beta/>").unwrap();
    assert!(beta_stats.producers.is_empty());
    assert!(beta_stats.faces.is_empty());

    // Fleet-wide operator grant (`ro:/f/alpha/>`) reads full operational Stats!
    let cap_op = mint(SECRET, "ro:/f/alpha/>").unwrap();
    let mut op = Client::connect(&sock).unwrap();
    op.attach(&cap_op.filter, &cap_op.tag).unwrap();
    let s1 = op.stats("/f/alpha/>").unwrap();
    assert!(s1.started_at_ms > 0);
    assert!(s1.listeners.iter().any(|l| l.starts_with("unix:")));
    #[cfg(feature = "aead")]
    assert!(s1.listeners.iter().any(|l| l.starts_with("sealed:")));
    assert_eq!(s1.producers.len(), 2);
    assert_eq!(s1.producers[0].principal, "n-worker1");
    assert_eq!(s1.producers[0].transport, "unix");
    assert_eq!(s1.producers[0].producer_id, pid_w1);
    assert!(s1.producers[0].attached_at_ms > 0);
    assert_eq!(s1.producers[0].last_bt_ms, Some(1_700_000_501_000));
    assert_eq!(s1.producers[1].principal, "n-worker2");
    #[cfg(feature = "aead")]
    assert_eq!(s1.producers[1].transport, "sealed");
    #[cfg(not(feature = "aead"))]
    assert_eq!(s1.producers[1].transport, "unix");
    assert_eq!(s1.producers[1].producer_id, pid_w2);
    assert_eq!(s1.producers[1].last_bt_ms, None);
    assert_eq!(s1.faces.len(), 1);
    assert_eq!(s1.faces[0].face, "/f/alpha/pub");
    assert_eq!(s1.faces[0].records, 1);
    assert!(s1.faces[0].bytes > 0);
    assert_eq!(s1.pending_wills, 1);
    assert!(s1.dedup_entries >= 1);
    assert!(s1.disk_segments >= 1);
    assert!(s1.disk_bytes > 0);

    // Exercise `asb` CLI: `asb stats <endpoint> <filter> unix <cap>`, `asb fetch --bt`, `asb last --bt`.
    let cap_file = dir.join("op.cap");
    let tag_hex: String = cap_op.tag.iter().map(|b| format!("{b:02x}")).collect();
    std::fs::write(&cap_file, format!("{} {tag_hex}\n", cap_op.filter)).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&cap_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let cap_path = cap_file.to_str().unwrap();

    let out_stats = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args(["stats", &sock, "/f/alpha/>", "--cap-file", cap_path])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        out_stats.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out_stats.stderr)
    );
    let stats_text = String::from_utf8_lossy(&out_stats.stdout);
    assert!(stats_text.contains("STATS started_at_ms="), "{stats_text}");
    assert!(stats_text.contains("LISTENER unix:"), "{stats_text}");
    assert!(
        stats_text.contains("PRODUCER principal=n-worker1")
            && stats_text.contains("last_bt_ms=1700000501000"),
        "{stats_text}"
    );
    assert!(
        stats_text.contains("PRODUCER principal=n-worker2")
            && stats_text.contains("last_bt_ms=none"),
        "{stats_text}"
    );
    assert!(
        stats_text.contains("FACE prefix=/f/alpha/pub records=1 bytes="),
        "{stats_text}"
    );
    assert!(
        !stats_text.contains("secret-body-never-in-stats"),
        "Stats never returns record bodies"
    );

    let out_fetch_bt = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "fetch",
            &sock,
            "/f/alpha/>",
            "--from",
            "0",
            "--max",
            "16",
            "--bt",
            "--cap-file",
            cap_path,
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        out_fetch_bt.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out_fetch_bt.stderr)
    );
    let fetch_bt_text = String::from_utf8_lossy(&out_fetch_bt.stdout);
    assert!(
        fetch_bt_text.contains(&format!(
            "{ev_off} 26 bt=1700000501000 /f/alpha/pub/n1/w1/ev"
        )),
        "{fetch_bt_text}"
    );

    let out_last_bt = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "last",
            &sock,
            "/f/alpha/>",
            "--max",
            "16",
            "--bt",
            "--cap-file",
            cap_path,
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        out_last_bt.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out_last_bt.stderr)
    );
    let last_bt_text = String::from_utf8_lossy(&out_last_bt.stdout);
    assert!(
        last_bt_text.contains(&format!(
            "{ev_off} 26 bt=1700000501000 /f/alpha/pub/n1/w1/ev"
        )),
        "{last_bt_text}"
    );

    // Kill Producer 1 -> its Will fires -> Stats shows 1 attached producer (`n-worker2`),
    // `pending_wills == 0`, and `records == 2` (original event + goodbye) under `/f/alpha/pub`!
    clock.store(1_700_000_505_000, Ordering::Relaxed);
    drop(p1);
    wait_until("p1 will settled", || broker.stats().wills_settled >= 1);

    let s2 = op.stats("/f/alpha/>").unwrap();
    assert_eq!(s2.producers.len(), 1);
    assert_eq!(s2.producers[0].principal, "n-worker2");
    assert_eq!(s2.pending_wills, 0);
    assert_eq!(s2.faces.len(), 1);
    assert_eq!(s2.faces[0].face, "/f/alpha/pub");
    assert_eq!(s2.faces[0].records, 2);

    // A revoked principal's quiet connection, attached until its next request, is not listed:
    // the revocations are read against the copy of the attached connections, each lock taken
    // alone (`serve_stats`; a reload takes `revoked_identities` then `revoked_principals`).
    assert!(broker.revoke_principal("n-worker2"));
    let s3 = op.stats("/f/alpha/>").unwrap();
    assert!(s3.producers.is_empty(), "{:?}", s3.producers);

    drop(p2);
    drop(op);
    drop(beta);
    drop(narrow);
    drop(unauth);
    #[cfg(feature = "aead")]
    sealed_h.shutdown();
    unix_h.shutdown();
    let _ = std::fs::remove_dir_all(&dir);
}
