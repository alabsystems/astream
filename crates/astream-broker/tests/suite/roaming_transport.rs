// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.roam-udp-migration`: zero-gap AEAD-over-UDP connection
//! migration (`Broker::serve_udp_roaming`, `Client::connect_udp_roaming`, `RoamHandle`,
//! `asb serve --listen roam:<host:port>`).
//!
//! Proves over real OS `UdpSocket`s that migrating a live client across new local
//! IP:port sockets (including across an abrupt mid-flight blackhole) preserves:
//! - open `Subscription::recv()` streams without gap, duplication, or reconnect;
//! - pipelined `send_publish` / `recv_publish_ack` / `try_recv_publish_ack` exchanges;
//! - attached `astream-cap` capabilities without re-attaching;
//! - registered Last Wills without false firing during migration (while still firing
//!   the Last Will once the session genuinely closes).
#![cfg(all(feature = "handshake", feature = "cap"))]

use astream_broker::{mint, producer_id_of, Broker, Client, ROAM_WIRE_MAGIC, ROAM_WIRE_VERSION};
use std::net::UdpSocket;
use std::sync::atomic::{AtomicU64, Ordering};

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
            let _ = std::fs::remove_file(path);
            if path.is_dir() {
                let _ = std::fs::remove_dir_all(path);
            } else if let (Some(dir), Some(name)) = (path.parent(), path.file_name()) {
                let prefix = format!("{}.", name.to_string_lossy());
                for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                    if entry.file_name().to_string_lossy().starts_with(&prefix) {
                        let _ = std::fs::remove_file(entry.path());
                    }
                }
            }
        }
    }
}

fn log_path(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = std::env::temp_dir().join(format!("asroam_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&log]), log)
}

#[test]
fn zero_gap_live_subscription_pipelining_caps_and_will_across_udp_migrations() {
    let (_tmp, log) = log_path("live_mig");
    let secret = b"roam-guarded-mint-secret-32bytes";
    let psk = [0x42u8; 32];

    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let mut handle = broker.serve_udp_roaming("127.0.0.1:0", psk).unwrap();
    let addr = handle
        .tcp_addr()
        .expect("bound UDP roam endpoint")
        .to_owned();

    // 1. Connect subscriber, attach read grant, and start a live Subscription.
    let (mut sub_client, sub_roam) = Client::connect_udp_roaming(&addr, psk).unwrap();
    let cap_ro = mint(secret, "ro:/a/roam/>").unwrap();
    sub_client.attach(&cap_ro.filter, &cap_ro.tag).unwrap();
    let sub_sock_0 = sub_roam.local_addr().unwrap();
    let mut sub = sub_client.subscribe(0, "/a/roam/>").unwrap();

    // 2. Connect publisher, attach principal-bound write grant, and arm a Last Will.
    let (mut pub_client, pub_roam) = Client::connect_udp_roaming(&addr, psk).unwrap();
    let cap_rw = mint(secret, "rw,p=a-roamer:/a/roam/>").unwrap();
    pub_client.attach(&cap_rw.filter, &cap_rw.tag).unwrap();
    let pid = producer_id_of("a-roamer");
    pub_client
        .will(pid, 999, "/a/roam/will", b"roamer-disconnected")
        .unwrap();
    let pub_sock_0 = pub_roam.local_addr().unwrap();

    // 3. Publish 3 records over initial UDP sockets (`/a/bind` = 0, `/a/will` = 1, so
    //    seq `1..=3` land at offsets `2..=4`).
    for seq in 1..=3u64 {
        let (off, dup) = pub_client
            .publish(pid, seq, "/a/roam/events", format!("ev-{seq}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (seq + 1, false));
    }
    for seq in 1..=3u64 {
        let (off, subj, body) = sub.recv().unwrap().unwrap();
        assert_eq!(off, seq + 1);
        assert_eq!(subj, "/a/roam/events");
        assert_eq!(body, format!("ev-{seq}").as_bytes());
    }

    // 4. Blackhole BOTH sockets mid-flight, pipeline 3 publishes into the blackhole,
    //    then migrate BOTH clients onto fresh ephemeral UDP sockets!
    pub_roam.set_blackhole(true);
    sub_roam.set_blackhole(true);
    for seq in 4..=6u64 {
        pub_client
            .send_publish(pid, seq, "/a/roam/events", format!("ev-{seq}").as_bytes())
            .unwrap();
    }
    assert_eq!(pub_client.owed_acks(), 3);
    assert!(pub_client.try_recv_publish_ack().unwrap().is_none());

    let pub_sock_1 = pub_roam.migrate().unwrap();
    let sub_sock_1 = sub_roam.migrate().unwrap();
    assert_ne!(pub_sock_0, pub_sock_1);
    assert_ne!(sub_sock_0, sub_sock_1);
    assert_eq!(pub_roam.migration_epoch(), 1);
    assert_eq!(sub_roam.migration_epoch(), 1);

    // All 3 pipelined acks resolve in order without reconnecting or re-attaching caps!
    for seq in 4..=6u64 {
        let (off, dup) = pub_client.recv_publish_ack().unwrap();
        assert_eq!((off, dup), (seq + 1, false));
    }
    // Dedup across migration also holds!
    assert_eq!(
        pub_client
            .publish(pid, 5, "/a/roam/events", b"ev-5")
            .unwrap(),
        (6, true)
    );

    // Live subscription receives seq 4..=6 (offsets 5..=7) with zero gap and zero false Last Will!
    for seq in 4..=6u64 {
        let (off, subj, body) = sub.recv().unwrap().unwrap();
        assert_eq!(off, seq + 1);
        assert_eq!(subj, "/a/roam/events");
        assert_eq!(body, format!("ev-{seq}").as_bytes());
    }

    // 5. Migrate a SECOND time onto a third pair of UDP sockets and publish 7..=9.
    let pub_sock_2 = pub_roam.migrate().unwrap();
    let sub_sock_2 = sub_roam.migrate().unwrap();
    assert_ne!(pub_sock_1, pub_sock_2);
    assert_ne!(sub_sock_1, sub_sock_2);
    assert_eq!(pub_roam.migration_epoch(), 2);
    assert_eq!(sub_roam.migration_epoch(), 2);

    for seq in 7..=9u64 {
        let (off, dup) = pub_client
            .publish(pid, seq, "/a/roam/events", format!("ev-{seq}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (seq + 1, false));
    }
    for seq in 7..=9u64 {
        let (off, subj, body) = sub.recv().unwrap().unwrap();
        assert_eq!(off, seq + 1);
        assert_eq!(subj, "/a/roam/events");
        assert_eq!(body, format!("ev-{seq}").as_bytes());
    }

    // 6. Now genuinely close `pub_client`: its registered Last Will MUST fire at offset 11!
    drop(pub_client);
    let (will_off, will_subj, will_body) = sub.recv().unwrap().unwrap();
    assert_eq!(will_off, 11);
    assert_eq!(will_subj, "/a/roam/will");
    assert_eq!(will_body, b"roamer-disconnected");

    drop(sub);
    handle.shutdown();
}

#[test]
fn roam_negative_controls_spoofed_cid_and_garbage_datagrams_preserve_live_session() {
    let (_tmp, log) = log_path("neg_roam");
    let psk = [0x7Bu8; 32];

    let broker = Broker::open(&log).unwrap();
    let mut handle = broker.serve_udp_roaming("127.0.0.1:0", psk).unwrap();
    let addr = handle.tcp_addr().unwrap().to_owned();

    let (mut c, roam) = Client::connect_udp_roaming(&addr, psk).unwrap();
    assert_eq!(c.publish(1, 1, "/a/ok", b"v1").unwrap(), (0, false));

    // Flood spoofed CID datagrams and malformed frames from an attacker UDP socket:
    // the broker must silently drop all of them without hijacking or poisoning `c`.
    let attacker = UdpSocket::bind("127.0.0.1:0").unwrap();
    let _ = attacker.send_to(b"PLAIN-GARBAGE-UDP", &addr);
    let mut spoofed = Vec::new();
    spoofed.extend_from_slice(&ROAM_WIRE_MAGIC);
    spoofed.push(ROAM_WIRE_VERSION);
    spoofed.push(0x05);
    spoofed.extend_from_slice(&roam.cid());
    spoofed.extend_from_slice(&0u64.to_be_bytes());
    spoofed.extend_from_slice(&[0xFFu8; 64]);
    for _ in 0..8 {
        let _ = attacker.send_to(&spoofed, &addr);
    }

    assert_eq!(c.publish(1, 2, "/a/ok", b"v2").unwrap(), (1, false));
    let _ = roam.migrate().unwrap();
    assert_eq!(c.publish(1, 3, "/a/ok", b"v3").unwrap(), (2, false));

    let (rows, _) = c.fetch(0, "/a/ok", 16).unwrap();
    assert_eq!(rows.len(), 3);

    drop(c);
    handle.shutdown();
}

#[cfg(unix)]
#[test]
fn cli_asb_serve_roam_udp_with_guarded_caps_and_live_migration() {
    use std::io::{BufRead, BufReader};
    use std::os::unix::fs::PermissionsExt;
    use std::process::{Command, Stdio};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("asb_roam_cli_{}_{n}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let _clean = Cleanup::new(&[&dir]);

    let psk = [0x9Cu8; 32];
    let mut psk_hex = String::with_capacity(64);
    for b in psk {
        psk_hex.push_str(&format!("{b:02x}"));
    }
    psk_hex.push('\n');
    let key_path = dir.join("roam.key");
    std::fs::write(&key_path, psk_hex.as_bytes()).unwrap();
    std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600)).unwrap();

    let secret = b"cli-roam-mint-secret-0123456789abcdef";
    let secret_path = dir.join("mint.secret");
    std::fs::write(&secret_path, secret).unwrap();
    std::fs::set_permissions(&secret_path, std::fs::Permissions::from_mode(0o600)).unwrap();

    let log_file = dir.join("roam_cli.log");
    let mut child = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "serve",
            log_file.to_str().unwrap(),
            "--listen",
            "roam:127.0.0.1:0",
            "--key-file",
            key_path.to_str().unwrap(),
            "--secret-file",
            secret_path.to_str().unwrap(),
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    struct KillChild(std::process::Child);
    impl Drop for KillChild {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut r = BufReader::new(child.stdout.take().unwrap());
    let guard = KillChild(child);

    let mut ready = String::new();
    r.read_line(&mut ready).unwrap();
    let addr = ready
        .strip_prefix("listening ")
        .expect("asb serve readiness line")
        .trim_end()
        .to_owned();

    let (mut c, roam) = Client::connect_udp_roaming(&addr, psk).unwrap();
    let cap = mint(secret, "rw,p=a-cli-roam:/a/cli/>").unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    let pid = producer_id_of("a-cli-roam");
    assert_eq!(
        c.publish(pid, 1, "/a/cli/r", b"before-roam").unwrap(),
        (1, false)
    );

    let _ = roam.migrate().unwrap();
    assert_eq!(roam.migration_epoch(), 1);
    assert_eq!(
        c.publish(pid, 2, "/a/cli/r", b"after-roam").unwrap(),
        (2, false)
    );

    let (rows, _) = c.fetch(0, "/a/cli/>", 16).unwrap();
    assert_eq!(
        rows,
        vec![
            (1, "/a/cli/r".to_owned(), b"before-roam".to_vec()),
            (2, "/a/cli/r".to_owned(), b"after-roam".to_vec()),
        ]
    );
    drop(c);
    drop(guard);
}
