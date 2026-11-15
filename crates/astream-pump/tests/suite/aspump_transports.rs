// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `pump.cli.security-transports`: Rung 7–10 multi-machine security
//! transports in the `aspump` CLI (`--handshake`, `--roam`, `--host-key-file` +
//! `--client-key-file`, and `--cert-file` + `--ca-key-file` + `--ssh-agent-sock` +
//! `--host-principal`), including durable `--group` commits, `--task-subject` queue
//! posting, principal-bound capabilities, and fail-closed argv/feature rejection.
#![cfg(all(unix, feature = "identity", feature = "cap"))]

use astream_broker::{
    identity_principal, mint, producer_id_of, Broker, CertRole, CertTrustStore,
    CertificateAuthority, Client, HostCertRotator, IdentityKeypair, IdentitySigner,
    SharedCertTrust, SshAgentServer,
};
use astream_pump::drain_wake_tasks;
use std::os::unix::fs::PermissionsExt;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Self {
        Self(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
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

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn write_secret_file(path: &std::path::Path, text: &str) {
    std::fs::write(path, text.as_bytes()).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600)).unwrap();
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}

fn session_chunks() -> [&'static [u8]; 6] {
    [
        b"\x1b[2J\x1b[H",
        b"\x1b]133;A\x07$ ",
        b"echo ok\r\n",
        b"\x1b]133;C\x07",
        b"ok\r\n",
        b"\x1b]133;D;0\x07",
    ]
}

#[test]
fn aspump_cli_tails_and_commits_over_handshake_and_roam_udp_transports() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::path::PathBuf::from(format!("/tmp/asp_r710_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let _clean = Cleanup::new(&[&dir]);

    let log = dir.join("broker.log");
    let sock = dir.join("b.s");
    let key_path = dir.join("psk.key");
    let cap_path = dir.join("pump.cap");

    let psk = [0x5Au8; 32];
    write_secret_file(&key_path, &format!("{}\n", hex(&psk)));

    let secret = b"aspump-r710-mint-secret-32bytes!";
    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let mut h_unix = broker.serve(&sock).unwrap();
    let mut h_hs = broker.serve_tcp_handshake("127.0.0.1:0", psk).unwrap();
    let mut h_roam = broker.serve_udp_roaming("127.0.0.1:0", psk).unwrap();

    let hs_addr = h_hs.tcp_addr().unwrap().to_owned();
    let roam_addr = h_roam.tcp_addr().unwrap().to_owned();

    let mut prod = Client::connect(&sock).unwrap();
    let w_cap = mint(secret, "rw,p=a-prod:/a/>").unwrap();
    prod.attach(&w_cap.filter, &w_cap.tag).unwrap();
    let prod_id = producer_id_of("a-prod");
    for (i, chunk) in session_chunks().iter().enumerate() {
        prod.publish(prod_id, (i + 1) as u64, "/a/stream/term/s_net/out", chunk)
            .unwrap();
    }

    let r_cap = mint(secret, "ro:/a/stream/term/s_net/>").unwrap();
    let g_cap = mint(secret, "rw,p=a-pump:/f/F/cur/>").unwrap();
    let t_cap = mint(secret, "rw,p=a-pump:/a/wake/>").unwrap();
    write_secret_file(
        &cap_path,
        &format!(
            "{} {}\n{} {}\n{} {}\n",
            r_cap.filter,
            hex(&r_cap.tag),
            g_cap.filter,
            hex(&g_cap.tag),
            t_cap.filter,
            hex(&t_cap.tag),
        ),
    );
    let pump_pid = producer_id_of("a-pump");

    // 1. Rung-7 `--handshake`: two consecutive `--once --group` runs advance durably!
    for (seq_start, want) in [
        ("0", "PROMPT_READY boffset=2\n"),
        ("1", "COMMAND_START boffset=4\n"),
        ("2", "COMMAND_END boffset=6 exit=0\n"),
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &hs_addr,
                "s_net",
                "--once",
                "--group",
                "/f/F/cur/hs",
                "--handshake",
                "--key-file",
                key_path.to_str().unwrap(),
                "--cap-file",
                cap_path.to_str().unwrap(),
                "--task-subject",
                "/a/wake/hs",
                "--task-producer",
                &pump_pid.to_string(),
                "--task-seq-start",
                seq_start,
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(0),
            "handshake stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), want);
    }

    // 2. Rung-10 `--roam` (UDP Connection-ID `AROM` v1): `--once --group` + `--task-subject`!
    for (seq_start, want) in [
        ("3", "PROMPT_READY boffset=2\n"),
        ("4", "COMMAND_START boffset=4\n"),
        ("5", "COMMAND_END boffset=6 exit=0\n"),
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &roam_addr,
                "s_net",
                "--once",
                "--group",
                "/f/F/cur/roam",
                "--roam",
                "--key-file",
                key_path.to_str().unwrap(),
                "--cap-file",
                cap_path.to_str().unwrap(),
                "--task-subject",
                "/a/wake/roam",
                "--task-producer",
                &pump_pid.to_string(),
                "--task-seq-start",
                seq_start,
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(0),
            "roam stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), want);
    }

    // Verify the task queues received all 3 wake items on both transports!
    let rd_cap = mint(secret, "ro:/a/wake/>").unwrap();
    let mut reader_hs = Client::connect(&sock).unwrap();
    reader_hs.attach(&rd_cap.filter, &rd_cap.tag).unwrap();
    reader_hs.attach(&g_cap.filter, &g_cap.tag).unwrap();
    let hs_items = drain_wake_tasks(reader_hs, "/f/F/cur/drain_hs", "/a/wake/hs", 16).unwrap();

    let mut reader_roam = Client::connect(&sock).unwrap();
    reader_roam.attach(&rd_cap.filter, &rd_cap.tag).unwrap();
    reader_roam.attach(&g_cap.filter, &g_cap.tag).unwrap();
    let roam_items =
        drain_wake_tasks(reader_roam, "/f/F/cur/drain_roam", "/a/wake/roam", 16).unwrap();
    assert_eq!(hs_items.len(), 3);
    assert_eq!(roam_items.len(), 3);
    assert_eq!(roam_items[2].1.wake_line, "COMMAND_END boffset=6 exit=0");

    // Wrong PSK on `--handshake` and `--roam` fails closed with exit 1!
    let bad_key_path = dir.join("bad.key");
    write_secret_file(&bad_key_path, &format!("{}\n", hex(&[0x99u8; 32])));
    for (addr, flag) in [(&hs_addr, "--handshake"), (&roam_addr, "--roam")] {
        let bad = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                addr.as_str(),
                "s_net",
                "--once",
                flag,
                "--key-file",
                bad_key_path.to_str().unwrap(),
                "--cap-file",
                cap_path.to_str().unwrap(),
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(bad.status.code(), Some(1), "{flag} wrong PSK must exit 1");
    }

    drop(prod);
    h_roam.shutdown();
    h_hs.shutdown();
    h_unix.shutdown();
}

#[test]
fn aspump_cli_tails_over_mutual_identity_and_certified_ssh_agent_transports() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::path::PathBuf::from(format!("/tmp/asp_r89_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let _clean = Cleanup::new(&[&dir]);

    let log = dir.join("broker.log");
    let sock = dir.join("b.s");
    let agent_sock = dir.join("ag.s");

    let secret = b"aspump-r89-mint-secret-012345678";
    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let mut h_unix = broker.serve(&sock).unwrap();

    // Publish fixture records onto `/a/stream/term/s_id/out`.
    let mut prod = Client::connect(&sock).unwrap();
    let w_cap = mint(secret, "rw,p=a-prod:/a/>").unwrap();
    prod.attach(&w_cap.filter, &w_cap.tag).unwrap();
    let prod_id = producer_id_of("a-prod");
    for (i, chunk) in session_chunks().iter().enumerate() {
        prod.publish(prod_id, (i + 1) as u64, "/a/stream/term/s_id/out", chunk)
            .unwrap();
    }

    // 1. Rung-8 mutual static Ed25519 identity (`--host-key-file` + `--client-key-file`).
    let host_id = IdentityKeypair::from_seed([0x21u8; 32]);
    let client_seed = [0x22u8; 32];
    let client_id = IdentityKeypair::from_seed(client_seed);
    let mut h_id = broker
        .serve_tcp_identity("127.0.0.1:0", host_id.clone(), vec![client_id.public()])
        .unwrap();
    let id_addr = h_id.tcp_addr().unwrap().to_owned();

    let host_pub_path = dir.join("host.pub");
    let client_seed_path = dir.join("client.seed");
    write_secret_file(&host_pub_path, &format!("{}\n", hex(&host_id.public())));
    write_secret_file(&client_seed_path, &format!("{}\n", hex(&client_seed)));

    let id_principal = identity_principal(&client_id.public());
    let r_cap = mint(secret, "ro:/a/stream/term/s_id/>").unwrap();
    let g_id_cap = mint(secret, &format!("rw,p={id_principal}:/f/F/cur/>")).unwrap();
    let id_cap_path = dir.join("id.cap");
    write_secret_file(
        &id_cap_path,
        &format!(
            "{} {}\n{} {}\n",
            r_cap.filter,
            hex(&r_cap.tag),
            g_id_cap.filter,
            hex(&g_id_cap.tag)
        ),
    );

    let out_id = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &id_addr,
            "s_id",
            "--once",
            "--group",
            "/f/F/cur/id",
            "--host-key-file",
            host_pub_path.to_str().unwrap(),
            "--client-key-file",
            client_seed_path.to_str().unwrap(),
            "--cap-file",
            id_cap_path.to_str().unwrap(),
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert_eq!(
        out_id.status.code(),
        Some(0),
        "identity stderr: {}",
        String::from_utf8_lossy(&out_id.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out_id.stdout),
        "PROMPT_READY boffset=2\n"
    );

    // 2. Rung-9 external CA certificate + `SSH_AUTH_SOCK` signing (`--cert-file` + `--ca-key-file` + `--ssh-agent-sock`).
    let ca_kp = IdentityKeypair::from_seed([0x31u8; 32]);
    let ca_pub = ca_kp.public();
    let ca =
        CertificateAuthority::new(IdentitySigner::from(ca_kp), "ssh-ca://aspump-test").unwrap();
    let cert_host_key = IdentityKeypair::from_seed([0x32u8; 32]);
    let cert_client_key = IdentityKeypair::from_seed([0x33u8; 32]);
    let now = now_ms();
    let host_cert = ca
        .issue(
            CertRole::Host,
            cert_host_key.public(),
            "broker-east",
            10,
            now.saturating_sub(1_000),
            now + 600_000,
        )
        .unwrap();
    let client_cert = ca
        .issue(
            CertRole::Client,
            cert_client_key.public(),
            "a-pump-cert",
            11,
            now.saturating_sub(1_000),
            now + 600_000,
        )
        .unwrap();

    let trust = CertTrustStore::new(vec![ca_pub], 3_600_000).unwrap();
    let shared_trust = SharedCertTrust::new(trust);
    let rotator = HostCertRotator::new(IdentitySigner::from(cert_host_key), host_cert).unwrap();
    let mut h_cert = broker
        .serve_tcp_certified("127.0.0.1:0", rotator, shared_trust)
        .unwrap();
    let cert_addr = h_cert.tcp_addr().unwrap().to_owned();

    let agent = SshAgentServer::bind(
        &agent_sock,
        vec![(cert_client_key, "pump-client".to_owned())],
    )
    .unwrap();

    let ca_pub_path = dir.join("ca.pub");
    let client_cert_path = dir.join("client.cert");
    write_secret_file(&ca_pub_path, &format!("{}\n", hex(&ca_pub)));
    write_secret_file(
        &client_cert_path,
        &format!("{}\n", hex(&client_cert.encode())),
    );

    let g_cert_cap = mint(secret, "rw,p=a-pump-cert:/f/F/cur/>").unwrap();
    let cert_cap_path = dir.join("cert.cap");
    write_secret_file(
        &cert_cap_path,
        &format!(
            "{} {}\n{} {}\n",
            r_cap.filter,
            hex(&r_cap.tag),
            g_cert_cap.filter,
            hex(&g_cert_cap.tag)
        ),
    );

    for want in [
        "PROMPT_READY boffset=2\n",
        "COMMAND_START boffset=4\n",
        "COMMAND_END boffset=6 exit=0\n",
    ] {
        let out_cert = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &cert_addr,
                "s_id",
                "--once",
                "--group",
                "/f/F/cur/cert",
                "--cert-file",
                client_cert_path.to_str().unwrap(),
                "--ca-key-file",
                ca_pub_path.to_str().unwrap(),
                "--ssh-agent-sock",
                agent_sock.to_str().unwrap(),
                "--host-principal",
                "broker-east",
                "--cap-file",
                cert_cap_path.to_str().unwrap(),
            ])
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(
            out_cert.status.code(),
            Some(0),
            "certified stderr: {}",
            String::from_utf8_lossy(&out_cert.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out_cert.stdout), want);
    }

    // Negative controls:
    // (a) Wrong expected `--host-principal` refuses at TLS/SIGMA handshake (exit 1).
    let bad_host = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &cert_addr,
            "s_id",
            "--once",
            "--cert-file",
            client_cert_path.to_str().unwrap(),
            "--ca-key-file",
            ca_pub_path.to_str().unwrap(),
            "--ssh-agent-sock",
            agent_sock.to_str().unwrap(),
            "--host-principal",
            "broker-west",
            "--cap-file",
            cert_cap_path.to_str().unwrap(),
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert_eq!(bad_host.status.code(), Some(1));

    // (b) Contradictory / inline-secret flags refuse at parse time (exit 2) before dialing.
    for bad_args in [
        vec!["/no/ep", "s1", "--client-key", "deadbeef"],
        vec!["/no/ep", "s1", "--handshake"],
        vec!["/no/ep", "s1", "--roam"],
        vec![
            "/no/ep",
            "s1",
            "--handshake",
            "--roam",
            "--key-file",
            ca_pub_path.to_str().unwrap(),
        ],
        vec![
            "/no/ep",
            "s1",
            "--cert-file",
            client_cert_path.to_str().unwrap(),
        ],
        vec![
            "/no/ep",
            "s1",
            "--cert-file",
            client_cert_path.to_str().unwrap(),
            "--ca-key-file",
            ca_pub_path.to_str().unwrap(),
            "--client-key-file",
            client_seed_path.to_str().unwrap(),
            "--ssh-agent-sock",
            agent_sock.to_str().unwrap(),
        ],
    ] {
        let res = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args(&bad_args)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert_eq!(
            res.status.code(),
            Some(2),
            "expected exit 2 for {bad_args:?}"
        );
    }

    agent.shutdown();
    drop(prod);
    h_cert.shutdown();
    h_id.shutdown();
    h_unix.shutdown();
}
