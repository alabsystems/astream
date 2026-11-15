// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.certified-tcp-roundtrip`: Rung 9. External identity authority
//! (`CertificateAuthority`, `IdentityCertificate`, `CertTrustStore`, `SharedCertTrust`),
//! zero-downtime overlapping host-key & CA rotation (`HostCertRotator`), external
//! `SSH_AUTH_SOCK` signing (`SshAgentServer` / `SshAgentSigner`), capability-to-certificate
//! principal binding on guarded brokers, and live certificate serial revocation.
#![cfg(all(feature = "identity", feature = "cap"))]

use astream_broker::{
    mint, producer_id_of, Broker, CertRole, CertTrustStore, CertificateAuthority, Client,
    FollowerTransport, HostCertRotator, IdentityKeypair, SharedCertTrust,
};
#[cfg(unix)]
use astream_broker::{IdentitySigner, SshAgentServer, SshAgentSigner};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

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
    let log = std::env::temp_dir().join(format!("ascert_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&log]), log)
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

fn expect_refused<F>(what: &str, op: F)
where
    F: FnOnce() -> std::io::Result<()> + Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(op().is_err());
    });
    match rx.recv_timeout(Duration::from_secs(5)) {
        Ok(errored) => assert!(errored, "{what} must be refused"),
        Err(_) => panic!("{what}: neither completed nor was refused within 5s"),
    }
}

#[cfg(unix)]
#[test]
fn ssh_agent_backed_certified_publish_subscribe_resume_and_dedup() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let agent_dir = std::path::PathBuf::from(format!("/tmp/ascert_ag_{}_{n}", std::process::id()));
    std::fs::create_dir_all(&agent_dir).unwrap();
    let (_tmp, log) = log_path("agent_e2e");
    let _agent_cleanup = Cleanup::new(&[&agent_dir]);

    let ca_kp = IdentityKeypair::generate();
    let host_kp = IdentityKeypair::generate();
    let client_kp = IdentityKeypair::generate();
    let ca_pub = ca_kp.public();
    let host_pub = host_kp.public();
    let client_pub = client_kp.public();

    let sock_path = agent_dir.join("a.s");
    let agent = SshAgentServer::bind(
        &sock_path,
        vec![
            (ca_kp, "fleet-ca".to_owned()),
            (host_kp, "broker-east".to_owned()),
            (client_kp, "alice".to_owned()),
        ],
    )
    .unwrap();

    let t0 = now_ms().saturating_sub(5_000);
    let t1 = t0 + 600_000;

    let ca = CertificateAuthority::new(
        SshAgentSigner::connect_for_key(&sock_path, ca_pub).unwrap(),
        "ssh-ca://prod-fleet",
    )
    .unwrap();
    let host_cert = ca
        .issue(CertRole::Host, host_pub, "n-broker-east", 1, t0, t1)
        .unwrap();
    let client_cert = ca
        .issue(CertRole::Client, client_pub, "h-alice", 101, t0, t1)
        .unwrap();

    let host_rotator = HostCertRotator::new(
        SshAgentSigner::connect_for_key(&sock_path, host_pub).unwrap(),
        host_cert,
    )
    .unwrap();
    let trust_store = CertTrustStore::new(vec![ca_pub], 3_600_000)
        .unwrap()
        .with_allowed_issuers(vec!["ssh-ca://prod-fleet".to_owned()])
        .unwrap();
    let shared_trust = SharedCertTrust::new(trust_store.clone());

    let broker = Broker::open(&log).unwrap();
    let mut handle = broker
        .serve_tcp_certified("127.0.0.1:0", host_rotator, shared_trust)
        .unwrap();
    let addr = handle.tcp_addr().expect("TCP endpoint").to_string();

    let client_signer =
        IdentitySigner::from(SshAgentSigner::connect_for_key(&sock_path, client_pub).unwrap());
    let (mut pub_c, verified_host) = Client::connect_tcp_certified_verified(
        &addr,
        client_signer.clone(),
        client_cert.clone(),
        &trust_store,
        Some("n-broker-east"),
    )
    .unwrap();
    assert_eq!(verified_host.principal, "n-broker-east");
    assert_eq!(verified_host.serial, 1);

    for i in 1..=4u64 {
        let (off, dup) = pub_c
            .publish(7, i, "/a/stream/cert", format!("v{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
    }
    assert_eq!(
        pub_c.publish(7, 2, "/a/stream/cert", b"v2").unwrap(),
        (1, true)
    );

    let mut sub = Client::connect_tcp_certified(
        &addr,
        client_signer,
        client_cert,
        &trust_store,
        Some("n-broker-east"),
    )
    .unwrap()
    .subscribe(2, "/a/stream/>")
    .unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (2, "/a/stream/cert".to_owned(), b"v3".to_vec())
    );
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (3, "/a/stream/cert".to_owned(), b"v4".to_vec())
    );

    drop(sub);
    drop(pub_c);
    handle.shutdown();
    agent.shutdown();
}

#[test]
fn live_host_rotation_ca_rollover_and_negative_controls() {
    let (_tmp, log) = log_path("rollover");
    let ca_v1 =
        CertificateAuthority::new(IdentityKeypair::generate(), "https://oidc.example.com").unwrap();
    let ca_v2 =
        CertificateAuthority::new(IdentityKeypair::generate(), "https://oidc.example.com").unwrap();
    let rogue_ca =
        CertificateAuthority::new(IdentityKeypair::generate(), "https://oidc.example.com").unwrap();

    let t0 = now_ms().saturating_sub(5_000);
    let t1 = t0 + 600_000;

    let host_1 = IdentityKeypair::generate();
    let host_cert_1 = ca_v1
        .issue(CertRole::Host, host_1.public(), "n-bus-01", 1, t0, t1)
        .unwrap();
    let rotator = HostCertRotator::new(host_1, host_cert_1).unwrap();

    let both_cas_store =
        CertTrustStore::new(vec![ca_v1.public(), ca_v2.public()], 3_600_000).unwrap();
    let server_trust = SharedCertTrust::new(both_cas_store.clone());

    let broker = Broker::open(&log).unwrap();
    let mut handle = broker
        .serve_tcp_certified("127.0.0.1:0", rotator.clone(), server_trust.clone())
        .unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    let client_v1_kp = IdentityKeypair::generate();
    let client_v1_cert = ca_v1
        .issue(
            CertRole::Client,
            client_v1_kp.public(),
            "a-worker-1",
            10,
            t0,
            t1,
        )
        .unwrap();
    let mut existing = Client::connect_tcp_certified(
        &addr,
        client_v1_kp.clone().into(),
        client_v1_cert.clone(),
        &both_cas_store,
        Some("n-bus-01"),
    )
    .unwrap();
    assert_eq!(
        existing.publish(1, 1, "/a/x", b"before").unwrap(),
        (0, false)
    );

    // Rotate host key + certificate live to ca_v2 without restarting listener!
    let host_2 = IdentityKeypair::generate();
    let host_cert_2 = ca_v2
        .issue(CertRole::Host, host_2.public(), "n-bus-01", 2, t0, t1)
        .unwrap();
    let cur = now_ms();
    assert_eq!(
        rotator
            .rotate(host_2, host_cert_2, cur + 60_000, cur)
            .unwrap(),
        2
    );

    // Existing TCP session keeps working, and new sessions verify generation-2 host cert!
    assert_eq!(
        existing.publish(1, 2, "/a/x", b"during").unwrap(),
        (1, false)
    );

    let client_v2_kp = IdentityKeypair::generate();
    let client_v2_cert = ca_v2
        .issue(
            CertRole::Client,
            client_v2_kp.public(),
            "a-worker-2",
            20,
            t0,
            t1,
        )
        .unwrap();
    let (mut fresh, verified_host) = Client::connect_tcp_certified_verified(
        &addr,
        client_v2_kp.clone().into(),
        client_v2_cert.clone(),
        &both_cas_store,
        Some("n-bus-01"),
    )
    .unwrap();
    assert_eq!(verified_host.serial, 2);
    assert_eq!(verified_host.ca_pub, ca_v2.public());
    assert_eq!(fresh.publish(2, 1, "/a/x", b"v2").unwrap(), (2, false));

    // Retire ca_v1 from the live broker trust store: ca_v1 client cert is now refused,
    // while ca_v2 client cert still connects!
    server_trust
        .rotate_trusted_cas(vec![ca_v2.public()])
        .unwrap();
    let addr_ret = addr.clone();
    let store_ret = both_cas_store.clone();
    expect_refused("retired CA client cert", move || {
        let mut c = Client::connect_tcp_certified(
            &addr_ret,
            client_v1_kp.into(),
            client_v1_cert,
            &store_ret,
            Some("n-bus-01"),
        )?;
        c.publish(3, 1, "/a/x", b"no").map(|_| ())
    });

    // Wrong expected host principal, rogue CA client, and plaintext TCP are all refused.
    let addr_wp = addr.clone();
    let store_wp = both_cas_store.clone();
    let c2_kp = client_v2_kp.clone();
    let c2_cert = client_v2_cert.clone();
    expect_refused("wrong expected host principal", move || {
        let _ = Client::connect_tcp_certified(
            &addr_wp,
            c2_kp.into(),
            c2_cert,
            &store_wp,
            Some("n-other-host"),
        )?;
        Ok(())
    });

    let rogue_kp = IdentityKeypair::generate();
    let rogue_cert = rogue_ca
        .issue(CertRole::Client, rogue_kp.public(), "a-rogue", 99, t0, t1)
        .unwrap();
    let addr_rg = addr.clone();
    let store_rg = both_cas_store;
    expect_refused("untrusted CA client cert", move || {
        let mut c = Client::connect_tcp_certified(
            &addr_rg,
            rogue_kp.into(),
            rogue_cert,
            &store_rg,
            Some("n-bus-01"),
        )?;
        c.publish(9, 1, "/a/x", b"no").map(|_| ())
    });

    let addr_pl = addr.clone();
    expect_refused("plaintext peer on certified endpoint", move || {
        let mut c = Client::connect_tcp(&addr_pl)?;
        c.publish(9, 1, "/a/x", b"no").map(|_| ())
    });

    handle.shutdown();
}

#[test]
fn guarded_cert_principal_binding_and_live_serial_revocation() {
    let (_tmp, log) = log_path("guarded_serial_rev");
    let rev_file = log.with_extension("rev");
    let _rev_cleanup = Cleanup::new(&[&rev_file]);

    let secret = b"cert-guarded-broker-secret-32byt";
    let ca = CertificateAuthority::new(IdentityKeypair::generate(), "ssh-ca://corp").unwrap();
    let t0 = now_ms().saturating_sub(5_000);
    let t1 = t0 + 600_000;

    let host_kp = IdentityKeypair::generate();
    let host_cert = ca
        .issue(CertRole::Host, host_kp.public(), "n-guarded", 1, t0, t1)
        .unwrap();
    let rotator = HostCertRotator::new(host_kp, host_cert).unwrap();
    let store = CertTrustStore::new(vec![ca.public()], 3_600_000).unwrap();
    let shared_trust = SharedCertTrust::new(store.clone());

    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let mut handle = broker
        .serve_tcp_certified("127.0.0.1:0", rotator, shared_trust)
        .unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    // Worker 1 holds certificate for `a-worker1` (serial 77).
    let w1_kp = IdentityKeypair::generate();
    let w1_cert = ca
        .issue(CertRole::Client, w1_kp.public(), "a-worker1", 77, t0, t1)
        .unwrap();

    let cap_w1 = mint(secret, "rw,p=a-worker1:/a/jobs/>").unwrap();
    let cap_w2 = mint(secret, "rw,p=a-worker2:/a/jobs/>").unwrap();
    let cap_obs = mint(secret, "ro:/a/>").unwrap();

    let mut c1 = Client::connect_tcp_certified(
        &addr,
        w1_kp.clone().into(),
        w1_cert.clone(),
        &store,
        Some("n-guarded"),
    )
    .unwrap();

    // Attaching a leaked capability minted for `a-worker2` over `a-worker1`'s certified
    // session MUST be refused (`ERR_UNAUTHORIZED`)!
    assert!(
        c1.attach(&cap_w2.filter, &cap_w2.tag).is_err(),
        "certified peer a-worker1 must not attach a grant bound to a-worker2"
    );

    // Attaching `a-worker1`'s own grant (`offset 0` = `/a/bind`) succeeds, publishes at
    // `offset 1`, and registers a last will (`offset 2` = `/a/will`).
    c1.attach(&cap_w1.filter, &cap_w1.tag).unwrap();
    let pid_w1 = producer_id_of("a-worker1");
    assert_eq!(
        c1.publish(pid_w1, 1, "/a/jobs/1", b"ok").unwrap(),
        (1, false)
    );
    c1.will(pid_w1, 2, "/a/jobs/dead", b"w1-died").unwrap();

    // Open a live subscriber on a second connection under serial 77.
    let mut sub_conn = Client::connect_tcp_certified(
        &addr,
        w1_kp.clone().into(),
        w1_cert.clone(),
        &store,
        Some("n-guarded"),
    )
    .unwrap();
    sub_conn.attach(&cap_w1.filter, &cap_w1.tag).unwrap();
    let mut sub = sub_conn.subscribe(0, "/a/jobs/>").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().0, 1);

    // Revoke serial 77 live on the broker: open stream terminates with an error, open
    // publisher is refused and its disconnecting will is suppressed, and new connects fail!
    assert!(broker.revoke_cert_serial(77));
    assert!(broker.is_cert_serial_revoked(77));

    let sub_after = sub.recv();
    assert!(
        sub_after.is_err(),
        "revoking certificate serial 77 must terminate open subscription, got {sub_after:?}"
    );
    assert!(
        c1.publish(pid_w1, 3, "/a/jobs/2", b"blocked").is_err(),
        "revoking certificate serial 77 must block open publisher"
    );
    drop(c1);

    // Verify `serial:<u64>` parsing in `load_revocation_file` and confirm `w1-died` will
    // was suppressed when `c1` dropped!
    std::fs::write(&rev_file, "# revoked cert serials\nserial:88\n").unwrap();
    assert_eq!(broker.load_revocation_file(&rev_file).unwrap(), 1);
    assert!(broker.is_cert_serial_revoked(88));

    let obs_kp = IdentityKeypair::generate();
    let obs_cert = ca
        .issue(CertRole::Client, obs_kp.public(), "h-auditor", 89, t0, t1)
        .unwrap();
    let mut obs =
        Client::connect_tcp_certified(&addr, obs_kp.into(), obs_cert, &store, Some("n-guarded"))
            .unwrap();
    obs.attach(&cap_obs.filter, &cap_obs.tag).unwrap();
    let (dead_rows, _) = obs.last("/a/jobs/dead", "", 16).unwrap();
    assert!(
        dead_rows.is_empty(),
        "revoked serial's pending last will must be suppressed on disconnect"
    );

    // Serial 88 from revocation file is refused at handshake/request.
    let w88_kp = IdentityKeypair::generate();
    let w88_cert = ca
        .issue(CertRole::Client, w88_kp.public(), "a-worker88", 88, t0, t1)
        .unwrap();
    let addr88 = addr.clone();
    let store88 = store;
    expect_refused("serial:88 from revocation file", move || {
        let mut c = Client::connect_tcp_certified(
            &addr88,
            w88_kp.into(),
            w88_cert,
            &store88,
            Some("n-guarded"),
        )?;
        c.publish(1, 1, "/a/jobs/x", b"x").map(|_| ())
    });

    handle.shutdown();
}

#[test]
fn replicated_tier_over_certified_follower_transport() {
    let (_tl, leader_log) = log_path("rep_leader");
    let (_tf1, f1_log) = log_path("rep_f1");
    let (_tf2, f2_log) = log_path("rep_f2");

    let ca = CertificateAuthority::new(IdentityKeypair::generate(), "ssh-ca://rep").unwrap();
    let t0 = now_ms().saturating_sub(5_000);
    let t1 = t0 + 600_000;
    let store = CertTrustStore::new(vec![ca.public()], 3_600_000).unwrap();
    let shared_trust = SharedCertTrust::new(store.clone());

    let f1_kp = IdentityKeypair::generate();
    let f1_cert = ca
        .issue(CertRole::Host, f1_kp.public(), "n-follower-1", 1, t0, t1)
        .unwrap();
    let f2_kp = IdentityKeypair::generate();
    let f2_cert = ca
        .issue(CertRole::Host, f2_kp.public(), "n-follower-2", 2, t0, t1)
        .unwrap();

    let f1 = Broker::open(&f1_log).unwrap();
    let mut f1_h = f1
        .serve_tcp_certified(
            "127.0.0.1:0",
            HostCertRotator::new(f1_kp, f1_cert).unwrap(),
            shared_trust.clone(),
        )
        .unwrap();
    let f1_addr = f1_h.tcp_addr().unwrap().to_string();

    let f2 = Broker::open(&f2_log).unwrap();
    let mut f2_h = f2
        .serve_tcp_certified(
            "127.0.0.1:0",
            HostCertRotator::new(f2_kp, f2_cert).unwrap(),
            shared_trust.clone(),
        )
        .unwrap();
    let f2_addr = f2_h.tcp_addr().unwrap().to_string();

    let leader_client_kp = IdentityKeypair::generate();
    let leader_client_cert = ca
        .issue(
            CertRole::Client,
            leader_client_kp.public(),
            "n-leader-rep",
            10,
            t0,
            t1,
        )
        .unwrap();
    let leader_host_kp = IdentityKeypair::generate();
    let leader_host_cert = ca
        .issue(
            CertRole::Host,
            leader_host_kp.public(),
            "n-leader-0",
            11,
            t0,
            t1,
        )
        .unwrap();

    let rep_transport = FollowerTransport::Certified {
        signer: leader_client_kp.into(),
        cert: leader_client_cert,
        trust: shared_trust.clone(),
        expected_principals: vec![
            Some("n-follower-1".to_owned()),
            Some("n-follower-2".to_owned()),
        ],
    };
    let leader = Broker::open_replicated_transport_with(
        &leader_log,
        &[f1_addr.clone(), f2_addr],
        rep_transport,
        1,
        Duration::from_secs(5),
    )
    .unwrap();
    let mut leader_h = leader
        .serve_tcp_certified(
            "127.0.0.1:0",
            HostCertRotator::new(leader_host_kp, leader_host_cert).unwrap(),
            shared_trust,
        )
        .unwrap();
    let leader_addr = leader_h.tcp_addr().unwrap().to_string();

    let prod_kp = IdentityKeypair::generate();
    let prod_cert = ca
        .issue(CertRole::Client, prod_kp.public(), "a-producer", 20, t0, t1)
        .unwrap();
    let mut prod = Client::connect_tcp_certified(
        &leader_addr,
        prod_kp.clone().into(),
        prod_cert.clone(),
        &store,
        Some("n-leader-0"),
    )
    .unwrap();
    assert_eq!(
        prod.publish(9, 1, "/a/rep/cert", b"quorum-ok").unwrap(),
        (0, false)
    );
    drop(prod);
    leader_h.shutdown();
    drop(leader);

    let mut reader = Client::connect_tcp_certified(
        &f1_addr,
        prod_kp.into(),
        prod_cert,
        &store,
        Some("n-follower-1"),
    )
    .unwrap();
    let (rows, _) = reader.fetch(0, "/a/rep/>", 16).unwrap();
    assert_eq!(
        rows,
        vec![(0, "/a/rep/cert".to_owned(), b"quorum-ok".to_vec())]
    );
    drop(reader);
    f1_h.shutdown();
    f2_h.shutdown();
}

#[cfg(unix)]
#[test]
fn cli_asb_serve_certified_with_ssh_agent_sock_and_guarded_caps() {
    use std::io::{BufRead, BufReader};
    use std::os::unix::fs::PermissionsExt;
    use std::process::{Command, Stdio};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("asb_cert_cli_{}_{n}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let _clean = Cleanup::new(&[&dir]);

    let agent_sock = std::path::PathBuf::from(format!("/tmp/asca_{}_{n}.s", std::process::id()));
    let _clean_sock = Cleanup::new(&[&agent_sock]);

    let ca_kp = IdentityKeypair::generate();
    let ca = CertificateAuthority::new(ca_kp, "https://ca.astream.cli").unwrap();
    let host_kp = IdentityKeypair::generate();
    let host_pub = host_kp.public();
    let t0 = now_ms().saturating_sub(5_000);
    let t1 = t0 + 600_000;
    let host_cert = ca
        .issue(CertRole::Host, host_pub, "n-cli-broker", 1, t0, t1)
        .unwrap();

    let agent =
        SshAgentServer::bind(&agent_sock, vec![(host_kp, "cli-host-key".to_owned())]).unwrap();

    let secret = b"cli-certified-mint-secret-0123456789abcdef";
    let secret_path = dir.join("mint.secret");
    std::fs::write(&secret_path, secret).unwrap();
    std::fs::set_permissions(&secret_path, std::fs::Permissions::from_mode(0o600)).unwrap();

    let cert_path = dir.join("host.acrt");
    std::fs::write(&cert_path, host_cert.encode()).unwrap();

    let mut ca_hex = String::with_capacity(64);
    for b in ca.public() {
        ca_hex.push_str(&format!("{b:02x}"));
    }
    ca_hex.push('\n');
    let ca_path = dir.join("ca.pub");
    std::fs::write(&ca_path, ca_hex.as_bytes()).unwrap();

    let log_path = dir.join("cli.log");

    // Negative CLI check: passing --host-cert on argv is refused with exit 2.
    let bad_argv = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "serve",
            log_path.to_str().unwrap(),
            "--host-cert",
            "deadbeef",
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(bad_argv.status.code(), Some(2));

    let mut child = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args([
            "serve",
            log_path.to_str().unwrap(),
            "--listen",
            "certified:127.0.0.1:0",
            "--ssh-agent-sock",
            agent_sock.to_str().unwrap(),
            "--host-cert-file",
            cert_path.to_str().unwrap(),
            "--ca-key-file",
            ca_path.to_str().unwrap(),
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

    let client_kp = IdentityKeypair::generate();
    let client_cert = ca
        .issue(
            CertRole::Client,
            client_kp.public(),
            "a-cli-worker",
            2,
            t0,
            t1,
        )
        .unwrap();
    let store = CertTrustStore::new(vec![ca.public()], 3_600_000).unwrap();

    let (mut c, verified) = Client::connect_tcp_certified_verified(
        &addr,
        client_kp.into(),
        client_cert,
        &store,
        Some("n-cli-broker"),
    )
    .unwrap();
    assert_eq!(verified.principal, "n-cli-broker");

    let cap_good = mint(secret, "rw,p=a-cli-worker:/a/cli/>").unwrap();
    let cap_wrong = mint(secret, "rw,p=a-impostor:/a/cli/>").unwrap();
    assert!(c.attach(&cap_wrong.filter, &cap_wrong.tag).is_err());
    c.attach(&cap_good.filter, &cap_good.tag).unwrap();

    let pid = producer_id_of("a-cli-worker");
    assert_eq!(
        c.publish(pid, 1, "/a/cli/msg", b"hello-cli-cert").unwrap(),
        (1, false)
    );
    let (rows, _) = c.fetch(0, "/a/cli/>", 16).unwrap();
    assert_eq!(
        rows,
        vec![(1, "/a/cli/msg".to_owned(), b"hello-cli-cert".to_vec())]
    );
    drop(c);
    drop(guard);
    agent.shutdown();
}
