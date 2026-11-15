// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for authenticated and encrypted cross-host `Replicated` follower links
//! ([`FollowerTransport`]: `Sealed`, `Handshake`, and `Identity` with per-follower
//! pinned Ed25519 host keys, capability `Attach`, revocation fencing, timeout backoff,
//! and divergent-follower recovery).

#[cfg(any(feature = "aead", feature = "handshake", feature = "identity"))]
mod encrypted {
    use astream_broker::{Broker, Client, Durability, FollowerTransport};
    use std::io::Read;
    use std::net::{TcpListener, TcpStream};
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::Arc;
    use std::thread::{self, JoinHandle};
    use std::time::Duration;

    static CTR: AtomicU64 = AtomicU64::new(0);

    struct Cleanup(Vec<PathBuf>);

    impl Cleanup {
        fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
            Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
        }
    }

    impl Drop for Cleanup {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
                let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
                    continue;
                };
                let prefix = format!("{}.", name.to_string_lossy());
                for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                    if entry.file_name().to_string_lossy().starts_with(&prefix) {
                        let _ = std::fs::remove_file(entry.path());
                    }
                }
            }
        }
    }

    fn log_paths(tag: &str, count: usize) -> (Cleanup, Vec<PathBuf>) {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let paths: Vec<PathBuf> = (0..count)
            .map(|i| std::env::temp_dir().join(format!("asrept_{tag}_{pid}_{n}_{i}.log")))
            .collect();
        for p in &paths {
            let _ = std::fs::remove_file(p);
        }
        (Cleanup::new(&paths), paths)
    }

    struct SilentPeer {
        addr: String,
        stop: Arc<AtomicBool>,
        acceptor: Option<JoinHandle<()>>,
    }

    impl SilentPeer {
        fn start() -> SilentPeer {
            let listener = TcpListener::bind("127.0.0.1:0").unwrap();
            let addr = listener.local_addr().unwrap().to_string();
            let stop = Arc::new(AtomicBool::new(false));
            let flag = stop.clone();
            let acceptor = thread::spawn(move || {
                while let Ok((mut s, _)) = listener.accept() {
                    if flag.load(Ordering::Relaxed) {
                        break;
                    }
                    thread::spawn(move || {
                        let mut sink = [0u8; 64];
                        while matches!(s.read(&mut sink), Ok(n) if n > 0) {}
                    });
                }
            });
            SilentPeer {
                addr,
                stop,
                acceptor: Some(acceptor),
            }
        }
    }

    impl Drop for SilentPeer {
        fn drop(&mut self) {
            if let Some(a) = self.acceptor.take() {
                self.stop.store(true, Ordering::Relaxed);
                let _ = TcpStream::connect(&self.addr);
                let _ = a.join();
            }
        }
    }

    #[cfg(feature = "aead")]
    #[test]
    fn sealed_follower_transport_replicates_quorum_and_rejects_wrong_key() {
        let (_tmp, paths) = log_paths("sealed", 4);
        let key = [0x42u8; 32];
        let wrong_key = [0x99u8; 32];

        let f1 = Broker::open_with(&paths[1], Durability::Relaxed).unwrap();
        let f2 = Broker::open_with(&paths[2], Durability::Relaxed).unwrap();
        let bad = Broker::open_with(&paths[3], Durability::Relaxed).unwrap();
        let h1 = f1.serve_tcp_sealed("127.0.0.1:0", key).unwrap();
        let h2 = f2.serve_tcp_sealed("127.0.0.1:0", key).unwrap();
        let h_bad = bad.serve_tcp_sealed("127.0.0.1:0", wrong_key).unwrap();
        let a1 = h1.tcp_addr().unwrap().to_string();
        let a2 = h2.tcp_addr().unwrap().to_string();
        let a_bad = h_bad.tcp_addr().unwrap().to_string();

        // Wrong-key follower alone fails cryptographic authentication immediately at open:
        let bad_leader_path = std::env::temp_dir().join(format!(
            "asrept_sealed_bad_{}_{}.log",
            std::process::id(),
            CTR.fetch_add(1, Ordering::Relaxed)
        ));
        let _tmp_bad = Cleanup::new(&[&bad_leader_path]);
        let bad_err = Broker::open_replicated_transport_with(
            &bad_leader_path,
            std::slice::from_ref(&a_bad),
            FollowerTransport::Sealed(key),
            1,
            Duration::from_millis(400),
        )
        .err()
        .expect("wrong-key sealed follower must fail quorum open");
        assert_eq!(bad_err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(bad.stats().visible_head, 0);

        // 2-follower quorum over Sealed(key) succeeds and replicates exact offsets + commits:
        let addrs = vec![a1.clone(), a2.clone()];
        let leader = Broker::open_replicated_transport_with(
            &paths[0],
            &addrs,
            FollowerTransport::Sealed(key),
            2,
            Duration::from_secs(5),
        )
        .unwrap();
        assert_eq!(
            format!("{:?}", FollowerTransport::Sealed(key)),
            "FollowerTransport::Sealed(<secret>)"
        );
        let hl = leader.serve_tcp("127.0.0.1:0").unwrap();
        let mut lc = Client::connect_tcp(hl.tcp_addr().unwrap()).unwrap();
        for i in 1..=5u64 {
            assert_eq!(
                lc.publish(7, i, "/r/item", format!("v{i}").as_bytes())
                    .unwrap(),
                (i - 1, false)
            );
        }
        assert_eq!(lc.commit("grp", 4).unwrap(), 5);
        assert_eq!(f1.stats().visible_head, 6);
        assert_eq!(f2.stats().visible_head, 6);

        let mut sub = Client::connect_tcp_sealed(&a1, key)
            .unwrap()
            .subscribe_group("grp", "/r/>")
            .unwrap();
        assert_eq!(lc.publish(7, 6, "/r/item", b"v6").unwrap(), (6, false));
        let (off, subj, body) = sub.recv().unwrap().unwrap();
        assert_eq!(
            (off, subj.as_str(), body.as_slice()),
            (6, "/r/item", b"v6".as_slice())
        );
    }

    #[cfg(all(feature = "handshake", feature = "cap"))]
    #[test]
    fn handshake_guarded_follower_transport_verifies_empty_log_and_survives_blackhole_and_restart()
    {
        use astream_broker::mint;
        let (_tmp, paths) = log_paths("hs", 4);
        let psk = [0x5Au8; 32];
        let wrong_psk = [0xA5u8; 32];
        let secret = b"replicated-handshake-cap-secret!";
        let repl_cap = mint(secret, "rw:/>").unwrap();

        // Even on an EMPTY leader log (`head == 0`), `Handshake` confirms the bidirectional
        // session at open time, so a wrong-PSK or plaintext follower is rejected before quorum!
        let f_wrong =
            Broker::open_guarded_with(&paths[3], secret.to_vec(), Durability::Relaxed).unwrap();
        let h_wrong = f_wrong
            .serve_tcp_handshake("127.0.0.1:0", wrong_psk)
            .unwrap();
        let a_wrong = h_wrong.tcp_addr().unwrap().to_string();
        let empty_leader_path = std::env::temp_dir().join(format!(
            "asrept_hs_empty_{}_{}.log",
            std::process::id(),
            CTR.fetch_add(1, Ordering::Relaxed)
        ));
        let _tmp_empty = Cleanup::new(&[&empty_leader_path]);
        let _hs_err = Broker::open_replicated_transport_with(
            &empty_leader_path,
            std::slice::from_ref(&a_wrong),
            FollowerTransport::Handshake(psk),
            1,
            Duration::from_millis(400),
        )
        .err()
        .expect("wrong-PSK handshake follower must fail quorum open even on empty log");
        // A rejected PSK can close the peer before a reply frame decodes. The open must
        // fail and leave the follower untouched; its incidental socket error is not a promise.
        assert_eq!(f_wrong.stats().visible_head, 0);

        // Now start 1 healthy guarded Handshake follower + 1 silent blackhole peer (quorum = 1):
        let f1 =
            Broker::open_guarded_with(&paths[1], secret.to_vec(), Durability::Relaxed).unwrap();
        let mut h1 = f1.serve_tcp_handshake("127.0.0.1:0", psk).unwrap();
        let a1 = h1.tcp_addr().unwrap().to_string();
        let silent = SilentPeer::start();
        let addrs = vec![a1.clone(), silent.addr.clone()];

        let leader = Broker::open_replicated_guarded_transport_with(
            &paths[0],
            secret.to_vec(),
            &addrs,
            FollowerTransport::Handshake(psk),
            repl_cap,
            1,
            Duration::from_millis(250),
        )
        .unwrap();
        let hl = leader.serve_tcp_handshake("127.0.0.1:0", psk).unwrap();
        let laddr = hl.tcp_addr().unwrap().to_string();
        let pub_cap = mint(secret, "rw,p=n-0102030405060708:/r/>").unwrap();
        let pid = astream_broker::producer_id_of("n-0102030405060708");

        let mut lc = Client::connect_tcp_handshake(&laddr, psk).unwrap();
        lc.attach(&pub_cap.filter, &pub_cap.tag).unwrap();
        // Offset 0 is `/a/bind`, offset 1..=3 are publishes; silent peer times out & backs off
        // while healthy follower `f1` satisfies quorum = 1:
        for seq in 1..=3u64 {
            let (_off, dup) = lc.publish(pid, seq, "/r/msg", b"payload").unwrap();
            assert!(!dup);
        }
        let head_after_3 = leader.stats().visible_head;
        assert_eq!(f1.stats().visible_head, head_after_3);

        // Restart `f1` on the same address: next publish reconnects over Handshake + Attach
        // and catches up seamlessly!
        h1.shutdown();
        drop(f1);
        let f1_re =
            Broker::open_guarded_with(&paths[1], secret.to_vec(), Durability::Relaxed).unwrap();
        let _h1_re = f1_re.serve_tcp_handshake(&a1, psk).unwrap();
        let (off4, dup4) = lc.publish(pid, 4, "/r/msg", b"after-restart").unwrap();
        assert!(!dup4);
        assert_eq!(f1_re.stats().visible_head, off4 + 1);
    }

    #[cfg(feature = "identity")]
    #[test]
    fn identity_follower_transport_pins_host_keys_enforces_revocation_and_recovers_diverged_replica(
    ) {
        use astream_broker::IdentityKeypair;
        let (_tmp, paths) = log_paths("id", 4);

        let leader_id = Arc::new(IdentityKeypair::generate());
        let leader_pub = leader_id.public();
        let f1_id = IdentityKeypair::generate();
        let f1_pub = f1_id.public();
        let f2_id = IdentityKeypair::generate();
        let f2_pub = f2_id.public();
        let impostor_id = IdentityKeypair::generate();

        // `expected_followers` length mismatch is rejected immediately with `InvalidInput`:
        let mismatch = Broker::open_replicated_transport(
            &paths[0],
            &["127.0.0.1:9".to_string()],
            FollowerTransport::Identity {
                identity: leader_id.clone(),
                expected_followers: vec![f1_pub, f2_pub],
            },
            1,
        );
        assert_eq!(
            mismatch.err().map(|e| e.kind()),
            Some(std::io::ErrorKind::InvalidInput)
        );

        // Follower 3 presents `impostor_id` while leader pins `f2_pub` -> MITM rejected!
        let f1 = Broker::open_with(&paths[1], Durability::Relaxed).unwrap();
        let mut h1 = f1
            .serve_tcp_identity("127.0.0.1:0", f1_id.clone(), vec![leader_pub])
            .unwrap();
        let a1 = h1.tcp_addr().unwrap().to_string();

        let f_mitm = Broker::open_with(&paths[3], Durability::Relaxed).unwrap();
        let h_mitm = f_mitm
            .serve_tcp_identity("127.0.0.1:0", impostor_id, vec![leader_pub])
            .unwrap();
        let a_mitm = h_mitm.tcp_addr().unwrap().to_string();

        let mitm_leader_path = std::env::temp_dir().join(format!(
            "asrept_id_mitm_{}_{}.log",
            std::process::id(),
            CTR.fetch_add(1, Ordering::Relaxed)
        ));
        let _tmp_mitm = Cleanup::new(&[&mitm_leader_path]);
        let mitm_err = Broker::open_replicated_transport_with(
            &mitm_leader_path,
            std::slice::from_ref(&a_mitm),
            FollowerTransport::Identity {
                identity: leader_id.clone(),
                expected_followers: vec![f2_pub],
            },
            1,
            Duration::from_millis(400),
        )
        .err()
        .expect("follower presenting unpinned Ed25519 host key must fail quorum open");
        assert_eq!(mitm_err.kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(f_mitm.stats().visible_head, 0);

        // Real 2-follower Identity cluster (quorum = 1 so we can fence/recover f2):
        let f2 = Broker::open_with(&paths[2], Durability::Relaxed).unwrap();
        let mut h2 = f2
            .serve_tcp_identity("127.0.0.1:0", f2_id.clone(), vec![leader_pub])
            .unwrap();
        let a2 = h2.tcp_addr().unwrap().to_string();

        let leader = Broker::open_replicated_transport_with(
            &paths[0],
            &[a1.clone(), a2.clone()],
            FollowerTransport::Identity {
                identity: leader_id.clone(),
                expected_followers: vec![f1_pub, f2_pub],
            },
            1,
            Duration::from_secs(5),
        )
        .unwrap();
        let hl = leader.serve_tcp("127.0.0.1:0").unwrap();
        let mut lc = Client::connect_tcp(hl.tcp_addr().unwrap()).unwrap();

        for i in 1..=3u64 {
            assert_eq!(lc.publish(10, i, "/id/ok", b"v").unwrap(), (i - 1, false));
        }
        assert_eq!(f1.stats().visible_head, 3);
        assert_eq!(f2.stats().visible_head, 3);

        // Live `revoke_identity(leader_pub)` on `f1` terminates and fences the replication
        // link with `ERR_UNAUTHORIZED`; when `f2` is also stopped, quorum writes fail until
        // `f1.unrevoke_identity(&leader_pub)` + `leader.rejoin_followers()` restores `f1`!
        assert!(f1.revoke_identity(leader_pub));
        h2.shutdown();
        drop(f2);
        assert!(
            lc.publish(10, 4, "/id/revoked", b"blocked").is_err(),
            "revoked leader identity on f1 + stopped f2 must refuse quorum"
        );
        assert!(f1.unrevoke_identity(&leader_pub));
        assert_eq!(leader.rejoin_followers().unwrap(), 1);
        // Retry `(10, 4)` is now already replicated by `rejoin_followers()` and acked deduped!
        assert_eq!(
            lc.publish(10, 4, "/id/revoked", b"blocked").unwrap(),
            (3, true)
        );
        assert_eq!(f1.stats().visible_head, 4);

        // Diverge `f2` offline at offset 3, restart `f2` on `a2`, watch `f2` fence on conflict,
        // then `truncate_replica_to(3)` + `rejoin_followers()` recovers `f2` over Identity!
        {
            let f2_div = Broker::open_with(&paths[2], Durability::Relaxed).unwrap();
            let h_div = f2_div.serve_tcp("127.0.0.1:0").unwrap();
            let mut dc = Client::connect_tcp(h_div.tcp_addr().unwrap()).unwrap();
            // Append a conflicting local record at offset 3 on `f2`:
            assert_eq!(
                dc.publish(999, 1, "/divergent/local", b"bad").unwrap(),
                (3, false)
            );
        }
        let f2_re = Broker::open_with(&paths[2], Durability::Relaxed).unwrap();
        let _h2_re = f2_re
            .serve_tcp_identity(&a2, f2_id, vec![leader_pub])
            .unwrap();

        // Publish offset 4: `f1` acks (quorum = 1), `f2_re` fences on offset 3 divergence!
        assert_eq!(lc.publish(10, 5, "/id/ok", b"v5").unwrap(), (4, false));
        assert_eq!(f1.stats().visible_head, 5);
        assert_eq!(f2_re.stats().visible_head, 4); // still holding divergent offset 3

        // Truncate `f2_re` back to common prefix `3` (drops 1 divergent record) and rejoin:
        assert_eq!(f2_re.truncate_replica_to(3).unwrap(), 1);
        assert_eq!(f2_re.head(), 3);
        assert_eq!(leader.rejoin_followers().unwrap(), 1);
        assert_eq!(f2_re.stats().visible_head, 5);

        // Shut down `f1` completely: `f2_re` alone now carries quorum = 1 over Identity!
        h1.shutdown();
        drop(f1);
        assert_eq!(lc.publish(10, 6, "/id/ok", b"v6").unwrap(), (5, false));
        assert_eq!(f2_re.stats().visible_head, 6);
    }
}
