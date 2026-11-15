// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `broker.federation`: cross-broker subtree mirroring (`FederationBridge`)
//! with durable consumer-group cursor recovery, deterministic `(producer_id, src_offset)`
//! crash-replay deduplication, bidirectional loop prevention (`SubjectRewrite`),
//! `LogIdentity` divergence detection, mutual Ed25519 + capability-guarded transport, and
//! Chandy-Lamport consistent cuts (`FederatedCut`) across independent broker logs.

#![cfg(unix)]

use astream_broker::{
    parse_federation_rules, Broker, Client, Durability, FederatedCut, FederationBridge,
    FederationConfig, FederationEndpoint, FederationError, FederationLink, FederationRunner,
    LogIdentity, SubjectRewrite, Transport,
};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

/// Receipt conversion, generation-qualified identities, and canonical persistence
/// must preserve a closure with a long reverse-ordered dependency chain.
#[test]
fn federated_cut_heals_a_reverse_receipt_chain_without_admitting_an_absent_generation() {
    const DEPTH: u64 = 64;
    let identity = |n: u64| LogIdentity {
        id: (u128::from(n) + 1).to_le_bytes(),
        generation: n % 3,
    };
    let link = |src_log, src_offset, dst_log, dst_offset| FederationLink {
        src_log,
        src_offset,
        dst_log,
        dst_offset,
        deduped: false,
        dst_subject: "/mirror/causal".to_string(),
    };
    let staged = identity(DEPTH + 1);
    let target = identity(DEPTH + 2);
    let mut links = vec![
        link(target, u64::MAX, staged, 1),
        link(staged, 1, identity(0), 0),
        link(target, 1, staged, 0),
        link(staged, 0, identity(1), 0),
    ];
    links.extend((0..DEPTH).map(|n| link(identity(n), 0, identity(n + 1), 0)));
    let dormant = identity(DEPTH + 3);
    let absent_generation = LogIdentity {
        generation: identity(DEPTH).generation + 1,
        ..identity(DEPTH)
    };
    links.push(link(dormant, 0, absent_generation, 0));

    let mut cut = FederatedCut::new();
    assert_eq!(cut.heal(&links), 0);
    assert!(cut.is_empty(), "absent offset zero is never admitted");
    cut.insert(identity(DEPTH), 0);
    assert_eq!(cut.heal(&links), DEPTH as usize + 4);
    assert_eq!(cut.len(), DEPTH as usize + 3);
    for n in 0..=DEPTH {
        assert_eq!(cut.frontier(&identity(n)), Some(0));
    }
    assert_eq!(cut.frontier(&staged), Some(1));
    assert_eq!(cut.frontier(&target), Some(u64::MAX));
    assert_eq!(cut.frontier(&absent_generation), None);
    assert_eq!(cut.frontier(&dormant), None);
    assert!(cut.is_consistent(&links));
    let mut persisted = FederatedCut::decode_text(&cut.encode_text()).unwrap();
    assert_eq!(persisted, cut);
    assert_eq!(persisted.heal(&links), 0);
    assert_eq!(persisted, cut);
}

static NEXT_FED: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str) -> Self {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT_FED.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asfd-{tag}-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Self(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch dir");
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }

    fn str_path(&self, name: &str) -> String {
        self.path(name).to_str().unwrap().to_string()
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn federation_bridge_mirrors_resumes_from_durable_group_and_deduplicates_crash_replay() {
    let s = Scratch::new("mirror");
    let b_src = Broker::open_with(s.path("src.log"), Durability::Relaxed).unwrap();
    let b_dst = Broker::open_with(s.path("dst.log"), Durability::Relaxed).unwrap();
    let sock_src = s.str_path("src.sock");
    let sock_dst = s.str_path("dst.sock");
    let _h_src = b_src.serve(&sock_src).unwrap();
    let _h_dst = b_dst.serve(&sock_dst).unwrap();

    let mut prod_a = Client::connect(&sock_src).unwrap();
    let (off0, _) = prod_a
        .publish(10, 1, "/f/pub/host-a/s1", b"hello-1")
        .unwrap();
    let (_off_noise, _) = prod_a.publish(10, 2, "/local/private", b"secret").unwrap();
    let (off2, _) = prod_a
        .publish(10, 3, "/f/pub/host-a/s2", b"hello-2")
        .unwrap();
    assert_eq!((off0, off2), (0, 2));

    let cfg = FederationConfig {
        source: FederationEndpoint::new(&sock_src, Transport::Unix),
        dest: FederationEndpoint::new(&sock_dst, Transport::Unix),
        group: "/g/fed/host-b".to_string(),
        filter: "/f/pub/host-a/>".to_string(),
        carry: Vec::new(),
        producer_id: 77_001,
        rewrite: SubjectRewrite::prefix_map("/f/pub/host-a", "/f/peer/host-a").unwrap(),
        relay: false,
    };

    {
        let mut bridge = FederationBridge::open(cfg.clone()).expect("open bridge #1");
        assert_ne!(bridge.source_identity().id, bridge.dest_identity().id);
        assert_eq!(bridge.cursor(), 0);

        let r1 = bridge.sync_once(64).expect("sync_once #1");
        assert_eq!(r1.fetched, 2);
        assert_eq!(r1.mirrored, 2);
        assert_eq!(r1.deduped, 0);
        assert_eq!(r1.committed_upto, Some(2));
        assert_eq!(r1.links.len(), 2);
        assert_eq!(r1.links[0].src_offset, 0);
        assert_eq!(r1.links[0].dst_offset, 0);
        assert_eq!(r1.links[0].dst_subject, "/f/peer/host-a/s1");
        assert_eq!(r1.links[1].src_offset, 2);
        assert_eq!(r1.links[1].dst_offset, 1);
        assert_eq!(r1.links[1].dst_subject, "/f/peer/host-a/s2");
    }

    // Verify destination broker holds only the 2 rewritten subjects.
    let mut dst_reader = Client::connect(&sock_dst).unwrap();
    let (on_dst, _) = dst_reader.fetch(0, "/>", 16).unwrap();
    assert_eq!(on_dst.len(), 2);
    assert_eq!(
        on_dst[0],
        (0, "/f/peer/host-a/s1".to_string(), b"hello-1".to_vec())
    );
    assert_eq!(
        on_dst[1],
        (1, "/f/peer/host-a/s2".to_string(), b"hello-2".to_vec())
    );

    // Simulate crash-before-commit on `s3` (source offset 4, after `/g/fed/host-b` commit at 3):
    // publish `s3` and `s4` on source, and pre-write `(producer_id = 77_001, seq = s3_off)` on dest!
    let (off_s3, _) = prod_a
        .publish(10, 4, "/f/pub/host-a/s3", b"hello-3")
        .unwrap();
    let (off_s4, _) = prod_a
        .publish(10, 5, "/f/pub/host-a/s4", b"hello-4")
        .unwrap();
    let (pre_dst_off, pre_dedup) = dst_reader
        .publish(77_001, off_s3, "/f/peer/host-a/s3", b"hello-3")
        .unwrap();
    assert!(!pre_dedup);
    assert_eq!(pre_dst_off, 2);

    // Reopen bridge from durable group cursor: skips offsets `0..=2` and replays `s3` + `s4`
    // with `s3` deduplicated (`deduped == 1`) so dest has ZERO duplicate records!
    let mut bridge2 = FederationBridge::open(cfg).expect("reopen bridge #2");
    assert_eq!(bridge2.cursor(), off_s3);
    let r2 = bridge2.sync_once(64).expect("sync_once #2");
    assert_eq!(r2.fetched, 2);
    assert_eq!(r2.mirrored, 2);
    assert_eq!(r2.deduped, 1);
    assert_eq!(r2.committed_upto, Some(off_s4));
    assert!(r2.links[0].deduped);
    assert_eq!(r2.links[0].dst_offset, 2);
    assert!(!r2.links[1].deduped);
    assert_eq!(r2.links[1].dst_offset, 3);

    let (all_dst, _) = dst_reader.fetch(0, "/>", 16).unwrap();
    assert_eq!(all_dst.len(), 4);
    assert_eq!(
        all_dst[2],
        (2, "/f/peer/host-a/s3".to_string(), b"hello-3".to_vec())
    );
    assert_eq!(
        all_dst[3],
        (3, "/f/peer/host-a/s4".to_string(), b"hello-4".to_vec())
    );
}

#[test]
fn bidirectional_federation_prevents_echo_loops_and_detects_source_log_divergence() {
    let s = Scratch::new("bidir");
    let b_a = Broker::open_with(s.path("a.log"), Durability::Relaxed).unwrap();
    let b_b = Broker::open_with(s.path("b.log"), Durability::Relaxed).unwrap();
    let sock_a = s.str_path("a.sock");
    let sock_b = s.str_path("b.sock");
    let mut h_a = b_a.serve(&sock_a).unwrap();
    let _h_b = b_b.serve(&sock_b).unwrap();

    // Unguarded self-federation onto the same broker must fail closed.
    let self_cfg = FederationConfig {
        source: FederationEndpoint::new(&sock_a, Transport::Unix),
        dest: FederationEndpoint::new(&sock_a, Transport::Unix),
        group: "/g/fed/self".to_string(),
        filter: "/bus/>".to_string(),
        carry: Vec::new(),
        producer_id: 1,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    };
    assert!(matches!(
        FederationBridge::open(self_cfg),
        Err(FederationError::Config(_))
    ));

    // Bidirectional Host A <-> Host B mirroring `/bus/>`:
    // A -> B maps `/bus/origin-a/*` -> `/bus/peer-a/*` and excludes `/bus/peer-b`
    // B -> A maps `/bus/origin-b/*` -> `/bus/peer-b/*` and excludes `/bus/peer-a`
    let mut bridge_ab = FederationBridge::open(FederationConfig {
        source: FederationEndpoint::new(&sock_a, Transport::Unix),
        dest: FederationEndpoint::new(&sock_b, Transport::Unix),
        group: "/g/fed/to-b".to_string(),
        filter: "/bus/>".to_string(),
        carry: Vec::new(),
        producer_id: 501,
        rewrite: SubjectRewrite::prefix_map("/bus/origin-a", "/bus/peer-a")
            .unwrap()
            .with_excluded_prefix("/bus/peer-b")
            .unwrap(),
        relay: false,
    })
    .unwrap();

    let mut bridge_ba = FederationBridge::open(FederationConfig {
        source: FederationEndpoint::new(&sock_b, Transport::Unix),
        dest: FederationEndpoint::new(&sock_a, Transport::Unix),
        group: "/g/fed/to-a".to_string(),
        filter: "/bus/>".to_string(),
        carry: Vec::new(),
        producer_id: 502,
        rewrite: SubjectRewrite::prefix_map("/bus/origin-b", "/bus/peer-b")
            .unwrap()
            .with_excluded_prefix("/bus/peer-a")
            .unwrap(),
        relay: false,
    })
    .unwrap();

    let mut ca = Client::connect(&sock_a).unwrap();
    let mut cb = Client::connect(&sock_b).unwrap();
    ca.publish(1, 1, "/bus/origin-a/ping", b"from-a").unwrap();
    cb.publish(2, 1, "/bus/origin-b/pong", b"from-b").unwrap();

    // Run multiple alternating sync rounds: neither bridge ever echoes peer traffic back!
    let ab1 = bridge_ab.sync_once(64).unwrap();
    assert_eq!((ab1.mirrored, ab1.skipped), (1, 0));
    let ba1 = bridge_ba.sync_once(64).unwrap();
    assert_eq!((ba1.mirrored, ba1.skipped), (1, 1)); // `/bus/peer-a/ping` excluded!
    let ab2 = bridge_ab.sync_once(64).unwrap();
    assert_eq!((ab2.mirrored, ab2.skipped), (0, 1)); // `/bus/peer-b/pong` excluded!
    let ba2 = bridge_ba.sync_once(64).unwrap();
    assert_eq!((ba2.fetched, ba2.mirrored), (0, 0));

    assert_eq!(ca.fetch(0, "/bus/>", 16).unwrap().0.len(), 2);
    assert_eq!(cb.fetch(0, "/bus/>", 16).unwrap().0.len(), 2);

    // Replace Host A's log with a brand-new unrelated log at the same socket: `bridge_ab.reconnect()`
    // MUST fail closed with `FederationError::SourceLogDiverged`!
    h_a.shutdown();
    drop(b_a);
    std::fs::remove_file(s.path("a.log")).unwrap();
    let b_a_replaced = Broker::open_with(s.path("a.log"), Durability::Relaxed).unwrap();
    let _h_a2 = b_a_replaced.serve(&sock_a).unwrap();

    let err = bridge_ab
        .reconnect()
        .expect_err("replaced source broker log must fail closed");
    assert!(
        matches!(err, FederationError::SourceLogDiverged { .. }),
        "expected SourceLogDiverged, got {err:?}"
    );
}

#[cfg(all(feature = "identity", feature = "cap"))]
#[test]
fn federation_bridge_authenticates_over_mutual_ed25519_identity_and_guarded_capabilities() {
    use astream_aead::IdentityKeypair;
    use astream_broker::identity_principal;
    use astream_cap::{mint, producer_id_of};
    use std::sync::Arc;

    const SRC_SECRET: &[u8] = b"fed-src-guarded-secret-0123456789abcdef";
    const DST_SECRET: &[u8] = b"fed-dst-guarded-secret-fedcba9876543210";

    let s = Scratch::new("idcap");
    let src_id = IdentityKeypair::from_seed([0x11; 32]);
    let dst_id = IdentityKeypair::from_seed([0x22; 32]);
    let bridge_id = Arc::new(IdentityKeypair::from_seed([0x33; 32]));
    let src_pub = src_id.public();
    let dst_pub = dst_id.public();
    let bridge_pub = bridge_id.public();

    let b_src =
        Broker::open_guarded_with(s.path("src.log"), SRC_SECRET.to_vec(), Durability::Relaxed)
            .unwrap();
    let b_dst =
        Broker::open_guarded_with(s.path("dst.log"), DST_SECRET.to_vec(), Durability::Relaxed)
            .unwrap();
    let h_src = b_src
        .serve_tcp_identity("127.0.0.1:0", src_id, vec![bridge_pub])
        .unwrap();
    let h_dst = b_dst
        .serve_tcp_identity("127.0.0.1:0", dst_id, vec![bridge_pub])
        .unwrap();
    let src_addr = h_src.tcp_addr().unwrap().to_string();
    let dst_addr = h_dst.tcp_addr().unwrap().to_string();

    // Seed a record on guarded `b_src` over a local Unix admin socket.
    let src_sock = s.str_path("src.sock");
    let _hu_src = b_src.serve(&src_sock).unwrap();
    let dst_sock = s.str_path("dst.sock");
    let _hu_dst = b_dst.serve(&dst_sock).unwrap();

    let admin_src = mint(SRC_SECRET, "rw:/>").unwrap();
    let mut c_src = Client::connect(&src_sock).unwrap();
    c_src.attach(&admin_src.filter, &admin_src.tag).unwrap();
    c_src
        .publish(1, 1, "/f/wan/events/e1", b"encrypted-wan-event")
        .unwrap();

    // Least-privilege capabilities for the bridge:
    // - On source: `ro` on `/f/wan/>` + `rw,p=<bridge_principal>` on `/g/fed/wan`.
    // - On dest: principal-bound `rw,p=<bridge_principal>:/f/wan/>` matching `bridge_id`'s Ed25519 key!
    // First, verify a mismatched principal is refused fail-closed on the mutual-Ed25519 link:
    let src_ro = mint(SRC_SECRET, "ro:/f/wan/>").unwrap();
    let bridge_principal = identity_principal(&bridge_pub);
    let src_grp = mint(SRC_SECRET, &format!("rw,p={bridge_principal}:/g/fed/wan")).unwrap();
    let wrong_dst_rw = mint(DST_SECRET, "rw,p=n-fed0000000000001:/f/wan/>").unwrap();
    assert!(
        FederationBridge::open(FederationConfig {
            source: FederationEndpoint::identity(&src_addr, Arc::clone(&bridge_id), src_pub)
                .with_caps(vec![src_ro.clone(), src_grp.clone()]),
            dest: FederationEndpoint::identity(&dst_addr, Arc::clone(&bridge_id), dst_pub)
                .with_caps(vec![wrong_dst_rw]),
            group: "/g/fed/wan".to_string(),
            filter: "/f/wan/>".to_string(),
            carry: Vec::new(),
            producer_id: producer_id_of("n-fed0000000000001"),
            rewrite: SubjectRewrite::passthrough(),
            relay: false,
        })
        .is_err(),
        "mismatched capability principal over Ed25519 identity transport must fail closed"
    );

    let dst_rw = mint(DST_SECRET, &format!("rw,p={bridge_principal}:/f/wan/>")).unwrap();
    let dst_pid = producer_id_of(&bridge_principal);

    let mut bridge = FederationBridge::open(FederationConfig {
        source: FederationEndpoint::identity(&src_addr, Arc::clone(&bridge_id), src_pub)
            .with_caps(vec![src_ro, src_grp]),
        dest: FederationEndpoint::identity(&dst_addr, Arc::clone(&bridge_id), dst_pub)
            .with_caps(vec![dst_rw]),
        group: "/g/fed/wan".to_string(),
        filter: "/f/wan/>".to_string(),
        carry: Vec::new(),
        producer_id: dst_pid,
        rewrite: SubjectRewrite::passthrough(),
        relay: false,
    })
    .expect("open mutual-Ed25519 + capability-guarded bridge");

    let rep = bridge.sync_once(32).expect("sync_once over identity+cap");
    assert_eq!(rep.mirrored, 1);

    let admin_dst = mint(DST_SECRET, "ro:/>").unwrap();
    let mut c_dst = Client::connect(&dst_sock).unwrap();
    c_dst.attach(&admin_dst.filter, &admin_dst.tag).unwrap();
    let (got, _) = c_dst.fetch(0, "/f/wan/>", 8).unwrap();
    assert_eq!(
        got,
        vec![(
            1, // offset 0 on guarded b_dst is the hidden `/a/bind` record for `n-fed0000000000001`!
            "/f/wan/events/e1".to_string(),
            b"encrypted-wan-event".to_vec()
        )]
    );
}

#[test]
fn federated_cut_checks_chandy_lamport_consistency_heals_transitive_chains_and_persists_text() {
    let s = Scratch::new("cut");
    let b_a = Broker::open_with(s.path("a.log"), Durability::Relaxed).unwrap();
    let b_b = Broker::open_with(s.path("b.log"), Durability::Relaxed).unwrap();
    let b_c = Broker::open_with(s.path("c.log"), Durability::Relaxed).unwrap();
    let sa = s.str_path("a.sock");
    let sb = s.str_path("b.sock");
    let sc = s.str_path("c.sock");
    let _ha = b_a.serve(&sa).unwrap();
    let _hb = b_b.serve(&sb).unwrap();
    let _hc = b_c.serve(&sc).unwrap();

    // Seed noise on A and B so causal offsets differ across all 3 brokers (`A@2 -> B@1 -> C@0`).
    let mut ca = Client::connect(&sa).unwrap();
    ca.publish(1, 1, "/noise/1", b"n").unwrap();
    ca.publish(1, 2, "/noise/2", b"n").unwrap();
    let (a_cause_off, _) = ca.publish(1, 3, "/hop1/cmd", b"plan").unwrap();
    assert_eq!(a_cause_off, 2);

    let mut cb = Client::connect(&sb).unwrap();
    cb.publish(2, 1, "/noise/b0", b"n").unwrap();

    let mut bridge_ab = FederationBridge::open(FederationConfig {
        source: FederationEndpoint::new(&sa, Transport::Unix),
        dest: FederationEndpoint::new(&sb, Transport::Unix),
        group: "/g/ab".to_string(),
        filter: "/hop1/>".to_string(),
        carry: Vec::new(),
        producer_id: 901,
        rewrite: SubjectRewrite::prefix_map("/hop1", "/hop2").unwrap(),
        relay: false,
    })
    .unwrap();
    let rep_ab = bridge_ab.sync_once(16).unwrap();
    assert_eq!(rep_ab.links.len(), 1);
    assert_eq!(rep_ab.links[0].src_offset, 2);
    assert_eq!(rep_ab.links[0].dst_offset, 1);

    let mut bridge_bc = FederationBridge::open(FederationConfig {
        source: FederationEndpoint::new(&sb, Transport::Unix),
        dest: FederationEndpoint::new(&sc, Transport::Unix),
        group: "/g/bc".to_string(),
        filter: "/hop2/>".to_string(),
        carry: Vec::new(),
        producer_id: 902,
        rewrite: SubjectRewrite::prefix_map("/hop2", "/hop3").unwrap(),
        relay: false,
    })
    .unwrap();
    let rep_bc = bridge_bc.sync_once(16).unwrap();
    assert_eq!(rep_bc.links.len(), 1);
    assert_eq!(rep_bc.links[0].src_offset, 1);
    assert_eq!(rep_bc.links[0].dst_offset, 0);

    let log_a = bridge_ab.source_identity();
    let log_b = bridge_ab.dest_identity();
    let log_c = bridge_bc.dest_identity();
    let mut all_links = rep_ab.links;
    all_links.extend(rep_bc.links);

    // Cut admitting `C@0` while `B` and `A` are absent violates Chandy-Lamport consistency!
    let mut cut = FederatedCut::new();
    cut.insert(log_c, 0);
    assert!(!cut.is_consistent(&all_links));
    let v = cut.first_violation(&all_links).expect("violation witness");
    assert_eq!(v.edge.cause.0, log_b);
    assert_eq!(v.edge.cause.1 .0, 1);
    assert_eq!(v.edge.effect.0, log_c);

    // `heal` closes the 2-hop transitive chain (`C@0 -> B@1 -> A@2`) in 1 call!
    let repairs = cut.heal(&all_links);
    assert_eq!(repairs, 2);
    assert!(cut.is_consistent(&all_links));
    assert_eq!(cut.frontier(&log_a), Some(2));
    assert_eq!(cut.frontier(&log_b), Some(1));
    assert_eq!(cut.frontier(&log_c), Some(0));

    // Lattice join/meet + deterministic canonical text persistence.
    let mut earlier = FederatedCut::new();
    earlier.insert(log_a, 2);
    assert!(earlier.is_consistent(&all_links));
    assert!(cut.dominates(&earlier));
    let joined = earlier.join(&cut);
    assert_eq!(joined, cut);
    let met = earlier.meet(&cut);
    assert!(met.is_consistent(&all_links));
    assert_eq!(met.frontier(&log_a), Some(2));
    assert_eq!(met.frontier(&log_b), None);

    let encoded = cut.encode_text();
    let decoded = FederatedCut::decode_text(&encoded).expect("decode_text round-trip");
    assert_eq!(decoded, cut);

    let dup_text = format!("{encoded}{log_a}=5\n");
    assert!(FederatedCut::decode_text(&dup_text).is_err());
    assert!(FederatedCut::decode_text("not-a-log-id=3\n").is_err());
}

#[test]
fn declarative_federation_rules_and_runner_coordinate_multi_subtree_fabric_mirroring() {
    let rules_text = "
        # Multi-subtree aterm fabric federation topology
        group=/g/fed/term  filter=/f/F/term/>  rewrite=/f/F=>/f/peer/host-a exclude=/f/F/term/private batch=64
        group=/g/fed/inbox filter=/f/F/inbox/> rewrite=passthrough          id=8802 hops=0/1
    ";
    let rules = parse_federation_rules(rules_text).expect("valid federation rules");
    assert_eq!(rules.len(), 2);
    assert_eq!(rules[0].group, "/g/fed/term");
    assert_eq!(rules[0].batch_size, 64);
    assert_eq!(rules[0].producer_id, None);
    assert_eq!(rules[1].group, "/g/fed/inbox");
    assert_eq!(rules[1].producer_id, Some(8802));

    // Fail-closed grammar & duplicate-group checks.
    assert!(parse_federation_rules("# comments only\n\n").is_err());
    assert!(
        parse_federation_rules("group=/g/dup filter=/a/>\ngroup=/g/dup filter=/b/>\n").is_err()
    );
    assert!(parse_federation_rules("group=/a/commit filter=/a/>\n").is_err());
    assert!(parse_federation_rules("group=/g/ok filter=/a/> unknown=1\n").is_err());

    let s = Scratch::new("runner");
    let b_src = Broker::open_with(s.path("src.log"), Durability::Relaxed).unwrap();
    let b_dst = Broker::open_with(s.path("dst.log"), Durability::Relaxed).unwrap();
    let src_sock = s.str_path("src.sock");
    let dst_sock = s.str_path("dst.sock");
    let _hs = b_src.serve(&src_sock).unwrap();
    let _hd = b_dst.serve(&dst_sock).unwrap();

    let mut c_src = Client::connect(&src_sock).unwrap();
    c_src
        .publish(10, 1, "/f/F/term/s-1/out", b"pane-1")
        .unwrap();
    c_src
        .publish(10, 2, "/f/F/term/private/secret", b"skip-me")
        .unwrap();
    c_src
        .publish(10, 3, "/f/F/inbox/n-b/msg", b"hello-peer")
        .unwrap();

    let mut runner = FederationRunner::open(
        FederationEndpoint::new(&src_sock, Transport::Unix),
        FederationEndpoint::new(&dst_sock, Transport::Unix),
        8801,
        rules,
    )
    .expect("open multi-rule FederationRunner");
    assert_eq!(runner.rule_count(), 2);

    let reports = runner
        .drain_until_caught_up(16)
        .expect("drain_until_caught_up");
    assert_eq!(reports.len(), 2);
    assert_eq!(reports[0].0, "/g/fed/term");
    assert_eq!(reports[0].1.fetched, 2);
    assert_eq!(reports[0].1.mirrored, 1);
    assert_eq!(reports[0].1.skipped, 1);
    assert_eq!(reports[1].0, "/g/fed/inbox");
    assert_eq!(reports[1].1.fetched, 1);
    assert_eq!(reports[1].1.mirrored, 1);

    let mut cut = FederatedCut::new();
    runner.record_into_cut(&reports, &mut cut);
    let mut all_links = reports[0].1.links.clone();
    all_links.extend(reports[1].1.links.clone());
    assert!(cut.is_consistent(&all_links));

    let mut c_dst = Client::connect(&dst_sock).unwrap();
    let (dst_recs, _) = c_dst.fetch(0, "/>", 16).unwrap();
    assert_eq!(
        dst_recs,
        vec![
            (
                0,
                "/f/peer/host-a/term/s-1/out".to_string(),
                b"pane-1".to_vec()
            ),
            (1, "/f/F/inbox/n-b/msg".to_string(), b"hello-peer".to_vec()),
        ]
    );

    let closer = runner.closer();
    assert!(!closer.is_closed());
    closer.close();
    assert!(runner.is_stopped());
}

#[test]
fn asb_federate_cli_mirrors_rules_file_persists_cut_and_refuses_argv_secrets() {
    use std::process::Command;

    let asb = env!("CARGO_BIN_EXE_asb");
    let s = Scratch::new("cli");
    let b_src = Broker::open_with(s.path("src.log"), Durability::Relaxed).unwrap();
    let b_dst = Broker::open_with(s.path("dst.log"), Durability::Relaxed).unwrap();
    let src_sock = s.str_path("src.sock");
    let dst_sock = s.str_path("dst.sock");
    let _hs = b_src.serve(&src_sock).unwrap();
    let _hd = b_dst.serve(&dst_sock).unwrap();

    let mut c_src = Client::connect(&src_sock).unwrap();
    c_src
        .publish(1, 1, "/f/F/term/s-9/out", b"cli-out")
        .unwrap();
    c_src.publish(1, 2, "/f/F/state/s-9", b"running").unwrap();

    let rules_path = s.path("fed.rules");
    std::fs::write(
        &rules_path,
        "group=/g/cli/term filter=/f/F/term/> rewrite=/f/F=>/f/remote\n\
         group=/g/cli/state filter=/f/F/state/> rewrite=passthrough\n",
    )
    .unwrap();
    let cut_path = s.path("fed.cut");

    // 1. Missing stable producer id exits 2 with nothing mirrored.
    let missing_id = Command::new(asb)
        .args([
            "federate",
            &src_sock,
            &dst_sock,
            "--rules-file",
            rules_path.to_str().unwrap(),
            "--once",
        ])
        .output()
        .unwrap();
    assert_eq!(missing_id.status.code(), Some(2));

    // 2. `--dst-key` secret on argv is refused with exit 2.
    let bad_secret = Command::new(asb)
        .args([
            "federate",
            &src_sock,
            &dst_sock,
            "--group",
            "/g/cli/term",
            "--filter",
            "/f/F/>",
            "--id",
            "77",
            "--once",
            "--dst-key=0000000000000000000000000000000000000000000000000000000000000000",
        ])
        .output()
        .unwrap();
    assert_eq!(bad_secret.status.code(), Some(2));

    // 3. One-shot multi-rule federation mirrors both subtrees and writes Chandy-Lamport cut file!
    let run1 = Command::new(asb)
        .args([
            "federate",
            &src_sock,
            &dst_sock,
            "--rules-file",
            rules_path.to_str().unwrap(),
            "--id",
            "5501",
            "--once",
            "--cut-file",
            cut_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(
        run1.status.code(),
        Some(0),
        "stderr={}",
        String::from_utf8_lossy(&run1.stderr)
    );
    let stdout1 = String::from_utf8(run1.stdout).unwrap();
    assert!(
        stdout1.contains("federated group=/g/cli/term fetched=1 mirrored=1 deduped=0 skipped=0"),
        "{stdout1}"
    );
    assert!(
        stdout1.contains("federated group=/g/cli/state fetched=1 mirrored=1 deduped=0 skipped=0"),
        "{stdout1}"
    );

    let cut_text = std::fs::read_to_string(&cut_path).unwrap();
    let decoded_cut = FederatedCut::decode_text(&cut_text).expect("valid persisted FederatedCut");
    assert_eq!(decoded_cut.len(), 2);

    // 4. Re-running `asb federate --once` resumes from durable group cursors (`fetched=0`).
    let run2 = Command::new(asb)
        .args([
            "federate",
            &src_sock,
            &dst_sock,
            "--rules-file",
            rules_path.to_str().unwrap(),
            "--id",
            "5501",
            "--once",
            "--cut-file",
            cut_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(run2.status.code(), Some(0));
    let stdout2 = String::from_utf8(run2.stdout).unwrap();
    assert!(
        stdout2.contains("federated group=/g/cli/term fetched=0 mirrored=0"),
        "{stdout2}"
    );

    let mut c_dst = Client::connect(&dst_sock).unwrap();
    let (dst_recs, _) = c_dst.fetch(0, "/>", 16).unwrap();
    assert_eq!(
        dst_recs,
        vec![
            (0, "/f/remote/term/s-9/out".to_string(), b"cli-out".to_vec()),
            (1, "/f/F/state/s-9".to_string(), b"running".to_vec()),
        ]
    );
}

#[cfg(feature = "cap")]
#[test]
fn asb_federate_cli_derives_bound_producer_id_across_distinct_guarded_brokers() {
    use astream_cap::{capfile, mint};
    use std::process::Command;

    const SRC_SEC: &[u8] = b"asb-fed-src-secret-0123456789abcdef";
    const DST_SEC: &[u8] = b"asb-fed-dst-secret-fedcba9876543210";

    let asb = env!("CARGO_BIN_EXE_asb");
    let s = Scratch::new("clicap");
    let b_src = Broker::open_guarded_with(s.path("src.log"), SRC_SEC.to_vec(), Durability::Relaxed)
        .unwrap();
    let b_dst = Broker::open_guarded_with(s.path("dst.log"), DST_SEC.to_vec(), Durability::Relaxed)
        .unwrap();
    let h_src = b_src.serve_tcp("127.0.0.1:0").unwrap();
    let h_dst = b_dst.serve_tcp("127.0.0.1:0").unwrap();
    let src_addr = h_src.tcp_addr().unwrap().to_string();
    let dst_addr = h_dst.tcp_addr().unwrap().to_string();

    let admin_src = mint(SRC_SEC, "rw:/>").unwrap();
    let mut c_src = Client::connect_tcp(&src_addr).unwrap();
    c_src.attach(&admin_src.filter, &admin_src.tag).unwrap();
    c_src
        .publish(1, 1, "/f/guarded/inbox/m1", b"guarded-payload")
        .unwrap();

    let src_ro = mint(SRC_SEC, "ro:/f/guarded/>").unwrap();
    let src_grp = mint(SRC_SEC, "rw,p=n-fedsrc01:/g/fed/guarded").unwrap();
    let src_cap_path = s.path("src.cap");
    std::fs::write(
        &src_cap_path,
        format!(
            "{}\n{}\n",
            capfile::format_line(&src_ro.filter, &src_ro.tag),
            capfile::format_line(&src_grp.filter, &src_grp.tag),
        ),
    )
    .unwrap();

    // Destination grant binds `n-feddst01`, so `asb federate` derives `producer_id` automatically!
    let dst_rw = mint(DST_SEC, "rw,p=n-feddst01:/f/guarded/>").unwrap();
    let dst_cap_path = s.path("dst.cap");
    std::fs::write(
        &dst_cap_path,
        format!("{}\n", capfile::format_line(&dst_rw.filter, &dst_rw.tag)),
    )
    .unwrap();

    let out = Command::new(asb)
        .args([
            "federate",
            &src_addr,
            &dst_addr,
            "--tcp",
            "--group",
            "/g/fed/guarded",
            "--filter",
            "/f/guarded/>",
            "--cap-file",
            src_cap_path.to_str().unwrap(),
            "--dst-cap-file",
            dst_cap_path.to_str().unwrap(),
            "--once",
        ])
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(0),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        String::from_utf8_lossy(&out.stdout).contains("mirrored=1"),
        "{}",
        String::from_utf8_lossy(&out.stdout)
    );

    let admin_dst = mint(DST_SEC, "ro:/>").unwrap();
    let mut c_dst = Client::connect_tcp(&dst_addr).unwrap();
    c_dst.attach(&admin_dst.filter, &admin_dst.tag).unwrap();
    let (got, _) = c_dst.fetch(0, "/f/guarded/>", 8).unwrap();
    assert_eq!(got.len(), 1);
    assert_eq!(got[0].1, "/f/guarded/inbox/m1");
    assert_eq!(got[0].2, b"guarded-payload");
}

#[test]
fn dynamic_peer_discovery_and_multi_region_mesh_route_and_fail_over_cleanly() {
    use astream_broker::{
        FederationDirectory, FederationMesh, FederationMeshConfig, PeerAdvertisement,
        PeerHealthState, PeerTransportKind, DEFAULT_PEER_REGISTRY_PREFIX,
    };
    let s = Scratch::new("mesh");
    let b_seed = Broker::open_with(s.path("seed.log"), Durability::Relaxed).unwrap();
    let b_west = Broker::open_with(s.path("west.log"), Durability::Relaxed).unwrap();
    let b_east1 = Broker::open_with(s.path("east1.log"), Durability::Relaxed).unwrap();
    let b_east2 = Broker::open_with(s.path("east2.log"), Durability::Relaxed).unwrap();
    let b_eu = Broker::open_with(s.path("eu.log"), Durability::Relaxed).unwrap();

    let seed_sock = s.str_path("seed.sock");
    let west_sock = s.str_path("west.sock");
    let east1_sock = s.str_path("east1.sock");
    let east2_sock = s.str_path("east2.sock");
    let eu_sock = s.str_path("eu.sock");

    let _h_seed = b_seed.serve(&seed_sock).unwrap();
    let _h_west = b_west.serve(&west_sock).unwrap();
    let _h_east1 = b_east1.serve(&east1_sock).unwrap();
    let _h_east2 = b_east2.serve(&east2_sock).unwrap();
    let _h_eu = b_eu.serve(&eu_sock).unwrap();

    let seed_ep = FederationEndpoint::new(&seed_sock, Transport::Unix);
    let west_ep = FederationEndpoint::new(&west_sock, Transport::Unix);

    // Advertise two gateways in `us-east` (`us-east-a` wins deterministic tie-break or faster RTT)
    // and one gateway in `eu-west` onto the seed registry broker.
    let ad_east1 = PeerAdvertisement::new(
        "us-east-a",
        "us-east",
        &east1_sock,
        PeerTransportKind::Unix,
        1,
        PeerHealthState::Alive,
        vec!["/f/us-east".to_string()],
    )
    .unwrap();
    let ad_east2 = PeerAdvertisement::new(
        "us-east-b",
        "us-east",
        &east2_sock,
        PeerTransportKind::Unix,
        1,
        PeerHealthState::Alive,
        vec!["/f/us-east".to_string()],
    )
    .unwrap();
    let ad_eu = PeerAdvertisement::new(
        "eu-west-a",
        "eu-west",
        &eu_sock,
        PeerTransportKind::Unix,
        1,
        PeerHealthState::Alive,
        vec!["/f/eu-west".to_string()],
    )
    .unwrap();

    FederationDirectory::publish_advertisement(
        &seed_ep,
        DEFAULT_PEER_REGISTRY_PREFIX,
        701,
        1,
        &ad_east1,
    )
    .unwrap();
    FederationDirectory::publish_advertisement(
        &seed_ep,
        DEFAULT_PEER_REGISTRY_PREFIX,
        702,
        1,
        &ad_east2,
    )
    .unwrap();
    FederationDirectory::publish_advertisement(
        &seed_ep,
        DEFAULT_PEER_REGISTRY_PREFIX,
        703,
        1,
        &ad_eu,
    )
    .unwrap();

    // Publish regional events on `east1` and `eu`, plus a split-horizon echo candidate `/f/us-west/...`
    // inside `east1`'s log (under `/f/us-east` vs `/f/us-west`: test split-horizon with a sub-prefix!).
    let mut c_east1 = Client::connect(&east1_sock).unwrap();
    c_east1
        .publish(11, 1, "/f/us-east/events/e1", b"from-east-gw1")
        .unwrap();
    c_east1
        .publish(
            11,
            2,
            "/f/us-east/origin-west/loopback",
            b"must-be-suppressed",
        )
        .unwrap();

    let mut c_eu = Client::connect(&eu_sock).unwrap();
    c_eu.publish(22, 1, "/f/eu-west/events/w1", b"from-eu-gw1")
        .unwrap();

    let mut cfg = FederationMeshConfig::new("us-west", west_ep, 9900);
    cfg.seed_registries = vec![seed_ep.clone()];
    cfg.local_export_prefixes = vec![
        "/f/us-west".to_string(),
        "/f/us-east/origin-west".to_string(),
    ];

    let mut mesh = FederationMesh::open(cfg).expect("open FederationMesh");
    // Seed deterministic RTT preference so `us-east-a` is strictly preferred before wire probe jitter.
    mesh.refresh_discovery().expect("initial discovery");
    mesh.probe_peers();
    assert!(mesh.directory_mut().record_rtt_sample("us-east-a", 1_000));
    assert!(mesh.directory_mut().record_rtt_sample("us-east-b", 25_000));

    let rep1 = mesh.sync_once(false).expect("initial multi-region sync");
    assert_eq!(rep1.discovered_peers, 3);
    assert_eq!(rep1.active_regions, 2);
    assert_eq!(
        rep1.active_gateways,
        vec![
            ("eu-west".to_string(), "eu-west-a".to_string()),
            ("us-east".to_string(), "us-east-a".to_string()),
        ]
    );
    assert_eq!(rep1.mirrored, 2);
    assert_eq!(rep1.skipped, 1);

    // Transition `us-east-a` to `Draining` at incarnation 2 on the seed registry and publish
    // a new event at offset 0 on `us-east-b` (independent broker log!).
    let ad_east1_drain = PeerAdvertisement::new(
        "us-east-a",
        "us-east",
        &east1_sock,
        PeerTransportKind::Unix,
        2,
        PeerHealthState::Draining,
        vec!["/f/us-east".to_string()],
    )
    .unwrap();
    FederationDirectory::publish_advertisement(
        &seed_ep,
        DEFAULT_PEER_REGISTRY_PREFIX,
        701,
        2,
        &ad_east1_drain,
    )
    .unwrap();

    let mut c_east2 = Client::connect(&east2_sock).unwrap();
    c_east2
        .publish(12, 1, "/f/us-east/events/e2", b"from-east-gw2-failover")
        .unwrap();

    let rep2 = mesh.sync_once(true).expect("failover multi-region sync");
    assert_eq!(
        rep2.active_gateways,
        vec![
            ("eu-west".to_string(), "eu-west-a".to_string()),
            ("us-east".to_string(), "us-east-b".to_string()),
        ]
    );
    assert_eq!(rep2.route_switches, 1);
    assert_eq!(rep2.mirrored, 1);

    let mut c_west = Client::connect(&west_sock).unwrap();
    let (west_records, _) = c_west.fetch(0, "/>", 16).unwrap();
    assert_eq!(west_records.len(), 3);
    assert_eq!(west_records[0].1, "/f/eu-west/events/w1");
    assert_eq!(west_records[1].1, "/f/us-east/events/e1");
    assert_eq!(west_records[2].1, "/f/us-east/events/e2");
    assert_eq!(west_records[2].2, b"from-east-gw2-failover");
    assert!(mesh.cut().len() >= 3);
}
