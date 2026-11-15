//! Evidence for `broker.agent-native-fork-and-cognition`: the delivery verbs no
//! other bus has, built on the broker's SUBSCRIBE primitive.
//!
//! 1. COUNTERFACTUAL fork-delivery: a sandbox consumer receives the alternate
//!    timeline (the topic forked at offset N with one message swapped) while the
//!    live log and live subscribers are untouched.
//! 2. COGNITION routing: a REAL astream-agent CogRecord (a tool_use) published to a
//!    cognition subject is routed by the Filter grammar to an auditor that pages on
//!    every tool_use touching a secret — across sessions, excluding non-secret ones.
//!
//! Fully in-process, no sleeps.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_agent::{cog::CogRecord, cog::StopReason, cog::ToolUse, CogEnvelope, Offset};
use astream_broker::{Broker, BrokerHandle, Client};
use astream_wire::Frame;
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
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

fn fresh(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/asbn_{pid}_{tag}_{n}.sock");
    let log = format!("/tmp/asbn_{pid}_{tag}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

fn client(sock: &str) -> Client {
    Client::connect(sock).unwrap()
}

/// Drain a subscription to EOF (used for the one-shot fork snapshot).
fn drain(sub: &mut astream_broker::Subscription) -> Vec<(u64, String, Vec<u8>)> {
    let mut out = Vec::new();
    while let Some(d) = sub.recv().unwrap() {
        out.push(d);
    }
    out
}

#[test]
fn fork_delivery_streams_a_counterfactual_timeline_without_touching_the_live_log() {
    let (_tmp, _b, _h, sock) = fresh("fork");
    let mut p = client(&sock);
    for i in 1..=5u64 {
        p.publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
    }

    // COUNTERFACTUAL: fork at offset 2, swap that message for "SWAPPED".
    let mut fork = client(&sock)
        .fork_subscribe(2, "/a/stream/x", b"SWAPPED", "/a/stream/>")
        .unwrap();
    let alt = drain(&mut fork);
    assert_eq!(
        alt.iter().map(|(o, ..)| *o).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4]
    );
    assert_eq!(
        alt[2].2, b"SWAPPED",
        "the forked record diverges at the swap"
    );
    assert_eq!(alt[1].2, b"m2", "the prefix is the recorded history");
    assert_eq!(alt[3].2, b"m4", "the suffix is the recorded history");

    // The LIVE log is unchanged — a fresh live subscriber still sees the original m3.
    let mut live = client(&sock).subscribe(0, "/a/stream/>").unwrap();
    let original: Vec<Vec<u8>> = (0..5).map(|_| live.recv().unwrap().unwrap().2).collect();
    assert_eq!(
        original[2], b"m3",
        "fork-delivery did not mutate the live log"
    );
}

fn cog_body(reasoning: &str, cmd: &str) -> Vec<u8> {
    let cog = CogRecord::Completion {
        text: reasoning.to_string(),
        calls: vec![ToolUse {
            id: "t1".to_string(),
            name: "bash".to_string(),
            input: format!("{{\"command\":\"{cmd}\"}}").into_bytes(),
        }],
        stop: StopReason::ToolUse,
    };
    CogEnvelope {
        seq: Offset(0),
        ts_logical: 0,
        record: cog,
    }
    .encode()
    .unwrap()
}

fn decode_cog(body: &[u8]) -> CogRecord {
    let d = Frame::decode(body).unwrap().unwrap();
    CogEnvelope::from_payload(&d.frame.payload).unwrap().record
}

#[test]
fn cognition_routing_pages_the_auditor_on_secret_tool_use() {
    let (_tmp, _b, _h, sock) = fresh("cog");
    let mut p = client(&sock);
    // Real cognition events to the cognition subtree; the subject tags whether the
    // tool_use touched a secret (the publisher's classification).
    p.publish(
        1,
        1,
        "/a/cog/s1/tool_use/secret",
        &cog_body("read the key", "cat /etc/secret"),
    )
    .unwrap(); // off 0
    p.publish(
        1,
        2,
        "/a/cog/s1/tool_use/plain",
        &cog_body("list files", "ls"),
    )
    .unwrap(); // off 1
    p.publish(
        1,
        3,
        "/a/cog/s2/tool_use/secret",
        &cog_body("dump creds", "cat ~/.aws/credentials"),
    )
    .unwrap(); // off 2

    // The auditor pages on EVERY session's secret-touching tool_use, not the plain one.
    let mut auditor = client(&sock)
        .subscribe(0, "/a/cog/*/tool_use/secret")
        .unwrap();
    let first = auditor.recv().unwrap().unwrap();
    let second = auditor.recv().unwrap().unwrap();
    assert_eq!(first.0, 0, "s1 secret tool_use");
    assert_eq!(
        second.0, 2,
        "s2 secret tool_use — the plain one (offset 1) was filtered out"
    );

    // The delivered bodies are REAL CogRecords (cognition flows through the bus).
    match decode_cog(&first.2) {
        CogRecord::Completion { calls, .. } => {
            assert_eq!(calls[0].name, "bash");
            assert!(String::from_utf8_lossy(&calls[0].input).contains("/etc/secret"));
        }
        _ => panic!("expected a Completion"),
    }
}
