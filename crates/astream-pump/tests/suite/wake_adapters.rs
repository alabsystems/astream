// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `pump.wake-adapters`: `DESIGN-drive-pipe.md` §5 step 4 (`docs/ROADMAP.md` §5).
//! Proves broker task-queue wake posting & non-blocking top-of-turn draining (`WakeTaskQueue`,
//! `drain_wake_tasks`, `aspump --task-subject`), Claude Code (`Notification` / `Stop`) and
//! Codex (`turn.wake`) JSON hook delivery over Unix & TCP sockets (`aspump --hook-unix`,
//! `aspump --hook-tcp`, `aspump --hook-format`), and commit-after-ack failure recovery under
//! `--group` (an unreachable hook socket exits `1` before advancing the durable group cursor,
//! so a restarted `aspump --group` re-delivers the wake once the hook listener is up).
#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, Client};
use astream_pump::{drain_wake_tasks, task_subject, WakeTaskItem};
use std::io::Read;
use std::net::TcpListener;
use std::os::unix::net::UnixListener;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

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
            if let (Some(dir), Some(name)) = (path.parent(), path.file_name()) {
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

fn fresh_broker(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/aspw_{pid}_{tag}_{n}.s");
    let log = format!("/tmp/aspw_{pid}_{tag}_{n}.log");
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

#[test]
fn aspump_posts_to_broker_task_queue_and_driver_drains_per_turn() {
    let (_tmp, _broker, mut handle, sock) = fresh_broker("taskq");
    let out_subj = "/a/stream/term/worker7/out";
    let q_subj = task_subject("claude-driver");

    let mut prod = Client::connect(&sock).unwrap();
    prod.publish(1, 1, out_subj, b"\x1b]133;A\x07$ ").unwrap();
    prod.publish(1, 2, out_subj, b"\x1b]133;C\x07").unwrap();
    prod.publish(1, 3, out_subj, b"\x1b]133;D;0\x07").unwrap();

    // Run aspump --once twice under durable group `g-pump`, forwarding wakes to `q_subj`.
    for expected_seq in [1u64, 2u64] {
        let out = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &sock,
                "worker7",
                "--group",
                "g-pump",
                "--task-subject",
                &q_subj,
                "--task-seq-start",
                &(expected_seq - 1).to_string(),
                "--once",
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "aspump --task-subject failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    // Turn-based driver drains ready tasks non-blockingly at the top of its turn!
    let sub_c = Client::connect(&sock).unwrap();
    let mut commit_c = Client::connect(&sock).unwrap();
    let tasks = drain_wake_tasks(sub_c, "g-driver", &q_subj, 16).unwrap();
    assert_eq!(tasks.len(), 2);
    assert_eq!(
        tasks[0].1,
        WakeTaskItem {
            wake_seq: 1,
            boffset: 0,
            subject: out_subj.to_owned(),
            wake_line: "PROMPT_READY boffset=0".to_owned(),
        }
    );
    assert_eq!(
        tasks[1].1,
        WakeTaskItem {
            wake_seq: 2,
            boffset: 1,
            subject: out_subj.to_owned(),
            wake_line: "COMMAND_START boffset=1".to_owned(),
        }
    );
    commit_c.commit("g-driver", tasks[1].0).unwrap();

    // Immediate second drain before new wakes returns empty without blocking!
    let empty = drain_wake_tasks(Client::connect(&sock).unwrap(), "g-driver", &q_subj, 16).unwrap();
    assert!(empty.is_empty());

    handle.shutdown();
}

#[test]
fn aspump_delivers_claude_and_codex_hooks_and_holds_group_commit_on_hook_failure() {
    let (_tmp, _broker, mut handle, sock) = fresh_broker("hooks");
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let hook_sock = format!("/tmp/asphk_{}_{n}.s", std::process::id());
    let _ = std::fs::remove_file(&hook_sock);
    let _clean_hook = Cleanup::new(&[&hook_sock]);

    let mut prod = Client::connect(&sock).unwrap();
    prod.publish(1, 1, "/a/stream/term/s9/out", b"\x1b]133;A\x07$ ")
        .unwrap();

    // 1. Negative control: point `--hook-tcp` at a closed local port under `--group g-hook`.
    //    aspump MUST exit 1 BEFORE committing `g-hook`, so the wake is NOT lost!
    let closed_listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let closed_addr = closed_listener.local_addr().unwrap().to_string();
    drop(closed_listener);

    let failed = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &sock,
            "s9",
            "--group",
            "g-hook",
            "--hook-tcp",
            &closed_addr,
            "--hook-format",
            "claude-notification",
            "--once",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(
        failed.status.code(),
        Some(1),
        "failed hook delivery must exit 1 before committing group cursor"
    );

    // 2. Now bind the Unix hook listener and re-run under the SAME `--group g-hook`:
    //    because the failed attempt held the commit, `boffset=0` is re-delivered cleanly!
    let unix_listener = UnixListener::bind(&hook_sock).unwrap();
    let reader = std::thread::spawn(move || {
        let (mut s, _) = unix_listener.accept().unwrap();
        let _ = s.set_read_timeout(Some(Duration::from_secs(5)));
        let mut buf = String::new();
        s.read_to_string(&mut buf).unwrap();
        buf
    });

    let ok_unix = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &sock,
            "s9",
            "--group",
            "g-hook",
            "--hook-unix",
            &hook_sock,
            "--hook-format",
            "claude-notification",
            "--once",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert!(ok_unix.status.success());
    let hook_payload = reader.join().unwrap();
    assert_eq!(
        hook_payload,
        "{\"hook_event_name\":\"Notification\",\"wake_seq\":1,\"boffset\":0,\"subject\":\"/a/stream/term/s9/out\",\"wake\":\"PROMPT_READY boffset=0\"}\n"
    );

    // 3. Publish a second boundary and deliver Codex `turn.wake` JSON over TCP!
    prod.publish(1, 2, "/a/stream/term/s9/out", b"\x1b]133;D;0\x07")
        .unwrap();
    let tcp_listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let tcp_addr = tcp_listener.local_addr().unwrap().to_string();
    let tcp_reader = std::thread::spawn(move || {
        let (mut s, _) = tcp_listener.accept().unwrap();
        let _ = s.set_read_timeout(Some(Duration::from_secs(5)));
        let mut buf = String::new();
        s.read_to_string(&mut buf).unwrap();
        buf
    });

    let ok_tcp = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &sock,
            "s9",
            "--group",
            "g-hook",
            "--hook-tcp",
            &tcp_addr,
            "--hook-format",
            "codex-turn",
            "--once",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert!(ok_tcp.status.success());
    let codex_payload = tcp_reader.join().unwrap();
    assert_eq!(
        codex_payload,
        "{\"type\":\"turn.wake\",\"wake_seq\":1,\"boffset\":2,\"subject\":\"/a/stream/term/s9/out\",\"wake\":\"COMMAND_END boffset=2 exit=0\"}\n"
    );

    handle.shutdown();
}
