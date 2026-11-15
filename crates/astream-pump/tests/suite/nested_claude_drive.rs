// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! End-to-end hermetic verification of a nested Claude-Code-protocol TUI session driven
//! over a real PTY (`astream-host::Pty` + `Driver`), `astream-broker`, and
//! `aspump --profile claude --group --task-subject --hook-unix --hook-format claude-stop --meta`
//! (`docs/ROADMAP.md` §5, `Astream.Pump.TlaNestedDrive`).

#[cfg(unix)]
mod unix_tests {
    use astream_broker::{Broker, Client};
    use astream_engine::{Log, MemDisk, Offset as EngOffset, Seeded};
    use astream_host::{Driver, Pty};
    use astream_pump::{
        drain_wake_tasks, out_subject, parse_prompt_ready_boffset, NestedTurnState,
    };
    use astream_term::{screen::fold, Record as TermRecord};
    use std::io::Read;
    use std::os::unix::net::UnixListener;
    use std::path::PathBuf;
    use std::process::{Child, Command, Stdio};
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::time::{Duration, Instant};

    static SEQ: AtomicU64 = AtomicU64::new(1);

    struct ShortDir(PathBuf);

    impl ShortDir {
        fn new(tag: &str) -> Self {
            let n = SEQ.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/apn_{}_{}_{}", std::process::id(), tag, n));
            let _ = std::fs::remove_dir_all(&p);
            std::fs::create_dir_all(&p).unwrap();
            Self(p)
        }
    }

    impl Drop for ShortDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn wait_bounded(child: &mut Child, max_wait: Duration) -> std::process::ExitStatus {
        let start = Instant::now();
        loop {
            if let Some(st) = child.try_wait().unwrap() {
                return st;
            }
            assert!(
                start.elapsed() < max_wait,
                "aspump child timed out after {max_wait:?}"
            );
            thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn nested_claude_code_tui_drives_multi_turn_with_crash_resume_and_deterministic_replay() {
        let dir = ShortDir::new("cc");
        let log_path = dir.0.join("b.log");
        let broker_sock = dir.0.join("b.s");
        let hook_sock = dir.0.join("h.s");

        let broker = Broker::open(&log_path).unwrap();
        let _bhandle = broker.serve(&broker_sock).unwrap();
        let broker_ep = broker_sock.to_str().unwrap().to_owned();
        let hook_ep = hook_sock.to_str().unwrap().to_owned();

        // Collect every `ClaudeStopJson` hook frame delivered by `aspump --hook-unix`.
        let hook_listener = UnixListener::bind(&hook_sock).unwrap();
        hook_listener.set_nonblocking(true).unwrap();
        let hooks_rx: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
        let hooks_stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let hooks_rx_bg = Arc::clone(&hooks_rx);
        let hooks_stop_bg = Arc::clone(&hooks_stop);
        let hook_thread = thread::spawn(move || {
            while !hooks_stop_bg.load(Ordering::Relaxed) {
                match hook_listener.accept() {
                    Ok((mut s, _)) => {
                        let _ = s.set_read_timeout(Some(Duration::from_secs(2)));
                        let mut body = String::new();
                        let _ = s.read_to_string(&mut body);
                        if !body.is_empty() {
                            hooks_rx_bg.lock().unwrap().push(body);
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(10));
                    }
                    Err(_) => break,
                }
            }
        });

        // Spawn a real PTY child speaking Claude Code's exact terminal TUI protocol:
        // - Alternate buffer (`?1049h`), OSC 7 cwd, OSC 2 title, DEC `?2026h/?2026l` frame
        // - Initial `❯ ` composer prompt
        // - Turn 1: reads line, emits thinking spinner + `Context: 45%` progress (which
        //   would false-wake `--profile common` on `%`), sleeps 180ms so debounce settles
        //   mid-thought, then emits reply + second `❯ ` prompt
        // - Turn 2: reads line, emits `PATCH_APPLIED` + third `❯ ` prompt
        // - Turn 3: reads `/exit`, leaves `?1049l`, exits 0
        let claude_sim_script = concat!(
            "stty -echo; ",
            "printf '\\033[?1049h\\033]7;file://localhost/workspace/claude-nested\\007\\033]2;Claude Code\\007'; ",
            "printf '\\033[?2026h\\033[2J\\033[HClaude Code v1\\r\\n\\342\\235\\257 \\033[?2026l'; ",
            "IFS= read -r turn1 || exit 1; ",
            "printf '\\033[?2026h\\r\\nThinking... Context: 45%%\\033[?2026l'; ",
            "sleep 0.18; ",
            "printf '\\r\\nOBSERVED:%s\\r\\n\\342\\235\\257 ' \"$turn1\"; ",
            "IFS= read -r turn2 || exit 1; ",
            "printf '\\r\\nAPPLIED:%s\\r\\n\\342\\235\\257 ' \"$turn2\"; ",
            "IFS= read -r turn3 || exit 1; ",
            "printf '\\r\\nBYE:%s\\033[?1049l\\r\\n' \"$turn3\""
        );
        let pty = Pty::spawn("/bin/sh", &["-c", claude_sim_script], 80, 24).unwrap();
        let mut driver = Driver::new(pty, Seeded::new(77));

        let sid = "cc1";
        let out_subj = out_subject(sid);
        let task_subj = "/a/stream/tasks/claude-nested";
        let pump_group = "nested-pump-g";
        let task_group = "nested-driver-g";

        let mut pub_out = Client::connect(&broker_sock).unwrap();
        let mut out_seq = 0u64;
        let mut buf = [0u8; 4096];

        // Forward initial banner + first `❯ ` prompt onto the broker.
        let mut boot_bytes = Vec::new();
        let t0 = Instant::now();
        while !String::from_utf8_lossy(&boot_bytes).contains("❯ ") {
            assert!(t0.elapsed() < Duration::from_secs(5), "boot prompt timeout");
            let n = driver.read_and_record_chunk(&mut buf).unwrap();
            if n > 0 {
                boot_bytes.extend_from_slice(&buf[..n]);
                out_seq += 1;
                pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
            }
        }

        // Run `aspump --once` for Turn 1 discovery: posts task onto `task_subj` and
        // delivers Claude `Stop` JSON hook before committing `pump_group`.
        let mut pump1 = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &broker_ep,
                sid,
                "--profile",
                "claude",
                "--group",
                pump_group,
                "--debounce",
                "40",
                "--meta",
                "--task-subject",
                task_subj,
                "--task-producer",
                "51",
                "--hook-unix",
                &hook_ep,
                "--hook-format",
                "claude-stop",
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();

        // Wait until the first `PROMPT_READY` task lands in `task_subj`.
        let mut turn_ctl = NestedTurnState::new(700, 0, None);
        let mut prompt1_off = None;
        let t_w1 = Instant::now();
        while prompt1_off.is_none() {
            assert!(
                t_w1.elapsed() < Duration::from_secs(5),
                "turn 1 wake timeout"
            );
            let sub_c = Client::connect(&broker_sock).unwrap();
            let tasks = drain_wake_tasks(sub_c, task_group, task_subj, 16).unwrap();
            if let Some((last_task_off, _)) = tasks.last() {
                let mut cc = Client::connect(&broker_sock).unwrap();
                cc.commit(task_group, *last_task_off).unwrap();
            }
            for (_toff, item) in tasks {
                if let Some(boff) = parse_prompt_ready_boffset(&item.wake_line) {
                    assert!(
                        item.wake_line.contains("cwd=/workspace/claude-nested")
                            && item.wake_line.contains("title=Claude%20Code"),
                        "expected OSC 7/2 metadata on Claude wake: {:?}",
                        item.wake_line
                    );
                    prompt1_off = Some(boff);
                }
            }
            if prompt1_off.is_none() {
                thread::sleep(Duration::from_millis(15));
            }
        }
        let w1 = prompt1_off.unwrap();

        // Admit Turn 1 and verify duplicate re-admission of `w1` is rejected (`Ok(None)`).
        let (pid1, seq1) = turn_ctl
            .admit_prompt_wake(w1, b"inspect-repo\n")
            .unwrap()
            .expect("turn 1 admitted");
        assert_eq!((pid1, seq1), (700, 1));
        assert_eq!(
            turn_ctl.admit_prompt_wake(w1, b"inspect-repo\n").unwrap(),
            None
        );
        assert!(driver
            .drive_input(pid1, seq1, b"inspect-repo\n".to_vec())
            .unwrap());
        // Replaying the same `(pid1, seq1)` into `Driver::drive_input` deduplicates!
        assert!(!driver
            .drive_input(pid1, seq1, b"inspect-repo\n".to_vec())
            .unwrap());

        // Forward mid-turn `Thinking... Context: 45%` progress and let the 40ms debounce
        // settle while the child sleeps 180ms: `--profile claude` MUST NOT emit a false
        // `PROMPT_READY` on `45%`!
        let mut mid_bytes = Vec::new();
        let t_mid = Instant::now();
        while !String::from_utf8_lossy(&mid_bytes).contains("Context: 45%") {
            assert!(
                t_mid.elapsed() < Duration::from_secs(5),
                "mid progress timeout"
            );
            let n = driver.read_and_record_chunk(&mut buf).unwrap();
            if n > 0 {
                mid_bytes.extend_from_slice(&buf[..n]);
                out_seq += 1;
                pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
            }
        }
        thread::sleep(Duration::from_millis(90));
        let mid_tasks = drain_wake_tasks(
            Client::connect(&broker_sock).unwrap(),
            task_group,
            task_subj,
            16,
        )
        .unwrap();
        for (_toff, item) in &mid_tasks {
            assert!(
                parse_prompt_ready_boffset(&item.wake_line).is_none(),
                "--profile claude must never false-wake PROMPT_READY on 45% progress: {item:?}"
            );
        }
        if let Some((last_off, _)) = mid_tasks.last() {
            Client::connect(&broker_sock)
                .unwrap()
                .commit(task_group, *last_off)
                .unwrap();
        }

        // Simulate crash of `pump1` mid-turn BEFORE Turn 1 finishes, then forward the
        // completed reply (`OBSERVED:inspect-repo` + `❯ `) and reattach `pump2` with
        // `--group` + `--task-seq-start 10`!
        let _ = pump1.kill();
        let _ = wait_bounded(&mut pump1, Duration::from_secs(5));

        let mut reply1_bytes = Vec::new();
        let t_r1 = Instant::now();
        while !String::from_utf8_lossy(&reply1_bytes).contains("❯ ") {
            assert!(
                t_r1.elapsed() < Duration::from_secs(5),
                "turn 1 reply timeout"
            );
            let n = driver.read_and_record_chunk(&mut buf).unwrap();
            if n > 0 {
                reply1_bytes.extend_from_slice(&buf[..n]);
                out_seq += 1;
                pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
            }
        }
        assert!(String::from_utf8_lossy(&reply1_bytes).contains("OBSERVED:inspect-repo"));

        let mut pump2 = Command::new(env!("CARGO_BIN_EXE_aspump"))
            .args([
                &broker_ep,
                sid,
                "--profile",
                "claude",
                "--group",
                pump_group,
                "--debounce",
                "40",
                "--meta",
                "--task-subject",
                task_subj,
                "--task-producer",
                "51",
                "--task-seq-start",
                "10",
                "--hook-unix",
                &hook_ep,
                "--hook-format",
                "claude-stop",
            ])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();

        // Drain until a new `PROMPT_READY` strictly past `w1` arrives, then drive Turn 2.
        let mut prompt2_off = None;
        let t_w2 = Instant::now();
        while prompt2_off.is_none() {
            assert!(
                t_w2.elapsed() < Duration::from_secs(5),
                "turn 2 wake timeout"
            );
            let tasks = drain_wake_tasks(
                Client::connect(&broker_sock).unwrap(),
                task_group,
                task_subj,
                16,
            )
            .unwrap();
            if let Some((last_off, _)) = tasks.last() {
                Client::connect(&broker_sock)
                    .unwrap()
                    .commit(task_group, *last_off)
                    .unwrap();
            }
            for (_toff, item) in tasks {
                if let Some(boff) = parse_prompt_ready_boffset(&item.wake_line) {
                    if let Some((pid2, seq2)) =
                        turn_ctl.admit_prompt_wake(boff, b"apply-fix\n").unwrap()
                    {
                        assert_eq!((pid2, seq2), (700, 2));
                        assert!(driver
                            .drive_input(pid2, seq2, b"apply-fix\n".to_vec())
                            .unwrap());
                        prompt2_off = Some(boff);
                    }
                }
            }
            if prompt2_off.is_none() {
                thread::sleep(Duration::from_millis(15));
            }
        }

        // Forward Turn 2 reply (`APPLIED:apply-fix` + `❯ `), wake on Turn 3, and send `/exit`.
        let mut reply2_bytes = Vec::new();
        let t_r2 = Instant::now();
        while !String::from_utf8_lossy(&reply2_bytes).contains("❯ ") {
            assert!(
                t_r2.elapsed() < Duration::from_secs(5),
                "turn 2 reply timeout"
            );
            let n = driver.read_and_record_chunk(&mut buf).unwrap();
            if n > 0 {
                reply2_bytes.extend_from_slice(&buf[..n]);
                out_seq += 1;
                pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
            }
        }
        assert!(String::from_utf8_lossy(&reply2_bytes).contains("APPLIED:apply-fix"));

        let mut exited = false;
        let t_w3 = Instant::now();
        while !exited {
            assert!(
                t_w3.elapsed() < Duration::from_secs(5),
                "turn 3 wake timeout"
            );
            let tasks = drain_wake_tasks(
                Client::connect(&broker_sock).unwrap(),
                task_group,
                task_subj,
                16,
            )
            .unwrap();
            if let Some((last_off, _)) = tasks.last() {
                Client::connect(&broker_sock)
                    .unwrap()
                    .commit(task_group, *last_off)
                    .unwrap();
            }
            for (_toff, item) in tasks {
                if let Some(boff) = parse_prompt_ready_boffset(&item.wake_line) {
                    if let Some((pid3, seq3)) =
                        turn_ctl.admit_prompt_wake(boff, b"/exit\n").unwrap()
                    {
                        assert_eq!((pid3, seq3), (700, 3));
                        assert!(driver.drive_input(pid3, seq3, b"/exit\n".to_vec()).unwrap());
                        exited = true;
                    }
                }
            }
            if !exited {
                thread::sleep(Duration::from_millis(15));
            }
        }

        let _ = driver.drain_to_eof().unwrap();
        assert_eq!(driver.reap().unwrap(), 0);
        let _ = pump2.kill();
        let _ = wait_bounded(&mut pump2, Duration::from_secs(5));

        hooks_stop.store(true, Ordering::Relaxed);
        let _ = hook_thread.join();
        let captured_hooks = hooks_rx.lock().unwrap();
        assert!(
            captured_hooks
                .iter()
                .any(|h| h.contains("\"hook_event_name\":\"Stop\"") && h.contains("PROMPT_READY")),
            "expected Claude Stop JSON hook payloads over Unix socket, got: {captured_hooks:?}"
        );

        // Verify deterministic replay of the recorded `Driver` log folds cleanly.
        let disk = MemDisk::from_bytes(driver.log_bytes());
        let recorded: Vec<TermRecord> = Log::read_from(&disk, EngOffset::ZERO)
            .map(|r| r.unwrap().record)
            .collect();
        let replayed_screen = fold(80, 24, &recorded);
        let replayed_again = fold(80, 24, &recorded);
        assert_eq!(replayed_screen.serialize(), replayed_again.serialize());
    }
}
