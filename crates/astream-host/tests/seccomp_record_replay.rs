// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `seccomp-bpf` pre-filtering, replay-time `-1` syscall neutralization,
//! and unmodified `execve` foreign-process record/replay:
//! - Cross-platform Unix suite (`effects.seccomp-bpf-filter`, verified on macOS and Linux):
//!   verifies the 11-instruction classic-BPF filter (`compile_five_syscall_filter` /
//!   `eval_cbpf_seccomp`) across `AUDIT_ARCH_X86_64` and `AUDIT_ARCH_AARCH64`, and verifies
//!   `NeutralizedReplayDriver` (`NEUTRALIZED_SYSCALL_NR = -1`, `SYNTHETIC_REPLAY_FD = 1000`,
//!   loader passthrough, and fail-closed `ReplayAbort` on short, wrong-kind, path-divergent,
//!   and over-buffer tapes).
//! - Linux kernel suite (`effects.foreign-process.seccomp-record-replay`, `cfg(target_os = "linux")`):
//!   forks, installs `compile_five_syscall_filter` via `seccomp(SECCOMP_SET_MODE_FILTER)`,
//!   attaches `PTRACE_O_TRACESECCOMP`, and `execve`s the unmodified `seccomp_child` binary,
//!   recording `[Clock, Rand, File]` in `O(intercepted)` stops and replaying after deleting the
//!   target file on disk so any real kernel `openat`/`read`/`close` would fail.

#![cfg(unix)]

#[cfg(unix)]
mod bpf_and_neutralization {
    use astream_effects::{EffectRecord, EffectsLog};
    use astream_host::seccomp::{
        compile_five_syscall_filter, eval_cbpf_seccomp, NeutralizedReplayDriver, ReplayAbort,
        SeccompArch, SeccompReplayDecision, AUDIT_ARCH_AARCH64, AUDIT_ARCH_X86_64,
        NEUTRALIZED_SYSCALL_NR, SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, SECCOMP_RET_TRACE,
        SYNTHETIC_REPLAY_FD,
    };

    #[test]
    fn cbpf_five_syscall_prefilter_traces_only_intercepted_set_and_kills_foreign_arch() {
        for (arch, expected_nrs, foreign_arch) in [
            (
                SeccompArch::X86_64,
                [228u32, 318, 257, 0, 3],
                AUDIT_ARCH_AARCH64,
            ),
            (
                SeccompArch::Aarch64,
                [113u32, 278, 56, 63, 57],
                AUDIT_ARCH_X86_64,
            ),
        ] {
            let prog = compile_five_syscall_filter(arch);
            for nr in 0i32..512i32 {
                let got = eval_cbpf_seccomp(&prog, nr, arch.audit_arch())
                    .expect("valid DAG-bounded cBPF filter");
                if expected_nrs.contains(&(nr as u32)) {
                    assert_eq!(got, SECCOMP_RET_TRACE);
                    assert!(arch.classify_nr(i64::from(nr)).is_some());
                } else {
                    assert_eq!(got, SECCOMP_RET_ALLOW);
                    assert!(arch.classify_nr(i64::from(nr)).is_none());
                }
                assert_eq!(
                    eval_cbpf_seccomp(&prog, nr, foreign_arch),
                    Some(SECCOMP_RET_KILL_PROCESS)
                );
            }
        }
    }

    #[test]
    fn neutralized_replay_driver_rewrites_syscalls_to_noop_and_aborts_on_divergent_tapes() {
        let target = "/tmp/astream_seccomp_fixture.bin";
        let tape = EffectsLog(vec![
            EffectRecord::Clock(0x1234_5678_9ABC_DEF0),
            EffectRecord::Rand(0xCAFE_BABE_DEAD_BEEF),
            EffectRecord::File {
                path: target.to_owned(),
                bytes: b"neutralized-payload".to_vec(),
            },
        ]);

        let mut drv = NeutralizedReplayDriver::new(target, &tape);

        // Dynamic-linker `openat("/etc/ld.so.cache")` + `read(3, ..)` + `close(3)` pass through untouched.
        assert_eq!(
            drv.on_openat("/etc/ld.so.cache"),
            SeccompReplayDecision::PassthroughRuntimeIo
        );
        assert_eq!(
            drv.on_read(3, 4096).unwrap(),
            SeccompReplayDecision::PassthroughRuntimeIo
        );
        assert_eq!(drv.on_close(3), SeccompReplayDecision::PassthroughRuntimeIo);
        assert_eq!(drv.cursor(), 0);
        assert_eq!(drv.neutralized_count(), 0);

        // Intercepted `clock_gettime`: neutralized to `-1` + 16-byte timespec injected.
        match drv.on_clock_gettime().unwrap() {
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr,
                return_value,
                poke_bytes: Some(ts),
            } => {
                assert_eq!(rewritten_nr, NEUTRALIZED_SYSCALL_NR);
                assert_eq!(return_value, 0);
                assert_eq!(ts.len(), 16);
                let sec = u64::from_le_bytes(ts[0..8].try_into().unwrap());
                let nsec = u64::from_le_bytes(ts[8..16].try_into().unwrap());
                assert_eq!(sec ^ nsec, 0x1234_5678_9ABC_DEF0);
            }
            other => panic!("unexpected clock decision: {other:?}"),
        }

        // Intercepted `getrandom`: neutralized to `-1` + 8-byte rand word injected.
        match drv.on_getrandom(8).unwrap() {
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr,
                return_value,
                poke_bytes: Some(r),
            } => {
                assert_eq!(rewritten_nr, NEUTRALIZED_SYSCALL_NR);
                assert_eq!(return_value, 8);
                assert_eq!(
                    u64::from_le_bytes(r.try_into().unwrap()),
                    0xCAFE_BABE_DEAD_BEEF
                );
            }
            other => panic!("unexpected rand decision: {other:?}"),
        }

        // Target `openat(target)`: neutralized to `-1` + virtual `SYNTHETIC_REPLAY_FD` returned.
        assert_eq!(
            drv.on_openat(target),
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                return_value: SYNTHETIC_REPLAY_FD,
                poke_bytes: None,
            }
        );

        // Target `read(SYNTHETIC_REPLAY_FD, 256)`: neutralized to `-1` + taped bytes injected.
        match drv.on_read(SYNTHETIC_REPLAY_FD, 256).unwrap() {
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr,
                return_value,
                poke_bytes: Some(bytes),
            } => {
                assert_eq!(rewritten_nr, NEUTRALIZED_SYSCALL_NR);
                assert_eq!(return_value, 19);
                assert_eq!(bytes, b"neutralized-payload");
            }
            other => panic!("unexpected read decision: {other:?}"),
        }

        // Target `close(SYNTHETIC_REPLAY_FD)`: neutralized to `-1` + `0` returned.
        assert_eq!(
            drv.on_close(SYNTHETIC_REPLAY_FD),
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                return_value: 0,
                poke_bytes: None,
            }
        );
        assert_eq!(drv.cursor(), 3);
        assert_eq!(drv.neutralized_count(), 5);

        // Short tape -> TapeExhausted
        assert_eq!(drv.on_clock_gettime(), Err(ReplayAbort::TapeExhausted));

        // Wrong kind -> WrongEffectKind
        let swapped = EffectsLog(vec![EffectRecord::Rand(7)]);
        let mut bad_kind = NeutralizedReplayDriver::new(target, &swapped);
        assert_eq!(
            bad_kind.on_clock_gettime(),
            Err(ReplayAbort::WrongEffectKind { expected: "Clock" })
        );

        // Divergent path -> PathDiverged
        let wrong_path_tape = EffectsLog(vec![EffectRecord::File {
            path: "/tmp/other.bin".to_owned(),
            bytes: b"abc".to_vec(),
        }]);
        let mut bad_path = NeutralizedReplayDriver::new(target, &wrong_path_tape);
        let _ = bad_path.on_openat(target);
        assert_eq!(
            bad_path.on_read(SYNTHETIC_REPLAY_FD, 256),
            Err(ReplayAbort::PathDiverged {
                recorded: "/tmp/other.bin".to_owned(),
                actual: target.to_owned(),
            })
        );

        // Over-long File record -> ReadBufferOverrun
        let overlong_tape = EffectsLog(vec![EffectRecord::File {
            path: target.to_owned(),
            bytes: vec![b'z'; 512],
        }]);
        let mut bad_len = NeutralizedReplayDriver::new(target, &overlong_tape);
        let _ = bad_len.on_openat(target);
        assert_eq!(
            bad_len.on_read(SYNTHETIC_REPLAY_FD, 256),
            Err(ReplayAbort::ReadBufferOverrun {
                tape_bytes: 512,
                buf_cap: 256,
            })
        );
    }
}

#[cfg(target_os = "linux")]
mod linux_exec_seccomp {
    use astream_effects::EffectsLog;
    use astream_host::foreign::{self, Effect};

    struct Cleanup(String);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    fn fixture_path(tag: &str) -> (Cleanup, String) {
        let path = format!("/tmp/astream_seccomp_{}_{}.bin", std::process::id(), tag);
        (Cleanup(path.clone()), path)
    }

    #[allow(clippy::manual_rotate)]
    fn oracle(clock: u64, rand: u64, bytes: &[u8]) -> u64 {
        let rotl7 = (clock << 7) | (clock >> 57);
        let head = rotl7 ^ rand.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        bytes.iter().fold(head, |h, &b| {
            let m = (h ^ u64::from(b)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            (m << 11) | (m >> 53)
        })
    }

    fn replay_exec_aborts(bin: &str, path: &str, tape: &EffectsLog) -> bool {
        match std::panic::catch_unwind(|| foreign::replay_exec(bin, path, tape)) {
            Err(_) => true,
            Ok(Ok(_)) => false,
            Ok(Err(e)) => panic!("replay_exec machinery failed instead of aborting: {e}"),
        }
    }

    #[test]
    fn unmodified_exec_child_records_under_seccomp_and_replays_with_zero_real_syscalls() {
        let bin = env!("CARGO_BIN_EXE_seccomp_child");
        let (_tmp, path) = fixture_path("exec-main");
        std::fs::write(&path, b"seccomp-exec-fixture-v1").unwrap();

        let (tape, rec_digest) = foreign::record_exec(bin, &path).expect("record_exec");
        let [Effect::Clock(clock), Effect::Rand(rand), Effect::File {
            path: ref taped_path,
            ref bytes,
        }] = tape.0.as_slice()
        else {
            panic!("expected [Clock, Rand, File], got {:?}", tape.0);
        };
        assert_eq!(taped_path, &path);
        assert_eq!(bytes, b"seccomp-exec-fixture-v1");
        assert_eq!(rec_digest, oracle(*clock, *rand, bytes));

        // Remove the file completely before replay: if `openat`/`read` were NOT neutralized
        // before reaching the kernel, the child would see ENOENT / empty bytes!
        std::fs::remove_file(&path).unwrap();
        let rep_digest = foreign::replay_exec(bin, &path, &tape).expect("replay_exec");
        assert_eq!(rep_digest, rec_digest);

        // Short, wrong-kind, path-divergent, and over-buffer tapes abort fail-closed.
        let mut short = tape.clone();
        short.0.truncate(2);
        assert!(replay_exec_aborts(bin, &path, &short));

        let mut swapped = tape.clone();
        swapped.0.swap(0, 1);
        assert!(replay_exec_aborts(bin, &path, &swapped));

        let (_tmp2, other_path) = fixture_path("exec-other");
        assert!(replay_exec_aborts(bin, &other_path, &tape));

        let mut overlong = tape.clone();
        overlong.0[2] = Effect::File {
            path: path.clone(),
            bytes: vec![b'Q'; 4096],
        };
        assert!(replay_exec_aborts(bin, &path, &overlong));
    }
}
