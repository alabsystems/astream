// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Verified classic-BPF (`cBPF`) `seccomp-bpf` 5-syscall pre-filter compiler, deterministic
//! `seccomp_data` virtual machine, and full syscall-neutralization replay state machine
//! (`Astream.Host.TlaSeccompFilter`).
//!
//! Zero `unsafe`: compiled across all Unix targets (`macOS` and `Linux`) so `make ci` verifies
//! the exact `struct sock_filter` bytecode, `AUDIT_ARCH_*` enforcement, `SECCOMP_RET_TRACE`
//! 5-syscall routing (`clock_gettime`, `getrandom`, `openat`, `read`, `close`), `SECCOMP_RET_ALLOW`
//! fast-path passthrough for all dynamic-linker / runtime syscalls, and replay-time `-1`
//! syscall neutralization + virtual-FD (`SYNTHETIC_REPLAY_FD`) state transitions. On Linux,
//! `crate::foreign` installs [`compile_five_syscall_filter`] directly via
//! `seccomp(SECCOMP_SET_MODE_FILTER)` before `execve`.

use astream_effects::{EffectRecord, EffectsLog};

#[cfg(clean_islands)]
#[path = "seccomp_island.rs"]
mod seccomp_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{seccomp_buf_clamp, seccomp_tape_advance};
#[cfg(clean_islands)]
pub use seccomp_island::{seccomp_buf_clamp, seccomp_tape_advance};

contract_fn! {
    /// Verified check that the replay cursor has not overrun the recorded tape length,
    /// linked via `clean-kernel-defeq` to `seccomp_tape_within_len_isl`.
    #[must_use]
    pub const fn seccomp_tape_within_len(cursor: u64, tape_len: u64) -> bool
    clauses [ensures result == (cursor <= tape_len)]
    {
        cursor <= tape_len
    }
}

/// Linux `AUDIT_ARCH_X86_64` (`EM_X86_64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`).
pub const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;
/// Linux `AUDIT_ARCH_AARCH64` (`EM_AARCH64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`).
pub const AUDIT_ARCH_AARCH64: u32 = 0xC000_00B7;

/// Seccomp return action: kill the process immediately on foreign-ABI syscall confusion.
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
/// Seccomp return action: stop the tracee at `PTRACE_EVENT_SECCOMP` before kernel execution.
pub const SECCOMP_RET_TRACE: u32 = 0x7FF0_0000;
/// Seccomp return action: execute in-kernel with zero ptrace stops (`O(intercepted)` tracer cost).
pub const SECCOMP_RET_ALLOW: u32 = 0x7FFF_0000;

/// Neutralized syscall number (`-1`) written at `PTRACE_EVENT_SECCOMP` so the kernel skips
/// executing any real syscall (`-ENOSYS`), after which the tracer injects the taped result.
pub const NEUTRALIZED_SYSCALL_NR: i64 = -1;

/// Synthetic virtual file descriptor returned for neutralized `openat` of the target file on replay,
/// so no host file is ever opened, read, or closed in the kernel during replay.
pub const SYNTHETIC_REPLAY_FD: i64 = 1000;

/// Classic BPF instruction (`BPF_LD | BPF_W | BPF_ABS`).
pub const BPF_LD_W_ABS: u16 = 0x0020;
/// Classic BPF instruction (`BPF_JMP | BPF_JEQ | BPF_K`).
pub const BPF_JMP_JEQ_K: u16 = 0x0015;
/// Classic BPF instruction (`BPF_RET | BPF_K`).
pub const BPF_RET_K: u16 = 0x0006;

/// Byte offset of `nr` (`int`) in Linux `struct seccomp_data`.
pub const SECCOMP_DATA_NR_OFFSET: u32 = 0;
/// Byte offset of `arch` (`__u32`) in Linux `struct seccomp_data`.
pub const SECCOMP_DATA_ARCH_OFFSET: u32 = 4;

/// Number of `sock_filter` instructions in [`compile_five_syscall_filter`].
pub const FIVE_SYSCALL_FILTER_LEN: usize = 11;

/// ABI-compatible Linux `struct sock_filter` instruction (`8` bytes, `#[repr(C)]`).
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SockFilter {
    /// Filter opcode (`BPF_LD_W_ABS`, `BPF_JMP_JEQ_K`, `BPF_RET_K`).
    pub code: u16,
    /// Forward jump offset when comparison is true.
    pub jt: u8,
    /// Forward jump offset when comparison is false.
    pub jf: u8,
    /// Generic 32-bit constant / `seccomp_data` offset.
    pub k: u32,
}

/// Supported Linux `seccomp_data.arch` targets for foreign-process tracing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeccompArch {
    /// `x86_64` Linux (`AUDIT_ARCH_X86_64`).
    X86_64,
    /// `aarch64` Linux (`AUDIT_ARCH_AARCH64`).
    Aarch64,
}

/// Logical intercepted syscall class among the 5 traced effects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InterceptedSyscall {
    /// `clock_gettime(clk_id, tp)`
    ClockGettime,
    /// `getrandom(buf, buflen, flags)`
    Getrandom,
    /// `openat(dirfd, pathname, flags, mode)`
    Openat,
    /// `read(fd, buf, count)`
    Read,
    /// `close(fd)`
    Close,
}

impl SeccompArch {
    /// Linux `AUDIT_ARCH_*` constant for this architecture.
    #[must_use]
    pub const fn audit_arch(self) -> u32 {
        match self {
            SeccompArch::X86_64 => AUDIT_ARCH_X86_64,
            SeccompArch::Aarch64 => AUDIT_ARCH_AARCH64,
        }
    }

    /// Exact `[clock_gettime, getrandom, openat, read, close]` syscall numbers on this ABI.
    #[must_use]
    pub const fn intercepted_nrs(self) -> [u32; 5] {
        match self {
            SeccompArch::X86_64 => [228, 318, 257, 0, 3],
            SeccompArch::Aarch64 => [113, 278, 56, 63, 57],
        }
    }

    /// Classify a raw syscall number if it belongs to the 5 intercepted syscalls.
    #[must_use]
    pub const fn classify_nr(self, nr: i64) -> Option<InterceptedSyscall> {
        if nr < 0 || nr > (u32::MAX as i64) {
            return None;
        }
        let u = nr as u32;
        let [cg, gr, oa, rd, cl] = self.intercepted_nrs();
        if u == cg {
            Some(InterceptedSyscall::ClockGettime)
        } else if u == gr {
            Some(InterceptedSyscall::Getrandom)
        } else if u == oa {
            Some(InterceptedSyscall::Openat)
        } else if u == rd {
            Some(InterceptedSyscall::Read)
        } else if u == cl {
            Some(InterceptedSyscall::Close)
        } else {
            None
        }
    }
}

/// Compile the 11-instruction DAG-verified `seccomp-bpf` program that:
/// 1. Rejects any foreign `seccomp_data.arch` with `SECCOMP_RET_KILL_PROCESS` (preventing
///    `int 0x80` / compat-mode syscall-number aliasing).
/// 2. Emits `SECCOMP_RET_TRACE` ONLY for `{clock_gettime, getrandom, openat, read, close}`.
/// 3. Emits `SECCOMP_RET_ALLOW` for every other syscall (`O(intercepted)` tracer wakeups).
#[must_use]
pub const fn compile_five_syscall_filter(
    arch: SeccompArch,
) -> [SockFilter; FIVE_SYSCALL_FILTER_LEN] {
    let [s0, s1, s2, s3, s4] = arch.intercepted_nrs();
    [
        // [0] A = seccomp_data.arch
        SockFilter {
            code: BPF_LD_W_ABS,
            jt: 0,
            jf: 0,
            k: SECCOMP_DATA_ARCH_OFFSET,
        },
        // [1] if A == arch goto [3] else goto [2]
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 1,
            jf: 0,
            k: arch.audit_arch(),
        },
        // [2] foreign arch -> kill process
        SockFilter {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: SECCOMP_RET_KILL_PROCESS,
        },
        // [3] A = seccomp_data.nr
        SockFilter {
            code: BPF_LD_W_ABS,
            jt: 0,
            jf: 0,
            k: SECCOMP_DATA_NR_OFFSET,
        },
        // [4] clock_gettime -> [10] TRACE
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 5,
            jf: 0,
            k: s0,
        },
        // [5] getrandom -> [10] TRACE
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 4,
            jf: 0,
            k: s1,
        },
        // [6] openat -> [10] TRACE
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 3,
            jf: 0,
            k: s2,
        },
        // [7] read -> [10] TRACE
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 2,
            jf: 0,
            k: s3,
        },
        // [8] close -> [10] TRACE else [9] ALLOW
        SockFilter {
            code: BPF_JMP_JEQ_K,
            jt: 1,
            jf: 0,
            k: s4,
        },
        // [9] non-intercepted syscall -> ALLOW in kernel
        SockFilter {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: SECCOMP_RET_ALLOW,
        },
        // [10] intercepted syscall -> TRACE stop before kernel execution
        SockFilter {
            code: BPF_RET_K,
            jt: 0,
            jf: 0,
            k: SECCOMP_RET_TRACE,
        },
    ]
}

/// Evaluate a classic-BPF `seccomp` filter program on `(nr, arch)`.
///
/// Enforces Linux `bpf_check_classic` rules: non-empty program (`<= 4096` instructions),
/// aligned `seccomp_data` word loads (`0` or `4`), strictly forward bounded jumps (no loops),
/// and termination via `BPF_RET_K`. Returns `None` if `prog` is malformed.
#[must_use]
pub fn eval_cbpf_seccomp(prog: &[SockFilter], nr: i32, arch: u32) -> Option<u32> {
    if prog.is_empty() || prog.len() > 4096 {
        return None;
    }
    let mut acc: u32 = 0;
    let mut pc: usize = 0;
    while pc < prog.len() {
        let insn = *prog.get(pc)?;
        match insn.code {
            BPF_LD_W_ABS => {
                acc = match insn.k {
                    SECCOMP_DATA_NR_OFFSET => nr as u32,
                    SECCOMP_DATA_ARCH_OFFSET => arch,
                    _ => return None,
                };
                pc = pc.saturating_add(1);
            }
            BPF_JMP_JEQ_K => {
                let step = if acc == insn.k {
                    usize::from(insn.jt)
                } else {
                    usize::from(insn.jf)
                };
                let next_pc = pc.saturating_add(1).saturating_add(step);
                if next_pc >= prog.len() {
                    return None;
                }
                pc = next_pc;
            }
            BPF_RET_K => return Some(insn.k),
            _ => return None,
        }
    }
    None
}

/// Fail-closed replay divergence reason when driving a `seccomp`-stopped foreign process.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayAbort {
    /// Process requested more effects than the recorded tape holds.
    TapeExhausted,
    /// Next taped effect kind did not match the intercepted syscall.
    WrongEffectKind { expected: &'static str },
    /// Recorded `EffectRecord::File` path disagreed with the tracee's `openat` path.
    PathDiverged { recorded: String, actual: String },
    /// Recorded `EffectRecord::File` payload exceeded the tracee's `read` buffer `count`.
    ReadBufferOverrun { tape_bytes: usize, buf_cap: u64 },
}

/// Action decided at a `PTRACE_EVENT_SECCOMP` stop during replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeccompReplayDecision {
    /// Non-target runtime/loader file operation (e.g. `ld-linux.so` loading `libc.so.6`):
    /// allow kernel execution without touching the effect tape.
    PassthroughRuntimeIo,
    /// Target syscall MUST be neutralized (`rewritten_nr = -1` so no real syscall reaches
    /// the kernel), then `return_value` and optional `poke_bytes` injected into the tracee.
    NeutralizeAndInject {
        rewritten_nr: i64,
        return_value: i64,
        poke_bytes: Option<Vec<u8>>,
    },
}

/// Pure replay state machine driving `PTRACE_EVENT_SECCOMP` stops with full syscall
/// neutralization (`NEUTRALIZED_SYSCALL_NR = -1`) and virtual target-FD tracking.
pub struct NeutralizedReplayDriver<'a> {
    expected_path: &'a str,
    tape: &'a [EffectRecord],
    cursor: u64,
    virtual_fd_open: bool,
    neutralized_count: u64,
}

impl<'a> NeutralizedReplayDriver<'a> {
    /// Construct a new replay driver over `tape` expecting target file `expected_path`.
    #[must_use]
    pub fn new(expected_path: &'a str, tape: &'a EffectsLog) -> Self {
        Self {
            expected_path,
            tape: &tape.0,
            cursor: 0,
            virtual_fd_open: false,
            neutralized_count: 0,
        }
    }

    /// Current replay cursor position (`<= tape.len()`).
    #[must_use]
    pub const fn cursor(&self) -> u64 {
        self.cursor
    }

    /// Total number of syscalls neutralized (`rewritten_nr = -1`, zero kernel execution).
    #[must_use]
    pub const fn neutralized_count(&self) -> u64 {
        self.neutralized_count
    }

    fn take_next(&mut self) -> Result<&'a EffectRecord, ReplayAbort> {
        let len_u64 = self.tape.len() as u64;
        if !seccomp_tape_within_len(self.cursor, len_u64) || self.cursor == len_u64 {
            return Err(ReplayAbort::TapeExhausted);
        }
        let Ok(idx) = usize::try_from(self.cursor) else {
            return Err(ReplayAbort::TapeExhausted);
        };
        let item = self.tape.get(idx).ok_or(ReplayAbort::TapeExhausted)?;
        let cand = self.cursor.saturating_add(1);
        self.cursor = seccomp_buf_clamp(seccomp_tape_advance(self.cursor, cand), len_u64);
        Ok(item)
    }

    /// Decide `PTRACE_EVENT_SECCOMP` handling for `clock_gettime`.
    pub fn on_clock_gettime(&mut self) -> Result<SeccompReplayDecision, ReplayAbort> {
        match self.take_next()? {
            EffectRecord::Clock(v) => {
                let [b0, b1, b2, b3, b4, b5, b6, b7] = v.to_le_bytes();
                let ts = [0u8, 0, 0, 0, 0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7];
                self.neutralized_count = self.neutralized_count.saturating_add(1);
                Ok(SeccompReplayDecision::NeutralizeAndInject {
                    rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                    return_value: 0,
                    poke_bytes: Some(ts.to_vec()),
                })
            }
            _ => Err(ReplayAbort::WrongEffectKind { expected: "Clock" }),
        }
    }

    /// Decide `PTRACE_EVENT_SECCOMP` handling for `getrandom(buf, buflen)`.
    pub fn on_getrandom(&mut self, buflen: u64) -> Result<SeccompReplayDecision, ReplayAbort> {
        match self.take_next()? {
            EffectRecord::Rand(v) => {
                let clamped = seccomp_buf_clamp(8, buflen);
                let n = usize::try_from(clamped).unwrap_or(0);
                let raw = v.to_le_bytes();
                let payload = raw.get(..n).unwrap_or(&[]).to_vec();
                self.neutralized_count = self.neutralized_count.saturating_add(1);
                Ok(SeccompReplayDecision::NeutralizeAndInject {
                    rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                    return_value: n as i64,
                    poke_bytes: Some(payload),
                })
            }
            _ => Err(ReplayAbort::WrongEffectKind { expected: "Rand" }),
        }
    }

    /// Decide `PTRACE_EVENT_SECCOMP` handling for `openat(_, tracee_path, _)`.
    ///
    /// Dynamic-linker opens (`ld.so.cache`, `libc.so.6`) do not match `expected_path`
    /// and pass through; opening `expected_path` is neutralized (`nr = -1`) and assigned
    /// [`SYNTHETIC_REPLAY_FD`] without touching the filesystem.
    pub fn on_openat(&mut self, tracee_path: &str) -> SeccompReplayDecision {
        if tracee_path == self.expected_path {
            self.virtual_fd_open = true;
            self.neutralized_count = self.neutralized_count.saturating_add(1);
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                return_value: SYNTHETIC_REPLAY_FD,
                poke_bytes: None,
            }
        } else {
            SeccompReplayDecision::PassthroughRuntimeIo
        }
    }

    /// Decide `PTRACE_EVENT_SECCOMP` handling for `read(fd, buf, count)`.
    pub fn on_read(&mut self, fd: i64, count: u64) -> Result<SeccompReplayDecision, ReplayAbort> {
        if !self.virtual_fd_open || fd != SYNTHETIC_REPLAY_FD {
            return Ok(SeccompReplayDecision::PassthroughRuntimeIo);
        }
        match self.take_next()? {
            EffectRecord::File { path, bytes } => {
                if path != self.expected_path {
                    return Err(ReplayAbort::PathDiverged {
                        recorded: path.clone(),
                        actual: self.expected_path.to_owned(),
                    });
                }
                if (bytes.len() as u64) > count {
                    return Err(ReplayAbort::ReadBufferOverrun {
                        tape_bytes: bytes.len(),
                        buf_cap: count,
                    });
                }
                let clamped = seccomp_buf_clamp(bytes.len() as u64, count);
                let n = usize::try_from(clamped).unwrap_or(0);
                let out = bytes.get(..n).unwrap_or(&[]).to_vec();
                self.neutralized_count = self.neutralized_count.saturating_add(1);
                Ok(SeccompReplayDecision::NeutralizeAndInject {
                    rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                    return_value: n as i64,
                    poke_bytes: Some(out),
                })
            }
            _ => Err(ReplayAbort::WrongEffectKind { expected: "File" }),
        }
    }

    /// Decide `PTRACE_EVENT_SECCOMP` handling for `close(fd)`.
    pub fn on_close(&mut self, fd: i64) -> SeccompReplayDecision {
        if self.virtual_fd_open && fd == SYNTHETIC_REPLAY_FD {
            self.virtual_fd_open = false;
            self.neutralized_count = self.neutralized_count.saturating_add(1);
            SeccompReplayDecision::NeutralizeAndInject {
                rewritten_nr: NEUTRALIZED_SYSCALL_NR,
                return_value: 0,
                poke_bytes: None,
            }
        } else {
            SeccompReplayDecision::PassthroughRuntimeIo
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_origin_seccomp_kernels_and_cbpf_five_syscall_filter_hold() {
        assert_eq!(seccomp_tape_advance(2, 1), 2);
        assert_eq!(seccomp_tape_advance(2, 5), 5);
        assert_eq!(seccomp_buf_clamp(512, 256), 256);
        assert_eq!(seccomp_buf_clamp(64, 256), 64);
        assert!(seccomp_tape_within_len(3, 3));
        assert!(!seccomp_tape_within_len(4, 3));

        for arch in [SeccompArch::X86_64, SeccompArch::Aarch64] {
            let prog = compile_five_syscall_filter(arch);
            let intercepted = arch.intercepted_nrs();
            let wrong_arch = match arch {
                SeccompArch::X86_64 => AUDIT_ARCH_AARCH64,
                SeccompArch::Aarch64 => AUDIT_ARCH_X86_64,
            };
            for nr in 0i32..450i32 {
                let verdict = eval_cbpf_seccomp(&prog, nr, arch.audit_arch()).unwrap();
                if intercepted.contains(&(nr as u32)) {
                    assert_eq!(verdict, SECCOMP_RET_TRACE, "nr {nr} on {arch:?}");
                } else {
                    assert_eq!(verdict, SECCOMP_RET_ALLOW, "nr {nr} on {arch:?}");
                }
                assert_eq!(
                    eval_cbpf_seccomp(&prog, nr, wrong_arch),
                    Some(SECCOMP_RET_KILL_PROCESS)
                );
            }
        }
    }
}
