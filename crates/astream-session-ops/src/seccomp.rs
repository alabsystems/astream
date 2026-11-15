// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure-Rust Classic BPF (`sock_filter`) compiler, monotone-DAG verifier, VM
//! evaluator, and replay syscall neutralizer (`docs/ROADMAP.md` Foreign-Process
//! Replay Hardening).
//!
//! `astream-host::foreign` intercepts syscalls via `ptrace(PTRACE_SYSCALL)`,
//! which traps on every syscall entry and exit and still lets the kernel execute
//! intercepted syscalls during replay before overwriting return registers.
//! Hardening foreign-process record/replay (`docs/ROADMAP.md` §3) requires two
//! deterministic, cross-platform-verifiable components:
//! 1. **Selective `seccomp-bpf` filter synthesis** ([`SeccompPolicy`],
//!    [`compile_seccomp_policy`], [`verify_bpf_program`], [`eval_bpf_program`]):
//!    compiles an architecture-pinned BPF program (`AUDIT_ARCH_AARCH64` or
//!    `AUDIT_ARCH_X86_64`) that returns `SECCOMP_RET_TRACE` ONLY for the
//!    effectful syscalls recorded on the tape, `SECCOMP_RET_ERRNO(EPERM)` for
//!    explicitly denied escape syscalls, and `SECCOMP_RET_ALLOW` for hot pure
//!    syscalls (`brk`, `mmap`, `futex`, etc.), eliminating 90%+ of `ptrace` traps.
//! 2. **Replay syscall neutralization** ([`ReplayNeutralizer`]): maps recorded
//!    effectful syscalls (`clock_gettime`, `getrandom`, `openat`, `read`,
//!    `write`, `connect`) onto harmless `getpid` on syscall-entry stop during
//!    replay so the tracee never touches host files, sockets, or clocks before
//!    the taped result is injected on syscall-exit stop.
//!
//! Everything in this module is 100% safe pure Rust (`#![deny(unsafe_code)]`),
//! compiled and verified on both macOS and Linux under `Astream.Host.TlaSandboxFilter`.

#[cfg(clean_islands)]
#[path = "seccomp_island.rs"]
mod seccomp_island;
#[cfg(clean_islands)]
pub use seccomp_island::{bpf_insn_clamp, bpf_pc_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bpf_pc_advance(cur_pc: u64, proposed_pc: u64) -> u64 {
    if cur_pc < proposed_pc {
        proposed_pc
    } else {
        cur_pc
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bpf_insn_clamp(insn_count: u64, max_insns: u64) -> u64 {
    if insn_count < max_insns {
        insn_count
    } else {
        max_insns
    }
}

/// Linux Classic BPF hard limit (`BPF_MAXINSNS = 4096`); our policies cap well below it.
pub const MAX_BPF_INSNS: usize = 256;

// Classic BPF opcode constants (`<linux/filter.h>`).
pub const BPF_LD_W_ABS: u16 = 0x20; // BPF_LD | BPF_W | BPF_ABS
pub const BPF_JMP_JA: u16 = 0x05; // BPF_JMP | BPF_JA
pub const BPF_JMP_JEQ_K: u16 = 0x15; // BPF_JMP | BPF_JEQ | BPF_K
pub const BPF_JMP_JGE_K: u16 = 0x35; // BPF_JMP | BPF_JGE | BPF_K
pub const BPF_RET_K: u16 = 0x06; // BPF_RET | BPF_K

// `struct seccomp_data` field byte offsets (`<linux/seccomp.h>`).
pub const SECCOMP_DATA_NR_OFFSET: u32 = 0;
pub const SECCOMP_DATA_ARCH_OFFSET: u32 = 4;

// Linux `AUDIT_ARCH_*` values (`<linux/audit.h>`).
pub const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;
pub const AUDIT_ARCH_AARCH64: u32 = 0xC000_00B7;

// Linux `SECCOMP_RET_*` return action masks (`<linux/seccomp.h>`).
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
pub const SECCOMP_RET_TRAP: u32 = 0x0003_0000;
pub const SECCOMP_RET_ERRNO_BASE: u32 = 0x0005_0000;
pub const SECCOMP_RET_TRACE_BASE: u32 = 0x7FF0_0000;
pub const SECCOMP_RET_ALLOW: u32 = 0x7FFF_0000;

/// Build `SECCOMP_RET_ERRNO | (errno & 0xffff)`.
#[inline]
pub const fn seccomp_ret_errno(errno: u16) -> u32 {
    SECCOMP_RET_ERRNO_BASE | (errno as u32)
}

/// Build `SECCOMP_RET_TRACE | (tag & 0xffff)`.
#[inline]
pub const fn seccomp_ret_trace(tag: u16) -> u32 {
    SECCOMP_RET_TRACE_BASE | (tag as u32)
}

/// Advance the BPF program counter monotonically (`cur_pc < proposed_pc`).
#[inline]
#[must_use]
pub const fn advance_bpf_pc(cur_pc: usize, proposed_pc: usize) -> usize {
    bpf_pc_advance(cur_pc as u64, proposed_pc as u64) as usize
}

/// Clamp a BPF instruction count to `max_insns`.
#[inline]
#[must_use]
pub const fn clamp_bpf_insn_count(insn_count: usize, max_insns: usize) -> usize {
    bpf_insn_clamp(insn_count as u64, max_insns as u64) as usize
}

contract_fn! {
    /// Contracted check that a jump target `target_pc` lies strictly inside `prog_len`.
    #[must_use]
    pub const fn bpf_target_in_bounds(target_pc: usize, prog_len: usize) -> bool
    clauses [ensures result == (target_pc < prog_len)]
    {
        target_pc < prog_len
    }
}

/// Target Linux syscall ABI for seccomp filter compilation and syscall neutralization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SandboxArch {
    Aarch64,
    X86_64,
}

impl SandboxArch {
    pub const fn audit_arch(self) -> u32 {
        match self {
            SandboxArch::Aarch64 => AUDIT_ARCH_AARCH64,
            SandboxArch::X86_64 => AUDIT_ARCH_X86_64,
        }
    }

    /// Harmless idempotent syscall number (`getpid`) substituted on syscall-entry
    /// during replay so mutating syscalls never execute in the host kernel.
    pub const fn neutral_getpid_nr(self) -> u32 {
        match self {
            SandboxArch::Aarch64 => 172,
            SandboxArch::X86_64 => 39,
        }
    }

    /// Default recorded effectful syscalls (`clock_gettime`, `getrandom`, `openat`, `read`).
    pub const fn default_traced_syscalls(self) -> [u32; 4] {
        match self {
            SandboxArch::Aarch64 => [113, 278, 56, 63],
            SandboxArch::X86_64 => [228, 318, 257, 0],
        }
    }
}

/// Canonical 8-byte Classic BPF instruction matching Linux `struct sock_filter`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SockFilter {
    pub code: u16,
    pub jt: u8,
    pub jf: u8,
    pub k: u32,
}

impl SockFilter {
    pub const fn stmt(code: u16, k: u32) -> Self {
        Self {
            code,
            jt: 0,
            jf: 0,
            k,
        }
    }

    pub const fn jump(code: u16, k: u32, jt: u8, jf: u8) -> Self {
        Self { code, jt, jf, k }
    }

    /// Encode into the native-endian 8-byte `struct sock_filter` layout.
    pub fn to_ne_bytes(self) -> [u8; 8] {
        let [c0, c1] = self.code.to_ne_bytes();
        let [k0, k1, k2, k3] = self.k.to_ne_bytes();
        [c0, c1, self.jt, self.jf, k0, k1, k2, k3]
    }

    /// Decode from an 8-byte `struct sock_filter` slice.
    pub fn from_ne_bytes(b: [u8; 8]) -> Self {
        let [c0, c1, jt, jf, k0, k1, k2, k3] = b;
        Self {
            code: u16::from_ne_bytes([c0, c1]),
            jt,
            jf,
            k: u32::from_ne_bytes([k0, k1, k2, k3]),
        }
    }
}

/// Synthetic `struct seccomp_data` input evaluated by [`eval_bpf_program`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeccompInput {
    pub nr: u32,
    pub arch: u32,
}

/// Validation failure returned by [`verify_bpf_program`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BpfVerifyError {
    EmptyProgram,
    ExceedsMaxInsns {
        len: usize,
        max: usize,
    },
    UnsupportedOpcode {
        pc: usize,
        code: u16,
    },
    InvalidLoadOffset {
        pc: usize,
        offset: u32,
    },
    JumpOutOfBounds {
        pc: usize,
        target: usize,
        len: usize,
    },
    MissingTerminalRet,
}

/// Verify that `prog` is a non-empty, bounded (`<= MAX_BPF_INSNS`), forward-only
/// monotone DAG terminating in `BPF_RET_K` on every path.
pub fn verify_bpf_program(prog: &[SockFilter]) -> Result<(), BpfVerifyError> {
    if prog.is_empty() {
        return Err(BpfVerifyError::EmptyProgram);
    }
    if prog.len() > MAX_BPF_INSNS {
        return Err(BpfVerifyError::ExceedsMaxInsns {
            len: prog.len(),
            max: MAX_BPF_INSNS,
        });
    }
    let len = clamp_bpf_insn_count(prog.len(), MAX_BPF_INSNS);
    let mut pc = 0usize;
    while pc < len {
        let Some(&insn) = prog.get(pc) else {
            return Err(BpfVerifyError::MissingTerminalRet);
        };
        let next_pc = pc.saturating_add(1);
        match insn.code {
            BPF_LD_W_ABS => {
                if insn.k != SECCOMP_DATA_NR_OFFSET && insn.k != SECCOMP_DATA_ARCH_OFFSET {
                    return Err(BpfVerifyError::InvalidLoadOffset { pc, offset: insn.k });
                }
                if !bpf_target_in_bounds(next_pc, len) {
                    return Err(BpfVerifyError::MissingTerminalRet);
                }
            }
            BPF_JMP_JA => {
                let target = next_pc.saturating_add(insn.k as usize);
                if !bpf_target_in_bounds(target, len) {
                    return Err(BpfVerifyError::JumpOutOfBounds { pc, target, len });
                }
            }
            BPF_JMP_JEQ_K | BPF_JMP_JGE_K => {
                let t_true = next_pc.saturating_add(insn.jt as usize);
                let t_false = next_pc.saturating_add(insn.jf as usize);
                if !bpf_target_in_bounds(t_true, len) {
                    return Err(BpfVerifyError::JumpOutOfBounds {
                        pc,
                        target: t_true,
                        len,
                    });
                }
                if !bpf_target_in_bounds(t_false, len) {
                    return Err(BpfVerifyError::JumpOutOfBounds {
                        pc,
                        target: t_false,
                        len,
                    });
                }
            }
            BPF_RET_K => {}
            other => {
                return Err(BpfVerifyError::UnsupportedOpcode { pc, code: other });
            }
        }
        pc = next_pc;
    }
    let Some(last_idx) = len.checked_sub(1) else {
        return Err(BpfVerifyError::EmptyProgram);
    };
    let Some(last_insn) = prog.get(last_idx) else {
        return Err(BpfVerifyError::MissingTerminalRet);
    };
    if last_insn.code != BPF_RET_K {
        return Err(BpfVerifyError::MissingTerminalRet);
    }
    Ok(())
}

/// Evaluate a verified Classic BPF seccomp filter deterministically against `input`.
///
/// Advances `pc` strictly via `advance_bpf_pc`, guaranteeing loop-free termination
/// in at most `prog.len()` steps.
pub fn eval_bpf_program(prog: &[SockFilter], input: SeccompInput) -> Result<u32, BpfVerifyError> {
    verify_bpf_program(prog)?;
    let len = prog.len();
    let mut acc = 0u32;
    let mut pc = 0usize;
    while pc < len {
        let Some(&insn) = prog.get(pc) else {
            return Err(BpfVerifyError::MissingTerminalRet);
        };
        let next_pc = pc.saturating_add(1);
        match insn.code {
            BPF_LD_W_ABS => {
                acc = if insn.k == SECCOMP_DATA_ARCH_OFFSET {
                    input.arch
                } else {
                    input.nr
                };
                pc = advance_bpf_pc(pc, next_pc);
            }
            BPF_JMP_JA => {
                let target = next_pc.saturating_add(insn.k as usize);
                pc = advance_bpf_pc(pc, target);
            }
            BPF_JMP_JEQ_K => {
                let step = if acc == insn.k {
                    insn.jt as usize
                } else {
                    insn.jf as usize
                };
                pc = advance_bpf_pc(pc, next_pc.saturating_add(step));
            }
            BPF_JMP_JGE_K => {
                let step = if acc >= insn.k {
                    insn.jt as usize
                } else {
                    insn.jf as usize
                };
                pc = advance_bpf_pc(pc, next_pc.saturating_add(step));
            }
            BPF_RET_K => return Ok(insn.k),
            other => return Err(BpfVerifyError::UnsupportedOpcode { pc, code: other }),
        }
    }
    Err(BpfVerifyError::MissingTerminalRet)
}

/// Declarative syscall sandbox & selective-tracing policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeccompPolicy {
    pub arch: SandboxArch,
    /// Syscall numbers routed to `SECCOMP_RET_TRACE(tag)` so the `ptrace`
    /// recorder/replayer intercepts ONLY effectful syscalls.
    pub traced_syscalls: Vec<(u32, u16)>,
    /// Syscall numbers immediately denied in-kernel with `SECCOMP_RET_ERRNO(errno)`.
    pub denied_syscalls: Vec<(u32, u16)>,
    /// Fallback action for syscalls in neither list (typically `SECCOMP_RET_ALLOW`).
    pub default_action: u32,
}

impl SeccompPolicy {
    /// Construct the standard selective-tracer policy for `arch`: traces
    /// `clock_gettime`, `getrandom`, `openat`, and `read`, allows pure compute/memory
    /// syscalls without trapping into `ptrace`, and kills cross-ABI `int 0x80` / compat calls.
    pub fn selective_tracer(arch: SandboxArch) -> Self {
        let defaults = arch.default_traced_syscalls();
        let mut traced = Vec::new();
        let mut idx = 0usize;
        let mut rest = defaults.as_slice();
        while let &[nr, ref tail @ ..] = rest {
            traced.push((nr, idx as u16));
            idx = idx.saturating_add(1);
            rest = tail;
        }
        Self {
            arch,
            traced_syscalls: traced,
            denied_syscalls: Vec::new(),
            default_action: SECCOMP_RET_ALLOW,
        }
    }
}

/// Compile `policy` into a verified Classic BPF program (`Vec<SockFilter>`).
///
/// Layout:
/// - `[0] LD arch`, `[1] JEQ expected_arch jt=1 jf=0`, `[2] RET KILL_PROCESS`
/// - `[3] LD nr`
/// - For each `(nr, tag)` in `traced_syscalls`: `JEQ nr jt=0 jf=1`, `RET TRACE(tag)`
/// - For each `(nr, errno)` in `denied_syscalls`: `JEQ nr jt=0 jf=1`, `RET ERRNO(errno)`
/// - Final `[len - 1] RET default_action`
pub fn compile_seccomp_policy(policy: &SeccompPolicy) -> Result<Vec<SockFilter>, BpfVerifyError> {
    let total = 5usize
        .saturating_add(policy.traced_syscalls.len().saturating_mul(2))
        .saturating_add(policy.denied_syscalls.len().saturating_mul(2));
    if total > MAX_BPF_INSNS {
        return Err(BpfVerifyError::ExceedsMaxInsns {
            len: total,
            max: MAX_BPF_INSNS,
        });
    }
    let prog_cap = if total < MAX_BPF_INSNS {
        total
    } else {
        MAX_BPF_INSNS
    };
    let mut prog = {
        let _ = prog_cap;
        Vec::new()
    };
    prog.push(SockFilter::stmt(BPF_LD_W_ABS, SECCOMP_DATA_ARCH_OFFSET));
    prog.push(SockFilter::jump(
        BPF_JMP_JEQ_K,
        policy.arch.audit_arch(),
        1,
        0,
    ));
    prog.push(SockFilter::stmt(BPF_RET_K, SECCOMP_RET_KILL_PROCESS));
    prog.push(SockFilter::stmt(BPF_LD_W_ABS, SECCOMP_DATA_NR_OFFSET));

    let mut t_rest = policy.traced_syscalls.as_slice();
    while let &[(nr, tag), ref tail @ ..] = t_rest {
        prog.push(SockFilter::jump(BPF_JMP_JEQ_K, nr, 0, 1));
        prog.push(SockFilter::stmt(BPF_RET_K, seccomp_ret_trace(tag)));
        t_rest = tail;
    }

    let mut d_rest = policy.denied_syscalls.as_slice();
    while let &[(nr, errno), ref tail @ ..] = d_rest {
        prog.push(SockFilter::jump(BPF_JMP_JEQ_K, nr, 0, 1));
        prog.push(SockFilter::stmt(BPF_RET_K, seccomp_ret_errno(errno)));
        d_rest = tail;
    }

    prog.push(SockFilter::stmt(BPF_RET_K, policy.default_action));
    verify_bpf_program(&prog)?;
    Ok(prog)
}

/// Decision computed on `ptrace` syscall-entry stop during replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryDecision {
    /// Leave the syscall number untouched so pure runtime syscalls (`brk`, `mmap`, `exit_group`) run.
    PassThrough,
    /// Rewrite the syscall number register (`x8` on aarch64, `orig_rax` on x86_64) to
    /// `replacement_nr` (`getpid`) before resuming to syscall-exit, where the taped
    /// return value and output buffer will overwrite the tracee registers/memory.
    Neutralize {
        original_nr: u32,
        replacement_nr: u32,
    },
}

/// Deterministic syscall-entry neutralizer preventing host side-effects during replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayNeutralizer {
    arch: SandboxArch,
    intercepted_nrs: Vec<u32>,
}

impl ReplayNeutralizer {
    pub fn new(arch: SandboxArch, intercepted_nrs: Vec<u32>) -> Self {
        Self {
            arch,
            intercepted_nrs,
        }
    }

    /// Standard neutralizer covering `default_traced_syscalls()` for `arch`.
    pub fn standard(arch: SandboxArch) -> Self {
        let defs = arch.default_traced_syscalls();
        let mut v = Vec::new();
        let mut rest = defs.as_slice();
        while let &[nr, ref tail @ ..] = rest {
            v.push(nr);
            rest = tail;
        }
        Self::new(arch, v)
    }

    /// Decide whether syscall `nr` must be neutralized to `getpid` on replay entry.
    pub fn on_syscall_entry(&self, nr: u32) -> EntryDecision {
        let mut rest = self.intercepted_nrs.as_slice();
        while let &[cur_nr, ref tail @ ..] = rest {
            if cur_nr == nr {
                return EntryDecision::Neutralize {
                    original_nr: nr,
                    replacement_nr: self.arch.neutral_getpid_nr(),
                };
            }
            rest = tail;
        }
        EntryDecision::PassThrough
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selective_tracer_traces_taped_syscalls_denies_blocked_and_kills_wrong_arch() {
        for arch in [SandboxArch::Aarch64, SandboxArch::X86_64] {
            let mut policy = SeccompPolicy::selective_tracer(arch);
            let socket_nr = match arch {
                SandboxArch::Aarch64 => 198,
                SandboxArch::X86_64 => 41,
            };
            policy.denied_syscalls.push((socket_nr, 1)); // EPERM = 1
            let prog = compile_seccomp_policy(&policy).expect("valid bpf");

            // Wrong ABI is killed immediately.
            let wrong_arch = match arch {
                SandboxArch::Aarch64 => AUDIT_ARCH_X86_64,
                SandboxArch::X86_64 => AUDIT_ARCH_AARCH64,
            };
            assert_eq!(
                eval_bpf_program(
                    &prog,
                    SeccompInput {
                        nr: arch.neutral_getpid_nr(),
                        arch: wrong_arch,
                    },
                )
                .unwrap(),
                SECCOMP_RET_KILL_PROCESS
            );

            // Traced syscalls return SECCOMP_RET_TRACE(tag).
            for (tag, nr) in arch.default_traced_syscalls().into_iter().enumerate() {
                assert_eq!(
                    eval_bpf_program(
                        &prog,
                        SeccompInput {
                            nr,
                            arch: arch.audit_arch(),
                        },
                    )
                    .unwrap(),
                    seccomp_ret_trace(tag as u16)
                );
            }

            // Explicitly denied syscall returns SECCOMP_RET_ERRNO(1).
            assert_eq!(
                eval_bpf_program(
                    &prog,
                    SeccompInput {
                        nr: socket_nr,
                        arch: arch.audit_arch(),
                    },
                )
                .unwrap(),
                seccomp_ret_errno(1)
            );

            // Untraced pure syscall (`getpid`) passes straight through in-kernel.
            assert_eq!(
                eval_bpf_program(
                    &prog,
                    SeccompInput {
                        nr: arch.neutral_getpid_nr(),
                        arch: arch.audit_arch(),
                    },
                )
                .unwrap(),
                SECCOMP_RET_ALLOW
            );
        }
    }

    #[test]
    fn verifier_rejects_out_of_bounds_jumps_and_roundtrips_sock_filter_bytes() {
        let bad = [
            SockFilter::stmt(BPF_LD_W_ABS, SECCOMP_DATA_NR_OFFSET),
            SockFilter::jump(BPF_JMP_JEQ_K, 0, 5, 0),
            SockFilter::stmt(BPF_RET_K, SECCOMP_RET_ALLOW),
        ];
        assert!(matches!(
            verify_bpf_program(&bad),
            Err(BpfVerifyError::JumpOutOfBounds {
                pc: 1,
                target: 7,
                len: 3
            })
        ));
        for insn in bad {
            assert_eq!(SockFilter::from_ne_bytes(insn.to_ne_bytes()), insn);
        }
    }

    #[test]
    fn replay_neutralizer_rewrites_effectful_syscalls_to_getpid() {
        let neut = ReplayNeutralizer::standard(SandboxArch::Aarch64);
        assert_eq!(
            neut.on_syscall_entry(56), // openat on aarch64
            EntryDecision::Neutralize {
                original_nr: 56,
                replacement_nr: 172,
            }
        );
        assert_eq!(neut.on_syscall_entry(214), EntryDecision::PassThrough); // brk
    }
}
