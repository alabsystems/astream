// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Linux `seccomp-bpf` (`sock_filter`) intercepted-set bytecode compiler, in-Rust BPF virtual
//! machine verifier, and `SECCOMP_RET_TRACE` replay syscall neutralizer
//! (`Astream.Retire.TlaSeccompNeutralize`).
//!
//! Solves two foreign-process replay gaps:
//! 1. **Narrowed `seccomp-bpf` interception:** compiles a deterministic classic BPF program
//!    over `seccomp_data` (`arch` at offset `4`, `nr` at offset `0`) for `x86_64` or `aarch64`
//!    that returns `SECCOMP_RET_TRACE` ONLY for intercepted effect syscalls (`clock_gettime`,
//!    `getrandom`, `openat`, `read`, `close`), `SECCOMP_RET_ALLOW` for every pure compute /
//!    memory syscall, and `SECCOMP_RET_KILL_PROCESS` on unexpected architecture ABI switch.
//! 2. **True replay syscall neutralization:** computes the `PTRACE_EVENT_SECCOMP` register
//!    mutation (`orig_rax = u64::MAX` on `x86_64` / `x8 = -1` on `aarch64`) so the Linux kernel
//!    skips host syscall execution (`-ENOSYS`) and overwrites the return register + output
//!    buffer (clamped via Clean-origin `sc_buf_clamp`) from the recorded `EffectRecord` tape!

#[cfg(clean_islands)]
#[path = "seccomp_neutralize_island.rs"]
mod seccomp_neutralize_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sc_buf_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sc_cursor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use seccomp_neutralize_island::{sc_buf_clamp, sc_cursor_advance};

/// Linux `AUDIT_ARCH_X86_64`.
pub const AUDIT_ARCH_X86_64: u32 = 0xC000_003E;
/// Linux `AUDIT_ARCH_AARCH64`.
pub const AUDIT_ARCH_AARCH64: u32 = 0xC000_00B7;
/// `SECCOMP_RET_KILL_PROCESS` (`0x8000_0000`).
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
/// `SECCOMP_RET_TRACE` base (`0x7FF0_0000`).
pub const SECCOMP_RET_TRACE_BASE: u32 = 0x7FF0_0000;
/// `SECCOMP_RET_ALLOW` (`0x7FFF_0000`).
pub const SECCOMP_RET_ALLOW: u32 = 0x7FFF_0000;
/// Maximum bytes injected per neutralized `read` / `getrandom` replay step.
pub const MAX_INJECTED_SYSCALL_BUF: u64 = 65_536;

const BPF_LD_W_ABS: u16 = 0x20;
const BPF_JMP_JEQ_K: u16 = 0x15;
const BPF_RET_K: u16 = 0x06;

contract_fn! {
    /// Verified check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sc_neutralized_isl`.
    #[must_use]
    pub const fn sc_neutralized(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Target Linux syscall ABI for `seccomp-bpf` generation and register neutralization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinuxSyscallArch {
    X86_64,
    Aarch64,
}

impl LinuxSyscallArch {
    #[must_use]
    pub const fn audit_arch(self) -> u32 {
        match self {
            Self::X86_64 => AUDIT_ARCH_X86_64,
            Self::Aarch64 => AUDIT_ARCH_AARCH64,
        }
    }

    /// Canonical `(clock_gettime, getrandom, openat, read, close)` syscall numbers on this ABI.
    #[must_use]
    pub const fn effect_syscall_nrs(self) -> [u32; 5] {
        match self {
            Self::X86_64 => [228, 318, 257, 0, 3],
            Self::Aarch64 => [113, 278, 56, 63, 57],
        }
    }

    /// Sentinel syscall number (`u64::MAX`, `-1`) written at `PTRACE_EVENT_SECCOMP` stop to
    /// neutralize host kernel execution.
    #[must_use]
    pub const fn skip_syscall_sentinel(self) -> u64 {
        let _ = self;
        u64::MAX
    }
}

/// Classic Linux `struct sock_filter` instruction (`8` bytes on wire).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SockFilterInsn {
    pub code: u16,
    pub jt: u8,
    pub jf: u8,
    pub k: u32,
}

impl SockFilterInsn {
    /// Encodes the instruction as an 8-byte native/little-endian `sock_filter` struct.
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 8] {
        let [c0, c1] = self.code.to_le_bytes();
        let [k0, k1, k2, k3] = self.k.to_le_bytes();
        [c0, c1, self.jt, self.jf, k0, k1, k2, k3]
    }
}

/// Maximum instructions accepted by the pure-Rust classic BPF verifier.
pub const MAX_BPF_INSNS: usize = 4096;

/// Compiles the deterministic 11-instruction `seccomp-bpf` filter for `arch`.
#[must_use]
#[allow(clippy::vec_init_then_push)]
pub fn compile_effect_seccomp_filter(arch: LinuxSyscallArch) -> Vec<SockFilterInsn> {
    let [n0, n1, n2, n3, n4] = arch.effect_syscall_nrs();
    let mut prog = Vec::new();
    // 0: A = seccomp_data.arch (offset 4)
    prog.push(SockFilterInsn {
        code: BPF_LD_W_ABS,
        jt: 0,
        jf: 0,
        k: 4,
    });
    // 1: if A == audit_arch goto 3 else goto 2
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 1,
        jf: 0,
        k: arch.audit_arch(),
    });
    // 2: kill process on foreign ABI (e.g. int 0x80 ia32 compat bypass)
    prog.push(SockFilterInsn {
        code: BPF_RET_K,
        jt: 0,
        jf: 0,
        k: SECCOMP_RET_KILL_PROCESS,
    });
    // 3: A = seccomp_data.nr (offset 0)
    prog.push(SockFilterInsn {
        code: BPF_LD_W_ABS,
        jt: 0,
        jf: 0,
        k: 0,
    });
    // 4..=8: compare each of the 5 effect syscalls -> jump to TRACE return (index 10)
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 5,
        jf: 0,
        k: n0,
    });
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 4,
        jf: 0,
        k: n1,
    });
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 3,
        jf: 0,
        k: n2,
    });
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 2,
        jf: 0,
        k: n3,
    });
    prog.push(SockFilterInsn {
        code: BPF_JMP_JEQ_K,
        jt: 1,
        jf: 0,
        k: n4,
    });
    // 9: pure compute/memory syscall -> ALLOW without ptrace context switch!
    prog.push(SockFilterInsn {
        code: BPF_RET_K,
        jt: 0,
        jf: 0,
        k: SECCOMP_RET_ALLOW,
    });
    // 10: intercepted effect syscall -> PTRACE_EVENT_SECCOMP trace stop
    prog.push(SockFilterInsn {
        code: BPF_RET_K,
        jt: 0,
        jf: 0,
        k: SECCOMP_RET_TRACE_BASE | 1,
    });
    prog
}

/// Evaluates a compiled `sock_filter` program on `(nr, arch)` in pure Rust.
pub fn eval_seccomp_bpf(prog: &[SockFilterInsn], nr: u32, arch: u32) -> Result<u32, &'static str> {
    if prog.is_empty() || prog.len() > MAX_BPF_INSNS {
        return Err("invalid bpf program length");
    }
    let mut pc = 0usize;
    let mut acc = 0u32;
    let mut steps = 0usize;
    while steps <= prog.len() {
        let Some(&insn) = prog.get(pc) else {
            break;
        };
        steps = steps.saturating_add(1);
        match insn.code {
            BPF_LD_W_ABS => {
                acc = match insn.k {
                    0 => nr,
                    4 => arch,
                    _ => return Err("unsupported seccomp_data offset"),
                };
                pc = pc.saturating_add(1);
            }
            BPF_JMP_JEQ_K => {
                let hop = if acc == insn.k {
                    insn.jt as usize
                } else {
                    insn.jf as usize
                };
                pc = pc.saturating_add(1).saturating_add(hop);
            }
            BPF_RET_K => return Ok(insn.k),
            _ => return Err("unsupported bpf opcode"),
        }
    }
    Err("bpf program did not terminate")
}

/// Register + memory injection plan applied by the tracer at `PTRACE_EVENT_SECCOMP` during replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NeutralizedSyscallPlan {
    /// Syscall number register written before resuming (`u64::MAX` -> kernel skips execution!).
    pub neutralized_nr: u64,
    /// Return value register written at syscall-exit (`rax` / `x0`).
    pub injected_ret: i64,
    /// Clamped output bytes written into tracee's destination buffer (`<= tracee_buf_cap`).
    pub injected_bytes: Vec<u8>,
    /// Updated monotone tape cursor (`sc_cursor_advance`).
    pub next_tape_cursor: u64,
}

/// Stateful foreign-process replay neutralizer.
#[derive(Debug, Clone)]
pub struct SeccompReplayNeutralizer {
    arch: LinuxSyscallArch,
    tape_cursor: u64,
}

impl SeccompReplayNeutralizer {
    #[must_use]
    pub const fn new(arch: LinuxSyscallArch) -> Self {
        Self {
            arch,
            tape_cursor: 0,
        }
    }

    #[must_use]
    pub const fn tape_cursor(&self) -> u64 {
        self.tape_cursor
    }

    /// Produces a neutralized syscall plan for a taped output buffer, refusing over-buffer
    /// tapes fail-closed (`!sc_neutralized(tracee_buf_cap, taped_len)`).
    pub fn plan_buffer_injection(
        &mut self,
        taped_bytes: &[u8],
        tracee_buf_cap: u64,
    ) -> Result<NeutralizedSyscallPlan, &'static str> {
        let clamped_cap = sc_buf_clamp(tracee_buf_cap, MAX_INJECTED_SYSCALL_BUF);
        let taped_len = taped_bytes.len() as u64;
        if !sc_neutralized(clamped_cap, taped_len) {
            return Err("taped syscall payload exceeds tracee destination buffer");
        }
        let next = sc_cursor_advance(self.tape_cursor, self.tape_cursor.saturating_add(1));
        self.tape_cursor = next;
        let mut injected = Vec::new();
        injected.extend_from_slice(taped_bytes);
        Ok(NeutralizedSyscallPlan {
            neutralized_nr: self.arch.skip_syscall_sentinel(),
            injected_ret: taped_len as i64,
            injected_bytes: injected,
            next_tape_cursor: next,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bpf_filter_traces_exact_effect_set_kills_foreign_arch_and_neutralizes_replay() {
        for arch in [LinuxSyscallArch::X86_64, LinuxSyscallArch::Aarch64] {
            let prog = compile_effect_seccomp_filter(arch);
            assert_eq!(prog.len(), 11);
            assert_eq!(prog[0].to_le_bytes().len(), 8);
            for nr in arch.effect_syscall_nrs() {
                assert_eq!(
                    eval_seccomp_bpf(&prog, nr, arch.audit_arch()).unwrap(),
                    SECCOMP_RET_TRACE_BASE | 1
                );
            }
            // Non-effect syscalls (write=1/64, mmap=9/222, futex=202/98) run at native speed!
            for allow_nr in [9u32, 39, 98, 202, 222] {
                assert_eq!(
                    eval_seccomp_bpf(&prog, allow_nr, arch.audit_arch()).unwrap(),
                    SECCOMP_RET_ALLOW
                );
            }
            // Foreign arch is killed immediately (prevents x86 int 0x80 ABI confusion).
            assert_eq!(
                eval_seccomp_bpf(&prog, 0, 0x4000_0003).unwrap(),
                SECCOMP_RET_KILL_PROCESS
            );
        }

        let mut neut = SeccompReplayNeutralizer::new(LinuxSyscallArch::X86_64);
        assert!(neut.plan_buffer_injection(b"hello world", 4).is_err());
        assert_eq!(neut.tape_cursor(), 0);
        let plan = neut.plan_buffer_injection(b"taped-rng", 64).unwrap();
        assert_eq!(plan.neutralized_nr, u64::MAX);
        assert_eq!(plan.injected_ret, 9);
        assert_eq!(plan.injected_bytes, b"taped-rng");
        assert_eq!(plan.next_tape_cursor, 1);
    }
}
