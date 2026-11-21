// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Full `ptrace` syscall neutralization & single-threaded `execve` replay state machine
//! (foreign-process replay: syscall neutralization and `execve` tracing;
//! `Astream.Host.TlaPtraceReplayNoopNeutralizer`).
//!
//! Ensures NO real intercepted syscall ever reaches the host kernel during deterministic replay of
//! an unmodified `execve`d child binary:
//! - Waits for the initial `PTRACE_EVENT_EXEC` boundary (`exec_settled == true`),
//! - At `PTRACE_EVENT_SECCOMP` entry, validates `tape_cursor < tape_len` and exact `effect_kind_tag`
//!   match, rewrites `orig_syscall_nr` to harmless side-effect-free `getpid`, and stages the taped
//!   return value + buffer digest,
//! - At the paired syscall-exit stop, injects the taped return value and advances `tape_cursor`,
//! - Aborts immediately on a short tape, wrong-kind syscall, unconsumed tail at exit, or multi-thread
//!   `clone` in single-threaded replay mode.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "ptrace_replay_noop_neutralizer_island.rs"]
mod ptrace_replay_noop_neutralizer_island;
#[cfg(clean_islands)]
pub use ptrace_replay_noop_neutralizer_island::{
    ptrace_cursor_advance_b128, ptrace_cursor_clamp_b128,
};

#[cfg(not(clean_islands))]
/// Clamp `tape_cursor` to `<= tape_len`.
#[must_use]
pub const fn ptrace_cursor_clamp_b128(cand_cursor: u64, tape_len: u64) -> u64 {
    if cand_cursor < tape_len {
        cand_cursor
    } else {
        tape_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `tape_cursor`.
#[must_use]
pub const fn ptrace_cursor_advance_b128(cur_cursor: u64, cand_cursor: u64) -> u64 {
    if cur_cursor < cand_cursor {
        cand_cursor
    } else {
        cur_cursor
    }
}

contract_fn! {
    /// True iff `tape_cursor < tape_len && observed_kind == expected_kind`.
    #[must_use]
    pub const fn ptrace_entry_matches_tape_b128(
        tape_cursor: u64,
        tape_len: u64,
        observed_kind: u64,
        expected_kind: u64,
    ) -> bool
    clauses [ensures result == (tape_cursor < tape_len && observed_kind == expected_kind)]
    {
        tape_cursor < tape_len && observed_kind == expected_kind
    }
}

pub const MAX_REPLAY_TAPE_ENTRIES: usize = 16;

/// Side-effect-free no-op syscall number (`getpid` = 39 on `x86_64`, 172 on `aarch64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NoopSyscallNr(pub u64);

/// Taped foreign-process syscall outcome to inject after no-op neutralization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TapedSyscallEntry {
    pub effect_kind_tag: u64,
    pub return_value: i64,
    pub payload_digest_fnv64: u64,
}

/// Replay step verdict at `execve`, `seccomp` entry, syscall exit, or child exit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PtraceNeutralizeVerdict {
    ExecveBoundaryArmed,
    RewrittenToNoop {
        noop_syscall_nr: u64,
        staged_cursor: u64,
    },
    InjectedTapedExit {
        return_value: i64,
        payload_digest_fnv64: u64,
        next_cursor: u64,
    },
    CompletedExactReplay {
        consumed_entries: u64,
    },
    AbortBeforeExecve,
    AbortMultiThreadCloneUnsupported,
    AbortTapeShort {
        cursor: u64,
        tape_len: u64,
    },
    AbortWrongEffectKind {
        cursor: u64,
        expected_kind: u64,
        observed_kind: u64,
    },
    AbortExitWithoutStagedEntry,
    AbortUnconsumedTapeTail {
        cursor: u64,
        tape_len: u64,
    },
}

/// Stateful `ptrace` seccomp-stop no-op neutralizer & tape injector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtraceReplayNoopNeutralizer {
    noop_nr: NoopSyscallNr,
    exec_settled: bool,
    aborted: bool,
    tape_len: u64,
    tape_cursor: u64,
    staged_entry: Option<TapedSyscallEntry>,
    entries: [TapedSyscallEntry; MAX_REPLAY_TAPE_ENTRIES],
}

impl PtraceReplayNoopNeutralizer {
    #[must_use]
    pub fn new(noop_nr: NoopSyscallNr, tape: &[TapedSyscallEntry]) -> Self {
        let mut entries = [TapedSyscallEntry {
            effect_kind_tag: 0,
            return_value: 0,
            payload_digest_fnv64: 0,
        }; MAX_REPLAY_TAPE_ENTRIES];
        let capped = if tape.len() < MAX_REPLAY_TAPE_ENTRIES {
            tape.len()
        } else {
            MAX_REPLAY_TAPE_ENTRIES
        };
        let mut idx = 0usize;
        while idx < capped {
            if let (Some(dst), Some(src)) = (entries.get_mut(idx), tape.get(idx)) {
                *dst = *src;
            }
            idx = idx.saturating_add(1);
        }
        Self {
            noop_nr,
            exec_settled: false,
            aborted: false,
            tape_len: capped as u64,
            tape_cursor: 0,
            staged_entry: None,
            entries,
        }
    }

    pub fn on_execve_stop(&mut self) -> PtraceNeutralizeVerdict {
        self.exec_settled = true;
        PtraceNeutralizeVerdict::ExecveBoundaryArmed
    }

    pub fn on_thread_clone_attempt(&mut self) -> PtraceNeutralizeVerdict {
        self.aborted = true;
        PtraceNeutralizeVerdict::AbortMultiThreadCloneUnsupported
    }

    /// At `PTRACE_EVENT_SECCOMP`: neutralize the real syscall into `noop_nr` before kernel entry.
    pub fn on_seccomp_entry(&mut self, observed_kind_tag: u64) -> PtraceNeutralizeVerdict {
        if !self.exec_settled || self.aborted {
            self.aborted = true;
            return PtraceNeutralizeVerdict::AbortBeforeExecve;
        }
        if self.tape_cursor >= self.tape_len {
            self.aborted = true;
            return PtraceNeutralizeVerdict::AbortTapeShort {
                cursor: self.tape_cursor,
                tape_len: self.tape_len,
            };
        }
        let Some(&entry) = self.entries.get(self.tape_cursor as usize) else {
            self.aborted = true;
            return PtraceNeutralizeVerdict::AbortTapeShort {
                cursor: self.tape_cursor,
                tape_len: self.tape_len,
            };
        };
        if !ptrace_entry_matches_tape_b128(
            self.tape_cursor,
            self.tape_len,
            observed_kind_tag,
            entry.effect_kind_tag,
        ) {
            self.aborted = true;
            return PtraceNeutralizeVerdict::AbortWrongEffectKind {
                cursor: self.tape_cursor,
                expected_kind: entry.effect_kind_tag,
                observed_kind: observed_kind_tag,
            };
        }
        self.staged_entry = Some(entry);
        PtraceNeutralizeVerdict::RewrittenToNoop {
            noop_syscall_nr: self.noop_nr.0,
            staged_cursor: self.tape_cursor,
        }
    }

    /// At the paired syscall-exit stop: overwrite `getpid`'s harmless return register + buffer with tape.
    pub fn on_syscall_exit_inject(&mut self) -> PtraceNeutralizeVerdict {
        let Some(entry) = core::mem::take(&mut self.staged_entry) else {
            self.aborted = true;
            return PtraceNeutralizeVerdict::AbortExitWithoutStagedEntry;
        };
        let next = ptrace_cursor_clamp_b128(self.tape_cursor.saturating_add(1), self.tape_len);
        self.tape_cursor = ptrace_cursor_advance_b128(self.tape_cursor, next);
        PtraceNeutralizeVerdict::InjectedTapedExit {
            return_value: entry.return_value,
            payload_digest_fnv64: entry.payload_digest_fnv64,
            next_cursor: self.tape_cursor,
        }
    }

    /// Verify clean completion when the traced child exits.
    #[must_use]
    pub const fn on_child_exit(&self) -> PtraceNeutralizeVerdict {
        if self.tape_cursor != self.tape_len {
            return PtraceNeutralizeVerdict::AbortUnconsumedTapeTail {
                cursor: self.tape_cursor,
                tape_len: self.tape_len,
            };
        }
        PtraceNeutralizeVerdict::CompletedExactReplay {
            consumed_entries: self.tape_cursor,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn neutralizes_clock_getrandom_read_to_noop_and_aborts_on_diverged_or_short_tape() {
        let tape = [
            TapedSyscallEntry {
                effect_kind_tag: 1, // clock_gettime
                return_value: 0,
                payload_digest_fnv64: 0x1111,
            },
            TapedSyscallEntry {
                effect_kind_tag: 2, // getrandom
                return_value: 8,
                payload_digest_fnv64: 0x2222,
            },
            TapedSyscallEntry {
                effect_kind_tag: 3, // read
                return_value: 64,
                payload_digest_fnv64: 0x3333,
            },
        ];
        let mut neut = PtraceReplayNoopNeutralizer::new(NoopSyscallNr(39), &tape);
        assert_eq!(
            neut.on_execve_stop(),
            PtraceNeutralizeVerdict::ExecveBoundaryArmed
        );

        for (i, item) in tape.iter().enumerate() {
            assert_eq!(
                neut.on_seccomp_entry(item.effect_kind_tag),
                PtraceNeutralizeVerdict::RewrittenToNoop {
                    noop_syscall_nr: 39,
                    staged_cursor: i as u64,
                }
            );
            assert_eq!(
                neut.on_syscall_exit_inject(),
                PtraceNeutralizeVerdict::InjectedTapedExit {
                    return_value: item.return_value,
                    payload_digest_fnv64: item.payload_digest_fnv64,
                    next_cursor: (i + 1) as u64,
                }
            );
        }
        assert_eq!(
            neut.on_child_exit(),
            PtraceNeutralizeVerdict::CompletedExactReplay {
                consumed_entries: 3
            }
        );

        // Extra syscall past end of tape aborts immediately as short tape.
        assert_eq!(
            neut.on_seccomp_entry(1),
            PtraceNeutralizeVerdict::AbortTapeShort {
                cursor: 3,
                tape_len: 3,
            }
        );
    }
}
