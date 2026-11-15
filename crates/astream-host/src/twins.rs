// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Plain-Rust twins of the functions this crate's Clean islands compile.
//!
//! An island (`*_island.rs`) mounts only under `cfg(clean_islands)`, which build.rs
//! sets when the compiler answers that it is Trust: no stock rustc can lex Clean. Under
//! Trust, each function an island compiles from Clean (`clean_origin_mir` I5) is the one
//! Rust calls; under every other compiler it is its twin below, written from the same
//! definition. The tests hold the twins, and whichever function a build calls, to the
//! answers the island gives, which every Trust test run re-checks against the island.

/// `pty_pending_clamp` as `driver_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn pty_pending_clamp(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
    }
}

/// `pty_drain_cap_select` as `driver_island.rs` defines it in Clean:
/// `if cap < proposed_total then reject_val else admit_val`.
#[must_use]
pub const fn pty_drain_cap_select(
    cap: u64,
    proposed_total: u64,
    reject_val: u64,
    admit_val: u64,
) -> u64 {
    if cap < proposed_total {
        reject_val
    } else {
        admit_val
    }
}

/// `pty_reap_state_advance` as `host_island.rs` defines it in Clean:
/// `if cur < settled then settled else cur`.
#[must_use]
pub const fn pty_reap_state_advance(cur: u64, settled: u64) -> u64 {
    if cur < settled {
        settled
    } else {
        cur
    }
}

/// `sys_stdio_fd_floor` as `sys_island.rs` defines it in Clean:
/// `if min_fd < fd then fd else min_fd`.
#[must_use]
pub const fn sys_stdio_fd_floor(min_fd: u64, fd: u64) -> u64 {
    if min_fd < fd {
        fd
    } else {
        min_fd
    }
}

/// `seccomp_tape_advance` as `seccomp_island.rs` defines it in Clean:
/// `if cur < cand then cand else cur`.
#[must_use]
pub const fn seccomp_tape_advance(cur: u64, cand: u64) -> u64 {
    if cur < cand {
        cand
    } else {
        cur
    }
}

/// `seccomp_buf_clamp` as `seccomp_island.rs` defines it in Clean:
/// `if len < cap then len else cap`.
#[must_use]
pub const fn seccomp_buf_clamp(len: u64, cap: u64) -> u64 {
    if len < cap {
        len
    } else {
        cap
    }
}

#[cfg(test)]
#[path = "../../astream-wire/twin_answers.rs"]
mod twin_answers;

#[cfg(test)]
mod tests {
    use super::twin_answers::answers;

    // Each function's answers over every operand tuple of `EDGES` (`twin_answers.rs`), as
    // indices into it. `crate::...` is the island's function under Trust and the twin
    // elsewhere, so every build holds the twin to the island's answers.
    #[test]
    fn the_twins_answer_as_the_islands_do() {
        let want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::driver::pty_pending_clamp(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::pty_pending_clamp(a, b)), want);
        let want =
            "012012012000111222000111222012012012012012012000111222012012012012012012012012012";
        assert_eq!(
            answers(|[a, b, c, d]| crate::driver::pty_drain_cap_select(a, b, c, d)),
            want
        );
        assert_eq!(
            answers(|[a, b, c, d]| super::pty_drain_cap_select(a, b, c, d)),
            want
        );
        let want = "012112222";
        assert_eq!(
            answers(|[a, b]| crate::host::pty_reap_state_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::pty_reap_state_advance(a, b)), want);
        assert_eq!(answers(|[a, b]| crate::sys::sys_stdio_fd_floor(a, b)), want);
        assert_eq!(answers(|[a, b]| super::sys_stdio_fd_floor(a, b)), want);
        assert_eq!(
            answers(|[a, b]| crate::seccomp::seccomp_tape_advance(a, b)),
            want
        );
        assert_eq!(answers(|[a, b]| super::seccomp_tape_advance(a, b)), want);
        let clamp_want = "000011012";
        assert_eq!(
            answers(|[a, b]| crate::seccomp::seccomp_buf_clamp(a, b)),
            clamp_want
        );
        assert_eq!(answers(|[a, b]| super::seccomp_buf_clamp(a, b)), clamp_want);
    }

    // Not vacuous: `pty_pending_clamp` with its branches swapped answers otherwise.
    #[test]
    fn a_twin_with_its_branches_swapped_answers_otherwise() {
        assert_ne!(answers(|[a, b]| if a < b { b } else { a }), "000011012");
    }
}
