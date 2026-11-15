// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! POSIX PTY `TIOCSWINSZ` resize coalescer, `termios` `ECHO` password-prompt detector, foreground `tcgetpgrp` observer, ordered `SIGHUP`->`SIGTERM`->`SIGKILL` reaper, master-fd backpressure, and `FD_CLOEXEC` hygiene. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod cloexec_fd_hygiene;
pub mod fg_pgrp_observer;
pub mod pty_backpressure_water;
pub mod teardown_escalation;
pub mod termios_echo_tracker;
pub mod winsize_coalescer;

/// Four-byte magic prefix (`"APTY"`) for a 16-byte `astream-pty-signal` winsize/signal wire header.
pub const PTY_SIGNAL_WIRE_MAGIC: [u8; 4] = *b"APTY";

/// Wire format version for `astream-pty-signal` winsize/signal headers.
pub const PTY_SIGNAL_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-pty-signal` wire header:
/// `[0..4] = b"APTY"`, `[4] = version (1)`, `[5] = stage_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = cols_rows_packed (BE)`, `[12..16] = fg_pgid (BE)`.
#[must_use]
pub const fn encode_pty_signal_wire(
    stage_tag: u8,
    cols_rows_packed: u32,
    fg_pgid: u32,
) -> Option<[u8; 16]> {
    if stage_tag > 3 || cols_rows_packed == 0 {
        return None;
    }
    Some([
        PTY_SIGNAL_WIRE_MAGIC[0],
        PTY_SIGNAL_WIRE_MAGIC[1],
        PTY_SIGNAL_WIRE_MAGIC[2],
        PTY_SIGNAL_WIRE_MAGIC[3],
        PTY_SIGNAL_WIRE_VERSION,
        stage_tag,
        0,
        0,
        ((cols_rows_packed >> 24) & 0xFF) as u8,
        ((cols_rows_packed >> 16) & 0xFF) as u8,
        ((cols_rows_packed >> 8) & 0xFF) as u8,
        (cols_rows_packed & 0xFF) as u8,
        ((fg_pgid >> 24) & 0xFF) as u8,
        ((fg_pgid >> 16) & 0xFF) as u8,
        ((fg_pgid >> 8) & 0xFF) as u8,
        (fg_pgid & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-pty-signal` wire header into
/// `(stage_tag, cols_rows_packed, fg_pgid)`.
#[must_use]
pub const fn decode_pty_signal_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'P', b'T', b'Y', PTY_SIGNAL_WIRE_VERSION, stage_tag, 0, 0, c0, c1, c2, c3, p0, p1, p2, p3, ..] =
        *buf
    else {
        return None;
    };
    let cols_rows_packed =
        ((c0 as u32) << 24) | ((c1 as u32) << 16) | ((c2 as u32) << 8) | (c3 as u32);
    let fg_pgid = ((p0 as u32) << 24) | ((p1 as u32) << 16) | ((p2 as u32) << 8) | (p3 as u32);
    if stage_tag > 3 || cols_rows_packed == 0 {
        return None;
    }
    Some((stage_tag, cols_rows_packed, fg_pgid))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pty_signal_wire_roundtrips_and_rejects_zero_geometry() {
        let Some(frame) = encode_pty_signal_wire(1, (120 << 16) | 40, 4242) else {
            panic!("valid pty signal frame should encode");
        };
        assert_eq!(
            decode_pty_signal_wire(&frame),
            Some((1, (120 << 16) | 40, 4242))
        );
        assert_eq!(encode_pty_signal_wire(1, 0, 4242), None);
        assert_eq!(encode_pty_signal_wire(4, 80, 4242), None);
        let mut bad = frame;
        bad[3] = b'Z';
        assert_eq!(decode_pty_signal_wire(&bad), None);
    }
}
