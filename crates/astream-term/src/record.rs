//! The minimal session record model the screen folds over.
//!
//! The fold itself carries no offsets: records are processed in order and each
//! record's position *is* its implicit sequence. The full wire envelope — a
//! 1-byte type tag plus `seq: Offset`, a recorded logical clock and an optional
//! `caused_by` pointer, carried inside an `astream_wire::Frame` payload — is
//! `astream-engine`'s, which wraps exactly these records.
//!
//! Only [`Record::Out`] and [`Record::Resize`] paint. [`Record::In`] (the
//! keystrokes a client proposed) and [`Record::Exit`] are recorded for audit and
//! replay of *what happened*, but the fold ignores them: input never paints —
//! only the PTY's echoed output does.

/// One recorded terminal-session event.
#[derive(Debug, Clone, Eq)]
pub enum Record {
    /// Keystrokes the host accepted and wrote to the PTY master. The fold
    /// **ignores** these: input does not paint the screen; only echoed `Out`
    /// does. Kept on the log as the (agent's) action trace.
    ///
    /// `(client_id, client_seq)` is the exactly-once idempotency key: the host
    /// dedups proposals by it, so a keystroke re-sent after a reconnect is
    /// applied at most once. It rides on the record so the dedup high-water is
    /// rebuildable from the log alone (it survives a crash/reconnect).
    In {
        /// The keystroke bytes.
        bytes: Vec<u8>,
        /// Which client proposed this input.
        client_id: u64,
        /// The client's monotonic sequence number for this keystroke.
        client_seq: u64,
    },
    /// Raw PTY-master output bytes — the only record that paints.
    Out(Vec<u8>),
    /// A terminal resize (`TIOCSWINSZ`), ordered inline with output so it
    /// replays at its exact position.
    Resize { cols: u16, rows: u16 },
    /// The child terminated; the log is sealed after this. The fold ignores it.
    Exit { code: i32 },
}

impl PartialEq for Record {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::In {
                    bytes: ba,
                    client_id: ca,
                    client_seq: sa,
                },
                Self::In {
                    bytes: bb,
                    client_id: cb,
                    client_seq: sb,
                },
            ) => ca == cb && sa == sb && ba == bb,
            (Self::Out(a), Self::Out(b)) => a == b,
            (Self::Resize { cols: ca, rows: ra }, Self::Resize { cols: cb, rows: rb }) => {
                ca == cb && ra == rb
            }
            (Self::Exit { code: a }, Self::Exit { code: b }) => a == b,
            _ => false,
        }
    }
}

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "record_island.rs"]
mod record_island;
#[cfg(not(clean_islands))]
pub use crate::twins::record_client_seq_advance;
#[cfg(clean_islands)]
pub use record_island::record_client_seq_advance;

contract_fn! {
    /// Kernel-certified check that a normalized record paint tag (`1` for
    /// [`Record::Out`] / [`Record::Resize`], `0` for [`Record::In`] / [`Record::Exit`])
    /// mutates the screen fold (`tag == 1`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `record_tag_paints_screen_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn record_tag_paints_screen(tag: u8) -> bool
    clauses [ensures result == (tag == 1)]
    {
        tag == 1
    }
}

impl Record {
    /// Whether this record mutates the screen fold (`true` for [`Record::Out`]
    /// and [`Record::Resize`]; `false` for [`Record::In`] and [`Record::Exit`]).
    #[must_use]
    pub const fn paints(&self) -> bool {
        let tag = match self {
            Record::Out(_) | Record::Resize { .. } => 1u8,
            Record::In { .. } | Record::Exit { .. } => 0u8,
        };
        record_tag_paints_screen(tag)
    }
}
