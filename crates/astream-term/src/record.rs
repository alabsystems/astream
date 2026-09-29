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
#[derive(Debug, Clone, PartialEq, Eq)]
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
