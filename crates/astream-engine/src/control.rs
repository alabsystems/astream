//! Control arbitration for a shared session: who holds the single-writer keyboard.
//!
//! A session has exactly ONE writer at a time — the *holder* of its
//! [`ControlToken`]. Every other attached client is read-only: it sees the
//! screen (the fold of `/out`) but its input is not applied. The engine
//! **enforces** this at the ingest: [`Session::apply_input_as`] takes the token
//! and refuses a non-holder's input with [`EngineError::NotHolder`] before
//! anything reaches the log, so a read-only client's keystroke leaves no trace.
//!
//! Control moves two ways. The holder hands it off with [`grant`] — only the
//! holder can, so a viewer cannot grant itself the keyboard. Any client can
//! *seize* it with [`claim`]: the explicit, unconditional "human always wins"
//! override, so an operator can always take the keyboard back from a runaway
//! orchestrator. Both leave their trace in the log the same way: the next `In`
//! carries the new holder's `client_id`.
//!
//! The token is neither `Copy` nor `Clone`. There is one per session, owned by
//! whoever owns the session, so two writers cannot be minted from one token.
//!
//! The handoff is auditable for free, with no wire change: the only inputs that
//! reach the log are the holder's, each `Record::In` carrying the `client_id` of
//! whoever held control when it was applied. So the log's `In`-client-id sequence
//! **is** the control history — replayable and forkable like everything else.
//!
//! HONEST BOUNDARY: enforcement is at the engine's token-taking ingest
//! (`apply_input_as` / `apply_input_caused_as`). The plain [`Session::apply_input`]
//! takes no token — it is the single-writer path a host uses when there is no
//! shared keyboard — and the host `Driver` still calls that one; routing the host
//! driver through the token is a follow-up in the host crate.
//!
//! [`Session::apply_input_as`]: crate::Session::apply_input_as
//! [`Session::apply_input`]: crate::Session::apply_input
//! [`grant`]: ControlToken::grant
//! [`claim`]: ControlToken::claim

use crate::log::EngineError;

/// The single-writer control token for one session. Deliberately not `Copy` or
/// `Clone`: one token, one holder, one writer — a second writer cannot be
/// minted from it (checked by this `compile_fail` doctest):
///
/// ```compile_fail
/// let token = astream_engine::ControlToken::new(1);
/// let second_writer = token.clone(); // error: no method named `clone`
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct ControlToken {
    holder: u64,
}

impl ControlToken {
    /// A token initially held by `holder` (e.g. the orchestrator).
    pub fn new(holder: u64) -> ControlToken {
        ControlToken { holder }
    }

    /// The client currently allowed to write.
    pub fn holder(&self) -> u64 {
        self.holder
    }

    /// Whether `client` may write — true iff it holds control. Every other
    /// client is read-only.
    pub fn may_write(&self, client: u64) -> bool {
        client == self.holder
    }

    /// Whether `client` is currently read-only (the negation of [`may_write`]).
    ///
    /// [`may_write`]: ControlToken::may_write
    pub fn is_read_only(&self, client: u64) -> bool {
        !self.may_write(client)
    }

    /// `Ok(())` iff `client` holds control, else [`EngineError::NotHolder`] naming
    /// the actual holder — the check the engine's ingest applies.
    pub fn check(&self, client: u64) -> Result<(), EngineError> {
        if self.may_write(client) {
            Ok(())
        } else {
            Err(EngineError::NotHolder {
                holder: self.holder,
                client,
            })
        }
    }

    /// Hand control from `by` to `to`. Only the holder can hand off: if `by` does
    /// not hold control this is [`EngineError::NotHolder`] and the holder is
    /// unchanged. (Handing off to oneself is a no-op `Ok`.)
    pub fn grant(&mut self, by: u64, to: u64) -> Result<(), EngineError> {
        self.check(by)?;
        self.holder = to;
        Ok(())
    }

    /// Seize control for `client`, whoever holds it — the explicit override a
    /// human uses to claim the keyboard from an orchestrator. Unconditional by
    /// design; the seizure is visible in the log as the next `In`'s `client_id`.
    pub fn claim(&mut self, client: u64) {
        self.holder = client;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_holder_may_write_and_hand_off() {
        let mut t = ControlToken::new(1);
        assert!(t.may_write(1));
        assert!(t.is_read_only(2));
        assert_eq!(t.check(1), Ok(()));
        assert_eq!(
            t.check(2),
            Err(EngineError::NotHolder {
                holder: 1,
                client: 2
            })
        );

        // A non-holder cannot grant itself (or anyone) the keyboard.
        assert_eq!(
            t.grant(2, 2),
            Err(EngineError::NotHolder {
                holder: 1,
                client: 2
            })
        );
        assert_eq!(t.holder(), 1, "a refused grant leaves the holder unchanged");

        // The holder hands off; the old holder is now read-only.
        assert_eq!(t.grant(1, 2), Ok(()));
        assert!(t.is_read_only(1));
        assert!(t.may_write(2));
        assert_eq!(t.holder(), 2);
    }

    #[test]
    fn claim_seizes_control_unconditionally() {
        let mut t = ControlToken::new(1);
        t.claim(3);
        assert_eq!(t.holder(), 3);
        assert!(t.is_read_only(1));
        // ... and the new holder can hand it back.
        assert_eq!(t.grant(3, 1), Ok(()));
        assert_eq!(t.holder(), 1);
    }
}
