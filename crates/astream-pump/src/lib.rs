#![forbid(unsafe_code)]
//! `astream-pump` — the drive-pipe **pump**.
//!
//! The pump owns the block-forever end of the bus so a *turn-based* driving
//! agent does not have to. It holds a broker `SUBSCRIBE` on a target terminal
//! session's `/out` subtree, feeds each delivered `Out` record to
//! [`astream_term`]'s streaming [`EventClassifier`], and surfaces the **semantic
//! wake boundaries** — prompt-ready, command-start, command-end (+exit),
//! screen-quiescence — that the agent acts on.
//!
//! astream deliberately stops at a socket that blocks until an event, and the
//! entity that blocks is a *thread*, not an agent turn (`DESIGN-drive-pipe.md`
//! §5). The pump is that thread: [`Pump::next_wake`] is the no-poll wait (the broker
//! `recv` parks on a `Condvar` tail until a publish); [`Pump::quiesce`] is the
//! debounce boundary; and the events they return are what an outer runner turns
//! into an agent wake (a hook, a resumed turn, a queued task).
//!
//! **Subjects.** [`out_subject`] is the built PTY face
//! (`/a/stream/term/<sid>/out`) and stays the default, but the pump is not
//! bound to it: [`Pump::attach_subject`] takes an arbitrary subject, so a
//! fabric node's `/f/<F>/term/<node>/<sid>/out` face
//! (`DESIGN-aterm-fabric.md` §3.3) pumps through exactly the same code.
//!
//! **Cursors.** Two forms, and the difference is *where the read position
//! lives*:
//!
//! - [`Pump::attach`] / [`Pump::attach_subject`] — a **client-held** cursor. The
//!   broker delivers from `from_offset` **inclusive**, so a restarted pump
//!   resumes gaplessly and without re-delivering its last wake by attaching at
//!   [`Pump::next_offset`], not at [`Pump::offset`]. Get that argument wrong and
//!   you miss or double a boundary; nothing on the broker remembers for you.
//! - [`Pump::attach_group`] — a **broker-durable** cursor. The pump subscribes as
//!   a consumer group and calls [`Pump::commit`] once every wake that delivery
//!   can still produce is out — its marks AND the settle wakes [`Pump::quiesce`]
//!   fires at its offset, a trap [`Pump::commit`] spells out; the next pump for
//!   that group resumes from `committed + 1` with no offset argument at all.
//!   The two contracts agree by construction: `commit()` commits *through*
//!   [`Pump::offset`] (inclusive), so the group's next start is exactly
//!   [`Pump::next_offset`].
//!
//! **Offsets.** [`Pump::offset`] is the broker offset of the most recent
//! delivery — where a woken agent reads the target's screen (today by folding
//! `/out` through it; the designed `/a/state/term/<sid>/screen` snapshot is not
//! yet published by anything on the bus).

use std::io::{self, Read, Write};

use astream_broker::{Client, Subscription};
use astream_term::events::{EventClassifier, Profile, SessionEvent};
use astream_term::record::Record;

/// The subject subtree a target session publishes its PTY output to (the lash's
/// `/out` face). `<sid>` is the session id.
#[must_use]
pub fn out_subject(sid: &str) -> String {
    format!("/a/stream/term/{sid}/out")
}

/// The one-line rendering of a wake — `<KIND> boffset=<broker-offset> [exit=E]`
/// — that `aspump` prints and a shell/bridge parses. `boffset` is the broker
/// offset of the `/out` record that produced the event, i.e. where the woken
/// agent reads the target's screen.
///
/// It lives in the library, not the binary, so a wake rendered by an embedder is
/// byte-identical to the CLI's line.
#[must_use]
pub fn wake_line(ev: &SessionEvent, boffset: u64) -> String {
    match ev {
        SessionEvent::PromptReady { .. } => format!("PROMPT_READY boffset={boffset}"),
        SessionEvent::CommandStart { .. } => format!("COMMAND_START boffset={boffset}"),
        SessionEvent::CommandEnd { exit, .. } => match exit {
            Some(e) => format!("COMMAND_END boffset={boffset} exit={e}"),
            None => format!("COMMAND_END boffset={boffset}"),
        },
        SessionEvent::Quiesced { .. } => format!("QUIESCED boffset={boffset}"),
    }
}

// The durable half of a group attach. `SubscribeGroup` consumes its connection
// into a one-way delivery stream — the broker enters its tail loop and never
// reads another request on it — so a commit MUST travel on a second connection.
// That is why `attach_group` takes two clients rather than one.
struct GroupCursor<S: Read + Write> {
    commits: Client<S>,
    group: String,
    committed: Option<u64>,
}

/// A live pump attached to one target session's output stream.
pub struct Pump<S: Read + Write> {
    sub: Subscription<S>,
    classifier: EventClassifier,
    from: u64,
    // The broker offset of the most recent delivery; `None` until the first.
    last: Option<u64>,
    // `Some` only for a group attach: the durable cursor's commit channel.
    cursor: Option<GroupCursor<S>>,
}

impl<S: Read + Write> Pump<S> {
    /// Attach to `sid`'s built `/out` stream ([`out_subject`]) from `from_offset`
    /// **inclusive**. Shorthand for [`Pump::attach_subject`] on that subject.
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach(
        client: Client<S>,
        sid: &str,
        from_offset: u64,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        Self::attach_subject(client, &out_subject(sid), from_offset, cols, rows, profile)
    }

    /// Attach to an ARBITRARY `subject` from `from_offset` **inclusive** — the
    /// broker delivers every record at or after it — classifying it as a
    /// `cols`x`rows` session under `profile`. Consumes `client` into the
    /// subscription (one stream per connection).
    ///
    /// This is the general form. The built PTY face is `/a/stream/term/<sid>/out`
    /// ([`Pump::attach`]); a fabric node's face is
    /// `/f/<F>/term/<node>/<sid>/out`. The pump classifies whatever `Out` bytes
    /// the subject carries — it reads no meaning from the subject's shape, and
    /// `subject` may be any filter the broker accepts.
    ///
    /// **Resume contract.** [`Pump::offset`] names the record most recently
    /// delivered, so re-attaching *at* it delivers that record — and any wake it
    /// carries — a second time. To continue a stream after a pump stopped,
    /// attach at its [`Pump::next_offset`] (`offset() + 1`), or use
    /// [`Pump::attach_group`] and let the broker hold the cursor. The classifier
    /// starts from a blank screen at the attach point: OSC marks are exact from
    /// the first delivery, while the settle/glyph signals describe only what has
    /// been painted since.
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach_subject(
        client: Client<S>,
        subject: &str,
        from_offset: u64,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        let sub = client.subscribe(from_offset, subject)?;
        Ok(Pump {
            sub,
            classifier: EventClassifier::new(cols, rows, profile),
            from: from_offset,
            last: None,
            cursor: None,
        })
    }

    /// Attach to `subject` as consumer **`group`** — the DURABLE cursor. The
    /// broker resumes delivery from the group's committed offset (`committed + 1`,
    /// or 0 for a group that has never committed), so the read position lives on
    /// the broker and survives a pump restart: the replacement pump passes no
    /// offset at all and cannot get it wrong.
    ///
    /// Takes **two** connections because `SubscribeGroup` turns its own
    /// connection into a one-way delivery stream: `client` becomes the
    /// subscription, `commits` carries every [`Pump::commit`]. Under a
    /// capability-guarded broker both must already be attached, and the grant
    /// must cover the group name as a subject as well as the filter.
    ///
    /// **Resume contract**, consistent with the offset form: `commit()` commits
    /// *through* [`Pump::offset`] (the broker's `upto` is inclusive), so the
    /// group's next start is exactly [`Pump::next_offset`]. A wake that is
    /// delivered but not committed before the pump dies is re-delivered — the
    /// group is at-least-once on wakes, and the commit point is the caller's
    /// choice of "acted on".
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach_group(
        client: Client<S>,
        commits: Client<S>,
        group: &str,
        subject: &str,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        let sub = client.subscribe_group(group, subject)?;
        Ok(Pump {
            sub,
            classifier: EventClassifier::new(cols, rows, profile),
            // The start is the broker's to know, not ours; `offset()` before the
            // first delivery therefore reports 0 as a placeholder, NOT the
            // group's committed cursor (see `offset`).
            from: 0,
            last: None,
            cursor: Some(GroupCursor {
                commits,
                group: group.to_string(),
                committed: None,
            }),
        })
    }

    /// Block for the next `Out` delivery and classify it, returning the wake
    /// events it produced (often empty — a delivery that carries no boundary).
    /// `None` at end of stream. This is the pump's **no-poll wait**: the broker
    /// `recv` parks until a publish advances the log.
    ///
    /// An event's `offset` is the classifier's record index (`0` for the first
    /// delivery after attach); the broker offset the delivery sits at — the one
    /// a woken agent uses — is [`Pump::offset`].
    ///
    /// # Errors
    /// Propagates the broker's delivery I/O error — including a broker-side
    /// rejection of the subscription, which arrives as the first result.
    pub fn next_wake(&mut self) -> io::Result<Option<Vec<SessionEvent>>> {
        match self.sub.recv()? {
            Some((offset, _subject, body)) => {
                self.last = Some(offset);
                Ok(Some(self.classifier.push(&Record::Out(body))))
            }
            None => Ok(None),
        }
    }

    /// Signal that the debounce window elapsed with no new output: emit the
    /// settled-screen wakes (`Quiesced`, and a glyph `PromptReady` when the
    /// target has shown no shell integration).
    pub fn quiesce(&mut self) -> Vec<SessionEvent> {
        self.classifier.quiesce()
    }

    /// Durably advance this pump's group cursor **through** [`Pump::offset`] —
    /// the delivery just acted on. Returns the offset committed through, or
    /// `Ok(None)` when nothing has been delivered yet (there is no record to
    /// commit, and committing 0 would falsely claim record 0 was handled).
    ///
    /// The broker's `upto` is inclusive, so the next pump on this group starts at
    /// [`Pump::next_offset`]. The returned value is the *committed* offset, not
    /// the commit record's own log offset — those live in different spaces and
    /// the latter must never be used to resume.
    ///
    /// **When to call it.** Not merely after [`Pump::next_wake`] has been acted
    /// on: [`Pump::quiesce`] fires its settle wakes (`Quiesced`, and the glyph
    /// `PromptReady` for an unintegrated target) at the offset of the delivery
    /// that ended the burst, out of the classifier's screen state rather than out
    /// of any record. Commit that delivery before its settle window has closed —
    /// before the debounce fires, or before a later delivery supersedes it — and a
    /// pump that dies in between takes the boundary with it: the replacement
    /// resumes past the record, is delivered nothing, and its `quiesce()` (nothing
    /// pushed) yields nothing. `aspump` therefore holds each delivery's commit
    /// until exactly that point.
    ///
    /// # Errors
    /// [`io::ErrorKind::Unsupported`] for a pump attached with
    /// [`Pump::attach`]/[`Pump::attach_subject`]: it has no group, and its cursor
    /// lives in the pump process by construction. Otherwise propagates the
    /// broker's commit I/O error.
    pub fn commit(&mut self) -> io::Result<Option<u64>> {
        let last = self.last;
        let Some(cursor) = self.cursor.as_mut() else {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "pump has no durable cursor: attach_group is the committing form; attach/attach_subject hold the cursor in the pump process",
            ));
        };
        let Some(upto) = last else {
            return Ok(None);
        };
        if cursor.committed == Some(upto) {
            // Nothing delivered since the last commit: the group is already there,
            // and committing again would only append a redundant commit record.
            return Ok(Some(upto));
        }
        cursor.commits.commit(&cursor.group, upto)?;
        cursor.committed = Some(upto);
        Ok(Some(upto))
    }

    /// The consumer group this pump's durable cursor lives under, or `None` for
    /// the client-held-offset form.
    #[must_use]
    pub fn group(&self) -> Option<&str> {
        self.cursor.as_ref().map(|c| c.group.as_str())
    }

    /// The offset this pump has durably committed **through**, or `None` if it
    /// has committed nothing (including every non-group pump). This is the
    /// pump's own record of its commits, not a query of the broker's cursor.
    #[must_use]
    pub fn committed(&self) -> Option<u64> {
        self.cursor.as_ref().and_then(|c| c.committed)
    }

    /// The broker offset of the most recent delivery — where a woken agent reads
    /// the target's screen. Before the first delivery this is the attach offset
    /// `from_offset`, which is not a delivered record; for a group attach, where
    /// the start is the broker's to know, it is `0` as a placeholder — never read
    /// it as the group's committed cursor.
    #[must_use]
    pub fn offset(&self) -> u64 {
        self.last.unwrap_or(self.from)
    }

    /// The offset a restarted pump attaches from to continue this stream with no
    /// gap and no re-delivery: one past the most recent delivery, or
    /// `from_offset` while nothing has been delivered yet (for a group attach, the
    /// same `0` placeholder as [`Pump::offset`]). It is also exactly the offset a
    /// group resumes at once [`Pump::commit`] has run.
    #[must_use]
    pub fn next_offset(&self) -> u64 {
        self.last.map_or(self.from, |o| o.saturating_add(1))
    }
}
