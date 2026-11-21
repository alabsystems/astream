// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE SIGNAL TABLE (aterm tracker AF-15): the newest value of each subject a producer
//! SIGNALS, held in memory only. A signal is a volatile last-value publish
//! ([`Request::Signal`](crate::proto::Request::Signal)): it appends nothing to the log,
//! is in no `Fetch`, `Last`, `Subscribe`, replication link or bridge, and is gone when the
//! connection that sent it ends, or the broker stops.
//!
//! The table is pure: no I/O, no lock, no clock. The broker keeps one behind a leaf lock
//! (`signal_serve.rs`, mounted as `broker::signal_serve`) and every caller passes the
//! instant it judges by.
//!
//! WHAT A PUT DOES. One row per subject. A put replaces the row in place and moves it to a
//! new VERSION, a count of effective puts, so a reader that remembers the last version it
//! took reads each subject at most once however many times it was overwritten meanwhile:
//! that is the whole of conflation, and there is no queue per reader to bound.
//!
//! WHOSE ROW IT IS. A row belongs to the connection that last put it, and
//! [`drop_conn`](SignalTable::drop_conn) removes what a connection still owns. A put from
//! the owning connection always replaces, whatever its `seq`: one connection's puts arrive
//! in the order it sent them, and a producer republishes an unchanged value at an unchanged
//! `seq` to say it is still there. A put from ANOTHER connection under the same producer id
//! replaces only at a `seq` not below the row's, so the late bytes of a producer's earlier
//! incarnation cannot shadow the one that replaced it; at an EQUAL `seq` the NEWER
//! connection holds the row (connection ids only rise), which is a producer that
//! reconnected inside one incarnation while the broker still holds its dead connection. The
//! newer connection takes the row, and the older one's late bytes cannot take it back: were
//! they let to, the older connection's end would then remove a value its live successor
//! believes is held. So a producer that signals ONE subject from TWO live connections at
//! one `seq` has the older connection's puts acknowledged and dropped while the newer one
//! holds the row. Another producer id on the subject is last writer wins.
//!
//! WHEN ITS AUTHORITY ENDS. A row carries the instant the authority that admitted it
//! lapses (`until`, `u64::MAX` for none): a row at or past it is never taken, and is
//! removed by the take that meets it. A reader that is caught up meets none, so the broker
//! also drops them ([`drop_lapsed`](SignalTable::drop_lapsed)) before a put that a bound
//! would refuse ([`at_bound`](SignalTable::at_bound)): a row served to nobody holds no
//! room against a live one. Revocation is the broker's to judge
//! ([`drop_where`](SignalTable::drop_where)).

use astream_wire::Filter;
use std::collections::{BTreeMap, HashMap};
use std::ops::Bound;
use std::sync::Arc;

/// The largest body one signal may carry. A signal is a small current value (a cursor, a
/// presence row), never a transfer; a larger one is refused
/// ([`ERR_RECORD_REFUSED`](crate::proto::ERR_RECORD_REFUSED)).
pub const MAX_SIGNAL_BODY: usize = 64 * 1024;

/// How many subjects the table holds, broker-wide.
pub const MAX_SIGNAL_SUBJECTS: usize = 4096;

/// How many subjects one connection may own at once.
pub const MAX_SIGNAL_SUBJECTS_PER_CONN: usize = 64;

/// The bytes (each row's subject and body) the table holds, broker-wide.
pub const MAX_SIGNAL_BYTES: usize = 4 * 1024 * 1024;

/// The bytes (each row's subject and body) one connection may own at once: a sixteenth of
/// [`MAX_SIGNAL_BYTES`], so no one connection can fill the table against the others.
pub const MAX_SIGNAL_BYTES_PER_CONN: usize = 256 * 1024;

/// One row as a reader takes it: shared, so a take copies no body under the lock.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SignalRow {
    pub(crate) producer_id: u64,
    pub(crate) seq: u64,
    pub(crate) subject: Arc<str>,
    pub(crate) body: Arc<[u8]>,
}

/// What an admitted put did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Put {
    /// The row was replaced (or made) and moved to a new version: every reader takes it.
    Changed,
    /// Another connection of the same producer holds the subject at a higher `seq`, or at
    /// this `seq` and is the newer connection: nothing changed. Acknowledged, since to the
    /// late bytes of an earlier incarnation or of a connection left behind it is no error.
    Stale,
}

/// Why a put was refused. Nothing was kept.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SignalRefusal {
    /// The body is past [`MAX_SIGNAL_BODY`].
    BodyTooLarge { len: usize },
    /// The connection already owns [`MAX_SIGNAL_SUBJECTS_PER_CONN`] subjects.
    ConnSubjects,
    /// The connection's rows would pass [`MAX_SIGNAL_BYTES_PER_CONN`].
    ConnBytes,
    /// The table already holds [`MAX_SIGNAL_SUBJECTS`] subjects.
    TableSubjects,
    /// The table's rows would pass [`MAX_SIGNAL_BYTES`].
    TableBytes,
    /// The version count is spent (`u64::MAX` effective puts since the broker opened).
    Versions,
}

impl SignalRefusal {
    /// Whether this is a bound of the table that dropping rows could lift.
    const fn is_bound(&self) -> bool {
        match self {
            SignalRefusal::ConnSubjects
            | SignalRefusal::ConnBytes
            | SignalRefusal::TableSubjects
            | SignalRefusal::TableBytes => true,
            SignalRefusal::BodyTooLarge { .. } | SignalRefusal::Versions => false,
        }
    }

    /// The refusal's class on the wire. A body too large is the request's own fault and
    /// permanent; every bound is a state of the table that a later put may find lifted.
    pub(crate) const fn code(&self) -> u8 {
        match self {
            SignalRefusal::BodyTooLarge { .. } => crate::proto::ERR_RECORD_REFUSED,
            SignalRefusal::ConnSubjects
            | SignalRefusal::ConnBytes
            | SignalRefusal::TableSubjects
            | SignalRefusal::TableBytes
            | SignalRefusal::Versions => crate::proto::ERR_REFUSED,
        }
    }

    /// The refusal in words.
    pub(crate) fn message(&self) -> String {
        match self {
            SignalRefusal::BodyTooLarge { len } => {
                format!("signal body too large: {len} bytes (limit {MAX_SIGNAL_BODY})")
            }
            SignalRefusal::ConnSubjects => format!(
                "signal refused: this connection already holds {MAX_SIGNAL_SUBJECTS_PER_CONN} subjects"
            ),
            SignalRefusal::ConnBytes => format!(
                "signal refused: this connection's signals would pass {MAX_SIGNAL_BYTES_PER_CONN} bytes"
            ),
            SignalRefusal::TableSubjects => {
                format!("signal refused: the broker already holds {MAX_SIGNAL_SUBJECTS} signal subjects")
            }
            SignalRefusal::TableBytes => {
                format!("signal refused: the broker's signals would pass {MAX_SIGNAL_BYTES} bytes")
            }
            SignalRefusal::Versions => "signal refused: the signal version count is spent".to_string(),
        }
    }
}

/// A row as the table holds it.
struct Entry {
    /// The version of the put that made it: its key in `by_ver`.
    ver: u64,
    /// The connection that owns it.
    conn: u64,
    producer_id: u64,
    seq: u64,
    /// The unix-ms instant its authority lapses; `u64::MAX`: never.
    until: u64,
    body: Arc<[u8]>,
}

/// What one connection owns.
#[derive(Clone, Copy, Default)]
struct ConnUse {
    subjects: usize,
    bytes: usize,
}

/// What an admitted put leaves the table holding.
struct Admitted {
    /// What the putting connection then owns.
    own: ConnUse,
    /// The table's bytes.
    bytes: usize,
    /// The version the row moves to.
    version: u64,
}

/// The newest signalled value of each subject (see the module docs).
pub(crate) struct SignalTable {
    rows: HashMap<Arc<str>, Entry>,
    /// Every row by the version of its last put: what a take walks, oldest change first.
    by_ver: BTreeMap<u64, Arc<str>>,
    per_conn: HashMap<u64, ConnUse>,
    /// The version of the newest effective put.
    version: u64,
    /// Subject and body bytes over every row.
    bytes: usize,
    /// How many rows carry an instant their authority lapses at.
    timed: usize,
}

/// The bytes a row is charged: its subject and its body.
const fn row_cost(subject_len: usize, body_len: usize) -> usize {
    subject_len.saturating_add(body_len)
}

impl SignalTable {
    pub(crate) fn new() -> SignalTable {
        SignalTable {
            rows: HashMap::new(),
            by_ver: BTreeMap::new(),
            per_conn: HashMap::new(),
            version: 0,
            bytes: 0,
            timed: 0,
        }
    }

    /// What a put of `body_len` bytes as `subject` by connection `conn` would leave the
    /// table holding, every bound of the table judged, and nothing changed.
    fn admit(&self, conn: u64, subject: &str, body_len: usize) -> Result<Admitted, SignalRefusal> {
        let cost = row_cost(subject.len(), body_len);
        // What the subject holds now: its owner and the bytes it is charged.
        let held = self
            .rows
            .get(subject)
            .map(|e| (e.conn, row_cost(subject.len(), e.body.len())));
        let own = match self.per_conn.get(&conn) {
            Some(u) => *u,
            None => ConnUse::default(),
        };
        let own = match held {
            Some((owner, old_cost)) if owner == conn => ConnUse {
                subjects: own.subjects,
                bytes: own.bytes.saturating_sub(old_cost).saturating_add(cost),
            },
            _ => ConnUse {
                subjects: own.subjects.saturating_add(1),
                bytes: own.bytes.saturating_add(cost),
            },
        };
        if own.subjects > MAX_SIGNAL_SUBJECTS_PER_CONN {
            return Err(SignalRefusal::ConnSubjects);
        }
        if own.bytes > MAX_SIGNAL_BYTES_PER_CONN {
            return Err(SignalRefusal::ConnBytes);
        }
        if held.is_none() && self.rows.len() >= MAX_SIGNAL_SUBJECTS {
            return Err(SignalRefusal::TableSubjects);
        }
        let old_cost = match held {
            Some((_, old_cost)) => old_cost,
            None => 0,
        };
        let bytes = self.bytes.saturating_sub(old_cost).saturating_add(cost);
        if bytes > MAX_SIGNAL_BYTES {
            return Err(SignalRefusal::TableBytes);
        }
        let Some(version) = self.version.checked_add(1) else {
            return Err(SignalRefusal::Versions);
        };
        Ok(Admitted {
            own,
            bytes,
            version,
        })
    }

    /// Whether a put of `body_len` bytes as `subject` by connection `conn` would be refused
    /// at a bound of the table (this connection's subjects or bytes, the table's): the one
    /// refusal dropping rows could lift, so the broker drops the lapsed ones
    /// ([`drop_lapsed`](Self::drop_lapsed)) and the put is then judged on what is left.
    pub(crate) fn at_bound(&self, conn: u64, subject: &str, body_len: usize) -> bool {
        match self.admit(conn, subject, body_len) {
            Ok(_) => false,
            Err(why) => why.is_bound(),
        }
    }

    /// Put `body` as `subject`'s value for connection `conn`, under `(producer_id, seq)`,
    /// its authority lapsing at `until`. Every bound is judged before anything changes, so
    /// a refused put leaves the table as it was.
    pub(crate) fn put(
        &mut self,
        conn: u64,
        producer_id: u64,
        seq: u64,
        until: u64,
        subject: &str,
        body: Vec<u8>,
    ) -> Result<Put, SignalRefusal> {
        if body.len() > MAX_SIGNAL_BODY {
            return Err(SignalRefusal::BodyTooLarge { len: body.len() });
        }
        // Another connection of the same producer holds the subject at a higher `seq`, or
        // at this one and is the newer connection (ids only rise): these are the late bytes
        // of an earlier incarnation, or of a connection its producer left behind.
        if let Some(e) = self.rows.get(subject) {
            if e.producer_id == producer_id
                && e.conn != conn
                && (seq < e.seq || (seq == e.seq && conn < e.conn))
            {
                return Ok(Put::Stale);
            }
        }
        let Admitted {
            own,
            bytes,
            version,
        } = self.admit(conn, subject, body.len())?;

        // Admitted: from here on nothing fails.
        let key: Arc<str> = match self.rows.remove_entry(subject) {
            Some((key, old)) => {
                if old.conn != conn {
                    self.release(old.conn, row_cost(subject.len(), old.body.len()));
                }
                if old.until != u64::MAX {
                    self.timed = self.timed.saturating_sub(1);
                }
                self.by_ver.remove(&old.ver);
                key
            }
            None => Arc::from(subject),
        };
        self.per_conn.insert(conn, own);
        self.bytes = bytes;
        self.version = version;
        if until != u64::MAX {
            self.timed = self.timed.saturating_add(1);
        }
        self.by_ver.insert(version, Arc::clone(&key));
        self.rows.insert(
            key,
            Entry {
                ver: version,
                conn,
                producer_id,
                seq,
                until,
                body: Arc::from(body),
            },
        );
        Ok(Put::Changed)
    }

    /// Take one row of `old_cost` bytes off what `conn` owns.
    fn release(&mut self, conn: u64, old_cost: usize) {
        let left = match self.per_conn.get(&conn) {
            Some(u) => ConnUse {
                subjects: u.subjects.saturating_sub(1),
                bytes: u.bytes.saturating_sub(old_cost),
            },
            None => return,
        };
        if left.subjects == 0 {
            self.per_conn.remove(&conn);
        } else {
            self.per_conn.insert(conn, left);
        }
    }

    /// Remove `subject`'s row, with its accounting.
    fn remove(&mut self, subject: &str) {
        let Some(e) = self.rows.remove(subject) else {
            return;
        };
        let cost = row_cost(subject.len(), e.body.len());
        self.by_ver.remove(&e.ver);
        self.bytes = self.bytes.saturating_sub(cost);
        if e.until != u64::MAX {
            self.timed = self.timed.saturating_sub(1);
        }
        self.release(e.conn, cost);
    }

    /// Remove every row `gone(conn, producer_id)` says to; how many went. No version moves:
    /// a reader is not told a row was withdrawn, it stops being republished.
    pub(crate) fn drop_where(&mut self, mut gone: impl FnMut(u64, u64) -> bool) -> usize {
        let mut subjects: Vec<Arc<str>> = Vec::new();
        for (subject, e) in &self.rows {
            if gone(e.conn, e.producer_id) {
                subjects.push(Arc::clone(subject));
            }
        }
        for subject in &subjects {
            self.remove(subject);
        }
        subjects.len()
    }

    /// Remove every row whose authority lapsed at or before `now`; how many went. No
    /// version moves, as for any withdrawal. Walks the table only where some row carries
    /// such an instant.
    pub(crate) fn drop_lapsed(&mut self, now: u64) -> usize {
        if self.timed == 0 {
            return 0;
        }
        let mut subjects: Vec<Arc<str>> = Vec::new();
        for (subject, e) in &self.rows {
            if e.until != u64::MAX && now >= e.until {
                subjects.push(Arc::clone(subject));
            }
        }
        for subject in &subjects {
            self.remove(subject);
        }
        subjects.len()
    }

    /// Remove every row connection `conn` still owns; how many went.
    pub(crate) fn drop_conn(&mut self, conn: u64) -> usize {
        if !self.per_conn.contains_key(&conn) {
            return 0;
        }
        self.drop_where(|owner, _| owner == conn)
    }

    /// Whether `conn` owns any row.
    pub(crate) fn owns(&self, conn: u64) -> bool {
        self.per_conn.contains_key(&conn)
    }

    /// Each row's `(owning connection, producer id)`, for the broker's revocation sweep.
    pub(crate) fn owners(&self) -> Vec<(u64, u64)> {
        let mut out = Vec::new();
        for e in self.rows.values() {
            out.push((e.conn, e.producer_id));
        }
        out
    }

    /// Whether any row carries an instant its authority lapses at: a take over a table
    /// with none reads no clock.
    pub(crate) const fn has_deadlines(&self) -> bool {
        self.timed > 0
    }

    /// Whether a reader at `seen` has taken every row there is to take.
    pub(crate) const fn caught_up(&self, seen: u64) -> bool {
        seen >= self.version
    }

    /// The rows put after version `*seen` that `filter` matches, oldest change first, and
    /// `*seen` moved past every row visited, matched or not. Stops once the rows gathered
    /// hold `max_bytes`, so one hold of the broker's lock copies a bounded page; the next
    /// take resumes there. A row whose authority lapsed at or before `now` is not taken,
    /// and is removed.
    pub(crate) fn take_after(
        &mut self,
        seen: &mut u64,
        filter: &Filter,
        max_bytes: usize,
        now: u64,
    ) -> Vec<SignalRow> {
        let mut out = Vec::new();
        let mut lapsed: Vec<Arc<str>> = Vec::new();
        let mut gathered = 0usize;
        let mut full = false;
        for (ver, subject) in self
            .by_ver
            .range((Bound::Excluded(*seen), Bound::Unbounded))
        {
            *seen = *ver;
            let Some(e) = self.rows.get(subject) else {
                continue;
            };
            if e.until != u64::MAX && now >= e.until {
                lapsed.push(Arc::clone(subject));
                continue;
            }
            if !filter.matches_str(subject) {
                continue;
            }
            gathered = gathered.saturating_add(row_cost(subject.len(), e.body.len()));
            out.push(SignalRow {
                producer_id: e.producer_id,
                seq: e.seq,
                subject: Arc::clone(subject),
                body: Arc::clone(&e.body),
            });
            if gathered >= max_bytes {
                full = true;
                break;
            }
        }
        if !full {
            *seen = self.version;
        }
        for subject in &lapsed {
            self.remove(subject);
        }
        out
    }

    /// How many subjects the table holds.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.rows.len()
    }

    /// The bytes the table is charged.
    #[cfg(test)]
    pub(crate) const fn bytes(&self) -> usize {
        self.bytes
    }
}

#[cfg(test)]
#[path = "signal_tests.rs"]
mod tests;
