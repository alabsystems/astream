// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SIGNALS ON THE WIRE (aterm tracker AF-15): how the broker serves
//! [`Request::Signal`], a volatile last-value publish, and [`Request::SubscribeSignals`],
//! the stream that reads them. The table itself is `crate::signal`; this is the lock it
//! sits behind, the request, the stream and the three ways a row leaves it.
//!
//! NOT THE LOG. Nothing here touches `Shared::writes`, `Shared::log` or the writer thread:
//! a signal is acknowledged from the request loop, and no file changes. No bridge, replica,
//! `Fetch`, `Last`, `Subscribe`, `Stats` or health file reads the table, so a signal reaches
//! another machine only by its producer connecting there.
//!
//! A ROW LEAVES when its connection ends ([`drop_conn_signals`], from `ConnGuard`), when the
//! authority that admitted it lapses (its `until`, judged by each take, and by a put that
//! a bound would otherwise refuse), or when a revocation takes that authority
//! ([`sweep_revoked_signals`]): the peer's key, its certificate, or the principal its
//! producer id is bound to. The broker stopping takes them all, since the table is memory.
//! A reader is not told: the value stops being republished, and the reader ages it by its
//! own clock, which also covers a partition where no withdrawal could arrive.
//!
//! WHEN A CONNECTION IS SEEN TO END. A closed socket is an EOF on every transport. A TCP
//! peer that vanished without a FIN is noticed by the keepalive read deadline, which a kept
//! signal arms ([`serve_signal`]), and that deadline is the REQUEST LOOP's: a connection
//! that goes on to become a stream is read no more (its stream replaces the read timeout
//! with the peer probe's), so from then on such a peer is noticed only by a stream write
//! that fails, and the rows the connection owns last as long as its stream does. The same
//! holds for a `Keepalive` followed by a `Subscribe`. A producer keeps the connection it
//! signals on apart from its streams.
//!
//! A SLOW READER holds no queue. Each stream keeps one number, the table version it has
//! taken to, and takes what was put after it, a bounded page per hold of the lock. A subject
//! overwritten while the stream was blocked in a socket write has moved to a newer version,
//! so the stream reads it once, at its newest value.

use super::*;
use crate::proto::encode_signal;
use crate::signal::{Put, SignalTable};

/// The broker's signals, behind `Shared::signals`.
pub(super) struct Signals {
    table: SignalTable,
    /// The peer each owning connection authenticated as, where it authenticated as any:
    /// what a revocation sweep judges a connection by. A plain or Unix-socket connection
    /// has none and is not here.
    peers: HashMap<u64, PeerAuth>,
}

impl Signals {
    pub(super) fn new() -> Signals {
        Signals {
            table: SignalTable::new(),
            peers: HashMap::new(),
        }
    }

    /// How many subjects are held.
    #[cfg(all(test, unix))]
    pub(super) fn len(&self) -> usize {
        self.table.len()
    }
}

/// One [`Request::Signal`], as decoded.
pub(super) struct SignalPut {
    pub(super) producer_id: u64,
    pub(super) seq: u64,
    pub(super) subject: String,
    pub(super) body: Vec<u8>,
}

/// Whether `peer` proved anything a revocation could name.
const fn revocable(peer: &PeerAuth) -> bool {
    peer.pubkey.is_some() || peer.cert_serial.is_some() || peer.cert_principal_lower.is_some()
}

fn lock_signals(shared: &Shared) -> std::sync::MutexGuard<'_, Signals> {
    shared
        .signals
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Serve one [`Request::Signal`]: judge it, put it, wake the streams, answer a `Mark`.
/// Answered in the request loop after the connection's pending acks, as `Keepalive` is, so
/// the answer is in send order. `until` is when the request's authority lapses, kept with
/// the row.
#[allow(clippy::too_many_arguments)]
pub(super) fn serve_signal(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    wire: Wire,
    conn_id: u64,
    peer: &PeerAuth,
    until: u64,
    put: SignalPut,
) -> io::Result<bool> {
    let SignalPut {
        producer_id,
        seq,
        subject,
        body,
    } = put;
    finish_pipe(pipe)?;
    if let Some(err) = publish_subject_error(&subject) {
        return emit(stream, pipe, Err(err));
    }
    // The broker's own subtree holds no client's value, volatile or not.
    if subject == "/a" || subject.starts_with("/a/") {
        return emit(
            stream,
            pipe,
            Err(refusal(ERR_RECORD_REFUSED, reserved_msg(&subject))),
        );
    }
    if let Err(err) = check_publish_rate_limit(
        shared,
        producer_id,
        subject.len().saturating_add(body.len()),
    ) {
        return emit(stream, pipe, Err(err));
    }
    let res = {
        let mut signals = lock_signals(shared);
        // A row past its authority's instant is served to nobody, and leaves only when a
        // take meets it, which a caught-up stream never does: before a bound refuses this
        // put, drop those. A table with no deadline in it reads no clock.
        if signals.table.has_deadlines()
            && signals.table.at_bound(conn_id, &subject, body.len())
            && signals.table.drop_lapsed(now_unix_ms()) > 0
        {
            let Signals { table, peers } = &mut *signals;
            peers.retain(|conn, _| table.owns(*conn));
        }
        let res = signals
            .table
            .put(conn_id, producer_id, seq, until, &subject, body);
        if res == Ok(Put::Changed) && revocable(peer) && !signals.peers.contains_key(&conn_id) {
            signals.peers.insert(conn_id, peer.clone());
        }
        res
    };
    match res {
        Err(why) => emit(stream, pipe, Err(refusal(why.code(), why.message()))),
        Ok(Put::Stale) => {
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Ok(Put::Changed) => {
            // A revocation that landed between this request's gate and its put found no
            // row to sweep: judge the authority again now the row is there. One that lands
            // after this moves the epoch, and the next sweep finds the row.
            if let Some(why) = revoked_authority(shared, peer, producer_id) {
                let mut signals = lock_signals(shared);
                signals
                    .table
                    .drop_where(|conn, producer| conn == conn_id && producer == producer_id);
                if !signals.table.owns(conn_id) {
                    signals.peers.remove(&conn_id);
                }
                drop(signals);
                return emit(stream, pipe, Err(refusal(ERR_UNAUTHORIZED, why)));
            }
            // The value now outlives this request, so the session must be seen to end: on
            // TCP a peer that vanished without a FIN is noticed only by a read deadline
            // (`KEEPALIVE_DEADLINE`), which this arms exactly as a `Keepalive` does, at the
            // deadline as it now stands. It bounds the request loop's reads alone: see the
            // module docs for a connection that then becomes a stream.
            if wire == Wire::Tcp {
                let deadline =
                    Duration::from_millis(shared.keepalive_deadline_ms.load(Ordering::Relaxed));
                let _ = stream.set_read_timeout(Some(deadline));
            }
            shared.signals_cv.notify_all();
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
    }
}

/// Why a signal `peer` put under `producer_id` has no authority now, if a revocation took
/// it: the peer's key, certificate or certificate principal, or (on a guarded broker) the
/// principal `producer_id` is bound to, as a pending `Will`'s is judged.
fn revoked_authority(shared: &Shared, peer: &PeerAuth, producer_id: u64) -> Option<&'static str> {
    if let Some(why) = peer_revocation_reason(shared, peer) {
        return Some(why);
    }
    if is_will_principal_revoked(shared, producer_id) {
        return Some("unauthorized: capability principal has been revoked");
    }
    None
}

/// Drop every row a revocation since the last sweep took the authority of. Cheap when
/// nothing was revoked since: two atomic reads. The judging takes the revocation locks with
/// the signals lock released, so `Shared::signals` stays a leaf.
fn sweep_revoked_signals(shared: &Shared) {
    maybe_reload_revocation_file(shared);
    let epoch = shared.revocation_epoch.load(Ordering::Acquire);
    if shared.signals_swept.load(Ordering::Acquire) >= epoch {
        return;
    }
    let (owners, peers) = {
        let signals = lock_signals(shared);
        (signals.table.owners(), signals.peers.clone())
    };
    let mut gone_conns: HashSet<u64> = HashSet::new();
    for (conn, peer) in &peers {
        if peer_revocation_reason_raw(shared, peer).is_some() {
            gone_conns.insert(*conn);
        }
    }
    let mut judged: HashSet<u64> = HashSet::new();
    let mut gone_producers: HashSet<u64> = HashSet::new();
    for (_, producer) in owners {
        if judged.insert(producer) && is_will_principal_revoked(shared, producer) {
            gone_producers.insert(producer);
        }
    }
    if !gone_conns.is_empty() || !gone_producers.is_empty() {
        let mut signals = lock_signals(shared);
        signals.table.drop_where(|conn, producer| {
            gone_conns.contains(&conn) || gone_producers.contains(&producer)
        });
        let Signals { table, peers } = &mut *signals;
        peers.retain(|conn, _| table.owns(*conn));
    }
    // The epoch read BEFORE the judging: a revocation that landed during it moved the
    // epoch past this, and the next sweep judges again.
    shared.signals_swept.fetch_max(epoch, Ordering::AcqRel);
}

/// A connection ended: every row it still owns goes with it.
pub(super) fn drop_conn_signals(shared: &Shared, conn_id: u64) {
    let mut signals = lock_signals(shared);
    signals.table.drop_conn(conn_id);
    signals.peers.remove(&conn_id);
}

/// TEST SEAM: the next signal stream to start stops once, after it has written the `Mark`
/// that closes its first drain, its table version sent on `reached`, until `resume` yields
/// (or its sender is gone). That is where a stream sits while a socket write its peer does
/// not drain holds it: the window in which a test overwrites a subject many times. Unix
/// only, as the wire tests that arm it are.
#[cfg(all(test, unix))]
pub(crate) struct SignalPause {
    pub(crate) reached: Sender<u64>,
    pub(crate) resume: Receiver<()>,
}

/// Hold a stream at its [`SignalPause`], once.
#[cfg(all(test, unix))]
fn pause_once(pause: &mut Option<SignalPause>, seen: u64) {
    let Some(p) = pause.take() else {
        return;
    };
    if p.reached.send(seen).is_ok() {
        let _ = p.resume.recv();
    }
}

/// Serve one [`Request::SubscribeSignals`] to the end of its connection: the current value
/// of every subject `filter` matches, a `Mark`, then each change, newest value only.
///
/// Every round judges the stream's own authority after it parks and before it takes
/// (`stream_failure`), so a lapsed or revoked grant never authorizes a delivery, and sweeps
/// the table for revoked producers before it reads it.
pub(super) fn signal_loop(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    filter: Filter,
    mut until: u64,
    peer: &PeerAuth,
    mut cap_check: StreamCapCheck,
) -> io::Result<()> {
    #[cfg(all(test, unix))]
    let mut pause = shared
        .signal_pause
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take();
    let _ = stream.set_read_timeout(Some(PEER_PROBE_TIMEOUT));
    let _ = stream.set_write_timeout(Some(stream_write_timeout(shared)));
    let liveness_poll = Duration::from_millis(shared.liveness_poll_ms.load(Ordering::Relaxed));
    let idle_mark = Duration::from_millis(shared.idle_mark_ms.load(Ordering::Relaxed));
    let mut out = Vec::new();
    // The table version this stream has taken to: its whole state.
    let mut seen: u64 = 0;
    // Whether the `Mark` that closes the first drain has gone.
    let mut marked = false;
    let mut wrote_at = Instant::now();
    let mut probed = Instant::now();
    loop {
        // Park while there is nothing to take. The predicate is read under the lock a put
        // changes the table under, so a put between "caught up" and "wait" is not missed;
        // a timeout is the liveness poll.
        {
            let signals = lock_signals(shared);
            if marked && signals.table.caught_up(seen) && shared.running.load(Ordering::Relaxed) {
                let park = match until {
                    u64::MAX => liveness_poll,
                    t => liveness_poll.min(Duration::from_millis(t.saturating_sub(now_unix_ms()))),
                };
                drop(
                    shared
                        .signals_cv
                        .wait_timeout(signals, park)
                        .unwrap_or_else(std::sync::PoisonError::into_inner),
                );
            }
        }
        if !shared.running.load(Ordering::Relaxed) {
            return Ok(());
        }
        if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
            return end_stream_failure(stream, &mut out, failure);
        }
        sweep_revoked_signals(shared);
        let (rows, caught_up) = {
            let mut signals = lock_signals(shared);
            // A table with no deadline in it reads no clock, as an unguarded tail reads none.
            let now = if signals.table.has_deadlines() {
                now_unix_ms()
            } else {
                0
            };
            let rows = signals
                .table
                .take_after(&mut seen, &filter, EGRESS_CHUNK, now);
            (rows, signals.table.caught_up(seen))
        };
        let wrote = !rows.is_empty();
        for row in &rows {
            append_frame(
                &mut out,
                &encode_signal(row.producer_id, row.seq, &row.subject, &row.body),
            )?;
            if out.len() >= EGRESS_CHUNK {
                flush_egress(stream, &mut out)?;
            }
        }
        flush_egress(stream, &mut out)?;
        if wrote {
            wrote_at = Instant::now();
        }
        // A `Mark` says the stream is there with nothing more to send: once when the reader
        // has every current value, then after each idle interval, so a reader on a dead link
        // hears silence and a write to a vanished reader fails.
        if caught_up && (!marked || wrote_at.elapsed() >= idle_mark) {
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            marked = true;
            wrote_at = Instant::now();
        }
        #[cfg(all(test, unix))]
        if marked {
            pause_once(&mut pause, seen);
        }
        if !wrote && probed.elapsed() >= liveness_poll {
            probed = Instant::now();
            if probe_peer(shared, stream) {
                return Ok(());
            }
        }
    }
}

#[cfg(all(test, unix))]
#[path = "signal_serve_tests.rs"]
mod tests;
